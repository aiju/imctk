use std::collections::hash_map::Entry;

use imctk_ids::{id_vec::IdVec, indexed_id_vec::IndexedIdVec, Id, Id32};
use imctk_ir::{
    env::Env,
    node::fine::circuit::{FineCircuitNodeBuilder, InitNode, Input, InputNode, RegNode},
    prelude::{NodeBuilder, Term, TermDyn},
    var::{Lit, Pol, Var},
};
use imctk_util::vec_sink::VecSink;
use zwohash::HashMap;

use crate::{env_multimap::LitMultimap, time_step::TimeStep};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct UnrolledInput {
    pub input: Input,
    pub step: TimeStep,
}

impl Term for UnrolledInput {
    type Output = Lit;

    const NAME: &'static str = "UnrolledInput";

    fn input_var_iter(&self) -> impl Iterator<Item = Var> + '_ {
        [].into_iter()
    }

    fn apply_var_map(&mut self, _var_map: impl FnMut(Var) -> Lit) -> Pol {
        Pol::Pos
    }

    fn is_steady(&self, _input_steady: impl Fn(Var) -> bool) -> bool {
        true
    }
}

impl TermDyn for UnrolledInput {}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct UnknownPast {
    pub seq: Var,
}

impl Term for UnknownPast {
    type Output = Lit;

    const NAME: &'static str = "UnknownPast";

    fn input_var_iter(&self) -> impl Iterator<Item = Var> + '_ {
        [].into_iter()
    }

    fn apply_var_map(&mut self, _var_map: impl FnMut(Var) -> Lit) -> Pol {
        Pol::Pos
    }

    fn is_steady(&self, _input_steady: impl Fn(Var) -> bool) -> bool {
        true
    }
}

impl TermDyn for UnknownPast {}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ReleaseReset {
    pub step: TimeStep,
}

impl Term for ReleaseReset {
    type Output = Lit;

    const NAME: &'static str = "ReleaseReset";

    fn input_var_iter(&self) -> impl Iterator<Item = Var> + '_ {
        [].into_iter()
    }

    fn apply_var_map(&mut self, _var_map: impl FnMut(Var) -> Lit) -> Pol {
        Pol::Pos
    }

    fn is_steady(&self, _input_steady: impl Fn(Var) -> bool) -> bool {
        true
    }
}

impl TermDyn for ReleaseReset {}

// In Induction and Hybrid mode, the first step contains everything that's steady and the second
// step contains the unconstrained past.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnrollMode {
    Bmc,
    Induction,
    Hybrid,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct SeqFromCombEntry {
    step: TimeStep,
    lit: Lit,
}

impl std::ops::BitXorAssign<Pol> for SeqFromCombEntry {
    fn bitxor_assign(&mut self, rhs: Pol) {
        self.lit ^= rhs;
    }
}

impl std::ops::BitXor<Pol> for &'_ SeqFromCombEntry {
    type Output = SeqFromCombEntry;

    fn bitxor(self, rhs: Pol) -> SeqFromCombEntry {
        SeqFromCombEntry {
            step: self.step,
            lit: self.lit ^ rhs,
        }
    }
}

pub struct Unroll {
    seen_from_seq: IndexedIdVec<Id32, Var>,
    comb_from_seen: IdVec<TimeStep, IdVec<Id32, Option<Lit>>>,
    seq_from_comb: LitMultimap<SeqFromCombEntry>,

    reset_released: IdVec<TimeStep, Lit>,

    mode: UnrollMode,

    spec_reduce_classes: Option<HashMap<Var, Lit>>,
    class_reprs: HashMap<(TimeStep, Var), (Lit, Lit)>,

    spec_reductions: Vec<(TimeStep, [Lit; 2], [Lit; 2])>,

    var_stack: Vec<Var>,
}

impl Unroll {
    pub fn new(mode: UnrollMode) -> Self {
        let mut new = Self {
            seen_from_seq: Default::default(),
            comb_from_seen: Default::default(),
            seq_from_comb: Default::default(),

            reset_released: Default::default(),

            spec_reduce_classes: Default::default(),
            class_reprs: Default::default(),
            spec_reductions: Default::default(),

            mode,

            var_stack: vec![],
        };

        new.init();

        new
    }

    pub fn enable_spec_reduction(&mut self, classes: HashMap<Var, Lit>) {
        self.reset_keeping_classes(self.mode);

        if let Some(&false_class) = classes.get(&Var::FALSE) {
            self.class_reprs.insert(
                (TimeStep::FIRST, false_class.var()),
                (Lit::FALSE, Lit::FALSE ^ false_class.pol()),
            );
        }
        self.spec_reduce_classes = Some(classes);
    }

    pub fn spec_reductions(&self) -> &[(TimeStep, [Lit; 2], [Lit; 2])] {
        &self.spec_reductions
    }

    pub fn reset_keeping_classes(&mut self, mode: UnrollMode) {
        self.seen_from_seq.clear();
        self.comb_from_seen.clear();
        self.seq_from_comb.clear();

        self.reset_released.clear();

        self.class_reprs.clear();
        self.spec_reductions.clear();

        self.mode = mode;

        self.var_stack.clear();
        self.init();
    }

    fn init(&mut self) {
        self.seen_from_seq.insert(Var::FALSE);
        self.seq_from_comb.insert_repr(
            Lit::FALSE,
            SeqFromCombEntry {
                step: TimeStep::FIRST,
                lit: Lit::FALSE,
            },
        );
    }

    pub fn unroll_defer_spec(
        &mut self,
        source: &Env,
        dest: &mut Env,
        step: TimeStep,
        seq_lit: Lit,
    ) -> Lit {
        if seq_lit.is_const() {
            seq_lit
        } else {
            let seq_lit = source.var_defs().lit_repr(seq_lit);

            self.unroll_repr_var_uncached_inner(source, dest, step, seq_lit.var()) ^ seq_lit.pol()
        }
    }

    pub fn unroll(&mut self, source: &Env, dest: &mut Env, step: TimeStep, seq_lit: Lit) -> Lit {
        if seq_lit.is_const() {
            seq_lit
        } else {
            let seq_lit = source.var_defs().lit_repr(seq_lit);

            self.unroll_repr_var(source, dest, step, seq_lit.var()) ^ seq_lit.pol()
        }
    }

    pub fn find_unrolled(&self, source: &Env, step: TimeStep, seq_lit: Lit) -> Option<Lit> {
        if seq_lit.is_const() {
            Some(seq_lit)
        } else {
            let seq_lit = source.var_defs().lit_repr(seq_lit);
            self.find_unrolled_repr_var(step, seq_lit.var())
                .map(|lit| lit ^ seq_lit.pol())
        }
    }

    pub fn find_seq(
        &mut self,
        dest: &Env,
        unroll_lit: Lit,
    ) -> impl Iterator<Item = (TimeStep, Lit)> + '_ {
        self.seq_from_comb.merge_equivs(dest);
        self.seq_from_comb
            .lit_entries(unroll_lit)
            .map(|entry| (entry.step, entry.lit))
    }

    fn find_unrolled_repr_var(&self, step: TimeStep, seq_var: Var) -> Option<Lit> {
        let seen = self.seen_from_seq.get_id(&seq_var)?;
        let comb_from_seen = self.comb_from_seen.get(step)?;
        let slot = comb_from_seen.get(seen)?;
        *slot
    }

    fn unroll_repr_var(
        &mut self,
        source: &Env,
        dest: &mut Env,
        step: TimeStep,
        seq_var: Var,
    ) -> Lit {
        let seen = self.seen_from_seq.insert(seq_var).0;

        let comb_from_seen = self
            .comb_from_seen
            .grow_for_key_with(step, || IdVec::from_vec(vec![Some(Lit::FALSE)]));

        let slot = comb_from_seen.grow_for_key(seen);

        if let Some(comb_lit) = slot {
            return *comb_lit;
        }

        let unrolled_lit = self.unroll_repr_var_uncached(source, dest, step, seq_var);

        let comb_from_seen = self
            .comb_from_seen
            .grow_for_key_with(step, || IdVec::from_vec(vec![Some(Lit::FALSE)]));

        let slot = comb_from_seen.grow_for_key(seen);

        *slot = Some(unrolled_lit);

        unrolled_lit
    }

    fn unroll_repr_var_uncached_inner(
        &mut self,
        source: &Env,
        dest: &mut Env,
        step: TimeStep,
        seq_var: Var,
    ) -> Lit {
        let unrolled_lit = if source.var_defs().is_steady(seq_var) && step != TimeStep::FIRST {
            self.unroll_repr_var(source, dest, TimeStep::FIRST, seq_var)
        } else {
            match (step.id_index(), self.mode) {
                (0, _) => self.unroll_first_bmc(source, dest, seq_var),
                (1, UnrollMode::Hybrid | UnrollMode::Induction) => {
                    dest.term(UnknownPast { seq: seq_var })
                }
                (_, UnrollMode::Hybrid) => self.unroll_hybrid(source, dest, step, seq_var),
                _ => self.unroll_generic(source, dest, step, seq_var),
            }
        };

        self.seq_from_comb.insert(
            dest,
            unrolled_lit,
            SeqFromCombEntry {
                step,
                lit: seq_var.as_lit(),
            },
        );

        unrolled_lit
    }

    fn unroll_repr_var_uncached(
        &mut self,
        source: &Env,
        dest: &mut Env,
        step: TimeStep,
        seq_var: Var,
    ) -> Lit {
        let unrolled_lit = self.unroll_repr_var_uncached_inner(source, dest, step, seq_var);

        if let Some(classes) = &self.spec_reduce_classes {
            if let Some(&class) = classes.get(&seq_var) {
                match self.class_reprs.entry((step, class.var())) {
                    Entry::Occupied(entry) => {
                        let &(class_repr, class_repr_unrolled) = entry.get();

                        self.spec_reductions.push((
                            step,
                            [seq_var ^ class.pol(), class_repr],
                            [unrolled_lit ^ class.pol(), class_repr_unrolled],
                        ));

                        return class_repr_unrolled ^ class.pol();
                    }
                    Entry::Vacant(entry) => {
                        entry.insert((seq_var ^ class.pol(), unrolled_lit ^ class.pol()));
                    }
                }
            }
        }

        unrolled_lit
    }

    fn unroll_first_bmc(&mut self, source: &Env, dest: &mut Env, seq_var: Var) -> Lit {
        let node = source.def_node(seq_var).unwrap();
        let output_pol = node.output_lit().unwrap().pol();

        if let Some(reg) = node.dyn_cast::<RegNode>() {
            self.unroll(source, dest, TimeStep::FIRST, reg.term.init) ^ output_pol
        } else if let Some(init) = node.dyn_cast::<InitNode>() {
            self.unroll(source, dest, TimeStep::FIRST, init.term.input.as_lit()) ^ output_pol
        } else {
            self.unroll_generic(source, dest, TimeStep::FIRST, seq_var)
        }
    }

    fn unroll_hybrid(&mut self, source: &Env, dest: &mut Env, step: TimeStep, seq_var: Var) -> Lit {
        let node = source.def_node(seq_var).unwrap();
        let output_pol = node.output_lit().unwrap().pol();

        if let Some(reg) = node.dyn_cast::<RegNode>() {
            let prev_step = step.prev().unwrap();

            if self.reset_released.is_empty() {
                let release_step = self.reset_released.next_unused_key();
                self.reset_released
                    .push(dest.term(ReleaseReset { step: release_step }));
            }

            while self.reset_released.get(prev_step).is_none() {
                let release_step = self.reset_released.next_unused_key();
                let prev_release_step = release_step.prev().unwrap();

                let prev_released = self.reset_released[prev_release_step];
                let release_now = dest.term(ReleaseReset { step: release_step });
                let released = dest.or([prev_released, release_now]);

                self.reset_released.push(released);
            }

            let released = self.reset_released[prev_step];

            let init = self.unroll(source, dest, TimeStep::FIRST, reg.term.init);

            let masked_init = dest.and([init, !released]);

            let prev = self.unroll(source, dest, prev_step, reg.term.next.as_lit());

            let masked_prev = dest.and([prev, released]);

            dest.or([masked_init, masked_prev]) ^ output_pol
        } else {
            self.unroll_generic(source, dest, step, seq_var)
        }
    }

    fn unroll_generic(
        &mut self,
        source: &Env,
        dest: &mut Env,
        step: TimeStep,
        seq_var: Var,
    ) -> Lit {
        let node = source.def_node(seq_var).unwrap();
        let output_pol = node.output_lit().unwrap().pol();

        if let Some(reg) = node.dyn_cast::<RegNode>() {
            let prev_step = step.prev().unwrap();
            self.unroll(source, dest, prev_step, reg.term.next.as_lit()) ^ output_pol
        } else if let Some(init) = node.dyn_cast::<InitNode>() {
            self.unroll(source, dest, TimeStep::FIRST, init.term.input.as_lit()) ^ output_pol
        } else if let Some(&input) = node.dyn_cast::<InputNode>() {
            dest.term(UnrolledInput {
                input: input.term,
                step,
            }) ^ output_pol
        } else {
            let var_stack_len = self.var_stack.len();
            node.dyn_append_input_vars(VecSink::new(&mut self.var_stack));

            while self.var_stack.len() > var_stack_len {
                let var = self.var_stack.pop().unwrap();
                self.unroll(source, dest, step, var.as_lit());
            }

            node.dyn_term()
                .unwrap()
                .dyn_add_to_env_with_var_map(dest, &mut |var| {
                    self.find_unrolled(source, step, var.as_lit()).unwrap()
                })
                ^ output_pol
        }
    }
}
