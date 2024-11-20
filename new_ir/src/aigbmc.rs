use imctk_abc::sat::glucose2::{CnfOnly, Solver};
use imctk_ids::{id_vec::IdVec, Id, IdAlloc, IdRange};
use imctk_lit::{Lit, Var};
use imctk_paged_storage::index::IndexedTermRef;

use crate::{
    bitlevel::{BitlevelTerm, InputId, Reg},
    cnf::{CnfSink, IncrementalCnf},
    ir::BitIr,
};

#[derive(Id, Debug)]
#[repr(transparent)]
pub struct Frame(pub u32);

#[derive(Default, Debug)]
struct Unroller {
    var_map: IdVec<Frame, IdVec<Var, Option<Lit>>>,
    input_map: IdVec<Frame, IdVec<InputId, Option<InputId>>>,
    unrolled_input_alloc: IdAlloc<InputId>,
}

impl Unroller {
    fn get(&mut self, seq_ir: &BitIr, unrolled_ir: &mut BitIr, frame: Frame, lit: Lit) -> Lit {
        if let Some(unrolled_lit) = *self.var_map.grow_for_key(frame).grow_for_key(lit.var()) {
            return unrolled_lit ^ lit.pol();
        }
        let term: BitlevelTerm = seq_ir.primary_def(lit.var());
        dbg!(lit, &term);
        let unrolled_lit = match term {
            BitlevelTerm::Reg(Reg { init, next }) => {
                if frame.0 == 0 {
                    self.get(seq_ir, unrolled_ir, frame, init)
                } else {
                    self.get(seq_ir, unrolled_ir, Frame(frame.0 - 1), next)
                }
            }
            BitlevelTerm::Input(input_id) => {
                let unrolled_id = *self
                    .input_map
                    .grow_for_key(frame)
                    .grow_for_key(input_id)
                    .get_or_insert_with(|| self.unrolled_input_alloc.alloc());
                unrolled_ir.term(BitlevelTerm::Input(unrolled_id))
            }
            BitlevelTerm::ConstFalse(_)
            | BitlevelTerm::SteadyInput(_)
            | BitlevelTerm::And(_)
            | BitlevelTerm::Xor(_) => {
                let unrolled_term = term.map(|lit| self.get(seq_ir, unrolled_ir, frame, lit));
                unrolled_ir.term(unrolled_term)
            }
        };
        self.var_map[frame][lit.var()] = Some(unrolled_lit);
        unrolled_lit ^ lit.pol()
    }
}

pub struct Bmc {
    unroller: Unroller,
    unrolled_ir: BitIr,
    cnf: IncrementalCnf,
    solver: Solver<'static, CnfOnly>,
}

impl CnfSink for Solver<'_, CnfOnly> {
    type Var = Var;
    type Lit = Lit;
    type Error = ();
    fn var(&mut self, var: Var) -> Self::Var {
        var
    }
    fn clause(&mut self, clause: &[Self::Lit]) -> Result<(), Self::Error> {
        self.add_clause(clause);
        Ok(())
    }
}

pub struct BmcWitness<'a> {
    max_frame: Frame,
    bmc: &'a mut Bmc,
}

impl Bmc {
    pub fn new(mut solver: Solver<'static, CnfOnly>) -> Self {
        let unroller = Unroller::default();
        let mut unrolled_ir = BitIr::default();
        let cnf = IncrementalCnf::new_full(&mut unrolled_ir, &mut solver).unwrap();
        Bmc {
            unroller,
            unrolled_ir,
            cnf,
            solver,
        }
    }
    pub fn run(&mut self, seq_ir: &BitIr, depth: u32, bad_state: Lit) -> Option<BmcWitness<'_>> {
        for frame in <IdRange<Frame>>::from_index_range(0..depth as usize) {
            let unrolled_bad_state =
                self.unroller
                    .get(seq_ir, &mut self.unrolled_ir, frame, bad_state);
            self.cnf
                .update(&mut self.unrolled_ir, &mut self.solver)
                .unwrap();
            match self.solver.solve_assuming(&[unrolled_bad_state]) {
                None => unimplemented!(),
                Some(true) => {
                    return Some(BmcWitness {
                        max_frame: frame,
                        bmc: self,
                    });
                }
                Some(false) => {}
            }
        }
        None
    }
}

impl BmcWitness<'_> {
    pub fn get_lit(&mut self, frame: Frame, lit: Lit) -> Option<bool> {
        if frame > self.max_frame {
            None
        } else {
            let unrolled_lit = (*self.bmc.unroller.var_map.get(frame)?.get(lit.var())?)?;
            self.bmc.solver.value(unrolled_lit)
        }
    }
    pub fn get_input(&mut self, frame: Frame, input_id: InputId) -> Option<bool> {
        if frame > self.max_frame {
            None
        } else {
            let unrolled_input_id = (*self.bmc.unroller.input_map.get(frame)?.get(input_id)?)?;
            let unrolled_lit = self
                .bmc
                .unrolled_ir
                .find_term(BitlevelTerm::Input(unrolled_input_id))
                .unwrap();
            self.bmc.solver.value(unrolled_lit)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use crate::aiger::AigerImporter;

    use super::*;

    #[test]
    fn test() {
        let depth = 10;
        let file = std::fs::File::open("aiger_test.aig").unwrap();
        let file = BufReader::new(file);
        let mut seq_ir = BitIr::default();
        let (aiger_map, ordered_aig) = AigerImporter::default()
            .import_binary(&mut seq_ir, file)
            .unwrap();
        seq_ir.refresh();
        panic!("foo");
        let mut bmc = Bmc::new(Solver::default());
        for aiger_lit in ordered_aig.bad_state_properties {
            let seq_lit = aiger_lit.lookup(|var| aiger_map[var]);
            if let Some(witness) = bmc.run(&seq_ir, depth, seq_lit) {
                dbg!("doop");
            }
        }
    }
}
