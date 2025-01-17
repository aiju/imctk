//! Environments for storing and maintaining the internal representation.
use std::mem::{swap, take};

use imctk_ids::{id_vec::IdVec, Id, Id32};
use imctk_transparent::{NewtypeCast, SubtypeCast};
use imctk_util::give_take::Take;

use crate::{
    index::{DefsIndex, UsesIndex},
    var::VarOrLit,
};

use super::{
    index::{DynamicIndex, StructuralHashIndex},
    node::{
        builder::{NodeBuilder, NodeBuilderDyn},
        collections::{buf::NodeBuf, nodes::Nodes},
        generic::{dyn_term_into_dyn_term_node, DynNode, DynTerm, Node, Term, TermNode},
        NodeId,
    },
    var::{Lit, Var},
};

mod multimap;
mod node_builders;
mod rebuild_egraph;

pub use multimap::{LitMultimap, VarMultimap};
pub use updates::EnvUpdates;

/// Indicates whether a node is the primary definition or an equivalent definition of a variable or
/// alternatively whether it is a constraint on the node inputs.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum NodeRole {
    /// Used for a node that is the primary definition of a variable.
    PrimaryDef(Var),
    /// Used for a node that gives an equivalent definition of a variable.
    Equivalence(Var),
    /// Used for a node that constrains its inputs.
    Constraint,
}

/// Definition of a variable, either the defining node or an equivalent literal.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum VarDef {
    /// The referenced node is the primary definition of the variable.
    Node(NodeId),
    /// The referenced literal is the primary definition of the variable.
    Equiv(Lit),
}

/// Compact encoding of a (u31, Option<VarDef>)
#[derive(Default)]
struct EncodedVarDef {
    level_bound_and_flags: u32,
    id: Option<Id32>,
}

impl std::fmt::Debug for EncodedVarDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EncodedVarDef")
            .field("var_def", &self.def())
            .field("level_bound", &self.level_bound())
            .finish()
    }
}

impl EncodedVarDef {
    const EQUIV_MASK: u32 = 1 << 31;
    const STEADY_MASK: u32 = 1 << 30;

    const FLAGS_MASK: u32 = !((!0) >> 2);

    pub fn def(&self) -> Option<VarDef> {
        match (self.level_bound_and_flags & Self::EQUIV_MASK != 0, self.id) {
            (true, Some(id)) => Some(VarDef::Equiv(Lit::from_base_id(id))),
            (true, None) => unreachable!(),
            (false, Some(id)) => Some(VarDef::Node(NodeId::from_base_id(id))),
            (false, None) => None,
        }
    }

    pub fn def_node(&self) -> Option<NodeId> {
        if self.level_bound_and_flags & Self::EQUIV_MASK != 0 {
            None
        } else {
            self.id.map(NodeId::from_base_id)
        }
    }

    pub fn set_def(&mut self, var_def: Option<VarDef>) {
        match var_def {
            Some(VarDef::Node(node_id)) => {
                self.id = Some(node_id.into_base_id());
                self.level_bound_and_flags &= !Self::EQUIV_MASK;
            }
            Some(VarDef::Equiv(lit)) => {
                self.id = Some(lit.into_base_id());
                self.level_bound_and_flags |= Self::EQUIV_MASK;
            }
            None => {
                self.id = None;
                self.level_bound_and_flags &= !Self::EQUIV_MASK;
            }
        }
    }

    pub fn clear_def(&mut self) {
        self.set_def(None);
    }

    pub fn set_def_node(&mut self, node: NodeId) {
        self.set_def(Some(VarDef::Node(node)));
    }

    pub fn set_def_equiv(&mut self, lit: Lit) {
        self.set_def(Some(VarDef::Equiv(lit)));
    }

    pub fn def_is_none(&self) -> bool {
        self.id.is_none() && (self.level_bound_and_flags & Self::EQUIV_MASK == 0)
    }

    pub fn level_bound(&self) -> u32 {
        self.level_bound_and_flags & !Self::FLAGS_MASK
    }

    pub fn set_level_bound(&mut self, level_bound: u32) {
        debug_assert!(level_bound <= !Self::FLAGS_MASK);
        self.level_bound_and_flags = (self.level_bound_and_flags & Self::FLAGS_MASK) | level_bound;
    }

    pub fn set_max_level_bound(&mut self) {
        self.level_bound_and_flags |= !Self::FLAGS_MASK
    }

    pub fn is_steady(&self) -> bool {
        self.level_bound_and_flags & Self::STEADY_MASK != 0
    }

    pub fn set_steady(&mut self, steady: bool) {
        if steady {
            self.level_bound_and_flags |= Self::STEADY_MASK;
        } else {
            self.level_bound_and_flags &= !Self::STEADY_MASK;
        }
    }
}

/// Maintains the primary definitions of all variables.
///
/// This combines a polarity-aware union-find data structure over all equivalent literals with a map
/// storing the defining node for each equivalence class representative.
///
/// It also maintains a best-effort upper bound on the level for each variable. The level is defined
/// as the height of the DAG that defines a variable in terms of the inputs. While these bounds are
/// correctly updated when adding term nodes, equivalences and during egraph rebuilding, other
/// operations may not do so. This means correctness of these bounds is not a general environment
/// invariant.
pub struct VarDefs {
    var_defs: IdVec<Var, EncodedVarDef>,
}

impl Default for VarDefs {
    fn default() -> Self {
        let mut false_def: EncodedVarDef = Default::default();
        false_def.set_steady(true);
        Self {
            var_defs: IdVec::from_vec(vec![false_def]),
        }
    }
}

impl VarDefs {
    /// Retrieves the primary definition of a variable.
    ///
    /// Returns `None` when the environment does not contain a designed primary definition.
    pub fn var_def(&self, var: Var) -> Option<VarDef> {
        self.var_defs.get(var)?.def()
    }

    /// Returns the canonical representative literal equivalent to the given literal.
    pub fn lit_repr(&self, mut lit: Lit) -> Lit {
        while let Some(VarDef::Equiv(repr)) = self.var_def(lit.var()) {
            lit = repr ^ lit.pol();
        }

        lit
    }

    fn update_lit_repr(&mut self, mut lit: Lit) -> Lit {
        let repr = self.lit_repr(lit);

        while let Some(VarDef::Equiv(parent)) = self.var_def(lit.var()) {
            self.var_defs[lit.var()].set_def_equiv(repr ^ lit.pol());
            lit = parent ^ lit.pol();
        }

        repr
    }

    /// Returns the canonical representative variable for the given variable.
    ///
    /// This ignores polarities, and thus might return a variable that's equivalent to the negation
    /// of the passed variable. Most of the time, [`lit_repr`][Self::lit_repr] should be used
    /// instead.
    pub fn var_repr(&self, mut var: Var) -> Var {
        while let Some(VarDef::Equiv(repr)) = self.var_def(var) {
            var = repr.var()
        }

        var
    }

    /// Returns a best-effort upper bound on the level of the node that defines a given variable.
    // TODO go into more detail on how this is maintained, intended to be used, guarded inputs, etc.
    pub fn level_bound(&self, var: Var) -> u32 {
        if let Some(repr) = self.var_defs.get(self.var_repr(var)) {
            repr.level_bound()
        } else {
            0
        }
    }

    /// Returns whether the variable is known to have a steady value.
    ///
    /// A steady value remains constant at the value it has in the initial state.
    pub fn is_steady(&self, var: Var) -> bool {
        if let Some(def) = self.var_defs.get(self.var_repr(var)) {
            def.is_steady()
        } else {
            false
        }
    }

    /// Returns the number of assigned variables.
    pub fn len(&self) -> usize {
        self.var_defs.len()
    }

    /// Returns whether no variables have been assigned.
    pub fn is_empty(&self) -> bool {
        self.var_defs.is_empty()
    }

    /// Returns an iterator over all representative variables.
    ///
    /// Representative variables are variables not known to be equivalent to other variables or
    /// their negation.
    ///
    /// This will yield a double ended iterator of representative variables ordered by increasing
    /// id.
    pub fn repr_vars(&self) -> impl DoubleEndedIterator<Item = Var> + '_ {
        self.var_defs.iter().flat_map(|(var, def)| match def.def() {
            Some(VarDef::Equiv(_)) => None,
            _ => Some(var),
        })
    }
}

#[derive(Default)]
struct EnvIndex {
    structural_hash_index: StructuralHashIndex,
    defs_index: DefsIndex,
    uses_index: UsesIndex,
    equiv_trail: Vec<Var>,
    pending_equivs: usize,
    reduction_queue: Vec<NodeId>,
    pending_nodes: Vec<NodeId>,
}

impl EnvIndex {
    pub fn add_node<T: Node>(
        &mut self,
        nodes: &Nodes,
        node_id: NodeId,
        node: &T,
        node_role: NodeRole,
    ) {
        self.structural_hash_index
            .add_node(nodes, node_id, node, node_role);
        self.defs_index.add_node((), node_id, node, node_role);
        self.uses_index.add_node((), node_id, node, node_role);
        self.pending_nodes.push(node_id);
    }

    pub fn add_dyn_node(
        &mut self,
        nodes: &Nodes,
        node_id: NodeId,
        node: &DynNode,
        node_role: NodeRole,
    ) {
        self.structural_hash_index
            .add_dyn_node(nodes, node_id, node, node_role);
        self.defs_index.add_dyn_node((), node_id, node, node_role);
        self.uses_index.add_dyn_node((), node_id, node, node_role);
        self.pending_nodes.push(node_id);
    }

    pub fn remove_dyn_node(
        &mut self,
        nodes: &Nodes,
        node_id: NodeId,
        node: &DynNode,
        node_role: NodeRole,
    ) {
        self.structural_hash_index
            .remove_dyn_node(nodes, node_id, node, node_role);
        self.defs_index
            .remove_dyn_node((), node_id, node, node_role);
        self.uses_index
            .remove_dyn_node((), node_id, node, node_role);
    }

    pub fn change_primary_def(
        &mut self,
        nodes: &Nodes,
        var: Var,
        old_primary_def: Option<NodeId>,
        new_primary_def: Option<NodeId>,
    ) {
        log::trace!("change_primary_def {var} {old_primary_def:?} => {new_primary_def:?}");
        self.structural_hash_index
            .change_primary_def(nodes, var, old_primary_def, new_primary_def);
        self.defs_index
            .change_primary_def((), var, old_primary_def, new_primary_def);
        self.uses_index
            .change_primary_def((), var, old_primary_def, new_primary_def);
    }

    pub fn add_equiv(&mut self, nodes: &Nodes, repr: Lit, equiv: Var) {
        self.structural_hash_index.add_equiv(nodes, repr, equiv);
        self.defs_index.add_equiv((), repr, equiv);
        self.uses_index.add_equiv((), repr, equiv);

        self.equiv_trail.push(equiv);
    }

    #[inline(always)]
    fn rewrite_cost(&self, var: Var) -> usize {
        self.uses_index.use_count(var) + self.defs_index.non_primary_def_count(var)
    }
}

/// An environment for storing and maintaining the internal representation.
// TODO add a general overview, as this is the main entry point for the IR
#[derive(Default)]
pub struct Env {
    nodes: Nodes,
    var_defs: VarDefs,

    index: EnvIndex,

    node_buf: NodeBuf,

    updates: Option<EnvUpdates>,
}

/// Types that wrap and expose different aspects of an [environment][`Env`].
pub trait EnvWrapper {
    /// Returns a reference to the wrapped environment.
    fn env(&self) -> &Env;
    /// Returns a mutable reference to the wrapped environment.
    // TODO should this be a separate trait to allow wrappers with additional invariants?
    fn env_mut(&mut self) -> &mut Env;
}

impl Env {
    /// Returns the node that is the primary definition of a variable.
    pub fn def_node(&self, var: Var) -> Option<&DynNode> {
        let Some(VarDef::Node(node_id)) = self.var_defs().var_def(var) else { return None };
        Some(self.nodes().get_dyn(node_id).unwrap())
    }

    /// Returns the node id and node for the primary definition of a variable.
    pub fn def_node_with_id(&self, var: Var) -> Option<(NodeId, &DynNode)> {
        let Some(VarDef::Node(node_id)) = self.var_defs().var_def(var) else { return None };
        Some((node_id, self.nodes().get_dyn(node_id).unwrap()))
    }

    /// Returns the canonical representative literal equivalent to the given literal.
    ///
    /// This will perform path compression on the internal union-find data structure used to keep
    /// track of equivalent literals. To look up a canonical representative with a read-only
    /// environment reference (and thus without performing path-compression) [`VarDefs::lit_repr`]
    /// can be used via [`var_defs`][`Self::var_defs`].
    pub fn lit_repr(&mut self, lit: Lit) -> Lit {
        self.var_defs.update_lit_repr(lit)
    }

    /// Applies a variable map to a copy of node and adds it into the same environment.
    ///
    /// Note that this will also use the variable map for any output of the node, see
    /// [`Self::duplicate_term_with_var_map`] for a version that will use a fresh or an existing
    /// already equivalent variable instead.
    pub fn duplicate_node_with_var_map(
        &mut self,
        node_id: NodeId,
        mut var_map: impl FnMut(&Self, Var) -> Lit,
    ) {
        let node = self.nodes.get_dyn(node_id).unwrap();
        let mut node_buf = take(&mut self.node_buf);
        node.dyn_add_to_buf_with_var_map(&mut node_buf, &mut |var| var_map(self, var));
        node_buf.drain_into_node_builder(self);
        self.node_buf = node_buf;
    }

    /// Applies a variable map to a copy of a node's term and adds it into the same environment,
    /// returning the fresh or existing already equivalent output variable.
    ///
    /// This will panic if the given node is not a [`TermNode`], see
    /// [`Self::duplicate_node_with_var_map`] for a version that supports all nodes and also remaps
    /// the output variable.
    pub fn duplicate_term_with_var_map(
        &mut self,
        node_id: NodeId,
        mut var_map: impl FnMut(&Self, Var) -> Lit,
    ) -> Lit {
        let node = self.nodes.get_dyn(node_id).unwrap();
        let term = node.dyn_term().unwrap();
        let mut node_buf = take(&mut self.node_buf);
        let out_lit =
            term.dyn_add_to_buf_with_var_map(&mut node_buf, &mut |var| var_map(self, var));
        let var_map = node_buf.drain_into_node_builder(self);
        let out_lit = out_lit.lookup(|var| var_map.map_var(var));
        self.node_buf = node_buf;
        out_lit
    }
}

mod updates {
    #![allow(missing_docs)] // TODO document module
    use crate::{node::NodeId, var::Var};

    use super::Env;

    #[derive(Default, Debug)]
    pub struct EnvUpdates {
        pub equivs: Vec<Var>,
        pub steady: Vec<Var>,
        pub nodes: Vec<NodeId>,
    }

    impl Env {
        pub fn peek_updates(&self) -> Option<&EnvUpdates> {
            self.updates.as_ref()
        }

        pub fn track_updates(&mut self) -> Option<EnvUpdates> {
            self.updates.replace(EnvUpdates::default())
        }

        pub fn stop_tracking_updates(&mut self) -> Option<EnvUpdates> {
            self.updates.take()
        }

        pub fn equiv_vars(&self) -> &[Var] {
            &self.index.equiv_trail
        }

        pub fn substituted_equiv_vars(&self) -> &[Var] {
            &self.index.equiv_trail[..self.index.pending_equivs]
        }
    }
}

impl Env {
    // TODO move this elsewhere?

    /// Finds an existing node that assigns the given term to a variable.
    pub fn lookup_term<T: Term>(&self, term: &T) -> Option<(NodeId, T::Output)> {
        self.index
            .structural_hash_index
            .find_term(self.nodes(), term)
    }
}

#[cfg(test)]
mod tests {
    use zwohash::HashMap;

    use crate::node::fine::circuit::{FineCircuitNodeBuilder, Input};

    use super::*;

    #[test]
    fn duplicate_with_var_map() {
        let mut env = Env::default();

        let a = env.term(Input::from_id_index(0));
        let b = env.term(Input::from_id_index(1));
        let c = env.term(Input::from_id_index(2));
        let d = env.term(Input::from_id_index(3));

        let y = env.and([a, b]);

        let z = env.fresh_var_with_max_level_bound().as_lit();

        let y_def_id = env.def_node_with_id(y.var()).unwrap().0;

        let var_map =
            HashMap::from_iter([(a, c), (b, d), (y, z)].map(|(a, b)| (a.var(), b ^ a.pol())));

        env.duplicate_node_with_var_map(y_def_id, |_env, var| var_map[&var]);

        assert_eq!(env.and([c, d]), z);

        let y2 = env.xor([a, b]);

        let z2 = env.xor([c, d]);

        let y2_def_id = env.def_node_with_id(y2.var()).unwrap().0;

        assert_eq!(
            z2.var(),
            env.duplicate_term_with_var_map(y2_def_id, |_env, var| var_map[&var])
                .var()
        );
    }

    #[test]
    fn remove_nodes() {
        let mut env = Env::default();

        let a = env.term(Input::from_id_index(0));
        let b = env.term(Input::from_id_index(1));
        let y = env.and([a, b]);
        let id = env.def_node_with_id(y.var()).unwrap().0;
        env.raw_nodes().discard_node(id);
        let y2 = env.and([a, b]);
        assert_ne!(y, y2);
        let y3 = env.and([a, b]);
        assert_eq!(y2, y3);
    }
}
