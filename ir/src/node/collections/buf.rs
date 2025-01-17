//! Unindexed temporary storage of nodes, terms and equivalences.
use std::fmt::Debug;

use imctk_ids::Id;
use imctk_util::give_take::Take;

use crate::{
    node::{
        builder::{NodeBuilder, NodeBuilderDyn},
        generic::{
            dyn_term_into_dyn_term_wrapper, dyn_term_wrapper_as_dyn_term, DynNode, DynTerm, Node,
            Term, TermWrapper,
        },
        vtables::{DynNodeType, DynTermType, GenericNodeType, GenericTermType},
        NodeId,
    },
    var::{Lit, Var, VarOrLit},
};

#[derive(Clone, Copy, Debug)]
enum NodeBufEntry {
    Term(NodeId),
    Node(NodeId),
    Equiv([Lit; 2]),
}

#[derive(Debug)]
#[allow(dead_code)] // Currently only used for the Debug impl
enum NodeBufEntryView<'a> {
    Term(&'a DynTerm),
    Node(&'a DynNode),
    Equiv([Lit; 2]),
}

/// A mostly write-only collection of nodes, terms and equivalences stored outside of an
/// environment.
///
/// While individual nodes, terms and equivalences can be added using the [`NodeBuilder`] trait, the
/// only way to access the added items is by using [`Self::drain_into_node_builder`] to add all of
/// them to another [`NodeBuilder`] (e.g. an environment that does provide access to individual
/// nodes).
///
/// Note that when adding terms, a [`NodeBuf`] will allocate fresh variable with ids decreasing from
/// the maximal supported variable id. These will get remapped to fresh or existing equivalent
/// variables when draining the contents into another [`NodeBuilder`]. The resulting mapping is
/// returned as a [`NodeBufVarMap`] reference.
#[derive(Default)]
pub struct NodeBuf {
    nodes: super::nodes::Nodes,
    entries: Vec<NodeBufEntry>,
    terms: usize,
    recycle: usize,
    tmp_var_map: NodeBufVarMap,
}

impl Debug for NodeBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.entries.iter().map(|entry| match *entry {
                NodeBufEntry::Term(wrapper_id) => NodeBufEntryView::Term(
                    dyn_term_wrapper_as_dyn_term(self.nodes.get_dyn(wrapper_id).unwrap()).unwrap(),
                ),
                NodeBufEntry::Node(node_id) => {
                    NodeBufEntryView::Node(self.nodes.get_dyn(node_id).unwrap())
                }
                NodeBufEntry::Equiv(equiv) => NodeBufEntryView::Equiv(equiv),
            }))
            .finish()
    }
}

/// Variable mapping created when draining the contents of a [`NodeBuf`].
#[derive(Default)]
pub struct NodeBufVarMap {
    map: Vec<Lit>,
}

impl NodeBufVarMap {
    /// Applies the mapping determined when draining the contents of a [`NodeBuf`] into a
    /// [`NodeBuilder`]. This is an identity mapping for any variable or literal that was explicitly
    /// added to the [`NodeBuf`] but will remap the freshly allocated variables for [`Term`]
    /// outputs.
    pub fn map_var(&self, var: Var) -> Lit {
        self.map
            .get(Var::MAX_ID_INDEX - var.index())
            .copied()
            .unwrap_or(var.as_lit())
    }
}

impl NodeBuilderDyn for NodeBuf {
    fn dyn_term(&mut self, term: Take<DynTerm>) -> Lit {
        let lit = Var::from_index(Var::MAX_ID_INDEX.checked_sub(self.terms).unwrap()).as_lit();

        self.entries.push(NodeBufEntry::Term(
            self.nodes
                .insert_dyn(dyn_term_into_dyn_term_wrapper(term))
                .0,
        ));

        self.terms += 1;

        lit
    }

    fn dyn_node(&mut self, node: Take<DynNode>) {
        self.entries
            .push(NodeBufEntry::Node(self.nodes.insert_dyn(node).0));
    }

    fn equiv(&mut self, equiv: [Lit; 2]) {
        self.entries.push(NodeBufEntry::Equiv(equiv))
    }
}

impl NodeBuilder for NodeBuf {
    fn term<T: Term>(&mut self, term: T) -> T::Output {
        let lit = Var::from_index(Var::MAX_ID_INDEX.checked_sub(self.terms).unwrap()).as_lit();
        self.entries.push(NodeBufEntry::Term(
            self.nodes.insert(TermWrapper { term }).0,
        ));

        <T::Output as VarOrLit>::build_var_or_lit(lit, |lit| lit.var(), |lit| lit)
    }

    fn node<T: Node>(&mut self, node: T) {
        self.entries
            .push(NodeBufEntry::Node(self.nodes.insert(node).0));
    }
}

impl NodeBuf {
    /// Adds the contents of this buffer into another [`NodeBuilder`] and clear this buffer.
    ///
    /// This returns a [`NodeBufVarMap`] reference that contains the mapping for any variables
    /// freshly allocated for [`Term`] outputs.
    pub fn drain_into_node_builder(&mut self, builder: &mut impl NodeBuilder) -> &NodeBufVarMap {
        // We multiply by 2 since the builder will start allocating variables for our temporary
        // variables and we need to avoid any overlap until the very end.
        assert!(
            builder.valid_temporary_vars(self.terms * 2),
            "NodeBuf uses more temporary variables than available in the target builder"
        );
        self.tmp_var_map.map.clear();
        if self.entries.is_empty() {
            return &self.tmp_var_map;
        }

        for entry in self.entries.drain(..) {
            match entry {
                NodeBufEntry::Term(node_id) => {
                    self.nodes
                        .remove_dyn_with(node_id, |node| {
                            let term_type =
                                DynNodeType(node.node_type()).wrapped_term_type().unwrap();
                            // SAFETY: we know (and dynamically verified by calling
                            // `wrapped_term_type`) that the target node is a TermWrapper which is
                            // a transparent wrapper for a Term. We're also using the correct
                            // `TermType` obtained from the wrapper's `NodeType`.
                            let mut term = unsafe {
                                Take::from_raw_ptr(
                                    DynTermType(term_type)
                                        .cast_mut_ptr(node.into_raw_ptr() as *mut u8),
                                )
                            };

                            let map_pol =
                                term.dyn_apply_var_map(&mut |var| self.tmp_var_map.map_var(var));

                            let output_lit = builder.dyn_term(term);

                            self.tmp_var_map.map.push(output_lit ^ map_pol);
                        })
                        .unwrap();
                }
                NodeBufEntry::Node(node_id) => {
                    self.nodes
                        .remove_dyn_with(node_id, |mut node| {
                            node.dyn_apply_var_map(&mut |var| self.tmp_var_map.map_var(var));
                            builder.dyn_node(node);
                        })
                        .unwrap();
                }
                NodeBufEntry::Equiv(lits) => {
                    log::trace!("draining equiv {lits:?}");
                    builder.equiv(lits.map(|lit| lit.lookup(|var| self.tmp_var_map.map_var(var))));
                }
            }
        }

        // TODO improve `Nodes` memory management under node deletions and/or reimplement
        // `NodeBuf` using bump allocation
        self.recycle += 1;
        if self.recycle == 10000 {
            self.recycle = 0;
            self.nodes = Default::default();
        }

        &self.tmp_var_map
    }
}
