//! Validated, language-neutral rule records used by the native join kernel.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};

use crate::error::{NativeError, NativeResult};
use crate::model::{DependencySet, NodeHandle, NodeSort};

/// The two disjoint term domains in compiled DL clauses.
///
/// `Data` precedes `Object` deliberately: Python freezes bindings by the lexical
/// values `"data"` and `"object"`, so derived ordering has exact cross-backend
/// parity.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermSort {
    Data,
    Object,
}

impl TermSort {
    #[must_use]
    pub const fn node_sort(self) -> NodeSort {
        match self {
            Self::Data => NodeSort::Data,
            Self::Object => NodeSort::Object,
        }
    }
}

/// Complete predicate-kind vocabulary emitted by the Python clausifier.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PredicateKind {
    Concept,
    NegatedConcept,
    Nominal,
    NegatedNominal,
    ObjectRole,
    NegatedObjectRole,
    DataRole,
    NegatedDataRole,
    DataRange,
    NegatedDataRange,
    Equality,
    Inequality,
    AtLeastObject,
    AtLeastData,
    AnnotatedEquality,
    AutomatonState,
    DisjointGuard,
    OrderingGuard,
    NamedIndividual,
}

impl PredicateKind {
    #[must_use]
    pub const fn is_virtual_filter(self) -> bool {
        matches!(self, Self::Equality | Self::OrderingGuard)
    }

    #[must_use]
    pub const fn can_trigger(self) -> bool {
        !matches!(self, Self::OrderingGuard)
    }
}

/// Predicate identity and its checked argument signature.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RulePredicate {
    pub predicate_id: u32,
    pub kind: PredicateKind,
    pub argument_sorts: Vec<TermSort>,
    pub symbol_id: Option<u32>,
    pub role_id: Option<u32>,
    pub cardinality: Option<u32>,
    pub filler_predicate_id: Option<u32>,
    pub annotation: Vec<u32>,
    pub internal_key: Option<String>,
    /// Optional reciprocal link to the normalized logical opposite.
    pub opposite_predicate_id: Option<u32>,
}

impl RulePredicate {
    pub fn new(
        predicate_id: u32,
        kind: PredicateKind,
        argument_sorts: Vec<TermSort>,
    ) -> NativeResult<Self> {
        validate_predicate_signature(kind, &argument_sorts)?;
        Ok(Self {
            predicate_id,
            kind,
            argument_sorts,
            symbol_id: None,
            role_id: None,
            cardinality: None,
            filler_predicate_id: None,
            annotation: Vec::new(),
            internal_key: None,
            opposite_predicate_id: None,
        })
    }

    #[must_use]
    pub const fn with_symbol_id(mut self, symbol_id: u32) -> Self {
        self.symbol_id = Some(symbol_id);
        self
    }

    #[must_use]
    pub const fn with_role_id(mut self, role_id: u32) -> Self {
        self.role_id = Some(role_id);
        self
    }

    #[must_use]
    pub const fn with_cardinality(
        mut self,
        cardinality: u32,
        role_id: u32,
        filler_predicate_id: u32,
    ) -> Self {
        self.cardinality = Some(cardinality);
        self.role_id = Some(role_id);
        self.filler_predicate_id = Some(filler_predicate_id);
        self
    }

    #[must_use]
    pub fn with_annotation(mut self, annotation: Vec<u32>) -> Self {
        self.annotation = annotation;
        self
    }

    #[must_use]
    pub fn with_internal_key(mut self, internal_key: impl Into<String>) -> Self {
        self.internal_key = Some(internal_key.into());
        self
    }

    #[must_use]
    pub const fn with_opposite(mut self, opposite_predicate_id: u32) -> Self {
        self.opposite_predicate_id = Some(opposite_predicate_id);
        self
    }

    #[must_use]
    pub fn arity(&self) -> usize {
        self.argument_sorts.len()
    }
}

/// A compiled variable or ontology constant.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Term {
    Variable {
        sort: TermSort,
        variable_id: u32,
    },
    Individual {
        individual_id: u32,
    },
    DataConstant {
        source_literal_id: u32,
        data_identity_id: u32,
    },
}

impl Term {
    #[must_use]
    pub const fn variable(variable_id: u32, sort: TermSort) -> Self {
        Self::Variable { sort, variable_id }
    }

    #[must_use]
    pub const fn individual(individual_id: u32) -> Self {
        Self::Individual { individual_id }
    }

    #[must_use]
    pub const fn data_constant(source_literal_id: u32, data_identity_id: u32) -> Self {
        Self::DataConstant {
            source_literal_id,
            data_identity_id,
        }
    }

    #[must_use]
    pub const fn sort(&self) -> TermSort {
        match self {
            Self::Variable { sort, .. } => *sort,
            Self::Individual { .. } => TermSort::Object,
            Self::DataConstant { .. } => TermSort::Data,
        }
    }

    #[must_use]
    pub const fn variable_key(&self) -> Option<(TermSort, u32)> {
        match self {
            Self::Variable { sort, variable_id } => Some((*sort, *variable_id)),
            Self::Individual { .. } | Self::DataConstant { .. } => None,
        }
    }
}

/// One validated compiled body or head atom.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RuleAtom {
    pub predicate_id: u32,
    pub arguments: Vec<Term>,
}

impl RuleAtom {
    pub fn new(predicate_id: u32, arguments: Vec<Term>) -> NativeResult<Self> {
        if arguments.is_empty() {
            return Err(NativeError::wire("rule atoms must have positive arity"));
        }
        Ok(Self {
            predicate_id,
            arguments,
        })
    }

    /// Exact bytes used by Python `CanonicalRecord.canonical_bytes()` for an atom.
    #[must_use]
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut encoded = String::from("{\"arguments\":[");
        for (index, argument) in self.arguments.iter().enumerate() {
            if index != 0 {
                encoded.push(',');
            }
            push_term_json(&mut encoded, argument);
        }
        encoded.push_str("],\"predicate_id\":");
        encoded.push_str(&self.predicate_id.to_string());
        encoded.push_str(",\"schema_version\":1,\"type\":\"Atom\"}");
        encoded.into_bytes()
    }
}

/// Canonical grounded consequence shared with native head dispatch.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct GroundAtom {
    pub predicate_id: u32,
    pub arguments: Vec<NodeHandle>,
}

/// One queued annotated equality with its exact historical supports. The action
/// remains distinct from ordinary equality until nominal introduction consumes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PendingAnnotatedEquality {
    pub action_id: u32,
    pub atom: GroundAtom,
    pub supports: Vec<DependencySet>,
    pub provenance_ids: Vec<u32>,
}

impl PendingAnnotatedEquality {
    pub fn new(
        action_id: u32,
        atom: GroundAtom,
        mut supports: Vec<DependencySet>,
        mut provenance_ids: Vec<u32>,
    ) -> NativeResult<Self> {
        if supports.is_empty() {
            return Err(NativeError::invariant(
                "annotated equality action has no dependency support",
            ));
        }
        supports.sort();
        supports.dedup();
        provenance_ids.sort_unstable();
        provenance_ids.dedup();
        Ok(Self {
            action_id,
            atom,
            supports,
            provenance_ids,
        })
    }
}

impl GroundAtom {
    pub fn new(predicate_id: u32, arguments: Vec<NodeHandle>) -> NativeResult<Self> {
        if arguments.is_empty() {
            return Err(NativeError::wire(
                "ground rule atoms must have positive arity",
            ));
        }
        Ok(Self {
            predicate_id,
            arguments,
        })
    }
}

/// One canonical DL clause and its deterministic source join preference.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RuleClause {
    pub clause_id: u32,
    pub body: Vec<RuleAtom>,
    pub head: Vec<RuleAtom>,
    pub provenance_ids: Vec<u32>,
    pub join_order: Vec<u32>,
}

impl RuleClause {
    pub fn new(
        clause_id: u32,
        body: Vec<RuleAtom>,
        head: Vec<RuleAtom>,
        provenance_ids: Vec<u32>,
        join_order: Vec<u32>,
    ) -> NativeResult<Self> {
        if !strictly_canonical_atoms(&body) {
            return Err(NativeError::wire(
                "clause body atoms must be canonically sorted and unique",
            ));
        }
        if !strictly_canonical_atoms(&head) {
            return Err(NativeError::wire(
                "clause head atoms must be canonically sorted and unique",
            ));
        }
        if provenance_ids.is_empty() || !strictly_sorted(&provenance_ids) {
            return Err(NativeError::wire(
                "clause provenance IDs must be nonempty, sorted, and unique",
            ));
        }
        let body_len = u32::try_from(body.len())
            .map_err(|_| NativeError::wire("clause body exceeds u32 atom positions"))?;
        let mut ordered = join_order.clone();
        ordered.sort_unstable();
        if ordered != (0..body_len).collect::<Vec<_>>() {
            return Err(NativeError::wire(
                "join order must be a permutation of the canonical body",
            ));
        }
        Ok(Self {
            clause_id,
            body,
            head,
            provenance_ids,
            join_order,
        })
    }
}

/// Fully checked native rule program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleProgram {
    predicates: Vec<RulePredicate>,
    clauses: Vec<RuleClause>,
}

impl RuleProgram {
    pub fn new(predicates: Vec<RulePredicate>, clauses: Vec<RuleClause>) -> NativeResult<Self> {
        for (expected, predicate) in predicates.iter().enumerate() {
            if usize::try_from(predicate.predicate_id).ok() != Some(expected) {
                return Err(NativeError::wire("predicate IDs must be dense and ordered"));
            }
            validate_predicate_signature(predicate.kind, &predicate.argument_sorts)?;
            validate_predicate_semantics(predicate)?;
        }
        for predicate in &predicates {
            let Some(opposite_id) = predicate.opposite_predicate_id else {
                continue;
            };
            if opposite_id == predicate.predicate_id {
                return Err(NativeError::wire(
                    "a predicate cannot be its own logical opposite",
                ));
            }
            let opposite = predicates
                .get(usize_from_u32(opposite_id, "opposite predicate ID")?)
                .ok_or_else(|| NativeError::wire("opposite predicate ID is dangling"))?;
            if opposite.opposite_predicate_id != Some(predicate.predicate_id)
                || opposite.argument_sorts != predicate.argument_sorts
                || !opposite_kinds(predicate.kind, opposite.kind)
                || predicate.symbol_id != opposite.symbol_id
                || predicate.role_id != opposite.role_id
            {
                return Err(NativeError::wire(
                    "opposite predicate links must be reciprocal and sort-compatible",
                ));
            }
        }
        for (expected, clause) in clauses.iter().enumerate() {
            if usize::try_from(clause.clause_id).ok() != Some(expected) {
                return Err(NativeError::wire("clause IDs must be dense and ordered"));
            }
        }
        let program = Self {
            predicates,
            clauses,
        };
        program.validate_predicate_references()?;
        program.validate_clauses()?;
        Ok(program)
    }

    #[must_use]
    pub fn predicates(&self) -> &[RulePredicate] {
        &self.predicates
    }

    #[must_use]
    pub fn clauses(&self) -> &[RuleClause] {
        &self.clauses
    }

    pub fn predicate(&self, predicate_id: u32) -> NativeResult<&RulePredicate> {
        self.predicates
            .get(usize_from_u32(predicate_id, "predicate ID")?)
            .ok_or_else(|| NativeError::wire("predicate ID is dangling"))
    }

    pub fn predicate_kind(&self, predicate_id: u32) -> NativeResult<PredicateKind> {
        Ok(self.predicate(predicate_id)?.kind)
    }

    pub fn predicate_argument_sorts(&self, predicate_id: u32) -> NativeResult<&[TermSort]> {
        Ok(&self.predicate(predicate_id)?.argument_sorts)
    }

    pub fn opposite_predicate(&self, predicate_id: u32) -> NativeResult<Option<&RulePredicate>> {
        let Some(opposite_id) = self.predicate(predicate_id)?.opposite_predicate_id else {
            return Ok(None);
        };
        self.predicate(opposite_id).map(Some)
    }

    pub fn clause(&self, clause_id: u32) -> NativeResult<&RuleClause> {
        self.clauses
            .get(usize_from_u32(clause_id, "clause ID")?)
            .ok_or_else(|| NativeError::wire("clause ID is dangling"))
    }

    pub fn validate_ground_atom(&self, atom: &GroundAtom) -> NativeResult<()> {
        let predicate = self.predicate(atom.predicate_id)?;
        if atom.arguments.len() != predicate.arity() {
            return Err(NativeError::wire(
                "ground atom arity does not match its predicate",
            ));
        }
        Ok(())
    }

    fn validate_clauses(&self) -> NativeResult<()> {
        let mut identities = BTreeSet::new();
        for clause in &self.clauses {
            let identity = (
                clause.body.clone(),
                clause.head.clone(),
                clause.join_order.clone(),
            );
            if !identities.insert(identity) {
                return Err(NativeError::wire(
                    "clauses must have unique semantic identities",
                ));
            }
            self.validate_clause(clause)?;
        }
        Ok(())
    }

    fn validate_predicate_references(&self) -> NativeResult<()> {
        for predicate in &self.predicates {
            let Some(filler_id) = predicate.filler_predicate_id else {
                continue;
            };
            if filler_id == predicate.predicate_id {
                return Err(NativeError::wire(
                    "a cardinality predicate cannot be its own filler",
                ));
            }
            let filler = self.predicate(filler_id)?;
            let valid = match predicate.kind {
                PredicateKind::AtLeastObject | PredicateKind::AnnotatedEquality => {
                    filler.argument_sorts == [TermSort::Object]
                        && matches!(
                            filler.kind,
                            PredicateKind::Concept
                                | PredicateKind::NegatedConcept
                                | PredicateKind::Nominal
                                | PredicateKind::NegatedNominal
                        )
                }
                PredicateKind::AtLeastData => {
                    matches!(
                        filler.kind,
                        PredicateKind::DataRange | PredicateKind::NegatedDataRange
                    ) && filler.argument_sorts.len() == predicate.annotation.len()
                }
                _ => false,
            };
            if !valid {
                return Err(NativeError::wire(
                    "cardinality predicate has an incompatible filler predicate",
                ));
            }
        }
        Ok(())
    }

    fn validate_clause(&self, clause: &RuleClause) -> NativeResult<()> {
        if !strictly_canonical_atoms(&clause.body) || !strictly_canonical_atoms(&clause.head) {
            return Err(NativeError::wire("clause atoms lost canonical ordering"));
        }
        if clause.body.iter().any(|atom| clause.head.contains(atom)) {
            return Err(NativeError::wire("tautological clauses must be removed"));
        }

        let mut variable_sorts = BTreeMap::new();
        let mut first_occurrence = Vec::new();
        let mut body_variables = BTreeSet::new();
        let mut head_variables = BTreeSet::new();
        for (is_head, atoms) in [(false, &clause.body), (true, &clause.head)] {
            for atom in atoms {
                self.validate_atom(atom)?;
                let kind = self.predicate_kind(atom.predicate_id)?;
                if is_head && kind == PredicateKind::OrderingGuard {
                    return Err(NativeError::wire(
                        "ordering guards cannot occur in clause heads",
                    ));
                }
                for term in &atom.arguments {
                    let Some((sort, variable_id)) = term.variable_key() else {
                        continue;
                    };
                    match variable_sorts.insert(variable_id, sort) {
                        Some(known) if known != sort => {
                            return Err(NativeError::wire(
                                "one variable ID cannot have object and data sorts",
                            ));
                        }
                        None => first_occurrence.push(variable_id),
                        Some(_) => {}
                    }
                    if is_head {
                        head_variables.insert((sort, variable_id));
                    } else if kind != PredicateKind::OrderingGuard {
                        body_variables.insert((sort, variable_id));
                    }
                }
            }
        }
        let expected: Vec<_> = (0..u32::try_from(first_occurrence.len())
            .map_err(|_| NativeError::wire("clause variable count exceeds the u32 IR limit"))?)
            .collect();
        if first_occurrence != expected {
            return Err(NativeError::wire(
                "clause variables must follow canonical first-occurrence numbering",
            ));
        }
        if !head_variables.is_subset(&body_variables) {
            return Err(NativeError::wire(
                "head variables must be range-restricted by the body",
            ));
        }
        Ok(())
    }

    fn validate_atom(&self, atom: &RuleAtom) -> NativeResult<()> {
        let predicate = self.predicate(atom.predicate_id)?;
        if atom.arguments.len() != predicate.arity() {
            return Err(NativeError::wire("atom arity does not match its predicate"));
        }
        if atom
            .arguments
            .iter()
            .map(Term::sort)
            .ne(predicate.argument_sorts.iter().copied())
        {
            return Err(NativeError::wire(
                "atom argument sorts do not match its predicate",
            ));
        }
        if matches!(
            predicate.kind,
            PredicateKind::Equality | PredicateKind::Inequality
        ) && atom.arguments[1] < atom.arguments[0]
        {
            return Err(NativeError::wire(
                "equality and inequality arguments must be canonically ordered",
            ));
        }
        if predicate.kind == PredicateKind::OrderingGuard && atom.arguments[0] >= atom.arguments[1]
        {
            return Err(NativeError::wire(
                "ordering-guard arguments must be in strict canonical order",
            ));
        }
        if predicate.kind == PredicateKind::AnnotatedEquality
            && atom.arguments[1] < atom.arguments[0]
        {
            return Err(NativeError::wire(
                "annotated-equality pair arguments must be canonically ordered",
            ));
        }
        Ok(())
    }
}

/// One canonical variable assignment in a completed join.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct VariableBinding {
    pub sort: TermSort,
    pub variable_id: u32,
    pub node: NodeHandle,
}

/// One dependency-distinct body match.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JoinMatch {
    pub clause_id: u32,
    pub delta_body_index: u32,
    pub bindings: Vec<VariableBinding>,
    pub dependency: DependencySet,
    pub premise_row_ids: Vec<u32>,
}

impl JoinMatch {
    pub fn new(
        clause_id: u32,
        delta_body_index: u32,
        bindings: Vec<VariableBinding>,
        dependency: DependencySet,
        mut premise_row_ids: Vec<u32>,
    ) -> NativeResult<Self> {
        if bindings
            .windows(2)
            .any(|pair| (pair[0].sort, pair[0].variable_id) >= (pair[1].sort, pair[1].variable_id))
        {
            return Err(NativeError::wire(
                "join bindings must be uniquely sorted by variable",
            ));
        }
        premise_row_ids.sort_unstable();
        premise_row_ids.dedup();
        Ok(Self {
            clause_id,
            delta_body_index,
            bindings,
            dependency,
            premise_row_ids,
        })
    }
}

/// Bounded work controls for one native rule generation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RuleLimits {
    pub max_join_steps: u64,
    pub max_matches_per_generation: u64,
    pub cancellation_interval: u64,
}

impl RuleLimits {
    pub fn new(
        max_join_steps: u64,
        max_matches_per_generation: u64,
        cancellation_interval: u64,
    ) -> NativeResult<Self> {
        if max_join_steps == 0 || max_matches_per_generation == 0 || cancellation_interval == 0 {
            return Err(NativeError::wire("rule limits must be strictly positive"));
        }
        Ok(Self {
            max_join_steps,
            max_matches_per_generation,
            cancellation_interval,
        })
    }
}

impl Default for RuleLimits {
    fn default() -> Self {
        Self {
            max_join_steps: 10_000_000,
            max_matches_per_generation: 2_000_000,
            cancellation_interval: 256,
        }
    }
}

fn validate_predicate_signature(kind: PredicateKind, sorts: &[TermSort]) -> NativeResult<()> {
    let valid = match kind {
        PredicateKind::Concept
        | PredicateKind::NegatedConcept
        | PredicateKind::Nominal
        | PredicateKind::NegatedNominal
        | PredicateKind::AtLeastObject
        | PredicateKind::AtLeastData
        | PredicateKind::AutomatonState
        | PredicateKind::DisjointGuard
        | PredicateKind::NamedIndividual => sorts == [TermSort::Object],
        PredicateKind::ObjectRole | PredicateKind::NegatedObjectRole => {
            sorts == [TermSort::Object, TermSort::Object]
        }
        PredicateKind::DataRole | PredicateKind::NegatedDataRole => {
            sorts == [TermSort::Object, TermSort::Data]
        }
        PredicateKind::DataRange | PredicateKind::NegatedDataRange => {
            !sorts.is_empty() && sorts.iter().all(|sort| *sort == TermSort::Data)
        }
        PredicateKind::Equality | PredicateKind::Inequality | PredicateKind::OrderingGuard => {
            sorts.len() == 2 && sorts[0] == sorts[1]
        }
        PredicateKind::AnnotatedEquality => sorts == [TermSort::Object; 3],
    };
    if !valid {
        return Err(NativeError::wire(
            "predicate argument signature does not match its kind",
        ));
    }
    Ok(())
}

fn validate_predicate_semantics(predicate: &RulePredicate) -> NativeResult<()> {
    let concept_kind = matches!(
        predicate.kind,
        PredicateKind::Concept
            | PredicateKind::NegatedConcept
            | PredicateKind::Nominal
            | PredicateKind::NegatedNominal
            | PredicateKind::DataRange
            | PredicateKind::NegatedDataRange
    );
    let cardinality_kind = matches!(
        predicate.kind,
        PredicateKind::AtLeastObject
            | PredicateKind::AtLeastData
            | PredicateKind::AnnotatedEquality
    );
    let role_kind = matches!(
        predicate.kind,
        PredicateKind::ObjectRole
            | PredicateKind::NegatedObjectRole
            | PredicateKind::DataRole
            | PredicateKind::NegatedDataRole
    );
    if concept_kind != predicate.symbol_id.is_some() {
        return Err(NativeError::wire(
            "symbol IDs are required exactly for concept, nominal, and data-range predicates",
        ));
    }
    if cardinality_kind {
        if predicate.cardinality == Some(0)
            || predicate.cardinality.is_none()
            || predicate.role_id.is_none()
            || predicate.filler_predicate_id.is_none()
        {
            return Err(NativeError::wire(
                "cardinality predicates require positive cardinality, role, and filler IDs",
            ));
        }
    } else if predicate.cardinality.is_some() || predicate.filler_predicate_id.is_some() {
        return Err(NativeError::wire(
            "cardinality and filler IDs are reserved for cardinality predicates",
        ));
    }
    if (cardinality_kind || role_kind) != predicate.role_id.is_some() {
        return Err(NativeError::wire(
            "role IDs are required exactly for role and cardinality predicates",
        ));
    }

    let annotation_kind = matches!(
        predicate.kind,
        PredicateKind::Nominal
            | PredicateKind::NegatedNominal
            | PredicateKind::AtLeastData
            | PredicateKind::AutomatonState
            | PredicateKind::DisjointGuard
    );
    if !annotation_kind && !predicate.annotation.is_empty() {
        return Err(NativeError::wire(
            "predicate annotation is not valid for this predicate kind",
        ));
    }
    match predicate.kind {
        PredicateKind::Nominal | PredicateKind::NegatedNominal => {
            if predicate.annotation.is_empty()
                || predicate
                    .annotation
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
            {
                return Err(NativeError::wire(
                    "nominal annotation IDs must be nonempty, sorted, and unique",
                ));
            }
        }
        PredicateKind::AtLeastData => {
            if predicate.annotation.first().copied() != predicate.role_id
                || predicate
                    .annotation
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>()
                    .len()
                    != predicate.annotation.len()
            {
                return Err(NativeError::wire(
                    "data at-least annotations must list unique role IDs beginning with role_id",
                ));
            }
        }
        PredicateKind::AutomatonState if predicate.annotation.len() != 2 => {
            return Err(NativeError::wire(
                "automaton-state annotation requires component and state IDs",
            ));
        }
        PredicateKind::DisjointGuard if predicate.annotation.len() != 1 => {
            return Err(NativeError::wire(
                "disjoint-guard annotation requires one sequence ID",
            ));
        }
        _ => {}
    }

    let internal_kind = matches!(
        predicate.kind,
        PredicateKind::AutomatonState
            | PredicateKind::DisjointGuard
            | PredicateKind::OrderingGuard
            | PredicateKind::NamedIndividual
    );
    if internal_kind != predicate.internal_key.is_some() {
        return Err(NativeError::wire(
            "internal keys are required exactly for strategy predicates",
        ));
    }
    if predicate.kind == PredicateKind::OrderingGuard {
        let sort = match predicate.argument_sorts[0] {
            TermSort::Data => "data",
            TermSort::Object => "object",
        };
        let expected = format!("canonical-{sort}-order");
        if predicate.internal_key.as_deref() != Some(expected.as_str()) {
            return Err(NativeError::wire(
                "ordering-guard internal key does not match its term sort",
            ));
        }
    }
    Ok(())
}

const fn opposite_kinds(left: PredicateKind, right: PredicateKind) -> bool {
    matches!(
        (left, right),
        (PredicateKind::Concept, PredicateKind::NegatedConcept)
            | (PredicateKind::NegatedConcept, PredicateKind::Concept)
            | (PredicateKind::Nominal, PredicateKind::NegatedNominal)
            | (PredicateKind::NegatedNominal, PredicateKind::Nominal)
            | (PredicateKind::ObjectRole, PredicateKind::NegatedObjectRole)
            | (PredicateKind::NegatedObjectRole, PredicateKind::ObjectRole)
            | (PredicateKind::DataRole, PredicateKind::NegatedDataRole)
            | (PredicateKind::NegatedDataRole, PredicateKind::DataRole)
            | (PredicateKind::DataRange, PredicateKind::NegatedDataRange)
            | (PredicateKind::NegatedDataRange, PredicateKind::DataRange)
            | (PredicateKind::Equality, PredicateKind::Inequality)
            | (PredicateKind::Inequality, PredicateKind::Equality)
    )
}

fn strictly_sorted<T: Ord>(values: &[T]) -> bool {
    values.windows(2).all(|pair| pair[0] < pair[1])
}

fn strictly_canonical_atoms(values: &[RuleAtom]) -> bool {
    values
        .windows(2)
        .all(|pair| pair[0].canonical_bytes() < pair[1].canonical_bytes())
}

fn push_term_json(encoded: &mut String, term: &Term) {
    match term {
        Term::Variable { sort, variable_id } => {
            encoded.push_str("{\"index\":");
            encoded.push_str(&variable_id.to_string());
            encoded.push_str(",\"schema_version\":1,\"sort\":\"");
            encoded.push_str(match sort {
                TermSort::Data => "data",
                TermSort::Object => "object",
            });
            encoded.push_str("\",\"type\":\"Variable\"}");
        }
        Term::Individual { individual_id } => {
            encoded.push_str("{\"individual_id\":");
            encoded.push_str(&individual_id.to_string());
            encoded.push_str(",\"schema_version\":1,\"type\":\"IndividualTerm\"}");
        }
        Term::DataConstant {
            source_literal_id,
            data_identity_id,
        } => {
            encoded.push_str("{\"data_identity_id\":");
            encoded.push_str(&data_identity_id.to_string());
            encoded.push_str(",\"schema_version\":1,\"source_literal_id\":");
            encoded.push_str(&source_literal_id.to_string());
            encoded.push_str(",\"type\":\"DataConstant\"}");
        }
    }
}

fn usize_from_u32(value: u32, name: &str) -> NativeResult<usize> {
    usize::try_from(value)
        .map_err(|_| NativeError::wire(format!("{name} cannot fit this platform")))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(predicate_id: u32, arguments: Vec<Term>) -> NativeResult<RuleAtom> {
        RuleAtom::new(predicate_id, arguments)
    }

    #[test]
    fn predicate_shapes_and_ground_atoms_are_checked() {
        assert!(RulePredicate::new(
            0,
            PredicateKind::ObjectRole,
            vec![TermSort::Object, TermSort::Data],
        )
        .is_err());
        assert!(RulePredicate::new(
            0,
            PredicateKind::DataRange,
            vec![TermSort::Data, TermSort::Data],
        )
        .is_ok());
        assert!(GroundAtom::new(0, Vec::new()).is_err());
        assert!(RuleLimits::new(1, 1, 0).is_err());
    }

    #[test]
    fn atom_canonical_bytes_match_the_python_record_encoding() -> NativeResult<()> {
        let value = atom(
            7,
            vec![
                Term::variable(0, TermSort::Object),
                Term::individual(2),
                Term::data_constant(4, 3),
            ],
        )?;
        assert_eq!(
            String::from_utf8(value.canonical_bytes())
                .map_err(|_| NativeError::invariant("canonical atom bytes are not UTF-8"))?,
            "{\"arguments\":[{\"index\":0,\"schema_version\":1,\"sort\":\"object\",\"type\":\"Variable\"},{\"individual_id\":2,\"schema_version\":1,\"type\":\"IndividualTerm\"},{\"data_identity_id\":3,\"schema_version\":1,\"source_literal_id\":4,\"type\":\"DataConstant\"}],\"predicate_id\":7,\"schema_version\":1,\"type\":\"Atom\"}"
        );
        Ok(())
    }

    #[test]
    fn programs_reject_wrong_sorts_and_non_range_restricted_heads() -> NativeResult<()> {
        let predicates = vec![
            RulePredicate::new(0, PredicateKind::Concept, vec![TermSort::Object])?
                .with_symbol_id(0),
            RulePredicate::new(1, PredicateKind::DataRange, vec![TermSort::Data])?
                .with_symbol_id(1),
        ];
        let wrong = RuleClause::new(
            0,
            vec![atom(0, vec![Term::variable(0, TermSort::Data)])?],
            Vec::new(),
            vec![0],
            vec![0],
        )?;
        assert!(RuleProgram::new(predicates.clone(), vec![wrong]).is_err());

        let head_only = RuleClause::new(
            0,
            Vec::new(),
            vec![atom(0, vec![Term::variable(0, TermSort::Object)])?],
            vec![0],
            Vec::new(),
        )?;
        assert!(RuleProgram::new(predicates, vec![head_only]).is_err());
        Ok(())
    }

    #[test]
    fn lookup_exposes_exact_predicate_kind_and_sorts() -> NativeResult<()> {
        let predicate = RulePredicate::new(
            0,
            PredicateKind::DataRole,
            vec![TermSort::Object, TermSort::Data],
        )?
        .with_role_id(0);
        let program = RuleProgram::new(vec![predicate], Vec::new())?;
        assert_eq!(program.predicate_kind(0)?, PredicateKind::DataRole);
        assert_eq!(
            program.predicate_argument_sorts(0)?,
            [TermSort::Object, TermSort::Data]
        );
        assert!(program.predicate(1).is_err());
        Ok(())
    }

    #[test]
    fn opposite_links_are_reciprocal_and_shape_checked() -> NativeResult<()> {
        let positive = RulePredicate::new(0, PredicateKind::Concept, vec![TermSort::Object])?
            .with_symbol_id(0)
            .with_opposite(1);
        let negative =
            RulePredicate::new(1, PredicateKind::NegatedConcept, vec![TermSort::Object])?
                .with_symbol_id(0)
                .with_opposite(0);
        let program = RuleProgram::new(vec![positive.clone(), negative], Vec::new())?;
        assert_eq!(
            program
                .opposite_predicate(0)?
                .map(|value| value.predicate_id),
            Some(1)
        );

        let malformed =
            RulePredicate::new(1, PredicateKind::NegatedConcept, vec![TermSort::Object])?
                .with_symbol_id(0);
        assert!(RuleProgram::new(vec![positive, malformed], Vec::new()).is_err());
        Ok(())
    }

    #[test]
    fn cardinality_metadata_and_fillers_match_the_python_ir_contract() -> NativeResult<()> {
        let predicates = vec![
            RulePredicate::new(0, PredicateKind::Concept, vec![TermSort::Object])?
                .with_symbol_id(0),
            RulePredicate::new(
                1,
                PredicateKind::ObjectRole,
                vec![TermSort::Object, TermSort::Object],
            )?
            .with_role_id(7),
            RulePredicate::new(2, PredicateKind::AtLeastObject, vec![TermSort::Object])?
                .with_cardinality(3, 7, 0),
            RulePredicate::new(
                3,
                PredicateKind::AnnotatedEquality,
                vec![TermSort::Object; 3],
            )?
            .with_cardinality(3, 7, 0),
            RulePredicate::new(
                4,
                PredicateKind::DataRange,
                vec![TermSort::Data, TermSort::Data],
            )?
            .with_symbol_id(1),
            RulePredicate::new(
                5,
                PredicateKind::DataRole,
                vec![TermSort::Object, TermSort::Data],
            )?
            .with_role_id(9),
            RulePredicate::new(6, PredicateKind::AtLeastData, vec![TermSort::Object])?
                .with_cardinality(2, 9, 4)
                .with_annotation(vec![9, 10]),
        ];
        let program = RuleProgram::new(predicates, Vec::new())?;
        assert_eq!(program.predicate(2)?.cardinality, Some(3));
        assert_eq!(program.predicate(6)?.annotation, [9, 10]);

        let malformed = vec![
            RulePredicate::new(0, PredicateKind::Concept, vec![TermSort::Object])?
                .with_symbol_id(0),
            RulePredicate::new(
                1,
                PredicateKind::ObjectRole,
                vec![TermSort::Object, TermSort::Object],
            )?
            .with_role_id(7),
            RulePredicate::new(2, PredicateKind::AtLeastObject, vec![TermSort::Object])?
                .with_cardinality(2, 7, 1),
        ];
        assert!(RuleProgram::new(malformed, Vec::new()).is_err());
        assert!(RuleProgram::new(
            vec![RulePredicate::new(
                0,
                PredicateKind::Concept,
                vec![TermSort::Object],
            )?],
            Vec::new(),
        )
        .is_err());
        Ok(())
    }
}
