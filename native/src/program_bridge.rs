//! Linear-time bridge from validated input-wire records to the native rule program.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::blocking::{
    select_blocking_plan, BlockingLimits, BlockingManager, BlockingMode, BlockingRequirements,
    BlockingVocabulary, DirectChecker,
};
use crate::cancel::CancellationState;
use crate::datatypes::{
    decode_datatype_range_model, decode_literal_semantic, DataIdentity, DatatypeLimits,
    DecodedLiteral, NativeDatatypeRangeModel, OpaqueRangePolicy, RangeWireLimits,
};
use crate::error::{NativeError, NativeResult};
use crate::existentials::{
    expansion_program_from_rules, expansion_to_native, ExistentialExpansionManager,
    ExpansionLimits, ExpansionStrategy, SpecialRoleIds,
};
use crate::input_wire::{
    BlockingChoice, DecodedAtom, DecodedClause, DecodedGroundAtom, DecodedOntology,
    DecodedPredicate, DecodedProgram, DecodedTerm, ExistentialChoice,
    PredicateKind as InputPredicateKind, SymbolKind, TermSort as InputTermSort,
};
use crate::model::{DependencySet, NodeHandle, NodeKind};
use crate::nominals::NominalIntroductionManager;
use crate::operation_bridge::{
    blocking_error_to_native, datatype_error_to_native, role_error_to_native,
};
use crate::roles::{RoleAutomatonWire, RoleLimits, RoleRuntime, RoleTransition};
use crate::rules::{
    GroundAtom, PredicateKind, RuleAtom, RuleClause, RuleEngine, RulePredicate, RuleProgram, Term,
    TermSort,
};
use crate::store::TableauKernel;

/// Permanent native rule/kernel owners created without retaining Python objects.
pub struct LoadedRuleState {
    pub kernel: TableauKernel,
    pub engine: RuleEngine,
    pub roles: RoleRuntime,
    pub datatypes: LoadedDatatypeState,
    pub nominals: NominalIntroductionManager,
    pub existentials: ExistentialExpansionManager,
    pub blocking: BlockingManager<NodeHandle>,
}

/// Canonical datatype owners decoded once for the complete native session lifetime.
pub struct LoadedDatatypeState {
    pub ranges: NativeDatatypeRangeModel,
    pub literals: Vec<DecodedLiteral>,
    pub identities: BTreeMap<u32, DataIdentity>,
}

/// Convert the one fully validated input program into the checked rule-engine model.
///
/// Logical-opposite links are not duplicated on the wire. They are recovered with a
/// deterministic ordered index, keeping construction O(predicates log predicates) rather
/// than performing a quadratic search on large biomedical programs.
pub fn compile_rule_program(source: &DecodedProgram) -> NativeResult<RuleProgram> {
    let opposites = opposite_predicate_ids(&source.predicates)?;
    let predicates = source
        .predicates
        .iter()
        .map(|predicate| compile_predicate(predicate, opposites.get(&predicate.predicate_id)))
        .collect::<NativeResult<Vec<_>>>()?;
    let clauses = source
        .clauses
        .iter()
        .map(compile_clause)
        .collect::<NativeResult<Vec<_>>>()?;
    RuleProgram::new(predicates, clauses)
}

/// Allocate permanent source nodes, seed every asserted fact/disjunction, and initialize
/// the native hyperresolution engine as one checked operation root.
pub fn load_permanent_rule_state(
    ontology: &DecodedOntology,
    cancellation: Arc<CancellationState>,
    disjunction_learning: bool,
    existential_choice: ExistentialChoice,
    blocking_choice: BlockingChoice,
) -> NativeResult<LoadedRuleState> {
    cancellation.poll()?;
    let role_runtime = load_role_runtime(&ontology.program, cancellation.as_ref())?;
    let datatypes = load_datatype_state(&ontology.program, cancellation.as_ref())?;
    let mut kernel = TableauKernel::new();
    let named: BTreeSet<_> = ontology.named_individuals.iter().copied().collect();
    let individual_count =
        domain_count(&ontology.program, crate::input_wire::SymbolKind::Individual)?;
    let data_count = domain_count(&ontology.program, crate::input_wire::SymbolKind::DataValue)?;
    let mut source_nodes = BTreeMap::new();
    for individual_id in 0..individual_count {
        cancellation.poll()?;
        source_nodes.insert(
            individual_id,
            kernel.create_node(
                NodeKind::Root,
                None,
                named.contains(&individual_id),
                Some(individual_id),
                None,
                None,
            )?,
        );
    }
    let mut data_nodes = BTreeMap::new();
    for data_identity_id in 0..data_count {
        cancellation.poll()?;
        data_nodes.insert(
            data_identity_id,
            kernel.create_node(NodeKind::Concrete, None, false, None, None, None)?,
        );
    }
    let rule_program = compile_rule_program(&ontology.program)?;
    let reusable_fillers = reusable_atomic_fillers(&ontology.program)?;
    let expansion_program = expansion_program_from_rules(
        &rule_program,
        expansion_special_roles(&ontology.program, &rule_program)?,
        &reusable_fillers,
    )
    .map_err(expansion_to_native)?;
    let expansion_strategy = match existential_choice {
        ExistentialChoice::IndividualReuse => ExpansionStrategy::IndividualReuse,
        ExistentialChoice::Auto | ExistentialChoice::CreationOrder => {
            ExpansionStrategy::CreationOrder
        }
    };
    let existentials = ExistentialExpansionManager::new(
        expansion_program,
        expansion_strategy,
        ExpansionLimits::default(),
    )
    .map_err(expansion_to_native)?;
    let blocking = load_blocking_manager(&ontology.program, &rule_program, blocking_choice)?;
    let mut engine = RuleEngine::new(rule_program, source_nodes, data_nodes, disjunction_learning)?;
    for fact in ontology
        .program
        .positive_facts
        .iter()
        .chain(&ontology.program.negative_facts)
    {
        cancellation.poll()?;
        engine.dispatch_ground_atom(
            &mut kernel,
            compile_ground_atom(fact, &engine)?,
            DependencySet::empty(),
            true,
            &fact.provenance_ids,
        )?;
    }
    for disjunction in &ontology.program.ground_disjunctions {
        cancellation.poll()?;
        let atoms = disjunction
            .disjuncts
            .iter()
            .map(|atom| compile_ground_atom(atom, &engine))
            .collect::<NativeResult<Vec<_>>>()?;
        engine.apply_ground_head(
            &mut kernel,
            atoms,
            DependencySet::empty(),
            &disjunction.provenance_ids,
            &[],
        )?;
    }
    engine.initialize(&mut kernel, cancellation)?;
    kernel.check_invariants()?;
    Ok(LoadedRuleState {
        kernel,
        engine,
        roles: role_runtime,
        datatypes,
        nominals: NominalIntroductionManager::default(),
        existentials,
        blocking,
    })
}

fn reusable_atomic_fillers(program: &DecodedProgram) -> NativeResult<BTreeSet<u32>> {
    let class_symbols = program
        .domain(SymbolKind::ClassExpression)
        .ok_or_else(|| NativeError::wire("class-expression symbol domain is absent"))?;
    let mut reusable = BTreeSet::new();
    for predicate in &program.predicates {
        if predicate.kind != InputPredicateKind::Concept {
            continue;
        }
        let symbol_id = predicate
            .symbol_id
            .ok_or_else(|| NativeError::wire("concept predicate has no class-expression ID"))?;
        let symbol =
            class_symbols
                .values
                .get(usize::try_from(symbol_id).map_err(|_| {
                    NativeError::wire("class-expression ID cannot fit this platform")
                })?)
                .ok_or_else(|| {
                    NativeError::wire("concept predicate class-expression ID is dangling")
                })?;
        if !symbol.generated {
            reusable.insert(predicate.predicate_id);
        }
    }
    Ok(reusable)
}

fn expansion_special_roles(
    source: &DecodedProgram,
    rule_program: &RuleProgram,
) -> NativeResult<SpecialRoleIds> {
    let mut special = SpecialRoleIds {
        top_object: source.role_model.top_object_role_id,
        bottom_object: source.role_model.bottom_object_role_id,
        top_data: source.role_model.top_data_property_id,
        bottom_data: source.role_model.bottom_data_property_id,
    };
    let has_object_obligation = rule_program
        .predicates()
        .iter()
        .any(|predicate| predicate.kind == PredicateKind::AtLeastObject);
    if special.top_object == special.bottom_object {
        if has_object_obligation {
            return Err(NativeError::wire(
                "object existential program aliases top and bottom roles",
            ));
        }
        special.bottom_object = distinct_sentinel(special.top_object);
    }
    let has_data_obligation = rule_program
        .predicates()
        .iter()
        .any(|predicate| predicate.kind == PredicateKind::AtLeastData);
    if special.top_data == special.bottom_data {
        if has_data_obligation {
            return Err(NativeError::wire(
                "data existential program aliases top and bottom properties",
            ));
        }
        special.bottom_data = distinct_sentinel(special.top_data);
    }
    Ok(special)
}

const fn distinct_sentinel(value: u32) -> u32 {
    if value == u32::MAX {
        value - 1
    } else {
        value + 1
    }
}

fn load_blocking_manager(
    source: &DecodedProgram,
    rules: &RuleProgram,
    choice: BlockingChoice,
) -> NativeResult<BlockingManager<NodeHandle>> {
    let mode = match choice {
        BlockingChoice::Auto => BlockingMode::Auto,
        BlockingChoice::Anywhere => BlockingMode::Anywhere,
        BlockingChoice::ValidatedAnywhere => BlockingMode::ValidatedAnywhere,
        BlockingChoice::Ancestor => BlockingMode::Ancestor,
    };
    let requirements = BlockingRequirements {
        has_inverse_roles: source.expressivity.inverse_roles,
        has_nominals: source.expressivity.nominals,
        requires_validated_core: false,
        complex_core: false,
        has_additional_ontology: false,
        query_local_axioms: source
            .symbol_domains
            .iter()
            .flat_map(|domain| &domain.values)
            .any(|value| value.query_local),
        direct_checker_kind: None,
    };
    let plan = select_blocking_plan(mode, requirements).map_err(blocking_error_to_native)?;
    let concept_kinds = [
        PredicateKind::Concept,
        PredicateKind::NegatedConcept,
        PredicateKind::Nominal,
        PredicateKind::NegatedNominal,
        PredicateKind::AutomatonState,
        PredicateKind::DisjointGuard,
        PredicateKind::NamedIndividual,
    ];
    let vocabulary = BlockingVocabulary::new(
        rules
            .predicates()
            .iter()
            .filter(|predicate| concept_kinds.contains(&predicate.kind))
            .map(|predicate| predicate.predicate_id),
        rules
            .predicates()
            .iter()
            .filter(|predicate| predicate.kind == PredicateKind::ObjectRole)
            .map(|predicate| predicate.predicate_id),
    )
    .map_err(blocking_error_to_native)?;
    let checker = DirectChecker::new(
        plan.direct_checker_kind,
        vocabulary,
        source.expressivity.inverse_roles,
    )
    .map_err(blocking_error_to_native)?;
    BlockingManager::new(plan, checker, None, BlockingLimits::default(), 1_000_000)
        .map_err(blocking_error_to_native)
}

fn load_role_runtime(
    program: &DecodedProgram,
    cancellation: &CancellationState,
) -> NativeResult<RoleRuntime> {
    let source = &program.role_model;
    let automata = source
        .automata
        .iter()
        .map(|automaton| RoleAutomatonWire {
            component_id: automaton.component_id,
            state_count: automaton.state_count,
            initial_state: automaton.initial_state,
            final_states: automaton.final_states.clone(),
            transitions: automaton
                .transitions
                .iter()
                .map(|transition| RoleTransition {
                    source_state: transition.source_state,
                    target_state: transition.target_state,
                    role_id: transition.role_id,
                })
                .collect(),
        })
        .collect();
    RoleRuntime::new(
        source.object_role_count,
        source.inverse_role_ids.clone(),
        source.top_object_role_id,
        source.bottom_object_role_id,
        automata,
        RoleLimits::default(),
        cancellation,
    )
    .map_err(role_error_to_native)
}

fn load_datatype_state(
    program: &DecodedProgram,
    cancellation: &CancellationState,
) -> NativeResult<LoadedDatatypeState> {
    let source = &program.datatype_model;
    let range_limits = RangeWireLimits::default();
    let ranges = decode_datatype_range_model(
        source.semantic_payload_json.as_bytes(),
        range_limits,
        OpaqueRangePolicy::Preserve,
        cancellation,
    )
    .map_err(datatype_error_to_native)?;
    let literal_limits = DatatypeLimits::default();
    let mut literals = Vec::new();
    literals
        .try_reserve_exact(source.literal_identities.len())
        .map_err(|_| NativeError::invariant("datatype literal registry allocation failed"))?;
    let mut identities = BTreeMap::new();
    for literal in &source.literal_identities {
        cancellation.poll()?;
        let decoded = decode_literal_semantic(
            literal.source_literal_id,
            literal.semantic_payload_json.as_bytes(),
            literal_limits,
            cancellation,
        )
        .map_err(datatype_error_to_native)?;
        if let DecodedLiteral::Semantic(value) = &decoded {
            if let Some(previous) =
                identities.insert(literal.data_identity_id, value.data_identity.clone())
            {
                if previous != value.data_identity {
                    return Err(NativeError::wire(
                        "datatype identity ID maps to inconsistent semantic values",
                    ));
                }
            }
        }
        literals.push(decoded);
    }
    cancellation.poll()?;
    Ok(LoadedDatatypeState {
        ranges,
        literals,
        identities,
    })
}

fn domain_count(
    program: &DecodedProgram,
    kind: crate::input_wire::SymbolKind,
) -> NativeResult<u32> {
    let count = program
        .domain(kind)
        .ok_or_else(|| NativeError::wire("input program is missing a symbol domain"))?
        .values
        .len();
    u32::try_from(count).map_err(|_| NativeError::wire("symbol domain exceeds u32 identifiers"))
}

fn compile_ground_atom(
    source: &DecodedGroundAtom,
    engine: &RuleEngine,
) -> NativeResult<GroundAtom> {
    let arguments = source
        .arguments
        .iter()
        .map(|term| match term {
            DecodedTerm::Variable { .. } => Err(NativeError::wire(
                "validated ground atom unexpectedly contains a variable",
            )),
            DecodedTerm::Individual { individual_id } => engine
                .source_node(*individual_id)
                .ok_or_else(|| NativeError::wire("ground individual ID is dangling")),
            DecodedTerm::Data {
                data_identity_id, ..
            } => engine
                .data_node(*data_identity_id)
                .ok_or_else(|| NativeError::wire("ground data identity ID is dangling")),
        })
        .collect::<NativeResult<Vec<_>>>()?;
    GroundAtom::new(source.predicate_id, arguments)
}

fn compile_predicate(
    source: &DecodedPredicate,
    opposite: Option<&u32>,
) -> NativeResult<RulePredicate> {
    let mut predicate = RulePredicate::new(
        source.predicate_id,
        predicate_kind(source.kind),
        source
            .argument_sorts
            .iter()
            .copied()
            .map(term_sort)
            .collect(),
    )?;
    if let Some(value) = source.symbol_id {
        predicate = predicate.with_symbol_id(value);
    }
    if let (Some(cardinality), Some(role_id), Some(filler_predicate_id)) = (
        source.cardinality,
        source.role_id,
        source.filler_predicate_id,
    ) {
        predicate = predicate.with_cardinality(cardinality, role_id, filler_predicate_id);
    } else if let Some(value) = source.role_id {
        predicate = predicate.with_role_id(value);
    }
    if !source.annotation.is_empty() {
        predicate = predicate.with_annotation(source.annotation.clone());
    }
    if let Some(value) = &source.internal_key {
        predicate = predicate.with_internal_key(value.clone());
    }
    if let Some(value) = opposite {
        predicate = predicate.with_opposite(*value);
    }
    Ok(predicate)
}

fn compile_clause(source: &DecodedClause) -> NativeResult<RuleClause> {
    RuleClause::new(
        source.clause_id,
        source
            .body
            .iter()
            .map(compile_atom)
            .collect::<NativeResult<Vec<_>>>()?,
        source
            .head
            .iter()
            .map(compile_atom)
            .collect::<NativeResult<Vec<_>>>()?,
        source.provenance_ids.clone(),
        source.join_order.clone(),
    )
}

fn compile_atom(source: &DecodedAtom) -> NativeResult<RuleAtom> {
    RuleAtom::new(
        source.predicate_id,
        source.arguments.iter().map(compile_term).collect(),
    )
}

const fn compile_term(source: &DecodedTerm) -> Term {
    match source {
        DecodedTerm::Variable { index, sort } => Term::variable(*index, term_sort(*sort)),
        DecodedTerm::Individual { individual_id } => Term::individual(*individual_id),
        DecodedTerm::Data {
            source_literal_id,
            data_identity_id,
        } => Term::data_constant(*source_literal_id, *data_identity_id),
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct OppositeKey {
    family: u8,
    sorts: Vec<InputTermSort>,
    symbol_id: Option<u32>,
    role_id: Option<u32>,
    annotation: Vec<u32>,
}

fn opposite_predicate_ids(predicates: &[DecodedPredicate]) -> NativeResult<BTreeMap<u32, u32>> {
    let mut positive = BTreeMap::new();
    let mut negative = BTreeMap::new();
    for predicate in predicates {
        let Some((polarity, family)) = opposite_family(predicate.kind) else {
            continue;
        };
        let key = OppositeKey {
            family,
            sorts: predicate.argument_sorts.clone(),
            symbol_id: predicate.symbol_id,
            role_id: predicate.role_id,
            annotation: predicate.annotation.clone(),
        };
        let selected = if polarity {
            &mut positive
        } else {
            &mut negative
        };
        if selected.insert(key, predicate.predicate_id).is_some() {
            return Err(NativeError::wire(
                "input program contains duplicate logical-opposite predicate identities",
            ));
        }
    }
    let mut output = BTreeMap::new();
    for (key, positive_id) in positive {
        if let Some(negative_id) = negative.get(&key).copied() {
            output.insert(positive_id, negative_id);
            output.insert(negative_id, positive_id);
        }
    }
    Ok(output)
}

const fn opposite_family(kind: InputPredicateKind) -> Option<(bool, u8)> {
    match kind {
        InputPredicateKind::Concept => Some((true, 0)),
        InputPredicateKind::NegatedConcept => Some((false, 0)),
        InputPredicateKind::Nominal => Some((true, 1)),
        InputPredicateKind::NegatedNominal => Some((false, 1)),
        InputPredicateKind::ObjectRole => Some((true, 2)),
        InputPredicateKind::NegatedObjectRole => Some((false, 2)),
        InputPredicateKind::DataRole => Some((true, 3)),
        InputPredicateKind::NegatedDataRole => Some((false, 3)),
        InputPredicateKind::DataRange => Some((true, 4)),
        InputPredicateKind::NegatedDataRange => Some((false, 4)),
        InputPredicateKind::Equality => Some((true, 5)),
        InputPredicateKind::Inequality => Some((false, 5)),
        InputPredicateKind::AtLeastObject
        | InputPredicateKind::AtLeastData
        | InputPredicateKind::AnnotatedEquality
        | InputPredicateKind::AutomatonState
        | InputPredicateKind::DisjointGuard
        | InputPredicateKind::OrderingGuard
        | InputPredicateKind::NamedIndividual => None,
    }
}

const fn term_sort(value: InputTermSort) -> TermSort {
    match value {
        InputTermSort::Object => TermSort::Object,
        InputTermSort::Data => TermSort::Data,
    }
}

const fn predicate_kind(value: InputPredicateKind) -> PredicateKind {
    match value {
        InputPredicateKind::Concept => PredicateKind::Concept,
        InputPredicateKind::NegatedConcept => PredicateKind::NegatedConcept,
        InputPredicateKind::Nominal => PredicateKind::Nominal,
        InputPredicateKind::NegatedNominal => PredicateKind::NegatedNominal,
        InputPredicateKind::ObjectRole => PredicateKind::ObjectRole,
        InputPredicateKind::NegatedObjectRole => PredicateKind::NegatedObjectRole,
        InputPredicateKind::DataRole => PredicateKind::DataRole,
        InputPredicateKind::NegatedDataRole => PredicateKind::NegatedDataRole,
        InputPredicateKind::DataRange => PredicateKind::DataRange,
        InputPredicateKind::NegatedDataRange => PredicateKind::NegatedDataRange,
        InputPredicateKind::Equality => PredicateKind::Equality,
        InputPredicateKind::Inequality => PredicateKind::Inequality,
        InputPredicateKind::AtLeastObject => PredicateKind::AtLeastObject,
        InputPredicateKind::AtLeastData => PredicateKind::AtLeastData,
        InputPredicateKind::AnnotatedEquality => PredicateKind::AnnotatedEquality,
        InputPredicateKind::AutomatonState => PredicateKind::AutomatonState,
        InputPredicateKind::DisjointGuard => PredicateKind::DisjointGuard,
        InputPredicateKind::OrderingGuard => PredicateKind::OrderingGuard,
        InputPredicateKind::NamedIndividual => PredicateKind::NamedIndividual,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cancel::CancellationHandle;
    use crate::input_wire::{decode_ontology, DecodeLimits};

    fn decode_hex(value: &str) -> Vec<u8> {
        value
            .as_bytes()
            .chunks_exact(2)
            .filter_map(|pair| {
                let text = std::str::from_utf8(pair).ok()?;
                u8::from_str_radix(text, 16).ok()
            })
            .collect()
    }

    fn golden_ontology() -> Vec<u8> {
        let fixture: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/data/native-input-v1.json"))
                .unwrap_or(serde_json::Value::Null);
        fixture
            .get("documents")
            .and_then(|documents| documents.get("ontology"))
            .and_then(|document| document.get("hex"))
            .and_then(serde_json::Value::as_str)
            .map_or_else(Vec::new, decode_hex)
    }

    #[test]
    fn production_input_compiles_to_the_checked_rule_model() -> NativeResult<()> {
        let ontology = decode_ontology(golden_ontology(), &DecodeLimits::default())
            .map_err(|error| NativeError::wire(error.message))?;
        let rules = compile_rule_program(&ontology.program)?;
        assert_eq!(rules.predicates().len(), ontology.program.predicates.len());
        assert_eq!(rules.clauses().len(), ontology.program.clauses.len());
        Ok(())
    }

    #[test]
    fn production_input_loads_one_owned_permanent_rule_state() -> NativeResult<()> {
        let ontology = decode_ontology(golden_ontology(), &DecodeLimits::default())
            .map_err(|error| NativeError::wire(error.message))?;
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let loaded = load_permanent_rule_state(
            &ontology,
            cancellation,
            true,
            ExistentialChoice::CreationOrder,
            BlockingChoice::Auto,
        )?;
        assert!(loaded.engine.initialized());
        loaded.kernel.check_invariants()?;
        Ok(())
    }

    #[test]
    fn logical_opposites_are_recovered_without_wire_duplication() -> NativeResult<()> {
        let source = vec![
            decoded_predicate(0, InputPredicateKind::Concept, Some(7)),
            decoded_predicate(1, InputPredicateKind::NegatedConcept, Some(7)),
            decoded_predicate(2, InputPredicateKind::Concept, Some(8)),
        ];
        let opposites = opposite_predicate_ids(&source)?;
        assert_eq!(opposites.get(&0), Some(&1));
        assert_eq!(opposites.get(&1), Some(&0));
        assert!(!opposites.contains_key(&2));
        Ok(())
    }

    fn decoded_predicate(
        predicate_id: u32,
        kind: InputPredicateKind,
        symbol_id: Option<u32>,
    ) -> DecodedPredicate {
        DecodedPredicate {
            predicate_id,
            kind,
            argument_sorts: vec![InputTermSort::Object],
            symbol_id,
            role_id: None,
            cardinality: None,
            filler_predicate_id: None,
            annotation: Vec::new(),
            internal_key: None,
        }
    }
}
