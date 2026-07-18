//! WPR4 classification adapter over the transactional native session.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeSet;
use std::sync::Arc;

use sha2::{Digest, Sha256};

use crate::cancel::CancellationState;
use crate::error::{NativeError, NativeResult};
use crate::input_wire::{
    DecodedAtom, DecodedClause, DecodedConfig, DecodedGroundAtom, DecodedOntology,
    DecodedPredicate, DecodedProgram, DecodedProvenanceEntry, DecodedQuery, DecodedSymbolDomain,
    DecodedSymbolValue, DecodedTerm, PredicateKind, SymbolKind, TermSort,
};
use crate::native_tableau::ProductionTableau;
use crate::rules::{RuleAtom, Term as RuleTerm, TermSort as RuleTermSort};
use crate::services::{
    classify_cached, ClassificationCache, ClassificationCacheKey, ClassificationDomain,
    ClassificationLimits, ClassificationMode, ClassificationProblem, HierarchyIds,
};
use crate::session::{OperationControl, QueryKey, SessionQuery, SessionScheduler};

const OWL_THING_DISPLAY: &str = "class:http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING_DISPLAY: &str = "class:http://www.w3.org/2002/07/owl#Nothing";

struct DomainProblem {
    elements: Vec<u32>,
    top: u32,
    bottom: u32,
    known: Vec<(u32, u32)>,
}

/// Classify one public compiled-ID domain and atomically retain the complete hierarchy.
pub fn classify_domain(
    ontology: &Arc<DecodedOntology>,
    config: &DecodedConfig,
    scheduler: &SessionScheduler<ProductionTableau>,
    cache: &mut ClassificationCache,
    cancellation: &Arc<CancellationState>,
    domain: ClassificationDomain,
) -> NativeResult<Arc<HierarchyIds>> {
    cancellation.poll()?;
    let consistency = scheduler.check_permanent(cancellation.as_ref())?;
    if !consistency.satisfiable {
        return Err(NativeError::inconsistent(
            "classification is undefined for an inconsistent ontology",
        ));
    }
    cancellation.poll()?;
    let input = domain_problem(&ontology.program, domain)?;
    let key = ClassificationCacheKey::new(ontology.metadata.ontology_fingerprint, 0, domain);
    let mode = if config.force_quasi_order_classification || ontology.program.expressivity.non_horn
    {
        ClassificationMode::QuasiOrder
    } else {
        ClassificationMode::Deterministic
    };
    let mut limits = ClassificationLimits::default();
    if let Some(maximum) = config.max_memory_bytes {
        limits.max_memory_bytes = limits.max_memory_bytes.min(maximum);
    }
    let problem = ClassificationProblem {
        elements: &input.elements,
        top: input.top,
        bottom: input.bottom,
        known: &input.known,
        // The compiled told relation is a sound seed, but arbitrary OWL axioms can imply
        // additional class or property inclusions. Missing pairs therefore always use an
        // isolated native counterexample check.
        known_complete: false,
        mode,
        limits,
    };
    let result = classify_cached(
        key,
        problem,
        cache,
        cancellation.as_ref(),
        |pairs, control| test_subsumptions(ontology, scheduler, domain, pairs, control),
    )?;
    Ok(result.hierarchy)
}

fn domain_problem(
    program: &DecodedProgram,
    domain: ClassificationDomain,
) -> NativeResult<DomainProblem> {
    match domain {
        ClassificationDomain::Classes => class_problem(program),
        ClassificationDomain::ObjectProperties => object_property_problem(program),
        ClassificationDomain::DataProperties => data_property_problem(program),
    }
}

fn class_problem(program: &DecodedProgram) -> NativeResult<DomainProblem> {
    let values = symbol_domain(program, SymbolKind::ClassExpression)?;
    let elements = values
        .iter()
        .filter(|value| {
            !value.generated && !value.query_local && value.display.starts_with("class:")
        })
        .map(|value| value.identifier)
        .collect::<Vec<_>>();
    let top = symbol_by_display(values, OWL_THING_DISPLAY)?;
    let bottom = symbol_by_display(values, OWL_NOTHING_DISPLAY)?;
    validate_elements(&elements, top, bottom, "class")?;
    let element_set = elements.iter().copied().collect::<BTreeSet<_>>();
    let mut known = Vec::new();
    for clause in &program.clauses {
        if clause.body.len() != 1
            || clause.head.len() != 1
            || clause.body[0].arguments != clause.head[0].arguments
        {
            continue;
        }
        let Some(child) = positive_concept_symbol(program, &clause.body[0]) else {
            continue;
        };
        let Some(parent) = positive_concept_symbol(program, &clause.head[0]) else {
            continue;
        };
        if element_set.contains(&child) && element_set.contains(&parent) {
            known.push((child, parent));
        }
    }
    known.sort_unstable();
    known.dedup();
    Ok(DomainProblem {
        elements,
        top,
        bottom,
        known,
    })
}

fn object_property_problem(program: &DecodedProgram) -> NativeResult<DomainProblem> {
    let values = symbol_domain(program, SymbolKind::ObjectRole)?;
    let elements = values
        .iter()
        .filter(|value| {
            !value.generated
                && !value.query_local
                && (value.display.starts_with("object_property:")
                    || value.display.starts_with("inverse_object_property:"))
        })
        .map(|value| value.identifier)
        .collect::<Vec<_>>();
    let roles = &program.role_model;
    validate_elements(
        &elements,
        roles.top_object_role_id,
        roles.bottom_object_role_id,
        "object-property",
    )?;
    let element_set = elements.iter().copied().collect::<BTreeSet<_>>();
    let known = canonical_relations(&roles.simple_inclusions, &element_set);
    Ok(DomainProblem {
        elements,
        top: roles.top_object_role_id,
        bottom: roles.bottom_object_role_id,
        known,
    })
}

fn data_property_problem(program: &DecodedProgram) -> NativeResult<DomainProblem> {
    let values = symbol_domain(program, SymbolKind::DataProperty)?;
    let elements = values
        .iter()
        .filter(|value| {
            !value.generated && !value.query_local && value.display.starts_with("data_property:")
        })
        .map(|value| value.identifier)
        .collect::<Vec<_>>();
    let roles = &program.role_model;
    validate_elements(
        &elements,
        roles.top_data_property_id,
        roles.bottom_data_property_id,
        "data-property",
    )?;
    let element_set = elements.iter().copied().collect::<BTreeSet<_>>();
    let known = canonical_relations(&roles.data_inclusions, &element_set);
    Ok(DomainProblem {
        elements,
        top: roles.top_data_property_id,
        bottom: roles.bottom_data_property_id,
        known,
    })
}

fn symbol_domain(
    program: &DecodedProgram,
    kind: SymbolKind,
) -> NativeResult<&[DecodedSymbolValue]> {
    program
        .domain(kind)
        .map(|domain| domain.values.as_slice())
        .ok_or_else(|| NativeError::wire("classification symbol domain is absent"))
}

fn symbol_by_display(values: &[DecodedSymbolValue], display: &str) -> NativeResult<u32> {
    let mut matches = values.iter().filter(|value| value.display == display);
    let identifier = matches
        .next()
        .map(|value| value.identifier)
        .ok_or_else(|| NativeError::wire("classification built-in symbol is absent"))?;
    if matches.next().is_some() {
        return Err(NativeError::wire(
            "classification built-in symbol is duplicated",
        ));
    }
    Ok(identifier)
}

fn validate_elements(elements: &[u32], top: u32, bottom: u32, label: &str) -> NativeResult<()> {
    if elements.len() < 2 || elements.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(NativeError::wire(format!(
            "public {label} classification IDs are not canonical"
        )));
    }
    if top == bottom
        || elements.binary_search(&top).is_err()
        || elements.binary_search(&bottom).is_err()
    {
        return Err(NativeError::wire(format!(
            "public {label} classification domain lacks distinct top and bottom IDs"
        )));
    }
    Ok(())
}

fn canonical_relations(source: &[(u32, u32)], elements: &BTreeSet<u32>) -> Vec<(u32, u32)> {
    let mut relations = source
        .iter()
        .copied()
        .filter(|(child, parent)| elements.contains(child) && elements.contains(parent))
        .collect::<Vec<_>>();
    relations.sort_unstable();
    relations.dedup();
    relations
}

fn positive_concept_symbol(program: &DecodedProgram, atom: &DecodedAtom) -> Option<u32> {
    let predicate = program
        .predicates
        .get(usize::try_from(atom.predicate_id).ok()?)?;
    if predicate.kind != PredicateKind::Concept
        || atom.arguments.len() != 1
        || !matches!(
            atom.arguments.first(),
            Some(DecodedTerm::Variable {
                sort: TermSort::Object,
                ..
            })
        )
    {
        return None;
    }
    predicate.symbol_id
}

fn test_subsumptions(
    ontology: &Arc<DecodedOntology>,
    scheduler: &SessionScheduler<ProductionTableau>,
    domain: ClassificationDomain,
    pairs: &[(u32, u32)],
    control: &dyn OperationControl,
) -> NativeResult<Vec<bool>> {
    control.poll()?;
    let queries = pairs
        .iter()
        .copied()
        .map(|(child, parent)| build_counterexample_query(ontology, domain, child, parent))
        .collect::<NativeResult<Vec<_>>>()?;
    let results = scheduler.check_many(&queries, control)?;
    if results.len() != pairs.len() {
        return Err(NativeError::invariant(
            "classification check batch returned the wrong result count",
        ));
    }
    control.poll()?;
    Ok(results
        .into_iter()
        .map(|result| !result.satisfiable)
        .collect())
}

fn build_counterexample_query(
    ontology: &DecodedOntology,
    domain: ClassificationDomain,
    child: u32,
    parent: u32,
) -> NativeResult<SessionQuery<DecodedQuery>> {
    let query_hash = classification_query_hash(
        &ontology.metadata.ontology_fingerprint,
        domain,
        child,
        parent,
    );
    let mut symbol_domains = ontology.program.symbol_domains.clone();
    let first_local_symbols = symbol_boundaries(&symbol_domains)?;
    let first_local_predicate_id = u32::try_from(ontology.program.predicates.len())
        .map_err(|_| NativeError::wire("classification predicate boundary exceeds u32"))?;
    let mut predicates = ontology.program.predicates.clone();
    let mut facts = Vec::new();

    let first_individual = append_query_symbol(
        &mut symbol_domains,
        SymbolKind::Individual,
        &query_hash,
        0,
        "classification witness",
    )?;
    let second_individual = if domain == ClassificationDomain::ObjectProperties {
        Some(append_query_symbol(
            &mut symbol_domains,
            SymbolKind::Individual,
            &query_hash,
            1,
            "classification target",
        )?)
    } else {
        None
    };
    let data_term = if domain == ClassificationDomain::DataProperties {
        let source_literal_id = append_query_symbol(
            &mut symbol_domains,
            SymbolKind::SourceLiteral,
            &query_hash,
            2,
            "classification symbolic literal",
        )?;
        let data_identity_id = append_query_symbol(
            &mut symbol_domains,
            SymbolKind::DataValue,
            &query_hash,
            3,
            "classification symbolic data value",
        )?;
        Some(DecodedTerm::Data {
            source_literal_id,
            data_identity_id,
        })
    } else {
        None
    };

    let (positive_kind, negative_kind, argument_sorts, ground_arguments) = match domain {
        ClassificationDomain::Classes => (
            PredicateKind::Concept,
            PredicateKind::NegatedConcept,
            vec![TermSort::Object],
            vec![DecodedTerm::Individual {
                individual_id: first_individual,
            }],
        ),
        ClassificationDomain::ObjectProperties => (
            PredicateKind::ObjectRole,
            PredicateKind::NegatedObjectRole,
            vec![TermSort::Object, TermSort::Object],
            vec![
                DecodedTerm::Individual {
                    individual_id: first_individual,
                },
                DecodedTerm::Individual {
                    individual_id: second_individual.ok_or_else(|| {
                        NativeError::invariant("object classification target is absent")
                    })?,
                },
            ],
        ),
        ClassificationDomain::DataProperties => (
            PredicateKind::DataRole,
            PredicateKind::NegatedDataRole,
            vec![TermSort::Object, TermSort::Data],
            vec![
                DecodedTerm::Individual {
                    individual_id: first_individual,
                },
                data_term.ok_or_else(|| {
                    NativeError::invariant("data classification target is absent")
                })?,
            ],
        ),
    };

    let (top, bottom) = domain_bounds(&ontology.program, domain)?;
    // OWL Thing is true of every object witness. Top object/data properties, in contrast,
    // are represented as ordinary role predicates by the rule runtime and must be asserted
    // for this fresh pair to make the counterexample reduction explicit.
    if domain != ClassificationDomain::Classes || child != top {
        let predicate_id = ensure_predicate(
            &mut predicates,
            positive_kind,
            domain,
            child,
            &argument_sorts,
        )?;
        facts.push(DecodedGroundAtom {
            predicate_id,
            arguments: ground_arguments.clone(),
            provenance_ids: vec![0],
        });
    }

    let mut clauses = Vec::new();
    if parent != bottom {
        let positive_parent = ensure_predicate(
            &mut predicates,
            positive_kind,
            domain,
            parent,
            &argument_sorts,
        )?;
        let negative_parent = ensure_predicate(
            &mut predicates,
            negative_kind,
            domain,
            parent,
            &argument_sorts,
        )?;
        facts.push(DecodedGroundAtom {
            predicate_id: negative_parent,
            arguments: ground_arguments,
            provenance_ids: vec![0],
        });
        let variables = argument_sorts
            .iter()
            .copied()
            .enumerate()
            .map(|(index, sort)| {
                Ok(DecodedTerm::Variable {
                    index: u32::try_from(index)
                        .map_err(|_| NativeError::invariant("query variable exceeds u32"))?,
                    sort,
                })
            })
            .collect::<NativeResult<Vec<_>>>()?;
        let body = canonical_atoms(vec![
            DecodedAtom {
                predicate_id: positive_parent,
                arguments: variables.clone(),
            },
            DecodedAtom {
                predicate_id: negative_parent,
                arguments: variables,
            },
        ])?;
        let join_order = (0..body.len())
            .map(|index| {
                u32::try_from(index)
                    .map_err(|_| NativeError::invariant("query join position exceeds u32"))
            })
            .collect::<NativeResult<Vec<_>>>()?;
        clauses.push(DecodedClause {
            clause_id: 0,
            body,
            head: Vec::new(),
            provenance_ids: vec![0],
            join_order,
        });
    }

    let mut expressivity = ontology.program.expressivity;
    expressivity.abox = true;
    if domain == ClassificationDomain::DataProperties {
        expressivity.datatypes = true;
    }
    let overlay = DecodedProgram {
        symbol_domains,
        predicates,
        clauses,
        positive_facts: facts,
        negative_facts: Vec::new(),
        ground_disjunctions: Vec::new(),
        role_model: ontology.program.role_model.clone(),
        datatype_model: ontology.program.datatype_model.clone(),
        expressivity,
        provenance: vec![DecodedProvenanceEntry {
            provenance_id: 0,
            source_sha256: vec![query_hash],
            generated: true,
        }],
    };
    let query = DecodedQuery {
        permanent_program_sha256: ontology.metadata.program_sha256,
        query_hash,
        overlay_program_sha256: Some(query_hash),
        first_local_predicate_id,
        first_local_symbols,
        requires_rebuild: false,
        program: Some(overlay),
        reason: None,
        interpretation: vec![format!("classification:{domain:?}:{child}:{parent}")],
    };
    Ok(SessionQuery::new(QueryKey::new(query_hash), query))
}

fn domain_bounds(
    program: &DecodedProgram,
    domain: ClassificationDomain,
) -> NativeResult<(u32, u32)> {
    match domain {
        ClassificationDomain::Classes => {
            let values = symbol_domain(program, SymbolKind::ClassExpression)?;
            Ok((
                symbol_by_display(values, OWL_THING_DISPLAY)?,
                symbol_by_display(values, OWL_NOTHING_DISPLAY)?,
            ))
        }
        ClassificationDomain::ObjectProperties => Ok((
            program.role_model.top_object_role_id,
            program.role_model.bottom_object_role_id,
        )),
        ClassificationDomain::DataProperties => Ok((
            program.role_model.top_data_property_id,
            program.role_model.bottom_data_property_id,
        )),
    }
}

fn symbol_boundaries(domains: &[DecodedSymbolDomain]) -> NativeResult<[u32; 8]> {
    let mut boundaries = [0_u32; 8];
    let mut seen = [false; 8];
    for domain in domains {
        let index = domain.kind as usize;
        if seen[index] {
            return Err(NativeError::wire(
                "query symbol domain identity is duplicated",
            ));
        }
        seen[index] = true;
        boundaries[index] = u32::try_from(domain.values.len())
            .map_err(|_| NativeError::wire("query symbol boundary exceeds u32"))?;
    }
    if seen.iter().any(|present| !present) {
        return Err(NativeError::wire("query symbol domain is absent"));
    }
    Ok(boundaries)
}

fn append_query_symbol(
    domains: &mut [DecodedSymbolDomain],
    kind: SymbolKind,
    query_hash: &[u8; 32],
    discriminator: u8,
    label: &str,
) -> NativeResult<u32> {
    let domain = domains
        .iter_mut()
        .find(|domain| domain.kind == kind)
        .ok_or_else(|| NativeError::wire("query symbol domain is absent"))?;
    let identifier = u32::try_from(domain.values.len())
        .map_err(|_| NativeError::wire("query symbol identifier exceeds u32"))?;
    let mut key = Vec::with_capacity(34);
    key.extend_from_slice(query_hash);
    key.push(kind as u8);
    key.push(discriminator);
    domain.values.push(DecodedSymbolValue {
        identifier,
        key,
        display: format!("{label}:{discriminator}"),
        generated: false,
        query_local: true,
    });
    Ok(identifier)
}

fn ensure_predicate(
    predicates: &mut Vec<DecodedPredicate>,
    kind: PredicateKind,
    domain: ClassificationDomain,
    symbol_or_role_id: u32,
    argument_sorts: &[TermSort],
) -> NativeResult<u32> {
    let matches = predicates
        .iter()
        .filter(|predicate| {
            predicate.kind == kind
                && match domain {
                    ClassificationDomain::Classes => predicate.symbol_id == Some(symbol_or_role_id),
                    ClassificationDomain::ObjectProperties
                    | ClassificationDomain::DataProperties => {
                        predicate.role_id == Some(symbol_or_role_id)
                    }
                }
        })
        .map(|predicate| predicate.predicate_id)
        .collect::<Vec<_>>();
    if matches.len() > 1 {
        return Err(NativeError::wire(
            "classification predicate identity is duplicated",
        ));
    }
    if let Some(identifier) = matches.first() {
        return Ok(*identifier);
    }
    let predicate_id = u32::try_from(predicates.len())
        .map_err(|_| NativeError::wire("classification predicate ID exceeds u32"))?;
    predicates.push(DecodedPredicate {
        predicate_id,
        kind,
        argument_sorts: argument_sorts.to_vec(),
        symbol_id: (domain == ClassificationDomain::Classes).then_some(symbol_or_role_id),
        role_id: (domain != ClassificationDomain::Classes).then_some(symbol_or_role_id),
        cardinality: None,
        filler_predicate_id: None,
        annotation: Vec::new(),
        internal_key: None,
    });
    Ok(predicate_id)
}

fn canonical_atoms(values: Vec<DecodedAtom>) -> NativeResult<Vec<DecodedAtom>> {
    let mut keyed = values
        .into_iter()
        .map(|atom| decoded_rule_atom(&atom).map(|compiled| (compiled.canonical_bytes(), atom)))
        .collect::<NativeResult<Vec<_>>>()?;
    keyed.sort_by(|left, right| left.0.cmp(&right.0));
    if keyed.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Err(NativeError::invariant(
            "classification clash clause contains duplicate atoms",
        ));
    }
    Ok(keyed.into_iter().map(|(_key, atom)| atom).collect())
}

fn decoded_rule_atom(atom: &DecodedAtom) -> NativeResult<RuleAtom> {
    RuleAtom::new(
        atom.predicate_id,
        atom.arguments
            .iter()
            .map(|term| match term {
                DecodedTerm::Variable { index, sort } => RuleTerm::variable(
                    *index,
                    match sort {
                        TermSort::Object => RuleTermSort::Object,
                        TermSort::Data => RuleTermSort::Data,
                    },
                ),
                DecodedTerm::Individual { individual_id } => RuleTerm::individual(*individual_id),
                DecodedTerm::Data {
                    source_literal_id,
                    data_identity_id,
                } => RuleTerm::data_constant(*source_literal_id, *data_identity_id),
            })
            .collect(),
    )
}

fn classification_query_hash(
    ontology_fingerprint: &[u8; 32],
    domain: ClassificationDomain,
    child: u32,
    parent: u32,
) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(b"pyhermit:native-classification-query:v1\0");
    digest.update(ontology_fingerprint);
    digest.update([match domain {
        ClassificationDomain::Classes => 0,
        ClassificationDomain::ObjectProperties => 1,
        ClassificationDomain::DataProperties => 2,
    }]);
    digest.update(child.to_le_bytes());
    digest.update(parent.to_le_bytes());
    digest.finalize().into()
}
