//! First transactional phase of the encoded-native compiler.
//!
//! This phase performs exhaustive root dispatch and extracts the source entity
//! symbol seed plus declared-entity metadata into the same owned records used
//! by the scalar-wire decoder. Normalization may append generated entities in a
//! later phase; nothing here is sufficient to publish a reasoning session.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use serde::Serialize;

use super::model::{
    ComponentKind, ComponentRef, ComponentValue, NodeId, RootKind, ScalarRef, ValidatedModel,
};
use super::{u32_at, ByteSource, EncodedResult, EncodedValidationError};
use crate::input_wire::{DecodedEntity, DecodedSymbolDomain, DecodedSymbolValue, SymbolKind};

const SYMBOL_PHASE_SCHEMA_VERSION: u16 = 1;
const ENTITY_TAG: u16 = 2;
const IRI_TAG: u16 = 1;
const DECLARATION_TAG: u16 = 60;
const POSTINGS_ALL: u8 = 0;
const POSTINGS_INCLUDE: u8 = 1;
const POSTINGS_EXCLUDE: u8 = 2;

const BUILTIN_ENTITIES: &[(EntityKind, &str)] = &[
    (EntityKind::Class, "http://www.w3.org/2002/07/owl#Thing"),
    (EntityKind::Class, "http://www.w3.org/2002/07/owl#Nothing"),
    (
        EntityKind::Datatype,
        "http://www.w3.org/2000/01/rdf-schema#Literal",
    ),
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SymbolPhaseLimits {
    pub max_entities: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for SymbolPhaseLimits {
    fn default() -> Self {
        Self {
            max_entities: 16_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntityKind {
    Class,
    Datatype,
    ObjectProperty,
    DataProperty,
    AnnotationProperty,
    NamedIndividual,
}

impl EntityKind {
    fn from_scalar<B: ByteSource>(value: ScalarRef<B>) -> EncodedResult<Self> {
        if value.kind() != ComponentKind::Enum {
            return Err(EncodedValidationError::invariant(
                "validated entity kind is not an enum",
            ));
        }
        if value.bytes_equal(b"class") {
            Ok(Self::Class)
        } else if value.bytes_equal(b"datatype") {
            Ok(Self::Datatype)
        } else if value.bytes_equal(b"object_property") {
            Ok(Self::ObjectProperty)
        } else if value.bytes_equal(b"data_property") {
            Ok(Self::DataProperty)
        } else if value.bytes_equal(b"annotation_property") {
            Ok(Self::AnnotationProperty)
        } else if value.bytes_equal(b"named_individual") {
            Ok(Self::NamedIndividual)
        } else {
            Err(EncodedValidationError::invariant(
                "validated entity kind is no longer recognized",
            ))
        }
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Class => "class",
            Self::Datatype => "datatype",
            Self::ObjectProperty => "object_property",
            Self::DataProperty => "data_property",
            Self::AnnotationProperty => "annotation_property",
            Self::NamedIndividual => "named_individual",
        }
    }
}

/// Exact semantic destination for every schema-1 root constructor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RootHandler {
    OntologyAnnotation,
    Declaration,
    SubClassOf,
    EquivalentClasses,
    DisjointClasses,
    DisjointUnion,
    SubObjectPropertyOf,
    EquivalentObjectProperties,
    DisjointObjectProperties,
    InverseObjectProperties,
    ObjectPropertyDomain,
    ObjectPropertyRange,
    FunctionalObjectProperty,
    InverseFunctionalObjectProperty,
    ReflexiveObjectProperty,
    IrreflexiveObjectProperty,
    SymmetricObjectProperty,
    AsymmetricObjectProperty,
    TransitiveObjectProperty,
    SubDataPropertyOf,
    EquivalentDataProperties,
    DisjointDataProperties,
    DataPropertyDomain,
    DataPropertyRange,
    FunctionalDataProperty,
    DatatypeDefinition,
    HasKey,
    SameIndividual,
    DifferentIndividuals,
    ClassAssertion,
    ObjectPropertyAssertion,
    NegativeObjectPropertyAssertion,
    DataPropertyAssertion,
    NegativeDataPropertyAssertion,
    AnnotationAssertion,
    SubAnnotationPropertyOf,
    AnnotationPropertyDomain,
    AnnotationPropertyRange,
    SwrlRule,
}

impl RootHandler {
    fn from_root(kind: RootKind, tag: u16) -> EncodedResult<Self> {
        let handler = match (kind, tag) {
            (RootKind::OntologyAnnotation, 5) => Self::OntologyAnnotation,
            (RootKind::Axiom, 60) => Self::Declaration,
            (RootKind::Axiom, 61) => Self::SubClassOf,
            (RootKind::Axiom, 62) => Self::EquivalentClasses,
            (RootKind::Axiom, 63) => Self::DisjointClasses,
            (RootKind::Axiom, 64) => Self::DisjointUnion,
            (RootKind::Axiom, 70) => Self::SubObjectPropertyOf,
            (RootKind::Axiom, 71) => Self::EquivalentObjectProperties,
            (RootKind::Axiom, 72) => Self::DisjointObjectProperties,
            (RootKind::Axiom, 73) => Self::InverseObjectProperties,
            (RootKind::Axiom, 74) => Self::ObjectPropertyDomain,
            (RootKind::Axiom, 75) => Self::ObjectPropertyRange,
            (RootKind::Axiom, 76) => Self::FunctionalObjectProperty,
            (RootKind::Axiom, 77) => Self::InverseFunctionalObjectProperty,
            (RootKind::Axiom, 78) => Self::ReflexiveObjectProperty,
            (RootKind::Axiom, 79) => Self::IrreflexiveObjectProperty,
            (RootKind::Axiom, 80) => Self::SymmetricObjectProperty,
            (RootKind::Axiom, 81) => Self::AsymmetricObjectProperty,
            (RootKind::Axiom, 82) => Self::TransitiveObjectProperty,
            (RootKind::Axiom, 90) => Self::SubDataPropertyOf,
            (RootKind::Axiom, 91) => Self::EquivalentDataProperties,
            (RootKind::Axiom, 92) => Self::DisjointDataProperties,
            (RootKind::Axiom, 93) => Self::DataPropertyDomain,
            (RootKind::Axiom, 94) => Self::DataPropertyRange,
            (RootKind::Axiom, 95) => Self::FunctionalDataProperty,
            (RootKind::Axiom, 100) => Self::DatatypeDefinition,
            (RootKind::Axiom, 101) => Self::HasKey,
            (RootKind::Axiom, 110) => Self::SameIndividual,
            (RootKind::Axiom, 111) => Self::DifferentIndividuals,
            (RootKind::Axiom, 112) => Self::ClassAssertion,
            (RootKind::Axiom, 113) => Self::ObjectPropertyAssertion,
            (RootKind::Axiom, 114) => Self::NegativeObjectPropertyAssertion,
            (RootKind::Axiom, 115) => Self::DataPropertyAssertion,
            (RootKind::Axiom, 116) => Self::NegativeDataPropertyAssertion,
            (RootKind::Axiom, 120) => Self::AnnotationAssertion,
            (RootKind::Axiom, 121) => Self::SubAnnotationPropertyOf,
            (RootKind::Axiom, 122) => Self::AnnotationPropertyDomain,
            (RootKind::Axiom, 123) => Self::AnnotationPropertyRange,
            (RootKind::Extension, 148) => Self::SwrlRule,
            _ => {
                return Err(EncodedValidationError::invariant(
                    "validated root has no encoded compiler dispatch handler",
                ));
            }
        };
        Ok(handler)
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::OntologyAnnotation => "OntologyAnnotation",
            Self::Declaration => "Declaration",
            Self::SubClassOf => "SubClassOf",
            Self::EquivalentClasses => "EquivalentClasses",
            Self::DisjointClasses => "DisjointClasses",
            Self::DisjointUnion => "DisjointUnion",
            Self::SubObjectPropertyOf => "SubObjectPropertyOf",
            Self::EquivalentObjectProperties => "EquivalentObjectProperties",
            Self::DisjointObjectProperties => "DisjointObjectProperties",
            Self::InverseObjectProperties => "InverseObjectProperties",
            Self::ObjectPropertyDomain => "ObjectPropertyDomain",
            Self::ObjectPropertyRange => "ObjectPropertyRange",
            Self::FunctionalObjectProperty => "FunctionalObjectProperty",
            Self::InverseFunctionalObjectProperty => "InverseFunctionalObjectProperty",
            Self::ReflexiveObjectProperty => "ReflexiveObjectProperty",
            Self::IrreflexiveObjectProperty => "IrreflexiveObjectProperty",
            Self::SymmetricObjectProperty => "SymmetricObjectProperty",
            Self::AsymmetricObjectProperty => "AsymmetricObjectProperty",
            Self::TransitiveObjectProperty => "TransitiveObjectProperty",
            Self::SubDataPropertyOf => "SubDataPropertyOf",
            Self::EquivalentDataProperties => "EquivalentDataProperties",
            Self::DisjointDataProperties => "DisjointDataProperties",
            Self::DataPropertyDomain => "DataPropertyDomain",
            Self::DataPropertyRange => "DataPropertyRange",
            Self::FunctionalDataProperty => "FunctionalDataProperty",
            Self::DatatypeDefinition => "DatatypeDefinition",
            Self::HasKey => "HasKey",
            Self::SameIndividual => "SameIndividual",
            Self::DifferentIndividuals => "DifferentIndividuals",
            Self::ClassAssertion => "ClassAssertion",
            Self::ObjectPropertyAssertion => "ObjectPropertyAssertion",
            Self::NegativeObjectPropertyAssertion => "NegativeObjectPropertyAssertion",
            Self::DataPropertyAssertion => "DataPropertyAssertion",
            Self::NegativeDataPropertyAssertion => "NegativeDataPropertyAssertion",
            Self::AnnotationAssertion => "AnnotationAssertion",
            Self::SubAnnotationPropertyOf => "SubAnnotationPropertyOf",
            Self::AnnotationPropertyDomain => "AnnotationPropertyDomain",
            Self::AnnotationPropertyRange => "AnnotationPropertyRange",
            Self::SwrlRule => "SWRLRule",
        }
    }

    const fn contributes_source_symbols(self) -> bool {
        !matches!(
            self,
            Self::OntologyAnnotation
                | Self::AnnotationAssertion
                | Self::SubAnnotationPropertyOf
                | Self::AnnotationPropertyDomain
                | Self::AnnotationPropertyRange
                | Self::SwrlRule
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DispatchedRoot {
    pub kind: RootKind,
    pub node: NodeId,
    pub tag: u16,
    pub handler: RootHandler,
}

/// Owned output of the first encoded compiler transaction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolPhase {
    pub roots: Vec<DispatchedRoot>,
    pub entity_domain: DecodedSymbolDomain,
    pub declared_entities: Vec<DecodedEntity>,
    pub work: u64,
    pub owned_bytes: usize,
    entity_node_symbols: Vec<(NodeId, u32)>,
    source_declared_entity_ids: Vec<u32>,
    semantic_nodes: Vec<u8>,
    manifest_limit: usize,
}

impl SymbolPhase {
    /// Resolve a reachable encoded entity node into the owned entity domain.
    ///
    /// The mapping is deliberately private to encoded compiler phases.  It
    /// prevents later transactions from retaining or re-reading Python-owned
    /// buffers after symbol extraction has completed.
    pub(super) fn entity_symbol_for_node(&self, node: NodeId) -> Option<u32> {
        self.entity_node_symbols
            .binary_search_by_key(&node, |(candidate, _)| *candidate)
            .ok()
            .map(|index| self.entity_node_symbols[index].1)
    }

    /// Return whether a reachable entity has a declaration in its source.
    ///
    /// Source-local root selection controls the published declaration set, but
    /// normalization still needs the underlying declaration to prove that a
    /// restriction input has stable scalar symbol identity.
    pub(super) fn entity_has_source_declaration(&self, entity_id: u32) -> bool {
        self.source_declared_entity_ids
            .binary_search(&entity_id)
            .is_ok()
    }

    /// Return whether a node is reachable from the semantic fields of a
    /// selected logical root. Root annotations and ignored nonlogical roots are
    /// deliberately absent from this bitmap.
    pub(super) fn semantic_node_is_reachable(&self, node: NodeId) -> bool {
        usize::try_from(node.get() - 1)
            .ok()
            .and_then(|index| self.semantic_nodes.get(index))
            .is_some_and(|state| *state != 0)
    }

    /// Canonical test-only manifest used for scalar/encoded differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        let roots = self
            .roots
            .iter()
            .map(|root| RootManifest {
                kind: root_kind_name(root.kind),
                tag: root.tag,
                handler: root.handler.as_str(),
            })
            .collect();
        let entity_symbols = self
            .entity_domain
            .values
            .iter()
            .map(|value| EntitySymbolManifest {
                identifier: value.identifier,
                key_hex: crate::model::hex(&value.key),
                display: &value.display,
                generated: value.generated,
                query_local: value.query_local,
            })
            .collect();
        let declared_entities = self
            .declared_entities
            .iter()
            .map(|value| DeclaredEntityManifest {
                kind: &value.kind,
                iri: &value.iri,
                entity_id: value.entity_id,
            })
            .collect();
        let encoded = serde_json::to_vec(&SymbolManifest {
            schema_version: SYMBOL_PHASE_SCHEMA_VERSION,
            root_dispatch: roots,
            entity_symbols,
            declared_entities,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("encoded symbol manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "encoded symbol manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct SymbolManifest<'a> {
    schema_version: u16,
    root_dispatch: Vec<RootManifest>,
    entity_symbols: Vec<EntitySymbolManifest<'a>>,
    declared_entities: Vec<DeclaredEntityManifest<'a>>,
}

#[derive(Serialize)]
struct RootManifest {
    kind: &'static str,
    tag: u16,
    handler: &'static str,
}

#[derive(Serialize)]
struct EntitySymbolManifest<'a> {
    identifier: u32,
    key_hex: String,
    display: &'a str,
    generated: bool,
    query_local: bool,
}

#[derive(Serialize)]
struct DeclaredEntityManifest<'a> {
    kind: &'a str,
    iri: &'a str,
    entity_id: u32,
}

#[derive(Debug, Eq, PartialEq)]
struct ExtractedEntity {
    key: Vec<u8>,
    kind: EntityKind,
    iri: String,
    display: String,
}

#[derive(Debug, Eq, PartialEq)]
struct DeclaredIdentity {
    key: Vec<u8>,
    kind: EntityKind,
    iri: String,
}

struct PhaseBudget {
    limits: SymbolPhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: SymbolPhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("encoded symbol work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("encoded symbol work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "encoded symbol extraction exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("encoded symbol owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "encoded symbol extraction exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn entity(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_entities {
            Err(EncodedValidationError::resource(
                "encoded source entity count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }
}

#[derive(Clone, Copy)]
struct RootPostings<S: ByteSource> {
    postings: S,
    count: usize,
    cursor: usize,
}

impl<S: ByteSource> RootPostings<S> {
    fn new(postings: S, root_count: usize, name: &'static str) -> EncodedResult<Self> {
        if postings.len() % 4 != 0 {
            return Err(EncodedValidationError::protocol(format!(
                "encoded root {name} contain a partial u32"
            )));
        }
        let count = postings.len() / 4;
        if count == 0 {
            return Err(EncodedValidationError::protocol(format!(
                "encoded root {name} are empty"
            )));
        }
        let mut previous = 0_usize;
        for index in 0..count {
            let current = usize::try_from(u32_at(postings, index, name)?).map_err(|_| {
                EncodedValidationError::resource(format!(
                    "encoded root {name} exceeds the platform index width"
                ))
            })?;
            if current <= previous || current > root_count {
                return Err(EncodedValidationError::protocol(format!(
                    "encoded root {name} are not sorted unique in-range IDs"
                )));
            }
            previous = current;
        }
        Ok(Self {
            postings,
            count,
            cursor: 0,
        })
    }

    fn contains(&mut self, root_index: usize) -> EncodedResult<bool> {
        if self.cursor >= self.count {
            return Ok(false);
        }
        let current = usize::try_from(u32_at(self.postings, self.cursor, "root posting")?)
            .map_err(|_| {
                EncodedValidationError::resource(
                    "encoded root posting exceeds the platform index width",
                )
            })?;
        let local_root_id = root_index
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("encoded root index overflowed"))?;
        if current == local_root_id {
            self.cursor += 1;
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

#[derive(Clone, Copy)]
enum RootSelection<S: ByteSource> {
    All,
    Include(RootPostings<S>),
    Exclude(RootPostings<S>),
}

impl<S: ByteSource> RootSelection<S> {
    const fn selected_count(&self, root_count: usize) -> usize {
        match self {
            Self::All => root_count,
            Self::Include(inclusions) => inclusions.count,
            Self::Exclude(exclusions) => root_count - exclusions.count,
        }
    }

    const fn validation_work(&self) -> usize {
        match self {
            Self::All => 0,
            Self::Include(inclusions) => inclusions.count,
            Self::Exclude(exclusions) => exclusions.count,
        }
    }

    fn excludes(&mut self, root_index: usize) -> EncodedResult<bool> {
        match self {
            Self::All => Ok(false),
            Self::Include(inclusions) => Ok(!inclusions.contains(root_index)?),
            Self::Exclude(exclusions) => exclusions.contains(root_index),
        }
    }
}

/// Validate and own the root-dispatch/entity-symbol seed without publishing it.
pub fn compile_symbol_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    limits: SymbolPhaseLimits,
) -> EncodedResult<SymbolPhase> {
    compile_symbol_phase_with_selection(model, limits, RootSelection::<&[u8]>::All)
}

/// Compile only roots selected by source-local ALL, INCLUDE, or EXCLUDE postings.
pub fn compile_symbol_phase_selected<B: ByteSource, S: ByteSource>(
    model: &ValidatedModel<B>,
    limits: SymbolPhaseLimits,
    posting_mode: u8,
    postings: S,
) -> EncodedResult<SymbolPhase> {
    let selection = match posting_mode {
        POSTINGS_ALL if postings.is_empty() => RootSelection::All,
        POSTINGS_ALL => {
            return Err(EncodedValidationError::protocol(
                "ALL encoded root selection carries exclusions",
            ));
        }
        POSTINGS_INCLUDE => RootSelection::Include(RootPostings::new(
            postings,
            model.summary().root_count,
            "inclusions",
        )?),
        POSTINGS_EXCLUDE => RootSelection::Exclude(RootPostings::new(
            postings,
            model.summary().root_count,
            "exclusions",
        )?),
        _ => {
            return Err(EncodedValidationError::protocol(
                "encoded root selection mode is unsupported",
            ));
        }
    };
    compile_symbol_phase_with_selection(model, limits, selection)
}

fn compile_symbol_phase_with_selection<B: ByteSource, S: ByteSource>(
    model: &ValidatedModel<B>,
    limits: SymbolPhaseLimits,
    mut selection: RootSelection<S>,
) -> EncodedResult<SymbolPhase> {
    let summary = model.summary();
    let mut budget = PhaseBudget::new(limits);
    budget.claim_work(selection.validation_work())?;
    let selected_root_count = selection.selected_count(summary.root_count);
    let mut roots = Vec::new();
    budget.claim_owned(
        selected_root_count
            .checked_mul(size_of::<DispatchedRoot>())
            .ok_or_else(|| {
                EncodedValidationError::resource("encoded root dispatch allocation overflowed")
            })?,
    )?;
    roots
        .try_reserve_exact(selected_root_count)
        .map_err(|_| EncodedValidationError::resource("encoded root dispatch allocation failed"))?;
    let mut declarations = Vec::<DeclaredIdentity>::new();
    for root_index in 0..summary.root_count {
        budget.claim_work(1)?;
        if selection.excludes(root_index)? {
            continue;
        }
        let root = model
            .root(root_index)?
            .ok_or_else(|| EncodedValidationError::invariant("validated root row disappeared"))?;
        let node = model.node(root.node())?;
        let handler = RootHandler::from_root(root.kind(), node.tag())?;
        roots.push(DispatchedRoot {
            kind: root.kind(),
            node: root.node(),
            tag: node.tag(),
            handler,
        });
        if node.tag() == DECLARATION_TAG {
            let identity = declaration_identity(model, root.node(), &mut budget)?;
            budget.claim_owned(size_of::<DeclaredIdentity>())?;
            declarations.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource("encoded declaration allocation failed")
            })?;
            declarations.push(identity);
        }
    }

    let semantic_nodes = semantic_reachability(model, &roots, &mut budget)?;
    let mut entities = Vec::<ExtractedEntity>::new();
    let mut source_entity_nodes = Vec::<(NodeId, Vec<u8>)>::new();
    for (node_index, reachable) in semantic_nodes.iter().copied().enumerate() {
        budget.claim_work(1)?;
        let node = model
            .node_at(node_index)?
            .ok_or_else(|| EncodedValidationError::invariant("validated node row disappeared"))?;
        if node.tag() != ENTITY_TAG {
            continue;
        }
        // Every encoded entity must still satisfy the frozen core model even
        // when scalar normalization ignores its annotation-only occurrence.
        let entity = extract_entity(model, node.id(), &mut budget)?;
        if reachable == 0 {
            continue;
        }
        budget.entity(entities.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("encoded source entity count overflowed")
        })?)?;
        if entities
            .last()
            .is_some_and(|previous| previous.key >= entity.key)
        {
            return Err(EncodedValidationError::invariant(
                "validated source entities are not in canonical key order",
            ));
        }
        budget.claim_owned(size_of::<ExtractedEntity>())?;
        budget.claim_owned(size_of::<(NodeId, Vec<u8>)>())?;
        budget.claim_owned(entity.key.len())?;
        entities.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("encoded source entity allocation failed")
        })?;
        source_entity_nodes.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("encoded entity-node mapping allocation failed")
        })?;
        source_entity_nodes.push((node.id(), entity.key.clone()));
        entities.push(entity);
    }
    for (kind, iri) in BUILTIN_ENTITIES {
        let builtin = entity_from_parts(*kind, iri, &mut budget)?;
        match entities.binary_search_by(|candidate| candidate.key.cmp(&builtin.key)) {
            Ok(_) => {}
            Err(position) => {
                budget.entity(entities.len().checked_add(1).ok_or_else(|| {
                    EncodedValidationError::resource("encoded source entity count overflowed")
                })?)?;
                budget.claim_work(entities.len().saturating_sub(position))?;
                budget.claim_owned(size_of::<ExtractedEntity>())?;
                entities.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource("encoded built-in entity allocation failed")
                })?;
                entities.insert(position, builtin);
            }
        }
    }

    budget.claim_work(sort_work(declarations.len()))?;
    declarations.sort_by(|left, right| {
        (left.kind.as_str(), left.iri.as_str()).cmp(&(right.kind.as_str(), right.iri.as_str()))
    });
    declarations.dedup_by(|left, right| left.kind == right.kind && left.iri == right.iri);

    let mut declared_entities = Vec::new();
    budget.claim_owned(
        declarations
            .len()
            .checked_mul(size_of::<DecodedEntity>())
            .ok_or_else(|| {
                EncodedValidationError::resource("encoded declaration output size overflowed")
            })?,
    )?;
    declared_entities
        .try_reserve_exact(declarations.len())
        .map_err(|_| {
            EncodedValidationError::resource("encoded declaration output allocation failed")
        })?;
    for declaration in declarations {
        budget.claim_work(binary_search_work(entities.len()))?;
        let entity_id = entities
            .binary_search_by(|entity| entity.key.cmp(&declaration.key))
            .map_err(|_| {
                EncodedValidationError::invariant(
                    "declared entity is absent from the extracted entity domain",
                )
            })?;
        budget.claim_owned(declaration.kind.as_str().len())?;
        budget.claim_owned(declaration.iri.len())?;
        declared_entities.push(DecodedEntity {
            kind: declaration.kind.as_str().to_owned(),
            iri: declaration.iri,
            entity_id: u32::try_from(entity_id).map_err(|_| {
                EncodedValidationError::resource("encoded entity symbol ID exceeds u32")
            })?,
        });
    }

    let mut entity_node_symbols = Vec::new();
    budget.claim_owned(
        source_entity_nodes
            .len()
            .checked_mul(size_of::<(NodeId, u32)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("encoded entity-node output size overflowed")
            })?,
    )?;
    entity_node_symbols
        .try_reserve_exact(source_entity_nodes.len())
        .map_err(|_| {
            EncodedValidationError::resource("encoded entity-node output allocation failed")
        })?;
    for (node, key) in source_entity_nodes {
        budget.claim_work(binary_search_work(entities.len()))?;
        let identifier = entities
            .binary_search_by(|entity| entity.key.cmp(&key))
            .map_err(|_| {
                EncodedValidationError::invariant(
                    "reachable entity node is absent from the extracted entity domain",
                )
            })?;
        entity_node_symbols.push((
            node,
            u32::try_from(identifier).map_err(|_| {
                EncodedValidationError::resource("encoded entity symbol ID exceeds u32")
            })?,
        ));
    }
    let source_declared_entity_ids =
        source_declared_entity_ids(model, &semantic_nodes, &entity_node_symbols, &mut budget)?;

    let mut values = Vec::new();
    values.try_reserve_exact(entities.len()).map_err(|_| {
        EncodedValidationError::resource("encoded entity symbol output allocation failed")
    })?;
    budget.claim_owned(
        entities
            .len()
            .checked_mul(size_of::<DecodedSymbolValue>())
            .ok_or_else(|| {
                EncodedValidationError::resource("encoded entity symbol output size overflowed")
            })?,
    )?;
    for (identifier, entity) in entities.into_iter().enumerate() {
        values.push(DecodedSymbolValue {
            identifier: u32::try_from(identifier).map_err(|_| {
                EncodedValidationError::resource("encoded entity symbol ID exceeds u32")
            })?,
            key: entity.key,
            display: entity.display,
            generated: false,
            query_local: false,
        });
    }
    Ok(SymbolPhase {
        roots,
        entity_domain: DecodedSymbolDomain {
            kind: SymbolKind::Entity,
            values,
        },
        declared_entities,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        entity_node_symbols,
        source_declared_entity_ids,
        semantic_nodes,
        manifest_limit: limits.max_manifest_bytes,
    })
}

fn source_declared_entity_ids<B: ByteSource>(
    model: &ValidatedModel<B>,
    semantic_nodes: &[u8],
    entity_node_symbols: &[(NodeId, u32)],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let mut identifiers = Vec::new();
    for root_index in 0..model.summary().root_count {
        budget.claim_work(1)?;
        let root = model
            .root(root_index)?
            .ok_or_else(|| EncodedValidationError::invariant("validated root row disappeared"))?;
        let node = model.node(root.node())?;
        if node.tag() != DECLARATION_TAG {
            continue;
        }
        let entity = declaration_entity_node(model, root.node())?;
        let entity_index = usize::try_from(entity.get() - 1).map_err(|_| {
            EncodedValidationError::invariant("declaration entity index exceeds usize")
        })?;
        if semantic_nodes
            .get(entity_index)
            .is_none_or(|reachable| *reachable == 0)
        {
            continue;
        }
        budget.claim_work(binary_search_work(entity_node_symbols.len()))?;
        let symbol_index = entity_node_symbols
            .binary_search_by_key(&entity, |(candidate, _)| *candidate)
            .map_err(|_| {
                EncodedValidationError::invariant(
                    "reachable declared entity is absent from the entity-node mapping",
                )
            })?;
        budget.claim_owned(size_of::<u32>())?;
        identifiers.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("source declaration retention allocation failed")
        })?;
        identifiers.push(entity_node_symbols[symbol_index].1);
    }
    budget.claim_work(sort_work(identifiers.len()))?;
    identifiers.sort_unstable();
    identifiers.dedup();
    Ok(identifiers)
}

fn semantic_reachability<B: ByteSource>(
    model: &ValidatedModel<B>,
    roots: &[DispatchedRoot],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let node_count = model.summary().node_count;
    let stack_bytes = node_count.checked_mul(size_of::<NodeId>()).ok_or_else(|| {
        EncodedValidationError::resource("encoded semantic traversal stack size overflowed")
    })?;
    budget.claim_owned(node_count)?;
    budget.claim_owned(stack_bytes)?;
    let mut reached = Vec::new();
    reached.try_reserve_exact(node_count).map_err(|_| {
        EncodedValidationError::resource("encoded semantic reachability allocation failed")
    })?;
    reached.resize(node_count, 0);
    let mut stack = Vec::new();
    stack.try_reserve_exact(node_count).map_err(|_| {
        EncodedValidationError::resource("encoded semantic traversal stack allocation failed")
    })?;

    for root in roots {
        if !root.handler.contributes_source_symbols() {
            continue;
        }
        let node = model.node(root.node)?;
        let fields = node.fields();
        let semantic_end = fields.end.checked_sub(1).ok_or_else(|| {
            EncodedValidationError::invariant("encoded semantic root has no annotation field")
        })?;
        for field_index in fields.start..semantic_end {
            budget.claim_work(1)?;
            let component = required_component(model.field(field_index)?, "semantic root field")?;
            enqueue_component(model, component, &mut reached, &mut stack, budget)?;
        }
    }
    while let Some(identifier) = stack.pop() {
        budget.claim_work(1)?;
        let node = model.node(identifier)?;
        for field_index in node.fields() {
            budget.claim_work(1)?;
            let component = required_component(model.field(field_index)?, "semantic node field")?;
            enqueue_component(model, component, &mut reached, &mut stack, budget)?;
        }
    }
    Ok(reached)
}

fn enqueue_component<B: ByteSource>(
    model: &ValidatedModel<B>,
    component: ComponentRef,
    reached: &mut [u8],
    stack: &mut Vec<NodeId>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    match model.resolve(component)? {
        ComponentValue::Node(identifier) => enqueue_node(identifier, reached, stack),
        ComponentValue::Collection(collection) => {
            for item_index in collection.items() {
                budget.claim_work(1)?;
                let item = required_component(model.item(item_index)?, "semantic collection item")?;
                if let ComponentValue::Node(identifier) = model.resolve(item)? {
                    enqueue_node(identifier, reached, stack)?;
                }
            }
            Ok(())
        }
        ComponentValue::None | ComponentValue::Scalar(_) => Ok(()),
    }
}

fn enqueue_node(
    identifier: NodeId,
    reached: &mut [u8],
    stack: &mut Vec<NodeId>,
) -> EncodedResult<()> {
    let index = usize::try_from(identifier.get() - 1).map_err(|_| {
        EncodedValidationError::invariant("encoded semantic node index exceeds usize")
    })?;
    let state = reached.get_mut(index).ok_or_else(|| {
        EncodedValidationError::invariant("encoded semantic node ID is out of range")
    })?;
    if *state == 0 {
        *state = 1;
        stack.push(identifier);
    }
    Ok(())
}

fn declaration_identity<B: ByteSource>(
    model: &ValidatedModel<B>,
    declaration: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<DeclaredIdentity> {
    let entity_id = declaration_entity_node(model, declaration)?;
    let entity = extract_entity(model, entity_id, budget)?;
    Ok(DeclaredIdentity {
        key: entity.key,
        kind: entity.kind,
        iri: entity.iri,
    })
}

fn declaration_entity_node<B: ByteSource>(
    model: &ValidatedModel<B>,
    declaration: NodeId,
) -> EncodedResult<NodeId> {
    let node = model.node(declaration)?;
    if node.tag() != DECLARATION_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "declaration root no longer has schema-1 shape",
        ));
    }
    let field = required_component(model.field(node.fields().start)?, "declaration entity")?;
    let ComponentValue::Node(entity_id) = model.resolve(field)? else {
        return Err(EncodedValidationError::invariant(
            "declaration entity field did not resolve to a node",
        ));
    };
    Ok(entity_id)
}

fn extract_entity<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<ExtractedEntity> {
    let node = model.node(identifier)?;
    if node.tag() != ENTITY_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "entity node no longer has schema-1 shape",
        ));
    }
    let fields = node.fields();
    let kind_component = required_component(model.field(fields.start)?, "entity kind")?;
    let ComponentValue::Scalar(kind_scalar) = model.resolve(kind_component)? else {
        return Err(EncodedValidationError::invariant(
            "entity kind field did not resolve to a scalar",
        ));
    };
    let kind = EntityKind::from_scalar(kind_scalar)?;
    let iri_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::invariant("entity IRI field index overflowed"))?;
    let iri_component = required_component(model.field(iri_field)?, "entity IRI")?;
    let ComponentValue::Node(iri_id) = model.resolve(iri_component)? else {
        return Err(EncodedValidationError::invariant(
            "entity IRI field did not resolve to a node",
        ));
    };
    let iri_node = model.node(iri_id)?;
    if iri_node.tag() != IRI_TAG || iri_node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "entity IRI node no longer has schema-1 shape",
        ));
    }
    let iri_component =
        required_component(model.field(iri_node.fields().start)?, "entity IRI text")?;
    let ComponentValue::Scalar(iri_scalar) = model.resolve(iri_component)? else {
        return Err(EncodedValidationError::invariant(
            "entity IRI text did not resolve to a scalar",
        ));
    };
    if iri_scalar.kind() != ComponentKind::Text {
        return Err(EncodedValidationError::invariant(
            "entity IRI component is not text",
        ));
    }
    let iri_bytes = copy_scalar(iri_scalar, budget)?;
    let iri = String::from_utf8(iri_bytes).map_err(|_| {
        EncodedValidationError::invariant("validated entity IRI is no longer UTF-8")
    })?;
    validate_iri(&iri)?;
    entity_from_parts(kind, &iri, budget)
}

fn entity_from_parts(
    kind: EntityKind,
    iri: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<ExtractedEntity> {
    validate_iri(iri)?;
    let key = entity_key(kind, iri.as_bytes(), budget)?;
    let display_len = kind
        .as_str()
        .len()
        .checked_add(1)
        .and_then(|value| value.checked_add(iri.len()))
        .ok_or_else(|| EncodedValidationError::resource("entity display length overflowed"))?;
    budget.claim_owned(display_len)?;
    let mut display = String::new();
    display
        .try_reserve_exact(display_len)
        .map_err(|_| EncodedValidationError::resource("entity display allocation failed"))?;
    display.push_str(kind.as_str());
    display.push(':');
    display.push_str(iri);
    budget.claim_owned(iri.len())?;
    let mut owned_iri = String::new();
    owned_iri
        .try_reserve_exact(iri.len())
        .map_err(|_| EncodedValidationError::resource("entity IRI allocation failed"))?;
    owned_iri.push_str(iri);
    Ok(ExtractedEntity {
        key,
        kind,
        iri: owned_iri,
        display,
    })
}

fn entity_key(kind: EntityKind, iri: &[u8], budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let mut iri_key = Vec::new();
    push_varint(&mut iri_key, u64::from(IRI_TAG), budget)?;
    push_byte(&mut iri_key, 2, budget)?;
    push_frame(&mut iri_key, iri, budget)?;

    let mut entity_key = Vec::new();
    push_varint(&mut entity_key, u64::from(ENTITY_TAG), budget)?;
    push_byte(&mut entity_key, 5, budget)?;
    push_frame(&mut entity_key, kind.as_str().as_bytes(), budget)?;
    push_byte(&mut entity_key, 1, budget)?;
    push_frame(&mut entity_key, &iri_key, budget)?;
    Ok(entity_key)
}

fn push_frame(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    let length = u64::try_from(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical frame length exceeds u64"))?;
    push_varint(target, length, budget)?;
    push_bytes(target, value, budget)
}

fn push_varint(
    target: &mut Vec<u8>,
    mut value: u64,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    loop {
        let payload = u8::try_from(value & 0x7f)
            .map_err(|_| EncodedValidationError::invariant("canonical varint byte exceeds u8"))?;
        value >>= 7;
        push_byte(target, payload | if value == 0 { 0 } else { 0x80 }, budget)?;
        if value == 0 {
            return Ok(());
        }
    }
}

fn push_byte(target: &mut Vec<u8>, value: u8, budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(1)?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("canonical entity key allocation failed"))?;
    target.push(value);
    Ok(())
}

fn push_bytes(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(value.len())?;
    target
        .try_reserve(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical entity key allocation failed"))?;
    target.extend_from_slice(value);
    Ok(())
}

fn copy_scalar<B: ByteSource>(
    value: ScalarRef<B>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    budget.claim_work(value.len())?;
    budget.claim_owned(value.len())?;
    let mut output = Vec::new();
    output.try_reserve_exact(value.len()).map_err(|_| {
        EncodedValidationError::resource("encoded scalar extraction allocation failed")
    })?;
    for index in 0..value.len() {
        output.push(value.byte(index).ok_or_else(|| {
            EncodedValidationError::invariant("validated scalar byte disappeared")
        })?);
    }
    Ok(output)
}

fn validate_iri(value: &str) -> EncodedResult<()> {
    let bytes = value.as_bytes();
    let Some(colon) = bytes.iter().position(|byte| *byte == b':') else {
        return Err(invalid_iri());
    };
    if colon == 0
        || !bytes[0].is_ascii_alphabetic()
        || !bytes[1..colon]
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'+' | b'.' | b'-'))
    {
        return Err(invalid_iri());
    }
    for character in value.chars() {
        let codepoint = u32::from(character);
        if codepoint <= 0x20
            || matches!(
                character,
                '<' | '>' | '"' | '{' | '}' | '|' | '\\' | '^' | '`'
            )
            || (0x7f..=0x9f).contains(&codepoint)
            || (0xfdd0..=0xfdef).contains(&codepoint)
            || matches!(codepoint & 0xffff, 0xfffe | 0xffff)
        {
            return Err(invalid_iri());
        }
    }
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'%' {
            index += 1;
            continue;
        }
        let end = index.checked_add(3).ok_or_else(invalid_iri)?;
        if end > bytes.len() || !bytes[index + 1..end].iter().all(u8::is_ascii_hexdigit) {
            return Err(invalid_iri());
        }
        index = end;
    }
    Ok(())
}

fn invalid_iri() -> EncodedValidationError {
    EncodedValidationError::protocol("encoded entity IRI violates the core model contract")
}

fn required_component(
    value: Option<ComponentRef>,
    name: &'static str,
) -> EncodedResult<ComponentRef> {
    value.ok_or_else(|| {
        EncodedValidationError::invariant(format!("validated {name} component disappeared"))
    })
}

const fn root_kind_name(kind: RootKind) -> &'static str {
    match kind {
        RootKind::OntologyAnnotation => "ontology_annotation",
        RootKind::Axiom => "axiom",
        RootKind::Extension => "extension",
    }
}

fn sort_work(count: usize) -> usize {
    if count < 2 {
        return count;
    }
    let comparisons = usize::BITS - (count - 1).leading_zeros();
    count.saturating_mul(usize::try_from(comparisons).unwrap_or(usize::MAX))
}

fn binary_search_work(count: usize) -> usize {
    if count < 2 {
        1
    } else {
        usize::try_from(usize::BITS - (count - 1).leading_zeros())
            .unwrap_or(usize::MAX)
            .saturating_add(1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoded::model::ValidatedModel;
    use crate::encoded::{EncodedColumns, EncodedLimits};

    #[derive(Clone, Debug)]
    struct OwnedColumns {
        root_kinds: Vec<u8>,
        root_ids: Vec<u8>,
        node_tags: Vec<u8>,
        node_field_offsets: Vec<u8>,
        field_kinds: Vec<u8>,
        field_values: Vec<u8>,
        field_lengths: Vec<u8>,
        item_kinds: Vec<u8>,
        item_values: Vec<u8>,
        item_lengths: Vec<u8>,
        scalar_bytes: Vec<u8>,
    }

    impl OwnedColumns {
        fn borrowed(&self) -> EncodedColumns<&[u8]> {
            EncodedColumns {
                root_kinds: &self.root_kinds,
                root_ids: &self.root_ids,
                node_tags: &self.node_tags,
                node_field_offsets: &self.node_field_offsets,
                field_kinds: &self.field_kinds,
                field_values: &self.field_values,
                field_lengths: &self.field_lengths,
                item_kinds: &self.item_kinds,
                item_values: &self.item_values,
                item_lengths: &self.item_lengths,
                scalar_bytes: &self.scalar_bytes,
            }
        }
    }

    fn le16(values: &[u16]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn le32(values: &[u32]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn le64(values: &[u64]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn declaration(iri: &str) -> OwnedColumns {
        let iri_length = u64::try_from(iri.len()).unwrap_or(u64::MAX);
        let mut scalar_bytes = iri.as_bytes().to_vec();
        scalar_bytes.extend_from_slice(b"class");
        OwnedColumns {
            root_kinds: vec![2],
            root_ids: le32(&[3]),
            node_tags: le16(&[1, 2, 60]),
            node_field_offsets: le64(&[0, 1, 3, 5]),
            field_kinds: vec![2, 5, 1, 1, 6],
            field_values: le64(&[0, iri_length, 1, 2, 0]),
            field_lengths: le64(&[iri_length, 5, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes,
        }
    }

    #[test]
    fn root_dispatch_ledger_is_exhaustive_and_kind_sensitive() -> EncodedResult<()> {
        let expected = [
            (
                RootKind::OntologyAnnotation,
                5,
                RootHandler::OntologyAnnotation,
            ),
            (RootKind::Axiom, 60, RootHandler::Declaration),
            (RootKind::Axiom, 61, RootHandler::SubClassOf),
            (RootKind::Axiom, 62, RootHandler::EquivalentClasses),
            (RootKind::Axiom, 63, RootHandler::DisjointClasses),
            (RootKind::Axiom, 64, RootHandler::DisjointUnion),
            (RootKind::Axiom, 70, RootHandler::SubObjectPropertyOf),
            (RootKind::Axiom, 71, RootHandler::EquivalentObjectProperties),
            (RootKind::Axiom, 72, RootHandler::DisjointObjectProperties),
            (RootKind::Axiom, 73, RootHandler::InverseObjectProperties),
            (RootKind::Axiom, 74, RootHandler::ObjectPropertyDomain),
            (RootKind::Axiom, 75, RootHandler::ObjectPropertyRange),
            (RootKind::Axiom, 76, RootHandler::FunctionalObjectProperty),
            (
                RootKind::Axiom,
                77,
                RootHandler::InverseFunctionalObjectProperty,
            ),
            (RootKind::Axiom, 78, RootHandler::ReflexiveObjectProperty),
            (RootKind::Axiom, 79, RootHandler::IrreflexiveObjectProperty),
            (RootKind::Axiom, 80, RootHandler::SymmetricObjectProperty),
            (RootKind::Axiom, 81, RootHandler::AsymmetricObjectProperty),
            (RootKind::Axiom, 82, RootHandler::TransitiveObjectProperty),
            (RootKind::Axiom, 90, RootHandler::SubDataPropertyOf),
            (RootKind::Axiom, 91, RootHandler::EquivalentDataProperties),
            (RootKind::Axiom, 92, RootHandler::DisjointDataProperties),
            (RootKind::Axiom, 93, RootHandler::DataPropertyDomain),
            (RootKind::Axiom, 94, RootHandler::DataPropertyRange),
            (RootKind::Axiom, 95, RootHandler::FunctionalDataProperty),
            (RootKind::Axiom, 100, RootHandler::DatatypeDefinition),
            (RootKind::Axiom, 101, RootHandler::HasKey),
            (RootKind::Axiom, 110, RootHandler::SameIndividual),
            (RootKind::Axiom, 111, RootHandler::DifferentIndividuals),
            (RootKind::Axiom, 112, RootHandler::ClassAssertion),
            (RootKind::Axiom, 113, RootHandler::ObjectPropertyAssertion),
            (
                RootKind::Axiom,
                114,
                RootHandler::NegativeObjectPropertyAssertion,
            ),
            (RootKind::Axiom, 115, RootHandler::DataPropertyAssertion),
            (
                RootKind::Axiom,
                116,
                RootHandler::NegativeDataPropertyAssertion,
            ),
            (RootKind::Axiom, 120, RootHandler::AnnotationAssertion),
            (RootKind::Axiom, 121, RootHandler::SubAnnotationPropertyOf),
            (RootKind::Axiom, 122, RootHandler::AnnotationPropertyDomain),
            (RootKind::Axiom, 123, RootHandler::AnnotationPropertyRange),
            (RootKind::Extension, 148, RootHandler::SwrlRule),
        ];
        for (kind, tag, handler) in expected {
            assert_eq!(RootHandler::from_root(kind, tag)?, handler);
            assert!(!handler.as_str().is_empty());
        }
        assert!(RootHandler::from_root(RootKind::Axiom, 5).is_err());
        assert!(RootHandler::from_root(RootKind::Extension, 60).is_err());
        Ok(())
    }

    #[test]
    fn declaration_extracts_scalar_exact_entity_seed_and_manifest() -> EncodedResult<()> {
        let owned = declaration("urn:C");
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let phase = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;

        assert_eq!(phase.roots.len(), 1);
        assert_eq!(phase.roots[0].handler, RootHandler::Declaration);
        assert_eq!(phase.entity_domain.kind, SymbolKind::Entity);
        assert_eq!(phase.entity_domain.values.len(), 4);
        let source = phase
            .entity_domain
            .values
            .iter()
            .find(|value| value.display == "class:urn:C")
            .ok_or_else(|| EncodedValidationError::invariant("source entity is missing"))?;
        assert_eq!(source.key, b"\x02\x05\x05class\x01\x08\x01\x02\x05urn:C");
        assert!(!source.generated);
        assert!(!source.query_local);
        assert_eq!(
            phase.declared_entities,
            vec![DecodedEntity {
                kind: "class".to_owned(),
                iri: "urn:C".to_owned(),
                entity_id: source.identifier,
            }]
        );
        let manifest: serde_json::Value = serde_json::from_slice(&phase.canonical_manifest_json()?)
            .map_err(|_| EncodedValidationError::invariant("manifest did not decode"))?;
        assert_eq!(manifest["schema_version"], 1);
        assert_eq!(manifest["root_dispatch"][0]["handler"], "Declaration");
        assert_eq!(manifest["declared_entities"][0]["iri"], "urn:C");
        Ok(())
    }

    #[test]
    fn source_local_root_exclusions_filter_dispatch_before_owned_compilation() -> EncodedResult<()>
    {
        let owned = declaration("urn:C");
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let exclusions = le32(&[1]);

        let phase = compile_symbol_phase_selected(
            &model,
            SymbolPhaseLimits::default(),
            POSTINGS_EXCLUDE,
            exclusions.as_slice(),
        )?;

        assert!(phase.roots.is_empty());
        assert!(phase.declared_entities.is_empty());
        assert_eq!(phase.entity_domain.values.len(), BUILTIN_ENTITIES.len());
        let all = compile_symbol_phase_selected(
            &model,
            SymbolPhaseLimits::default(),
            POSTINGS_ALL,
            &[][..],
        )?;
        assert_eq!(all.roots.len(), 1);
        assert_eq!(all.declared_entities.len(), 1);
        Ok(())
    }

    #[test]
    fn source_local_root_inclusions_filter_dispatch_before_owned_compilation() -> EncodedResult<()>
    {
        let owned = declaration("urn:C");
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let inclusions = le32(&[1]);

        let phase = compile_symbol_phase_selected(
            &model,
            SymbolPhaseLimits::default(),
            POSTINGS_INCLUDE,
            inclusions.as_slice(),
        )?;

        assert_eq!(phase.roots.len(), 1);
        assert_eq!(phase.roots[0].handler, RootHandler::Declaration);
        assert_eq!(phase.declared_entities.len(), 1);
        Ok(())
    }

    #[test]
    fn source_local_root_exclusions_reject_hostile_postings() -> EncodedResult<()> {
        let owned = declaration("urn:C");
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        for (mode, postings, message) in [
            (POSTINGS_ALL, le32(&[1]), "ALL"),
            (POSTINGS_INCLUDE, Vec::new(), "empty"),
            (POSTINGS_INCLUDE, vec![1, 0], "partial"),
            (POSTINGS_INCLUDE, le32(&[2]), "in-range"),
            (POSTINGS_EXCLUDE, Vec::new(), "empty"),
            (POSTINGS_EXCLUDE, vec![1, 0], "partial"),
            (POSTINGS_EXCLUDE, le32(&[2]), "in-range"),
            (3, le32(&[1]), "unsupported"),
        ] {
            let error = compile_symbol_phase_selected(
                &model,
                SymbolPhaseLimits::default(),
                mode,
                postings.as_slice(),
            )
            .err();
            assert!(error.is_some_and(|value| {
                value.code == "NATIVE_ENCODED_VIEW_INVALID" && value.message.contains(message)
            }));
        }
        Ok(())
    }

    #[test]
    fn extraction_rejects_hostile_iri_and_resource_limits_before_publication() -> EncodedResult<()>
    {
        let hostile = declaration("relative");
        let hostile_model = ValidatedModel::new(hostile.borrowed(), EncodedLimits::default())?;
        let hostile_error =
            compile_symbol_phase(&hostile_model, SymbolPhaseLimits::default()).err();
        assert!(hostile_error.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_VIEW_INVALID" && error.message.contains("IRI")
        }));

        let owned = declaration("urn:C");
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let entity_limited = SymbolPhaseLimits {
            max_entities: 3,
            ..SymbolPhaseLimits::default()
        };
        let entity_error = compile_symbol_phase(&model, entity_limited).err();
        assert!(entity_error.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_RESOURCE_LIMIT" && error.message.contains("entity count")
        }));

        let memory_limited = SymbolPhaseLimits {
            max_owned_bytes: 1,
            ..SymbolPhaseLimits::default()
        };
        let memory_error = compile_symbol_phase(&model, memory_limited).err();
        assert!(memory_error.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_RESOURCE_LIMIT" && error.message.contains("owned-byte")
        }));
        Ok(())
    }
}
