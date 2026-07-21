//! Borrowed validation for pyowl-core encoded structural columns schema 1.
//!
//! This module is intentionally Python-free and does not advertise the encoded
//! compiler capability. It validates the frozen eleven-column shape, exact
//! constructor roles, graph integrity, and canonical dense order before any
//! future HermiT-specific compilation.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

pub(crate) mod canonical;
pub mod complex_roles;
pub mod data_inclusions;
pub mod data_role_hierarchy;
pub mod data_roles;
pub mod model;
pub mod named_classes;
pub mod object_role_hierarchy;
pub mod object_roles;
pub mod role_automata;
pub mod role_characteristics;
pub mod role_clauses;
pub mod role_model;
pub mod role_semantics;
pub mod simple_roles;
pub mod symbols;
pub(crate) mod xml_literal;

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::{Display, Formatter};

pub const DESCRIPTOR_SHA256_V1: [u8; 32] = [
    0x9a, 0xd2, 0x9d, 0xb6, 0xa7, 0xe6, 0x16, 0xf6, 0x5c, 0xea, 0x29, 0x57, 0xbc, 0x5b, 0xa8, 0xd1,
    0xf9, 0xb9, 0x9e, 0xf0, 0xeb, 0x1f, 0xe1, 0x43, 0x2c, 0x09, 0xbe, 0x25, 0x78, 0x62, 0x67, 0xb5,
];

const ROOT_ONTOLOGY_ANNOTATION: u8 = 1;
const ROOT_AXIOM: u8 = 2;
const ROOT_EXTENSION: u8 = 3;

const COMPONENT_NONE: u8 = 0;
const COMPONENT_NODE: u8 = 1;
const COMPONENT_TEXT: u8 = 2;
const COMPONENT_BYTES: u8 = 3;
const COMPONENT_INTEGER: u8 = 4;
const COMPONENT_ENUM: u8 = 5;
const COMPONENT_SET: u8 = 6;
const COMPONENT_SEQUENCE: u8 = 7;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EncodedValidationError {
    pub code: &'static str,
    pub message: String,
}

impl EncodedValidationError {
    fn protocol(message: impl Into<String>) -> Self {
        Self {
            code: "NATIVE_ENCODED_VIEW_INVALID",
            message: message.into(),
        }
    }

    pub(crate) fn resource(message: impl Into<String>) -> Self {
        Self {
            code: "NATIVE_ENCODED_RESOURCE_LIMIT",
            message: message.into(),
        }
    }

    fn invariant(message: impl Into<String>) -> Self {
        Self {
            code: "NATIVE_ENCODED_INVARIANT",
            message: message.into(),
        }
    }
}

impl Display for EncodedValidationError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}: {}", self.code, self.message)
    }
}

impl Error for EncodedValidationError {}

pub type EncodedResult<T> = Result<T, EncodedValidationError>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EntityKindRole {
    Class,
    Datatype,
    ObjectProperty,
    DataProperty,
    AnnotationProperty,
    NamedIndividual,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NodeRole {
    Iri,
    Entity,
    Class,
    Datatype,
    ObjectProperty,
    DataProperty,
    AnnotationProperty,
    Literal,
    Annotation,
    ObjectPropertyExpression,
    SubObjectPropertyExpression,
    FacetRestriction,
    DataRange,
    ClassExpression,
    Individual,
    AnnotationValue,
    AnnotationSubject,
    IndividualArgument,
    DataArgument,
    Atom,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FieldRole {
    Scalar(u8),
    EntityKind,
    OptionalText,
    Node(NodeRole),
    Set(NodeRole),
    Sequence(NodeRole),
}

const TEXT: FieldRole = FieldRole::Scalar(COMPONENT_TEXT);
const BYTES: FieldRole = FieldRole::Scalar(COMPONENT_BYTES);
const INTEGER: FieldRole = FieldRole::Scalar(COMPONENT_INTEGER);
const ENTITY_KIND: FieldRole = FieldRole::EntityKind;
const OPTIONAL_TEXT: FieldRole = FieldRole::OptionalText;

const N_IRI: FieldRole = FieldRole::Node(NodeRole::Iri);
const N_ENTITY: FieldRole = FieldRole::Node(NodeRole::Entity);
const N_CLASS: FieldRole = FieldRole::Node(NodeRole::Class);
const N_DATATYPE: FieldRole = FieldRole::Node(NodeRole::Datatype);
const N_OBJECT_PROPERTY: FieldRole = FieldRole::Node(NodeRole::ObjectProperty);
const N_DATA_PROPERTY: FieldRole = FieldRole::Node(NodeRole::DataProperty);
const N_ANNOTATION_PROPERTY: FieldRole = FieldRole::Node(NodeRole::AnnotationProperty);
const N_LITERAL: FieldRole = FieldRole::Node(NodeRole::Literal);
const N_OBJECT_PROPERTY_EXPRESSION: FieldRole = FieldRole::Node(NodeRole::ObjectPropertyExpression);
const N_SUB_OBJECT_PROPERTY_EXPRESSION: FieldRole =
    FieldRole::Node(NodeRole::SubObjectPropertyExpression);
const N_DATA_RANGE: FieldRole = FieldRole::Node(NodeRole::DataRange);
const N_CLASS_EXPRESSION: FieldRole = FieldRole::Node(NodeRole::ClassExpression);
const N_INDIVIDUAL: FieldRole = FieldRole::Node(NodeRole::Individual);
const N_ANNOTATION_VALUE: FieldRole = FieldRole::Node(NodeRole::AnnotationValue);
const N_ANNOTATION_SUBJECT: FieldRole = FieldRole::Node(NodeRole::AnnotationSubject);
const N_INDIVIDUAL_ARGUMENT: FieldRole = FieldRole::Node(NodeRole::IndividualArgument);
const N_DATA_ARGUMENT: FieldRole = FieldRole::Node(NodeRole::DataArgument);

const SET_ANNOTATION: FieldRole = FieldRole::Set(NodeRole::Annotation);
const SET_DATA_RANGE: FieldRole = FieldRole::Set(NodeRole::DataRange);
const SET_LITERAL: FieldRole = FieldRole::Set(NodeRole::Literal);
const SET_FACET_RESTRICTION: FieldRole = FieldRole::Set(NodeRole::FacetRestriction);
const SET_CLASS_EXPRESSION: FieldRole = FieldRole::Set(NodeRole::ClassExpression);
const SET_INDIVIDUAL: FieldRole = FieldRole::Set(NodeRole::Individual);
const SET_OBJECT_PROPERTY_EXPRESSION: FieldRole =
    FieldRole::Set(NodeRole::ObjectPropertyExpression);
const SET_DATA_PROPERTY: FieldRole = FieldRole::Set(NodeRole::DataProperty);
const SET_ATOM: FieldRole = FieldRole::Set(NodeRole::Atom);

const SEQUENCE_OBJECT_PROPERTY_EXPRESSION: FieldRole =
    FieldRole::Sequence(NodeRole::ObjectPropertyExpression);
const SEQUENCE_DATA_PROPERTY: FieldRole = FieldRole::Sequence(NodeRole::DataProperty);
const SEQUENCE_DATA_ARGUMENT: FieldRole = FieldRole::Sequence(NodeRole::DataArgument);

macro_rules! constructor_role_ledger {
    ($( $tag:literal => [$($role:expr),* $(,)?]),+ $(,)?) => {
        const fn constructor_roles(tag: u16) -> Option<&'static [FieldRole]> {
            match tag {
                $($tag => Some(&[$($role),*]),)+
                _ => None,
            }
        }

        #[cfg(test)]
        const CONSTRUCTOR_ROLE_LEDGER: &[(u16, &[FieldRole])] = &[
            $(($tag, &[$($role),*]),)+
        ];
    };
}

// Generated from the frozen pyowl-core model-schema-1 constructor ledger and
// structural-columns descriptor. Every tag retains its exact ordered roles.
constructor_role_ledger! {
    1 => [TEXT],
    2 => [ENTITY_KIND, N_IRI],
    3 => [BYTES, BYTES],
    4 => [TEXT, N_DATATYPE, OPTIONAL_TEXT],
    5 => [N_ANNOTATION_PROPERTY, N_ANNOTATION_VALUE, SET_ANNOTATION],
    10 => [N_OBJECT_PROPERTY],
    11 => [SEQUENCE_OBJECT_PROPERTY_EXPRESSION],
    20 => [N_IRI, N_LITERAL],
    21 => [SET_DATA_RANGE],
    22 => [SET_DATA_RANGE],
    23 => [N_DATA_RANGE],
    24 => [SET_LITERAL],
    25 => [N_DATATYPE, SET_FACET_RESTRICTION],
    30 => [SET_CLASS_EXPRESSION],
    31 => [SET_CLASS_EXPRESSION],
    32 => [N_CLASS_EXPRESSION],
    33 => [SET_INDIVIDUAL],
    34 => [N_OBJECT_PROPERTY_EXPRESSION, N_CLASS_EXPRESSION],
    35 => [N_OBJECT_PROPERTY_EXPRESSION, N_CLASS_EXPRESSION],
    36 => [N_OBJECT_PROPERTY_EXPRESSION, N_INDIVIDUAL],
    37 => [N_OBJECT_PROPERTY_EXPRESSION],
    38 => [INTEGER, N_OBJECT_PROPERTY_EXPRESSION, N_CLASS_EXPRESSION],
    39 => [INTEGER, N_OBJECT_PROPERTY_EXPRESSION, N_CLASS_EXPRESSION],
    40 => [INTEGER, N_OBJECT_PROPERTY_EXPRESSION, N_CLASS_EXPRESSION],
    41 => [SEQUENCE_DATA_PROPERTY, N_DATA_RANGE],
    42 => [SEQUENCE_DATA_PROPERTY, N_DATA_RANGE],
    43 => [N_DATA_PROPERTY, N_LITERAL],
    44 => [INTEGER, N_DATA_PROPERTY, N_DATA_RANGE],
    45 => [INTEGER, N_DATA_PROPERTY, N_DATA_RANGE],
    46 => [INTEGER, N_DATA_PROPERTY, N_DATA_RANGE],
    60 => [N_ENTITY, SET_ANNOTATION],
    61 => [N_CLASS_EXPRESSION, N_CLASS_EXPRESSION, SET_ANNOTATION],
    62 => [SET_CLASS_EXPRESSION, SET_ANNOTATION],
    63 => [SET_CLASS_EXPRESSION, SET_ANNOTATION],
    64 => [N_CLASS, SET_CLASS_EXPRESSION, SET_ANNOTATION],
    70 => [N_SUB_OBJECT_PROPERTY_EXPRESSION, N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    71 => [SET_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    72 => [SET_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    73 => [N_OBJECT_PROPERTY_EXPRESSION, N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    74 => [N_OBJECT_PROPERTY_EXPRESSION, N_CLASS_EXPRESSION, SET_ANNOTATION],
    75 => [N_OBJECT_PROPERTY_EXPRESSION, N_CLASS_EXPRESSION, SET_ANNOTATION],
    76 => [N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    77 => [N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    78 => [N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    79 => [N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    80 => [N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    81 => [N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    82 => [N_OBJECT_PROPERTY_EXPRESSION, SET_ANNOTATION],
    90 => [N_DATA_PROPERTY, N_DATA_PROPERTY, SET_ANNOTATION],
    91 => [SET_DATA_PROPERTY, SET_ANNOTATION],
    92 => [SET_DATA_PROPERTY, SET_ANNOTATION],
    93 => [N_DATA_PROPERTY, N_CLASS_EXPRESSION, SET_ANNOTATION],
    94 => [N_DATA_PROPERTY, N_DATA_RANGE, SET_ANNOTATION],
    95 => [N_DATA_PROPERTY, SET_ANNOTATION],
    100 => [N_DATATYPE, N_DATA_RANGE, SET_ANNOTATION],
    101 => [N_CLASS_EXPRESSION, SET_OBJECT_PROPERTY_EXPRESSION, SET_DATA_PROPERTY, SET_ANNOTATION],
    110 => [SET_INDIVIDUAL, SET_ANNOTATION],
    111 => [SET_INDIVIDUAL, SET_ANNOTATION],
    112 => [N_CLASS_EXPRESSION, N_INDIVIDUAL, SET_ANNOTATION],
    113 => [N_OBJECT_PROPERTY_EXPRESSION, N_INDIVIDUAL, N_INDIVIDUAL, SET_ANNOTATION],
    114 => [N_OBJECT_PROPERTY_EXPRESSION, N_INDIVIDUAL, N_INDIVIDUAL, SET_ANNOTATION],
    115 => [N_DATA_PROPERTY, N_INDIVIDUAL, N_LITERAL, SET_ANNOTATION],
    116 => [N_DATA_PROPERTY, N_INDIVIDUAL, N_LITERAL, SET_ANNOTATION],
    120 => [N_ANNOTATION_PROPERTY, N_ANNOTATION_SUBJECT, N_ANNOTATION_VALUE, SET_ANNOTATION],
    121 => [N_ANNOTATION_PROPERTY, N_ANNOTATION_PROPERTY, SET_ANNOTATION],
    122 => [N_ANNOTATION_PROPERTY, N_IRI, SET_ANNOTATION],
    123 => [N_ANNOTATION_PROPERTY, N_IRI, SET_ANNOTATION],
    140 => [N_IRI],
    141 => [N_CLASS_EXPRESSION, N_INDIVIDUAL_ARGUMENT],
    142 => [N_DATA_RANGE, N_DATA_ARGUMENT],
    143 => [N_OBJECT_PROPERTY_EXPRESSION, N_INDIVIDUAL_ARGUMENT, N_INDIVIDUAL_ARGUMENT],
    144 => [N_DATA_PROPERTY, N_INDIVIDUAL_ARGUMENT, N_DATA_ARGUMENT],
    145 => [N_IRI, SEQUENCE_DATA_ARGUMENT],
    146 => [N_INDIVIDUAL_ARGUMENT, N_INDIVIDUAL_ARGUMENT],
    147 => [N_INDIVIDUAL_ARGUMENT, N_INDIVIDUAL_ARGUMENT],
    148 => [SET_ATOM, SET_ATOM, SET_ANNOTATION],
}

/// Stable immutable bytes borrowed from direct or buffer-backed inputs.
pub trait ByteSource: Copy {
    fn len(self) -> usize;
    fn byte(self, index: usize) -> Option<u8>;

    fn is_empty(self) -> bool {
        self.len() == 0
    }
}

impl ByteSource for &[u8] {
    fn len(self) -> usize {
        <[u8]>::len(self)
    }

    fn byte(self, index: usize) -> Option<u8> {
        self.get(index).copied()
    }
}

/// The exact eleven borrowed columns in encoded structural schema 1.
#[derive(Clone, Copy, Debug)]
pub struct EncodedColumns<B: ByteSource> {
    pub root_kinds: B,
    pub root_ids: B,
    pub node_tags: B,
    pub node_field_offsets: B,
    pub field_kinds: B,
    pub field_values: B,
    pub field_lengths: B,
    pub item_kinds: B,
    pub item_values: B,
    pub item_lengths: B,
    pub scalar_bytes: B,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EncodedLimits {
    pub max_roots: usize,
    pub max_nodes: usize,
    pub max_fields: usize,
    pub max_items: usize,
    pub max_scalar_bytes: usize,
    pub max_work: u64,
}

impl Default for EncodedLimits {
    fn default() -> Self {
        Self {
            max_roots: 100_000_000,
            max_nodes: 100_000_000,
            max_fields: 400_000_000,
            max_items: 400_000_000,
            max_scalar_bytes: usize::try_from(8_589_934_592_u64).unwrap_or(usize::MAX),
            max_work: 2_000_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValidatedEncodedColumns {
    pub root_count: usize,
    pub node_count: usize,
    pub field_count: usize,
    pub item_count: usize,
    pub scalar_bytes: usize,
    pub work: u64,
}

#[derive(Clone, Copy)]
struct Component {
    kind: u8,
    value: usize,
    length: usize,
}

#[derive(Clone, Copy)]
struct FieldLocation {
    tag: u16,
    position: usize,
}

#[derive(Clone, Copy)]
struct ValidationContext<'a, B: ByteSource> {
    columns: &'a EncodedColumns<B>,
    node_count: usize,
}

#[derive(Clone, Copy, Debug)]
struct DfsFrame {
    node: usize,
    field_cursor: usize,
    field_end: usize,
    item_cursor: usize,
    item_end: usize,
}

impl DfsFrame {
    fn new<B: ByteSource>(node: usize, columns: &EncodedColumns<B>) -> EncodedResult<Self> {
        let field_cursor = usize_at(columns.node_field_offsets, node, "node field offset")?;
        let next = node
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("node field offset index overflow"))?;
        let field_end = usize_at(columns.node_field_offsets, next, "node field offset")?;
        Ok(Self {
            node,
            field_cursor,
            field_end,
            item_cursor: 0,
            item_end: 0,
        })
    }
}

/// Validate schema-v1 shape, scalar widths, root categories, tags, arity, and
/// exact field roles without copying an input column.
pub fn validate_columns<B: ByteSource>(
    columns: EncodedColumns<B>,
    limits: EncodedLimits,
) -> EncodedResult<ValidatedEncodedColumns> {
    let root_count = aligned_count(columns.root_ids, 4, "root_ids")?;
    if columns.root_kinds.len() != root_count {
        return Err(EncodedValidationError::protocol(
            "encoded root kind and root ID counts differ",
        ));
    }
    let node_count = aligned_count(columns.node_tags, 2, "node_tags")?;
    let offset_count = aligned_count(columns.node_field_offsets, 8, "node_field_offsets")?;
    if offset_count
        != node_count
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("encoded node count overflow"))?
    {
        return Err(EncodedValidationError::protocol(
            "encoded node field offsets must contain node_count + 1 rows",
        ));
    }
    let field_count = columns.field_kinds.len();
    if aligned_count(columns.field_values, 8, "field_values")? != field_count
        || aligned_count(columns.field_lengths, 8, "field_lengths")? != field_count
    {
        return Err(EncodedValidationError::protocol(
            "encoded field component columns differ in length",
        ));
    }
    let item_count = columns.item_kinds.len();
    if aligned_count(columns.item_values, 8, "item_values")? != item_count
        || aligned_count(columns.item_lengths, 8, "item_lengths")? != item_count
    {
        return Err(EncodedValidationError::protocol(
            "encoded item component columns differ in length",
        ));
    }
    enforce_count(root_count, limits.max_roots, "encoded root count")?;
    enforce_count(node_count, limits.max_nodes, "encoded node count")?;
    enforce_count(field_count, limits.max_fields, "encoded field count")?;
    enforce_count(item_count, limits.max_items, "encoded item count")?;
    enforce_count(
        columns.scalar_bytes.len(),
        limits.max_scalar_bytes,
        "encoded scalar byte count",
    )?;

    let mut work = 0_u64;
    claim_work(&mut work, 1, limits.max_work)?;
    if u64_at(columns.node_field_offsets, 0, "node field offset")? != 0 {
        return Err(EncodedValidationError::protocol(
            "encoded node field offsets must start at zero",
        ));
    }
    let mut final_offset = 0_usize;
    for node in 0..node_count {
        claim_work(&mut work, 1, limits.max_work)?;
        let start = usize_at(columns.node_field_offsets, node, "node field offset")?;
        let end = usize_at(columns.node_field_offsets, node + 1, "node field offset")?;
        if start != final_offset || end < start || end > field_count {
            return Err(EncodedValidationError::protocol(
                "encoded node field offsets are not contiguous and bounded",
            ));
        }
        let tag = u16_at(columns.node_tags, node, "node tag")?;
        let roles = constructor_roles(tag).ok_or_else(|| {
            EncodedValidationError::protocol(format!("unsupported encoded node tag {tag}"))
        })?;
        if end - start != roles.len() {
            return Err(EncodedValidationError::protocol(format!(
                "encoded node tag {tag} has the wrong field arity"
            )));
        }
        final_offset = end;
    }
    if final_offset != field_count {
        return Err(EncodedValidationError::protocol(
            "encoded node field offsets do not cover every field",
        ));
    }

    let context = ValidationContext {
        columns: &columns,
        node_count,
    };
    let mut item_cursor = 0_usize;
    let mut scalar_cursor = 0_usize;
    for node in 0..node_count {
        let tag = u16_at(columns.node_tags, node, "node tag")?;
        let roles = constructor_roles(tag).ok_or_else(|| {
            EncodedValidationError::protocol(format!("unsupported encoded node tag {tag}"))
        })?;
        let start = usize_at(columns.node_field_offsets, node, "node field offset")?;
        for (position, role) in roles.iter().copied().enumerate() {
            claim_work(&mut work, 1, limits.max_work)?;
            let field = start
                .checked_add(position)
                .ok_or_else(|| EncodedValidationError::resource("encoded field index overflow"))?;
            let component = Component {
                kind: byte_at(columns.field_kinds, field, "field kind")?,
                value: usize_at(columns.field_values, field, "field value")?,
                length: usize_at(columns.field_lengths, field, "field length")?,
            };
            let location = FieldLocation { tag, position };
            match role {
                FieldRole::Set(item_role) | FieldRole::Sequence(item_role) => {
                    let expected = if matches!(role, FieldRole::Set(_)) {
                        COMPONENT_SET
                    } else {
                        COMPONENT_SEQUENCE
                    };
                    if component.kind != expected {
                        return Err(field_role_error(location));
                    }
                    if component.value != item_cursor {
                        return Err(EncodedValidationError::protocol(
                            "encoded collection fields do not exactly cover item rows",
                        ));
                    }
                    let end = component
                        .value
                        .checked_add(component.length)
                        .ok_or_else(|| {
                            EncodedValidationError::resource("encoded item range overflow")
                        })?;
                    if end > item_count {
                        return Err(EncodedValidationError::protocol(
                            "encoded collection field exceeds item rows",
                        ));
                    }
                    let mut previous_set_item = None;
                    for item in component.value..end {
                        claim_work(&mut work, 1, limits.max_work)?;
                        let item_component = Component {
                            kind: byte_at(columns.item_kinds, item, "item kind")?,
                            value: usize_at(columns.item_values, item, "item value")?,
                            length: usize_at(columns.item_lengths, item, "item length")?,
                        };
                        validate_collection_item_role(
                            location,
                            item_role,
                            item_component,
                            context,
                        )?;
                        if expected == COMPONENT_SET {
                            let identifier = node_id_at(
                                columns.item_values,
                                item,
                                "canonical-set item node ID",
                            )?;
                            if previous_set_item.is_some_and(|prior| prior >= identifier) {
                                return Err(EncodedValidationError::protocol(
                                    "encoded canonical-set node IDs are not strictly ascending and unique",
                                ));
                            }
                            previous_set_item = Some(identifier);
                        }
                        validate_leaf_component(
                            item_component,
                            context,
                            &mut scalar_cursor,
                            &mut work,
                            limits.max_work,
                        )?;
                    }
                    item_cursor = end;
                }
                _ => {
                    validate_field_role(location, role, component, context)?;
                    validate_leaf_component(
                        component,
                        context,
                        &mut scalar_cursor,
                        &mut work,
                        limits.max_work,
                    )?;
                }
            }
        }
    }
    if item_cursor != item_count {
        return Err(EncodedValidationError::protocol(
            "encoded item rows are not exactly covered by collection fields",
        ));
    }
    if scalar_cursor != columns.scalar_bytes.len() {
        return Err(EncodedValidationError::protocol(
            "encoded scalar arena is not exactly covered by components",
        ));
    }

    // Dense-node validation below proves that one-based IDs are ranks in
    // canonical-model-v1 byte order, so this tuple comparison is equivalent
    // to the descriptor's `(root kind, canonical bytes)` ordering rule.
    let mut previous_root = None;
    for root in 0..root_count {
        claim_work(&mut work, 1, limits.max_work)?;
        let kind = byte_at(columns.root_kinds, root, "root kind")?;
        let identifier = u32_at(columns.root_ids, root, "root ID")?;
        let node = node_index(identifier, node_count)?;
        let tag = u16_at(columns.node_tags, node, "root node tag")?;
        if !root_accepts(kind, tag) {
            return Err(EncodedValidationError::protocol(
                "encoded root kind is inconsistent with its constructor tag",
            ));
        }
        if previous_root.is_some_and(|prior| prior >= (kind, identifier)) {
            return Err(EncodedValidationError::protocol(
                "encoded roots are not strictly ordered and unique",
            ));
        }
        previous_root = Some((kind, identifier));
    }

    let canonical_lengths =
        validate_graph_and_lengths(&columns, root_count, node_count, &mut work, limits.max_work)?;
    validate_dense_node_order(&columns, &canonical_lengths, &mut work, limits.max_work)?;

    Ok(ValidatedEncodedColumns {
        root_count,
        node_count,
        field_count,
        item_count,
        scalar_bytes: columns.scalar_bytes.len(),
        work,
    })
}

fn validate_field_role<B: ByteSource>(
    location: FieldLocation,
    role: FieldRole,
    component: Component,
    context: ValidationContext<'_, B>,
) -> EncodedResult<()> {
    match role {
        FieldRole::Scalar(expected) if component.kind == expected => Ok(()),
        FieldRole::EntityKind if component.kind == COMPONENT_ENUM => entity_kind_scalar(
            context.columns.scalar_bytes,
            component.value,
            component.length,
        )
        .map(drop),
        FieldRole::OptionalText if matches!(component.kind, COMPONENT_NONE | COMPONENT_TEXT) => {
            Ok(())
        }
        FieldRole::Node(expected) if component.kind == COMPONENT_NODE => {
            if node_role_accepts(expected, component.value, context)? {
                Ok(())
            } else {
                Err(field_role_error(location))
            }
        }
        FieldRole::Set(_) | FieldRole::Sequence(_) => Err(EncodedValidationError::invariant(
            "collection role reached scalar field validation",
        )),
        _ => Err(field_role_error(location)),
    }
}

fn validate_collection_item_role<B: ByteSource>(
    location: FieldLocation,
    role: NodeRole,
    component: Component,
    context: ValidationContext<'_, B>,
) -> EncodedResult<()> {
    if component.kind == COMPONENT_NODE && node_role_accepts(role, component.value, context)? {
        Ok(())
    } else {
        let FieldLocation { tag, position } = location;
        Err(EncodedValidationError::protocol(format!(
            "encoded node tag {tag} field {position} collection item has the wrong schema role"
        )))
    }
}

fn node_role_accepts<B: ByteSource>(
    role: NodeRole,
    identifier: usize,
    context: ValidationContext<'_, B>,
) -> EncodedResult<bool> {
    let identifier = u32::try_from(identifier)
        .map_err(|_| EncodedValidationError::protocol("encoded node ID exceeds u32"))?;
    let node = node_index(identifier, context.node_count)?;
    let tag = u16_at(context.columns.node_tags, node, "referenced node tag")?;
    match role {
        NodeRole::Iri => Ok(tag == 1),
        NodeRole::Entity => entity_role_accepts(tag, node, None, context.columns),
        NodeRole::Class => {
            entity_role_accepts(tag, node, Some(EntityKindRole::Class), context.columns)
        }
        NodeRole::Datatype => {
            entity_role_accepts(tag, node, Some(EntityKindRole::Datatype), context.columns)
        }
        NodeRole::ObjectProperty => entity_role_accepts(
            tag,
            node,
            Some(EntityKindRole::ObjectProperty),
            context.columns,
        ),
        NodeRole::DataProperty => entity_role_accepts(
            tag,
            node,
            Some(EntityKindRole::DataProperty),
            context.columns,
        ),
        NodeRole::AnnotationProperty => entity_role_accepts(
            tag,
            node,
            Some(EntityKindRole::AnnotationProperty),
            context.columns,
        ),
        NodeRole::Literal => Ok(tag == 4),
        NodeRole::Annotation => Ok(tag == 5),
        NodeRole::ObjectPropertyExpression => {
            if tag == 10 {
                Ok(true)
            } else {
                entity_role_accepts(
                    tag,
                    node,
                    Some(EntityKindRole::ObjectProperty),
                    context.columns,
                )
            }
        }
        NodeRole::SubObjectPropertyExpression => {
            if matches!(tag, 10 | 11) {
                Ok(true)
            } else {
                entity_role_accepts(
                    tag,
                    node,
                    Some(EntityKindRole::ObjectProperty),
                    context.columns,
                )
            }
        }
        NodeRole::FacetRestriction => Ok(tag == 20),
        NodeRole::DataRange => {
            if matches!(tag, 21..=25) {
                Ok(true)
            } else {
                entity_role_accepts(tag, node, Some(EntityKindRole::Datatype), context.columns)
            }
        }
        NodeRole::ClassExpression => {
            if matches!(tag, 30..=46) {
                Ok(true)
            } else {
                entity_role_accepts(tag, node, Some(EntityKindRole::Class), context.columns)
            }
        }
        NodeRole::Individual => {
            if tag == 3 {
                Ok(true)
            } else {
                entity_role_accepts(
                    tag,
                    node,
                    Some(EntityKindRole::NamedIndividual),
                    context.columns,
                )
            }
        }
        NodeRole::AnnotationValue => Ok(matches!(tag, 1 | 3 | 4)),
        NodeRole::AnnotationSubject => Ok(matches!(tag, 1 | 3)),
        NodeRole::IndividualArgument => {
            if matches!(tag, 3 | 140) {
                Ok(true)
            } else {
                entity_role_accepts(
                    tag,
                    node,
                    Some(EntityKindRole::NamedIndividual),
                    context.columns,
                )
            }
        }
        NodeRole::DataArgument => Ok(matches!(tag, 4 | 140)),
        NodeRole::Atom => Ok(matches!(tag, 141..=147)),
    }
}

fn entity_role_accepts<B: ByteSource>(
    tag: u16,
    node: usize,
    expected: Option<EntityKindRole>,
    columns: &EncodedColumns<B>,
) -> EncodedResult<bool> {
    if tag != 2 {
        return Ok(false);
    }
    let actual = entity_kind_at_node(node, columns)?;
    Ok(expected.is_none_or(|selected| selected == actual))
}

fn entity_kind_at_node<B: ByteSource>(
    node: usize,
    columns: &EncodedColumns<B>,
) -> EncodedResult<EntityKindRole> {
    let field = usize_at(columns.node_field_offsets, node, "entity field offset")?;
    if byte_at(columns.field_kinds, field, "entity kind")? != COMPONENT_ENUM {
        return Err(EncodedValidationError::protocol(
            "encoded entity kind has the wrong schema role",
        ));
    }
    entity_kind_scalar(
        columns.scalar_bytes,
        usize_at(columns.field_values, field, "entity kind value")?,
        usize_at(columns.field_lengths, field, "entity kind length")?,
    )
}

fn entity_kind_scalar<B: ByteSource>(
    scalars: B,
    start: usize,
    length: usize,
) -> EncodedResult<EntityKindRole> {
    const KINDS: &[(EntityKindRole, &[u8])] = &[
        (EntityKindRole::Class, b"class"),
        (EntityKindRole::Datatype, b"datatype"),
        (EntityKindRole::ObjectProperty, b"object_property"),
        (EntityKindRole::DataProperty, b"data_property"),
        (EntityKindRole::AnnotationProperty, b"annotation_property"),
        (EntityKindRole::NamedIndividual, b"named_individual"),
    ];
    for (kind, expected) in KINDS {
        if scalar_equals(scalars, start, length, expected)? {
            return Ok(*kind);
        }
    }
    Err(EncodedValidationError::protocol(
        "encoded entity kind is not a model-schema-1 value",
    ))
}

fn scalar_equals<B: ByteSource>(
    scalars: B,
    start: usize,
    length: usize,
    expected: &[u8],
) -> EncodedResult<bool> {
    let end = start
        .checked_add(length)
        .ok_or_else(|| EncodedValidationError::resource("encoded scalar range overflow"))?;
    if end > scalars.len() {
        return Err(EncodedValidationError::protocol(
            "encoded scalar component is out of bounds",
        ));
    }
    if length != expected.len() {
        return Ok(false);
    }
    for (offset, byte) in expected.iter().copied().enumerate() {
        if byte_at(scalars, start + offset, "entity kind scalar")? != byte {
            return Ok(false);
        }
    }
    Ok(true)
}

fn field_role_error(location: FieldLocation) -> EncodedValidationError {
    let FieldLocation { tag, position } = location;
    EncodedValidationError::protocol(format!(
        "encoded node tag {tag} field {position} has the wrong schema role"
    ))
}

fn validate_leaf_component<B: ByteSource>(
    component: Component,
    context: ValidationContext<'_, B>,
    scalar_cursor: &mut usize,
    work: &mut u64,
    max_work: u64,
) -> EncodedResult<()> {
    let Component {
        kind,
        value,
        length,
    } = component;
    match kind {
        COMPONENT_NONE => {
            if value != 0 || length != 0 {
                return Err(EncodedValidationError::protocol(
                    "encoded none component must have zero value and length",
                ));
            }
        }
        COMPONENT_NODE => {
            if length != 0 {
                return Err(EncodedValidationError::protocol(
                    "encoded node component must have zero length",
                ));
            }
            let identifier = u32::try_from(value)
                .map_err(|_| EncodedValidationError::protocol("encoded node ID exceeds u32"))?;
            node_index(identifier, context.node_count)?;
        }
        COMPONENT_TEXT | COMPONENT_BYTES | COMPONENT_INTEGER | COMPONENT_ENUM => {
            if value != *scalar_cursor {
                return Err(EncodedValidationError::protocol(
                    "encoded scalar components do not exactly cover the scalar arena",
                ));
            }
            let end = value
                .checked_add(length)
                .ok_or_else(|| EncodedValidationError::resource("encoded scalar range overflow"))?;
            if end > context.columns.scalar_bytes.len() {
                return Err(EncodedValidationError::protocol(
                    "encoded scalar component is out of bounds",
                ));
            }
            if matches!(kind, COMPONENT_TEXT | COMPONENT_ENUM) {
                claim_work(
                    work,
                    u64::try_from(length).map_err(|_| {
                        EncodedValidationError::resource("encoded scalar scan exceeds u64")
                    })?,
                    max_work,
                )?;
            }
            match kind {
                COMPONENT_TEXT => validate_utf8(context.columns.scalar_bytes, value, end)?,
                COMPONENT_INTEGER => {
                    if length == 0
                        || (length > 1
                            && byte_at(context.columns.scalar_bytes, end - 1, "integer scalar")?
                                == 0)
                    {
                        return Err(EncodedValidationError::protocol(
                            "encoded integer component is not minimal little-endian",
                        ));
                    }
                }
                COMPONENT_ENUM => {
                    if length == 0 {
                        return Err(EncodedValidationError::protocol(
                            "encoded enum component must be nonempty ASCII",
                        ));
                    }
                    for index in value..end {
                        if !byte_at(context.columns.scalar_bytes, index, "enum scalar")?.is_ascii()
                        {
                            return Err(EncodedValidationError::protocol(
                                "encoded enum component must be nonempty ASCII",
                            ));
                        }
                    }
                }
                COMPONENT_BYTES => {}
                _ => {
                    return Err(EncodedValidationError::invariant(
                        "non-scalar kind reached scalar validation",
                    ));
                }
            }
            *scalar_cursor = end;
        }
        COMPONENT_SET | COMPONENT_SEQUENCE => {
            return Err(EncodedValidationError::protocol(
                "encoded nested collection item is not supported by schema 1",
            ));
        }
        _ => {
            return Err(EncodedValidationError::protocol(
                "unknown encoded component kind",
            ));
        }
    }
    Ok(())
}

fn validate_graph_and_lengths<B: ByteSource>(
    columns: &EncodedColumns<B>,
    root_count: usize,
    node_count: usize,
    work: &mut u64,
    max_work: u64,
) -> EncodedResult<Vec<u64>> {
    claim_work(
        work,
        u64::try_from(node_count)
            .map_err(|_| EncodedValidationError::resource("encoded graph scan exceeds u64"))?,
        max_work,
    )?;
    let mut states = Vec::new();
    states.try_reserve_exact(node_count).map_err(|_| {
        EncodedValidationError::resource("encoded reachability state allocation failed")
    })?;
    states.resize(node_count, 0_u8);
    let mut canonical_lengths = Vec::new();
    canonical_lengths
        .try_reserve_exact(node_count)
        .map_err(|_| {
            EncodedValidationError::resource("encoded canonical length allocation failed")
        })?;
    canonical_lengths.resize(node_count, 0_u64);
    let mut stack = Vec::<DfsFrame>::new();
    for root in 0..root_count {
        let identifier = u32_at(columns.root_ids, root, "root ID")?;
        let node = node_index(identifier, node_count)?;
        if states[node] == 2 {
            continue;
        }
        if states[node] == 1 {
            return Err(EncodedValidationError::protocol(
                "encoded structural graph is cyclic",
            ));
        }
        states[node] = 1;
        push_dfs_frame(&mut stack, DfsFrame::new(node, columns)?)?;
        while let Some(frame) = stack.last_mut() {
            claim_work(work, 1, max_work)?;
            let child = if frame.item_cursor < frame.item_end {
                let item = frame.item_cursor;
                frame.item_cursor += 1;
                (byte_at(columns.item_kinds, item, "item kind")? == COMPONENT_NODE)
                    .then(|| node_id_at(columns.item_values, item, "item node ID"))
                    .transpose()?
            } else if frame.field_cursor < frame.field_end {
                let field = frame.field_cursor;
                frame.field_cursor += 1;
                match byte_at(columns.field_kinds, field, "field kind")? {
                    COMPONENT_NODE => {
                        Some(node_id_at(columns.field_values, field, "field node ID")?)
                    }
                    COMPONENT_SET | COMPONENT_SEQUENCE => {
                        frame.item_cursor =
                            usize_at(columns.field_values, field, "field item offset")?;
                        frame.item_end = frame
                            .item_cursor
                            .checked_add(usize_at(
                                columns.field_lengths,
                                field,
                                "field item length",
                            )?)
                            .ok_or_else(|| {
                                EncodedValidationError::resource("encoded item range overflow")
                            })?;
                        None
                    }
                    _ => None,
                }
            } else {
                let completed = frame.node;
                states[completed] = 2;
                stack.pop();
                canonical_lengths[completed] =
                    canonical_node_length(completed, columns, &canonical_lengths, work, max_work)?;
                continue;
            };
            let Some(child) = child else {
                continue;
            };
            let child = node_index(child, node_count)?;
            match states[child] {
                0 => {
                    states[child] = 1;
                    push_dfs_frame(&mut stack, DfsFrame::new(child, columns)?)?;
                }
                1 => {
                    return Err(EncodedValidationError::protocol(
                        "encoded structural graph is cyclic",
                    ));
                }
                2 => {}
                _ => {
                    return Err(EncodedValidationError::invariant(
                        "invalid encoded DFS state",
                    ));
                }
            }
        }
    }
    if states.iter().any(|state| *state != 2) {
        return Err(EncodedValidationError::protocol(
            "encoded structural graph contains unreachable nodes",
        ));
    }
    Ok(canonical_lengths)
}

fn push_dfs_frame(stack: &mut Vec<DfsFrame>, frame: DfsFrame) -> EncodedResult<()> {
    stack
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("encoded graph stack allocation failed"))?;
    stack.push(frame);
    Ok(())
}

fn canonical_node_length<B: ByteSource>(
    node: usize,
    columns: &EncodedColumns<B>,
    canonical_lengths: &[u64],
    work: &mut u64,
    max_work: u64,
) -> EncodedResult<u64> {
    let tag = u16_at(columns.node_tags, node, "node tag")?;
    let mut total = u64::try_from(canonical_varint_width(u64::from(tag)))
        .map_err(|_| EncodedValidationError::resource("encoded canonical length exceeds u64"))?;
    let start = usize_at(columns.node_field_offsets, node, "node field offset")?;
    let end = usize_at(columns.node_field_offsets, node + 1, "node field offset")?;
    for field in start..end {
        claim_work(work, 1, max_work)?;
        let kind = byte_at(columns.field_kinds, field, "field kind")?;
        let value = usize_at(columns.field_values, field, "field value")?;
        let length = usize_at(columns.field_lengths, field, "field length")?;
        if matches!(kind, COMPONENT_SET | COMPONENT_SEQUENCE) {
            let count = u64::try_from(length).map_err(|_| {
                EncodedValidationError::resource("encoded collection length exceeds u64")
            })?;
            add_canonical_length(&mut total, 1)?;
            add_canonical_length(
                &mut total,
                u64::try_from(canonical_varint_width(count)).map_err(|_| {
                    EncodedValidationError::resource("encoded canonical length exceeds u64")
                })?,
            )?;
            let item_end = value
                .checked_add(length)
                .ok_or_else(|| EncodedValidationError::resource("encoded item range overflow"))?;
            for item in value..item_end {
                claim_work(work, 1, max_work)?;
                let item_kind = byte_at(columns.item_kinds, item, "item kind")?;
                let item_value = usize_at(columns.item_values, item, "item value")?;
                let item_length = usize_at(columns.item_lengths, item, "item length")?;
                let item_size = canonical_leaf_length(
                    item_kind,
                    item_value,
                    item_length,
                    columns,
                    canonical_lengths,
                )?;
                if kind == COMPONENT_SET {
                    // Canonical sets frame node bytes directly; sequence items
                    // retain their component marker before the node frame.
                    let framed = item_size.checked_sub(1).ok_or_else(|| {
                        EncodedValidationError::invariant("canonical set item has no node marker")
                    })?;
                    add_canonical_length(&mut total, framed)?;
                } else {
                    add_canonical_length(&mut total, item_size)?;
                }
            }
        } else {
            add_canonical_length(
                &mut total,
                canonical_leaf_length(kind, value, length, columns, canonical_lengths)?,
            )?;
        }
    }
    Ok(total)
}

fn canonical_leaf_length<B: ByteSource>(
    kind: u8,
    value: usize,
    length: usize,
    columns: &EncodedColumns<B>,
    canonical_lengths: &[u64],
) -> EncodedResult<u64> {
    match kind {
        COMPONENT_NONE => Ok(1),
        COMPONENT_NODE => {
            let identifier = u32::try_from(value)
                .map_err(|_| EncodedValidationError::protocol("encoded node ID exceeds u32"))?;
            let node = node_index(identifier, canonical_lengths.len())?;
            let nested = canonical_lengths[node];
            if nested == 0 {
                return Err(EncodedValidationError::invariant(
                    "canonical child length was not computed before its parent",
                ));
            }
            let mut total = 1_u64;
            add_canonical_length(
                &mut total,
                u64::try_from(canonical_varint_width(nested)).map_err(|_| {
                    EncodedValidationError::resource("encoded canonical length exceeds u64")
                })?,
            )?;
            add_canonical_length(&mut total, nested)?;
            Ok(total)
        }
        COMPONENT_TEXT | COMPONENT_BYTES | COMPONENT_ENUM => {
            let payload = u64::try_from(length).map_err(|_| {
                EncodedValidationError::resource("encoded scalar length exceeds u64")
            })?;
            let mut total = 1_u64;
            add_canonical_length(
                &mut total,
                u64::try_from(canonical_varint_width(payload)).map_err(|_| {
                    EncodedValidationError::resource("encoded canonical length exceeds u64")
                })?,
            )?;
            add_canonical_length(&mut total, payload)?;
            Ok(total)
        }
        COMPONENT_INTEGER => {
            let width = canonical_integer_varint_width(columns.scalar_bytes, value, length)?;
            1_u64
                .checked_add(u64::try_from(width).map_err(|_| {
                    EncodedValidationError::resource("encoded integer width exceeds u64")
                })?)
                .ok_or_else(|| {
                    EncodedValidationError::resource("encoded canonical length exceeds u64")
                })
        }
        COMPONENT_SET | COMPONENT_SEQUENCE => Err(EncodedValidationError::invariant(
            "nested collection reached canonical leaf sizing",
        )),
        _ => Err(EncodedValidationError::invariant(
            "invalid component reached canonical leaf sizing",
        )),
    }
}

fn add_canonical_length(total: &mut u64, amount: u64) -> EncodedResult<()> {
    *total = total.checked_add(amount).ok_or_else(|| {
        EncodedValidationError::resource("encoded canonical model length exceeds u64")
    })?;
    Ok(())
}

#[derive(Clone, Copy)]
enum ComponentRow {
    Field(usize),
    Item(usize),
}

#[derive(Clone, Copy)]
struct ScalarRange {
    start: usize,
    length: usize,
}

#[derive(Clone, Copy)]
enum CanonicalCompareTask {
    Node {
        left: usize,
        right: usize,
    },
    Fields {
        left: usize,
        right: usize,
        remaining: usize,
    },
    Collection {
        kind: u8,
        left: usize,
        right: usize,
        remaining: usize,
    },
}

fn validate_dense_node_order<B: ByteSource>(
    columns: &EncodedColumns<B>,
    canonical_lengths: &[u64],
    work: &mut u64,
    max_work: u64,
) -> EncodedResult<()> {
    for right in 1..canonical_lengths.len() {
        let left = right - 1;
        if compare_canonical_nodes(left, right, columns, canonical_lengths, work, max_work)?
            != Ordering::Less
        {
            return Err(EncodedValidationError::protocol(
                "encoded structural node IDs are not canonical and unique",
            ));
        }
    }
    Ok(())
}

fn compare_canonical_nodes<B: ByteSource>(
    left: usize,
    right: usize,
    columns: &EncodedColumns<B>,
    canonical_lengths: &[u64],
    work: &mut u64,
    max_work: u64,
) -> EncodedResult<Ordering> {
    let mut tasks = Vec::new();
    push_compare_task(&mut tasks, CanonicalCompareTask::Node { left, right })?;
    while let Some(task) = tasks.pop() {
        claim_work(work, 1, max_work)?;
        match task {
            CanonicalCompareTask::Node { left, right } => {
                if left == right {
                    continue;
                }
                let left_tag = u64::from(u16_at(columns.node_tags, left, "node tag")?);
                let right_tag = u64::from(u16_at(columns.node_tags, right, "node tag")?);
                let ordering = compare_u64_varints(left_tag, right_tag);
                if ordering != Ordering::Equal {
                    return Ok(ordering);
                }
                let left_start = usize_at(columns.node_field_offsets, left, "node field offset")?;
                let left_end = usize_at(columns.node_field_offsets, left + 1, "node field offset")?;
                let right_start = usize_at(columns.node_field_offsets, right, "node field offset")?;
                let right_end =
                    usize_at(columns.node_field_offsets, right + 1, "node field offset")?;
                let remaining = left_end - left_start;
                if right_end - right_start != remaining {
                    return Err(EncodedValidationError::invariant(
                        "equal constructor tags have different validated arities",
                    ));
                }
                push_compare_task(
                    &mut tasks,
                    CanonicalCompareTask::Fields {
                        left: left_start,
                        right: right_start,
                        remaining,
                    },
                )?;
            }
            CanonicalCompareTask::Fields {
                left,
                right,
                remaining,
            } => {
                if remaining == 0 {
                    continue;
                }
                push_compare_task(
                    &mut tasks,
                    CanonicalCompareTask::Fields {
                        left: left.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource("encoded field index overflow")
                        })?,
                        right: right.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource("encoded field index overflow")
                        })?,
                        remaining: remaining - 1,
                    },
                )?;
                if let Some(ordering) = schedule_component_comparison(
                    ComponentRow::Field(left),
                    ComponentRow::Field(right),
                    columns,
                    canonical_lengths,
                    &mut tasks,
                    work,
                    max_work,
                )? {
                    return Ok(ordering);
                }
            }
            CanonicalCompareTask::Collection {
                kind,
                left,
                right,
                remaining,
            } => {
                if remaining == 0 {
                    continue;
                }
                push_compare_task(
                    &mut tasks,
                    CanonicalCompareTask::Collection {
                        kind,
                        left: left.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource("encoded item index overflow")
                        })?,
                        right: right.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource("encoded item index overflow")
                        })?,
                        remaining: remaining - 1,
                    },
                )?;
                if kind == COMPONENT_SET {
                    let left_node = node_index(
                        node_id_at(columns.item_values, left, "set item node ID")?,
                        canonical_lengths.len(),
                    )?;
                    let right_node = node_index(
                        node_id_at(columns.item_values, right, "set item node ID")?,
                        canonical_lengths.len(),
                    )?;
                    let ordering = compare_u64_varints(
                        canonical_lengths[left_node],
                        canonical_lengths[right_node],
                    );
                    if ordering != Ordering::Equal {
                        return Ok(ordering);
                    }
                    push_compare_task(
                        &mut tasks,
                        CanonicalCompareTask::Node {
                            left: left_node,
                            right: right_node,
                        },
                    )?;
                } else if let Some(ordering) = schedule_component_comparison(
                    ComponentRow::Item(left),
                    ComponentRow::Item(right),
                    columns,
                    canonical_lengths,
                    &mut tasks,
                    work,
                    max_work,
                )? {
                    return Ok(ordering);
                }
            }
        }
    }
    Ok(Ordering::Equal)
}

fn schedule_component_comparison<B: ByteSource>(
    left: ComponentRow,
    right: ComponentRow,
    columns: &EncodedColumns<B>,
    canonical_lengths: &[u64],
    tasks: &mut Vec<CanonicalCompareTask>,
    work: &mut u64,
    max_work: u64,
) -> EncodedResult<Option<Ordering>> {
    let (left_kind, left_value, left_length) = component_parts(left, columns)?;
    let (right_kind, right_value, right_length) = component_parts(right, columns)?;
    let ordering = left_kind.cmp(&right_kind);
    if ordering != Ordering::Equal {
        return Ok(Some(ordering));
    }
    match left_kind {
        COMPONENT_NONE => Ok(None),
        COMPONENT_NODE => {
            let left_node = node_index(
                u32::try_from(left_value)
                    .map_err(|_| EncodedValidationError::protocol("encoded node ID exceeds u32"))?,
                canonical_lengths.len(),
            )?;
            let right_node = node_index(
                u32::try_from(right_value)
                    .map_err(|_| EncodedValidationError::protocol("encoded node ID exceeds u32"))?,
                canonical_lengths.len(),
            )?;
            let ordering =
                compare_u64_varints(canonical_lengths[left_node], canonical_lengths[right_node]);
            if ordering != Ordering::Equal {
                return Ok(Some(ordering));
            }
            push_compare_task(
                tasks,
                CanonicalCompareTask::Node {
                    left: left_node,
                    right: right_node,
                },
            )?;
            Ok(None)
        }
        COMPONENT_TEXT | COMPONENT_BYTES | COMPONENT_ENUM => {
            let left_size = u64::try_from(left_length).map_err(|_| {
                EncodedValidationError::resource("encoded scalar length exceeds u64")
            })?;
            let right_size = u64::try_from(right_length).map_err(|_| {
                EncodedValidationError::resource("encoded scalar length exceeds u64")
            })?;
            let ordering = compare_u64_varints(left_size, right_size);
            if ordering != Ordering::Equal {
                return Ok(Some(ordering));
            }
            let ordering = compare_scalar_ranges(
                columns.scalar_bytes,
                left_value,
                right_value,
                left_length,
                work,
                max_work,
            )?;
            Ok((ordering != Ordering::Equal).then_some(ordering))
        }
        COMPONENT_INTEGER => {
            let ordering = compare_integer_components(
                columns.scalar_bytes,
                ScalarRange {
                    start: left_value,
                    length: left_length,
                },
                ScalarRange {
                    start: right_value,
                    length: right_length,
                },
                work,
                max_work,
            )?;
            Ok((ordering != Ordering::Equal).then_some(ordering))
        }
        COMPONENT_SET | COMPONENT_SEQUENCE => {
            let left_size = u64::try_from(left_length).map_err(|_| {
                EncodedValidationError::resource("encoded collection length exceeds u64")
            })?;
            let right_size = u64::try_from(right_length).map_err(|_| {
                EncodedValidationError::resource("encoded collection length exceeds u64")
            })?;
            let ordering = compare_u64_varints(left_size, right_size);
            if ordering != Ordering::Equal {
                return Ok(Some(ordering));
            }
            push_compare_task(
                tasks,
                CanonicalCompareTask::Collection {
                    kind: left_kind,
                    left: left_value,
                    right: right_value,
                    remaining: left_length,
                },
            )?;
            Ok(None)
        }
        _ => Err(EncodedValidationError::invariant(
            "invalid component reached canonical comparison",
        )),
    }
}

fn component_parts<B: ByteSource>(
    row: ComponentRow,
    columns: &EncodedColumns<B>,
) -> EncodedResult<(u8, usize, usize)> {
    match row {
        ComponentRow::Field(index) => Ok((
            byte_at(columns.field_kinds, index, "field kind")?,
            usize_at(columns.field_values, index, "field value")?,
            usize_at(columns.field_lengths, index, "field length")?,
        )),
        ComponentRow::Item(index) => Ok((
            byte_at(columns.item_kinds, index, "item kind")?,
            usize_at(columns.item_values, index, "item value")?,
            usize_at(columns.item_lengths, index, "item length")?,
        )),
    }
}

fn compare_scalar_ranges<B: ByteSource>(
    scalars: B,
    left: usize,
    right: usize,
    length: usize,
    work: &mut u64,
    max_work: u64,
) -> EncodedResult<Ordering> {
    if left == right {
        return Ok(Ordering::Equal);
    }
    claim_work(
        work,
        u64::try_from(length).map_err(|_| {
            EncodedValidationError::resource("encoded scalar comparison exceeds u64")
        })?,
        max_work,
    )?;
    for offset in 0..length {
        let left_byte = byte_at(
            scalars,
            left.checked_add(offset).ok_or_else(|| {
                EncodedValidationError::resource("encoded scalar offset overflow")
            })?,
            "canonical scalar",
        )?;
        let right_byte = byte_at(
            scalars,
            right.checked_add(offset).ok_or_else(|| {
                EncodedValidationError::resource("encoded scalar offset overflow")
            })?,
            "canonical scalar",
        )?;
        let ordering = left_byte.cmp(&right_byte);
        if ordering != Ordering::Equal {
            return Ok(ordering);
        }
    }
    Ok(Ordering::Equal)
}

fn compare_integer_components<B: ByteSource>(
    scalars: B,
    left: ScalarRange,
    right: ScalarRange,
    work: &mut u64,
    max_work: u64,
) -> EncodedResult<Ordering> {
    let left_width = canonical_integer_varint_width(scalars, left.start, left.length)?;
    let right_width = canonical_integer_varint_width(scalars, right.start, right.length)?;
    let compared = left_width.max(right_width);
    claim_work(
        work,
        u64::try_from(compared).map_err(|_| {
            EncodedValidationError::resource("encoded integer comparison exceeds u64")
        })?,
        max_work,
    )?;
    for index in 0..compared {
        let left_byte = (index < left_width)
            .then(|| integer_varint_byte(scalars, left.start, left.length, index, left_width));
        let right_byte = (index < right_width)
            .then(|| integer_varint_byte(scalars, right.start, right.length, index, right_width));
        let ordering = match (left_byte, right_byte) {
            (Some(left_byte), Some(right_byte)) => left_byte?.cmp(&right_byte?),
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
        };
        if ordering != Ordering::Equal {
            return Ok(ordering);
        }
    }
    Ok(Ordering::Equal)
}

fn canonical_integer_varint_width<B: ByteSource>(
    scalars: B,
    start: usize,
    length: usize,
) -> EncodedResult<usize> {
    let last = length.checked_sub(1).ok_or_else(|| {
        EncodedValidationError::invariant("validated integer has an empty payload")
    })?;
    let high = byte_at(
        scalars,
        start
            .checked_add(last)
            .ok_or_else(|| EncodedValidationError::resource("encoded integer offset overflow"))?,
        "integer scalar",
    )?;
    let lower_bits = last
        .checked_mul(8)
        .ok_or_else(|| EncodedValidationError::resource("encoded integer bit length overflow"))?;
    let high_bits = usize::try_from(u8::BITS - high.leading_zeros()).map_err(|_| {
        EncodedValidationError::resource("encoded integer bit length exceeds usize")
    })?;
    let bit_length = lower_bits
        .checked_add(high_bits)
        .ok_or_else(|| EncodedValidationError::resource("encoded integer bit length overflow"))?;
    Ok(bit_length.div_ceil(7).max(1))
}

fn integer_varint_byte<B: ByteSource>(
    scalars: B,
    start: usize,
    payload_length: usize,
    index: usize,
    encoded_width: usize,
) -> EncodedResult<u8> {
    let bit_offset = index
        .checked_mul(7)
        .ok_or_else(|| EncodedValidationError::resource("encoded integer bit offset overflow"))?;
    let source_index = bit_offset / 8;
    let shift = u32::try_from(bit_offset % 8)
        .map_err(|_| EncodedValidationError::resource("encoded integer bit shift exceeds u32"))?;
    let absolute = start
        .checked_add(source_index)
        .ok_or_else(|| EncodedValidationError::resource("encoded integer offset overflow"))?;
    let mut window = u16::from(byte_at(scalars, absolute, "integer scalar")?) >> shift;
    if shift != 0 && source_index + 1 < payload_length {
        window |= u16::from(byte_at(scalars, absolute + 1, "integer scalar")?) << (8 - shift);
    }
    let mut output = u8::try_from(window & 0x7f)
        .map_err(|_| EncodedValidationError::invariant("integer varint chunk exceeds u8"))?;
    if index + 1 < encoded_width {
        output |= 0x80;
    }
    Ok(output)
}

fn compare_u64_varints(left: u64, right: u64) -> Ordering {
    let left_width = canonical_varint_width(left);
    let right_width = canonical_varint_width(right);
    for index in 0..left_width.max(right_width) {
        let left_byte = (index < left_width).then(|| u64_varint_byte(left, index, left_width));
        let right_byte = (index < right_width).then(|| u64_varint_byte(right, index, right_width));
        let ordering = left_byte.cmp(&right_byte);
        if ordering != Ordering::Equal {
            return ordering;
        }
    }
    Ordering::Equal
}

fn canonical_varint_width(value: u64) -> usize {
    let bits = usize::try_from(u64::BITS - value.leading_zeros()).unwrap_or(usize::MAX);
    bits.div_ceil(7).max(1)
}

fn u64_varint_byte(value: u64, index: usize, width: usize) -> u8 {
    debug_assert!(index < width && width <= 10);
    let shift = u32::try_from(index * 7).unwrap_or(u32::MAX);
    let mut output = u8::try_from((value >> shift) & 0x7f).unwrap_or(0x7f);
    if index + 1 < width {
        output |= 0x80;
    }
    output
}

fn push_compare_task(
    tasks: &mut Vec<CanonicalCompareTask>,
    task: CanonicalCompareTask,
) -> EncodedResult<()> {
    tasks.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("encoded canonical comparison stack allocation failed")
    })?;
    tasks.push(task);
    Ok(())
}

fn validate_utf8<B: ByteSource>(bytes: B, start: usize, end: usize) -> EncodedResult<()> {
    let mut cursor = start;
    while cursor < end {
        let first = byte_at(bytes, cursor, "text scalar")?;
        cursor += 1;
        match first {
            0x00..=0x7f => {}
            0xc2..=0xdf => require_continuation(bytes, &mut cursor, end)?,
            0xe0 => {
                let second = next_text_byte(bytes, &mut cursor, end)?;
                if !(0xa0..=0xbf).contains(&second) {
                    return Err(invalid_utf8());
                }
                require_continuation(bytes, &mut cursor, end)?;
            }
            0xe1..=0xec | 0xee..=0xef => {
                require_continuation(bytes, &mut cursor, end)?;
                require_continuation(bytes, &mut cursor, end)?;
            }
            0xed => {
                let second = next_text_byte(bytes, &mut cursor, end)?;
                if !(0x80..=0x9f).contains(&second) {
                    return Err(invalid_utf8());
                }
                require_continuation(bytes, &mut cursor, end)?;
            }
            0xf0 => {
                let second = next_text_byte(bytes, &mut cursor, end)?;
                if !(0x90..=0xbf).contains(&second) {
                    return Err(invalid_utf8());
                }
                require_continuation(bytes, &mut cursor, end)?;
                require_continuation(bytes, &mut cursor, end)?;
            }
            0xf1..=0xf3 => {
                require_continuation(bytes, &mut cursor, end)?;
                require_continuation(bytes, &mut cursor, end)?;
                require_continuation(bytes, &mut cursor, end)?;
            }
            0xf4 => {
                let second = next_text_byte(bytes, &mut cursor, end)?;
                if !(0x80..=0x8f).contains(&second) {
                    return Err(invalid_utf8());
                }
                require_continuation(bytes, &mut cursor, end)?;
                require_continuation(bytes, &mut cursor, end)?;
            }
            _ => return Err(invalid_utf8()),
        }
    }
    Ok(())
}

fn invalid_utf8() -> EncodedValidationError {
    EncodedValidationError::protocol("encoded text component is not valid UTF-8")
}

fn next_text_byte<B: ByteSource>(bytes: B, cursor: &mut usize, end: usize) -> EncodedResult<u8> {
    if *cursor >= end {
        return Err(invalid_utf8());
    }
    let byte = byte_at(bytes, *cursor, "text scalar")?;
    *cursor += 1;
    Ok(byte)
}

fn require_continuation<B: ByteSource>(
    bytes: B,
    cursor: &mut usize,
    end: usize,
) -> EncodedResult<()> {
    if !(0x80..=0xbf).contains(&next_text_byte(bytes, cursor, end)?) {
        return Err(invalid_utf8());
    }
    Ok(())
}

const fn root_accepts(kind: u8, tag: u16) -> bool {
    match kind {
        ROOT_ONTOLOGY_ANNOTATION => tag == 5,
        ROOT_AXIOM => matches!(
            tag,
            60..=64 | 70..=82 | 90..=95 | 100..=101 | 110..=116 | 120..=123
        ),
        ROOT_EXTENSION => tag == 148,
        _ => false,
    }
}

fn node_index(identifier: u32, node_count: usize) -> EncodedResult<usize> {
    let index = identifier
        .checked_sub(1)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| {
            EncodedValidationError::protocol("encoded node IDs are one-based and nonzero")
        })?;
    if index >= node_count {
        return Err(EncodedValidationError::protocol(
            "encoded node ID is out of range",
        ));
    }
    Ok(index)
}

fn byte_at<B: ByteSource>(bytes: B, index: usize, name: &str) -> EncodedResult<u8> {
    bytes
        .byte(index)
        .ok_or_else(|| EncodedValidationError::protocol(format!("encoded {name} is truncated")))
}

fn aligned_count<B: ByteSource>(bytes: B, width: usize, name: &str) -> EncodedResult<usize> {
    if bytes.len() % width != 0 {
        return Err(EncodedValidationError::protocol(format!(
            "encoded {name} is not aligned to {width} bytes"
        )));
    }
    Ok(bytes.len() / width)
}

fn u16_at<B: ByteSource>(bytes: B, index: usize, name: &str) -> EncodedResult<u16> {
    let start = index.checked_mul(2).ok_or_else(|| {
        EncodedValidationError::resource(format!("encoded {name} offset overflow"))
    })?;
    Ok(u16::from_le_bytes([
        byte_at(bytes, start, name)?,
        byte_at(bytes, start + 1, name)?,
    ]))
}

fn u32_at<B: ByteSource>(bytes: B, index: usize, name: &str) -> EncodedResult<u32> {
    let start = index.checked_mul(4).ok_or_else(|| {
        EncodedValidationError::resource(format!("encoded {name} offset overflow"))
    })?;
    Ok(u32::from_le_bytes([
        byte_at(bytes, start, name)?,
        byte_at(bytes, start + 1, name)?,
        byte_at(bytes, start + 2, name)?,
        byte_at(bytes, start + 3, name)?,
    ]))
}

fn u64_at<B: ByteSource>(bytes: B, index: usize, name: &str) -> EncodedResult<u64> {
    let start = index.checked_mul(8).ok_or_else(|| {
        EncodedValidationError::resource(format!("encoded {name} offset overflow"))
    })?;
    Ok(u64::from_le_bytes([
        byte_at(bytes, start, name)?,
        byte_at(bytes, start + 1, name)?,
        byte_at(bytes, start + 2, name)?,
        byte_at(bytes, start + 3, name)?,
        byte_at(bytes, start + 4, name)?,
        byte_at(bytes, start + 5, name)?,
        byte_at(bytes, start + 6, name)?,
        byte_at(bytes, start + 7, name)?,
    ]))
}

fn node_id_at<B: ByteSource>(bytes: B, index: usize, name: &str) -> EncodedResult<u32> {
    u32::try_from(u64_at(bytes, index, name)?)
        .map_err(|_| EncodedValidationError::protocol(format!("encoded {name} exceeds u32")))
}

fn usize_at<B: ByteSource>(bytes: B, index: usize, name: &str) -> EncodedResult<usize> {
    usize::try_from(u64_at(bytes, index, name)?)
        .map_err(|_| EncodedValidationError::resource(format!("encoded {name} exceeds usize")))
}

fn enforce_count(value: usize, maximum: usize, name: &str) -> EncodedResult<()> {
    if value > maximum {
        Err(EncodedValidationError::resource(format!(
            "{name} exceeds its limit"
        )))
    } else {
        Ok(())
    }
}

fn claim_work(work: &mut u64, amount: u64, maximum: u64) -> EncodedResult<()> {
    let following = work
        .checked_add(amount)
        .ok_or_else(|| EncodedValidationError::resource("encoded validation work overflow"))?;
    if following > maximum {
        return Err(EncodedValidationError::resource(
            "encoded validation exceeds its work limit",
        ));
    }
    *work = following;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy)]
    struct IndexedBytes<'a>(&'a [u8]);

    impl ByteSource for IndexedBytes<'_> {
        fn len(self) -> usize {
            self.0.len()
        }

        fn byte(self, index: usize) -> Option<u8> {
            self.0.get(index).copied()
        }
    }

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
                root_kinds: self.root_kinds.as_slice(),
                root_ids: self.root_ids.as_slice(),
                node_tags: self.node_tags.as_slice(),
                node_field_offsets: self.node_field_offsets.as_slice(),
                field_kinds: self.field_kinds.as_slice(),
                field_values: self.field_values.as_slice(),
                field_lengths: self.field_lengths.as_slice(),
                item_kinds: self.item_kinds.as_slice(),
                item_values: self.item_values.as_slice(),
                item_lengths: self.item_lengths.as_slice(),
                scalar_bytes: self.scalar_bytes.as_slice(),
            }
        }

        fn indexed(&self) -> EncodedColumns<IndexedBytes<'_>> {
            EncodedColumns {
                root_kinds: IndexedBytes(&self.root_kinds),
                root_ids: IndexedBytes(&self.root_ids),
                node_tags: IndexedBytes(&self.node_tags),
                node_field_offsets: IndexedBytes(&self.node_field_offsets),
                field_kinds: IndexedBytes(&self.field_kinds),
                field_values: IndexedBytes(&self.field_values),
                field_lengths: IndexedBytes(&self.field_lengths),
                item_kinds: IndexedBytes(&self.item_kinds),
                item_values: IndexedBytes(&self.item_values),
                item_lengths: IndexedBytes(&self.item_lengths),
                scalar_bytes: IndexedBytes(&self.scalar_bytes),
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

    fn empty() -> OwnedColumns {
        OwnedColumns {
            root_kinds: Vec::new(),
            root_ids: Vec::new(),
            node_tags: Vec::new(),
            node_field_offsets: le64(&[0]),
            field_kinds: Vec::new(),
            field_values: Vec::new(),
            field_lengths: Vec::new(),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: Vec::new(),
        }
    }

    fn declaration() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![ROOT_AXIOM],
            root_ids: le32(&[3]),
            node_tags: le16(&[1, 2, 60]),
            node_field_offsets: le64(&[0, 1, 3, 5]),
            field_kinds: vec![
                COMPONENT_TEXT,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 1, 2, 0]),
            field_lengths: le64(&[5, 5, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: b"urn:Cclass".to_vec(),
        }
    }

    fn annotation() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![ROOT_ONTOLOGY_ANNOTATION],
            root_ids: le32(&[3]),
            node_tags: le16(&[1, 2, 5]),
            node_field_offsets: le64(&[0, 1, 3, 6]),
            field_kinds: vec![
                COMPONENT_TEXT,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 1, 2, 1, 0]),
            field_lengths: le64(&[5, 19, 0, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: b"urn:aannotation_property".to_vec(),
        }
    }

    fn property_chain() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![ROOT_AXIOM],
            root_ids: le32(&[4]),
            node_tags: le16(&[1, 2, 11, 70]),
            node_field_offsets: le64(&[0, 1, 3, 4, 7]),
            field_kinds: vec![
                COMPONENT_TEXT,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_SEQUENCE,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 1, 0, 3, 2, 1]),
            field_lengths: le64(&[5, 15, 0, 1, 0, 0, 0]),
            item_kinds: vec![COMPONENT_NODE],
            item_values: le64(&[2]),
            item_lengths: le64(&[0]),
            scalar_bytes: b"urn:pobject_property".to_vec(),
        }
    }

    fn equivalent_classes() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![ROOT_AXIOM],
            root_ids: le32(&[5]),
            node_tags: le16(&[1, 1, 2, 2, 62]),
            node_field_offsets: le64(&[0, 1, 2, 4, 6, 8]),
            field_kinds: vec![
                COMPONENT_TEXT,
                COMPONENT_TEXT,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_SET,
                COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 10, 1, 15, 2, 0, 2]),
            field_lengths: le64(&[5, 5, 5, 0, 5, 0, 2, 0]),
            item_kinds: vec![COMPONENT_NODE, COMPONENT_NODE],
            item_values: le64(&[3, 4]),
            item_lengths: le64(&[0, 0]),
            scalar_bytes: b"urn:Aurn:Bclassclass".to_vec(),
        }
    }

    fn data_range_cycle() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![ROOT_AXIOM],
            root_ids: le32(&[4]),
            node_tags: le16(&[1, 2, 23, 94]),
            node_field_offsets: le64(&[0, 1, 3, 4, 7]),
            field_kinds: vec![
                COMPONENT_TEXT,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 1, 3, 2, 3, 0]),
            field_lengths: le64(&[5, 13, 0, 0, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: b"urn:pdata_property".to_vec(),
        }
    }

    fn two_declarations() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![ROOT_AXIOM, ROOT_AXIOM],
            root_ids: le32(&[5, 6]),
            node_tags: le16(&[1, 1, 2, 2, 60, 60]),
            node_field_offsets: le64(&[0, 1, 2, 4, 6, 8, 10]),
            field_kinds: vec![
                COMPONENT_TEXT,
                COMPONENT_TEXT,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_SET,
                COMPONENT_NODE,
                COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 10, 1, 15, 2, 3, 0, 4, 0]),
            field_lengths: le64(&[5, 5, 5, 0, 5, 0, 0, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: b"urn:Aurn:Bclassclass".to_vec(),
        }
    }

    fn equivalent_class_pair() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![ROOT_AXIOM, ROOT_AXIOM],
            root_ids: le32(&[7, 8]),
            node_tags: le16(&[1, 1, 1, 2, 2, 2, 62, 62]),
            node_field_offsets: le64(&[0, 1, 2, 3, 5, 7, 9, 11, 13]),
            field_kinds: vec![
                COMPONENT_TEXT,
                COMPONENT_TEXT,
                COMPONENT_TEXT,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_SET,
                COMPONENT_SET,
                COMPONENT_SET,
                COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 10, 15, 1, 20, 2, 25, 3, 0, 2, 2, 4]),
            field_lengths: le64(&[5, 5, 5, 5, 0, 5, 0, 5, 0, 2, 0, 2, 0]),
            item_kinds: vec![
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_NODE,
            ],
            item_values: le64(&[4, 5, 4, 6]),
            item_lengths: le64(&[0, 0, 0, 0]),
            scalar_bytes: b"urn:Aurn:Burn:Cclassclassclass".to_vec(),
        }
    }

    fn cardinality_pair() -> OwnedColumns {
        let mut scalar_bytes = b"urn:Curn:pclassobject_property".to_vec();
        scalar_bytes.extend([0x00, 0x01, 0xff]);
        OwnedColumns {
            root_kinds: vec![ROOT_AXIOM],
            root_ids: le32(&[7]),
            node_tags: le16(&[1, 1, 2, 2, 38, 38, 62]),
            node_field_offsets: le64(&[0, 1, 2, 4, 6, 9, 12, 14]),
            field_kinds: vec![
                COMPONENT_TEXT,
                COMPONENT_TEXT,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_ENUM,
                COMPONENT_NODE,
                COMPONENT_INTEGER,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_INTEGER,
                COMPONENT_NODE,
                COMPONENT_NODE,
                COMPONENT_SET,
                COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 10, 1, 15, 2, 30, 4, 3, 32, 4, 3, 0, 2]),
            field_lengths: le64(&[5, 5, 5, 0, 15, 0, 2, 0, 0, 1, 0, 0, 2, 0]),
            item_kinds: vec![COMPONENT_NODE, COMPONENT_NODE],
            item_values: le64(&[5, 6]),
            item_lengths: le64(&[0, 0]),
            scalar_bytes,
        }
    }

    fn assert_protocol_contains(columns: &OwnedColumns, expected: &str) {
        assert!(matches!(
            validate_columns(columns.borrowed(), EncodedLimits::default()),
            Err(error) if error.code == "NATIVE_ENCODED_VIEW_INVALID"
                && error.message.contains(expected)
        ));
    }

    fn assert_role_error(columns: &OwnedColumns) {
        assert_protocol_contains(columns, "schema role");
    }

    #[test]
    fn constructor_role_ledger_covers_every_frozen_model_tag() {
        const TAGS: [u16; 76] = [
            1, 2, 3, 4, 5, 10, 11, 20, 21, 22, 23, 24, 25, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
            40, 41, 42, 43, 44, 45, 46, 60, 61, 62, 63, 64, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
            80, 81, 82, 90, 91, 92, 93, 94, 95, 100, 101, 110, 111, 112, 113, 114, 115, 116, 120,
            121, 122, 123, 140, 141, 142, 143, 144, 145, 146, 147, 148,
        ];
        assert_eq!(
            CONSTRUCTOR_ROLE_LEDGER
                .iter()
                .map(|(tag, _roles)| *tag)
                .collect::<Vec<_>>(),
            TAGS
        );
        assert_eq!(
            CONSTRUCTOR_ROLE_LEDGER
                .iter()
                .map(|(_tag, roles)| roles.len())
                .sum::<usize>(),
            176
        );
        for (tag, roles) in CONSTRUCTOR_ROLE_LEDGER {
            assert_eq!(constructor_roles(*tag), Some(*roles));
        }
        assert!(constructor_roles(0).is_none());
        assert!(constructor_roles(149).is_none());
        assert_eq!(
            DESCRIPTOR_SHA256_V1,
            [
                0x9a, 0xd2, 0x9d, 0xb6, 0xa7, 0xe6, 0x16, 0xf6, 0x5c, 0xea, 0x29, 0x57, 0xbc, 0x5b,
                0xa8, 0xd1, 0xf9, 0xb9, 0x9e, 0xf0, 0xeb, 0x1f, 0xe1, 0x43, 0x2c, 0x09, 0xbe, 0x25,
                0x78, 0x62, 0x67, 0xb5,
            ]
        );
    }

    #[test]
    fn borrowed_and_indexed_columns_validate_without_materialization() {
        let empty_result = validate_columns(empty().borrowed(), EncodedLimits::default());
        assert_eq!(empty_result.map(|validated| validated.node_count), Ok(0));

        let owned = declaration();
        let limits = EncodedLimits {
            max_roots: 1,
            max_nodes: 3,
            max_fields: 5,
            max_items: 0,
            max_scalar_bytes: 10,
            max_work: 64,
        };
        let borrowed = validate_columns(owned.borrowed(), limits);
        let indexed = validate_columns(owned.indexed(), limits);
        assert_eq!(borrowed, indexed);
        assert_eq!(
            borrowed,
            Ok(ValidatedEncodedColumns {
                root_count: 1,
                node_count: 3,
                field_count: 5,
                item_count: 0,
                scalar_bytes: 10,
                work: 38,
            })
        );
    }

    #[test]
    fn exact_width_shape_tag_arity_root_and_limits_fail_closed() {
        let mut malformed = declaration();
        malformed.root_ids.pop();
        assert_protocol_contains(&malformed, "root_ids is not aligned");

        let mut malformed = declaration();
        malformed.root_kinds.push(ROOT_AXIOM);
        assert_protocol_contains(&malformed, "root kind and root ID counts differ");

        let mut malformed = declaration();
        malformed.node_field_offsets = le64(&[0, 1, 3]);
        assert_protocol_contains(&malformed, "node_count + 1");

        let mut malformed = declaration();
        malformed.field_values.pop();
        assert_protocol_contains(&malformed, "field_values is not aligned");

        let mut malformed = property_chain();
        malformed.item_lengths.pop();
        assert_protocol_contains(&malformed, "item_lengths is not aligned");

        let mut malformed = declaration();
        malformed.node_tags = le16(&[1, 2, 149]);
        assert_protocol_contains(&malformed, "unsupported encoded node tag 149");

        let mut malformed = declaration();
        malformed.node_field_offsets = le64(&[0, 1, 3, 4]);
        assert_protocol_contains(&malformed, "wrong field arity");

        let mut malformed = declaration();
        malformed.root_kinds[0] = ROOT_EXTENSION;
        assert_protocol_contains(&malformed, "root kind is inconsistent");

        let mut malformed = declaration();
        malformed.root_ids = le32(&[1]);
        assert_protocol_contains(&malformed, "root kind is inconsistent");

        let tight_nodes = EncodedLimits {
            max_nodes: 2,
            ..EncodedLimits::default()
        };
        assert!(matches!(
            validate_columns(declaration().borrowed(), tight_nodes),
            Err(error) if error.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
        ));
        let tight_work = EncodedLimits {
            max_work: 1,
            ..EncodedLimits::default()
        };
        assert!(matches!(
            validate_columns(declaration().borrowed(), tight_work),
            Err(error) if error.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
        ));
    }

    #[test]
    fn arity_preserving_role_confusions_fail_closed() {
        let mut malformed = declaration();
        malformed.field_kinds[0] = COMPONENT_BYTES;
        assert_role_error(&malformed);

        let mut malformed = declaration();
        malformed.field_kinds[1] = COMPONENT_TEXT;
        assert_role_error(&malformed);

        let mut malformed = declaration();
        malformed.field_kinds[4] = COMPONENT_SEQUENCE;
        assert_role_error(&malformed);

        let mut malformed = annotation();
        malformed.field_values = le64(&[0, 5, 1, 1, 2, 0]);
        assert_role_error(&malformed);

        let mut malformed = annotation();
        malformed.field_lengths = le64(&[5, 19, 0, 0, 0, 1]);
        malformed.item_kinds = vec![COMPONENT_NODE];
        malformed.item_values = le64(&[1]);
        malformed.item_lengths = le64(&[0]);
        assert_role_error(&malformed);

        let mut malformed = property_chain();
        malformed.field_kinds[3] = COMPONENT_SET;
        assert_role_error(&malformed);

        let mut malformed = property_chain();
        malformed.item_values = le64(&[1]);
        assert_role_error(&malformed);

        let mut malformed = declaration();
        malformed.scalar_bytes[5..10].copy_from_slice(b"other");
        assert_protocol_contains(&malformed, "model-schema-1");
    }

    #[test]
    fn arenas_require_exact_ordered_nonoverlapping_coverage() {
        assert!(
            validate_columns(equivalent_classes().borrowed(), EncodedLimits::default()).is_ok()
        );

        let mut malformed = equivalent_classes();
        malformed.node_field_offsets = le64(&[1, 1, 2, 4, 6, 8]);
        assert_protocol_contains(&malformed, "offsets must start at zero");

        let mut malformed = equivalent_classes();
        malformed.node_field_offsets = le64(&[0, 1, 2, 4, 6, 9]);
        assert_protocol_contains(&malformed, "offsets are not contiguous and bounded");

        let mut malformed = equivalent_classes();
        malformed.field_kinds.push(COMPONENT_NONE);
        malformed.field_values.extend(le64(&[0]));
        malformed.field_lengths.extend(le64(&[0]));
        assert_protocol_contains(&malformed, "offsets do not cover every field");

        let mut malformed = equivalent_classes();
        malformed.field_values = le64(&[0, 5, 10, 1, 15, 2, 1, 2]);
        assert_protocol_contains(&malformed, "exactly cover item rows");

        let mut malformed = equivalent_classes();
        malformed.field_values = le64(&[0, 5, 10, 1, 15, 2, 0, 1]);
        assert_protocol_contains(&malformed, "exactly cover item rows");

        let mut malformed = equivalent_classes();
        malformed.field_lengths = le64(&[5, 5, 5, 0, 5, 0, 3, 0]);
        assert_protocol_contains(&malformed, "collection field exceeds item rows");

        let mut malformed = equivalent_classes();
        malformed.item_kinds.push(COMPONENT_NODE);
        malformed.item_values.extend(le64(&[4]));
        malformed.item_lengths.extend(le64(&[0]));
        assert_protocol_contains(&malformed, "item rows are not exactly covered");

        let mut malformed = equivalent_classes();
        malformed.field_values = le64(&[1, 5, 10, 1, 15, 2, 0, 2]);
        assert_protocol_contains(&malformed, "exactly cover the scalar arena");

        let mut malformed = equivalent_classes();
        malformed.field_values = le64(&[0, 4, 10, 1, 15, 2, 0, 2]);
        assert_protocol_contains(&malformed, "exactly cover the scalar arena");

        let mut malformed = equivalent_classes();
        malformed.field_lengths = le64(&[21, 5, 5, 0, 5, 0, 2, 0]);
        assert_protocol_contains(&malformed, "scalar component is out of bounds");

        let mut malformed = equivalent_classes();
        malformed.scalar_bytes.push(b'x');
        assert_protocol_contains(&malformed, "scalar arena is not exactly covered");
    }

    #[test]
    fn references_sets_roots_and_reachability_are_integral() {
        let mut malformed = declaration();
        malformed.root_ids = le32(&[0]);
        assert_protocol_contains(&malformed, "one-based and nonzero");

        let mut malformed = declaration();
        malformed.root_ids = le32(&[4]);
        assert_protocol_contains(&malformed, "node ID is out of range");

        let mut malformed = declaration();
        malformed.field_values = le64(&[0, 5, 0, 2, 0]);
        assert_protocol_contains(&malformed, "one-based and nonzero");

        let mut malformed = declaration();
        malformed.field_values = le64(&[0, 5, 4, 2, 0]);
        assert_protocol_contains(&malformed, "node ID is out of range");

        let mut malformed = equivalent_classes();
        malformed.item_values = le64(&[0, 4]);
        assert_protocol_contains(&malformed, "one-based and nonzero");

        let mut malformed = equivalent_classes();
        malformed.item_values = le64(&[3, 6]);
        assert_protocol_contains(&malformed, "node ID is out of range");

        let mut malformed = equivalent_classes();
        malformed.item_values = le64(&[4, 3]);
        assert_protocol_contains(&malformed, "not strictly ascending and unique");

        let mut malformed = equivalent_classes();
        malformed.item_values = le64(&[3, 3]);
        assert_protocol_contains(&malformed, "not strictly ascending and unique");

        let mut sequence = property_chain();
        sequence.field_values = le64(&[0, 5, 1, 0, 3, 2, 2]);
        sequence.field_lengths = le64(&[5, 15, 0, 2, 0, 0, 0]);
        sequence.item_kinds = vec![COMPONENT_NODE, COMPONENT_NODE];
        sequence.item_values = le64(&[2, 2]);
        sequence.item_lengths = le64(&[0, 0]);
        assert!(validate_columns(sequence.borrowed(), EncodedLimits::default()).is_ok());

        assert_protocol_contains(&data_range_cycle(), "structural graph is cyclic");

        let mut unreachable = declaration();
        unreachable.node_tags = le16(&[1, 2, 60, 1]);
        unreachable.node_field_offsets = le64(&[0, 1, 3, 5, 6]);
        unreachable.field_kinds.push(COMPONENT_TEXT);
        unreachable.field_values.extend(le64(&[10]));
        unreachable.field_lengths.extend(le64(&[1]));
        unreachable.scalar_bytes.push(b'z');
        assert_protocol_contains(&unreachable, "contains unreachable nodes");

        let graph_limited = EncodedLimits {
            max_work: 20,
            ..EncodedLimits::default()
        };
        assert!(matches!(
            validate_columns(declaration().borrowed(), graph_limited),
            Err(error) if error.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
        ));
    }

    #[test]
    fn root_kind_tag_and_order_rules_cover_the_frozen_ledger() {
        const AXIOM_TAGS: [u16; 37] = [
            60, 61, 62, 63, 64, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 90, 91, 92, 93,
            94, 95, 100, 101, 110, 111, 112, 113, 114, 115, 116, 120, 121, 122, 123,
        ];
        for (tag, _roles) in CONSTRUCTOR_ROLE_LEDGER {
            assert_eq!(root_accepts(ROOT_ONTOLOGY_ANNOTATION, *tag), *tag == 5);
            assert_eq!(root_accepts(ROOT_AXIOM, *tag), AXIOM_TAGS.contains(tag));
            assert_eq!(root_accepts(ROOT_EXTENSION, *tag), *tag == 148);
            assert!(!root_accepts(0, *tag));
            assert!(!root_accepts(4, *tag));
        }
        for tag in [0, 6, 59, 65, 83, 96, 102, 117, 124, 139, 149] {
            assert!(!root_accepts(ROOT_ONTOLOGY_ANNOTATION, tag));
            assert!(!root_accepts(ROOT_AXIOM, tag));
            assert!(!root_accepts(ROOT_EXTENSION, tag));
        }

        assert!(validate_columns(annotation().borrowed(), EncodedLimits::default()).is_ok());

        let mut malformed = annotation();
        malformed.root_kinds[0] = ROOT_AXIOM;
        assert_protocol_contains(&malformed, "inconsistent with its constructor tag");

        let mut malformed = equivalent_classes();
        malformed.root_ids = le32(&[2]);
        assert_protocol_contains(&malformed, "inconsistent with its constructor tag");

        let mut malformed = equivalent_classes();
        malformed.root_kinds = vec![ROOT_AXIOM, ROOT_AXIOM];
        malformed.root_ids = le32(&[5, 5]);
        assert_protocol_contains(&malformed, "strictly ordered and unique");
    }

    #[test]
    fn dense_nodes_and_roots_follow_canonical_model_v1_bytes() {
        for columns in [
            equivalent_classes(),
            two_declarations(),
            equivalent_class_pair(),
            cardinality_pair(),
        ] {
            assert!(validate_columns(columns.borrowed(), EncodedLimits::default()).is_ok());
        }

        let mut malformed = equivalent_classes();
        malformed.scalar_bytes = b"urn:Burn:Aclassclass".to_vec();
        assert_protocol_contains(&malformed, "node IDs are not canonical and unique");

        let mut malformed = equivalent_classes();
        malformed.scalar_bytes = b"urn:Aurn:Aclassclass".to_vec();
        assert_protocol_contains(&malformed, "node IDs are not canonical and unique");

        let mut malformed = equivalent_classes();
        malformed.field_values = le64(&[0, 5, 10, 2, 15, 1, 0, 2]);
        assert_protocol_contains(&malformed, "node IDs are not canonical and unique");

        let mut malformed = equivalent_class_pair();
        malformed.item_values = le64(&[4, 6, 4, 5]);
        assert_protocol_contains(&malformed, "node IDs are not canonical and unique");

        let mut framed = equivalent_classes();
        framed.field_values = le64(&[0, 3, 7, 1, 12, 2, 0, 2]);
        framed.field_lengths = le64(&[3, 4, 5, 0, 5, 0, 2, 0]);
        framed.scalar_bytes = b"z:aaa:bclassclass".to_vec();
        assert!(validate_columns(framed.borrowed(), EncodedLimits::default()).is_ok());

        let mut malformed = equivalent_classes();
        malformed.field_values = le64(&[0, 4, 7, 1, 12, 2, 0, 2]);
        malformed.field_lengths = le64(&[4, 3, 5, 0, 5, 0, 2, 0]);
        malformed.scalar_bytes = b"aa:bz:aclassclass".to_vec();
        assert_protocol_contains(&malformed, "node IDs are not canonical and unique");

        let mut malformed = cardinality_pair();
        malformed.scalar_bytes.truncate(30);
        malformed.scalar_bytes.extend([0xff, 0x00, 0x01]);
        malformed.field_values = le64(&[0, 5, 10, 1, 15, 2, 30, 4, 3, 31, 4, 3, 0, 2]);
        malformed.field_lengths = le64(&[5, 5, 5, 0, 15, 0, 1, 0, 0, 2, 0, 0, 2, 0]);
        assert_protocol_contains(&malformed, "node IDs are not canonical and unique");

        let mut malformed = two_declarations();
        malformed.root_ids = le32(&[6, 5]);
        assert_protocol_contains(&malformed, "roots are not strictly ordered and unique");

        let owned = equivalent_classes();
        let columns = owned.borrowed();
        let mut work = 0;
        let lengths = validate_graph_and_lengths(&columns, 1, 5, &mut work, u64::MAX);
        assert!(lengths.is_ok());
        let lengths = lengths.unwrap_or_default();
        let mut comparison_work = 0;
        assert!(matches!(
            compare_canonical_nodes(
                0,
                1,
                &columns,
                &lengths,
                &mut comparison_work,
                1,
            ),
            Err(error) if error.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
                && error.message.contains("work limit")
        ));
    }

    #[test]
    fn canonical_varints_and_integer_normalization_match_the_descriptor() {
        fn oracle_varint(mut value: u64) -> Vec<u8> {
            let mut output = Vec::new();
            loop {
                let chunk = u8::try_from(value & 0x7f).unwrap_or_default();
                value >>= 7;
                output.push(chunk | if value == 0 { 0 } else { 0x80 });
                if value == 0 {
                    return output;
                }
            }
        }

        let values = [
            0,
            1,
            0x7f,
            0x80,
            0xff,
            0x100,
            0x3fff,
            0x4000,
            u64::from(u32::MAX),
            u64::MAX,
        ];
        for left in values {
            for right in values {
                assert_eq!(
                    compare_u64_varints(left, right),
                    oracle_varint(left).cmp(&oracle_varint(right))
                );
            }
        }

        for (payload, expected) in [
            (&[0x00][..], &[0x00][..]),
            (&[0x7f][..], &[0x7f][..]),
            (&[0x80][..], &[0x80, 0x01][..]),
            (&[0xff][..], &[0xff, 0x01][..]),
            (&[0x00, 0x01][..], &[0x80, 0x02][..]),
            (&[0x00, 0x40][..], &[0x80, 0x80, 0x01][..]),
        ] {
            let width = canonical_integer_varint_width(payload, 0, payload.len());
            assert!(width.is_ok());
            let width = width.unwrap_or_default();
            let actual = (0..width)
                .map(|index| integer_varint_byte(payload, 0, payload.len(), index, width))
                .collect::<EncodedResult<Vec<_>>>();
            assert_eq!(actual.as_deref(), Ok(expected));
        }

        let mut malformed = cardinality_pair();
        malformed.scalar_bytes[31] = 0;
        assert_protocol_contains(&malformed, "integer component is not minimal");

        let mut malformed = cardinality_pair();
        malformed.field_lengths = le64(&[5, 5, 5, 0, 15, 0, 0, 0, 0, 1, 0, 0, 2, 0]);
        assert_protocol_contains(&malformed, "integer component is not minimal");

        let mut total = u64::MAX;
        assert!(matches!(
            add_canonical_length(&mut total, 1),
            Err(error) if error.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
        ));
    }

    #[test]
    fn leaf_scalars_and_node_identifiers_are_checked_before_handoff() {
        let mut malformed = declaration();
        malformed.scalar_bytes[0] = 0xff;
        assert_protocol_contains(&malformed, "valid UTF-8");

        for invalid in [
            &[0x80][..],
            &[0xc0, 0x80],
            &[0xe0, 0x80, 0x80],
            &[0xed, 0xa0, 0x80],
            &[0xf4, 0x90, 0x80, 0x80],
        ] {
            assert!(validate_utf8(invalid, 0, invalid.len()).is_err());
        }
        for valid in ["", "plain", "é", "€", "𐍈"] {
            assert!(validate_utf8(valid.as_bytes(), 0, valid.len()).is_ok());
        }

        let mut scalar_columns = empty();
        scalar_columns.scalar_bytes = vec![1, 0];
        let borrowed = scalar_columns.borrowed();
        let context = ValidationContext {
            columns: &borrowed,
            node_count: 0,
        };
        let mut scalar_cursor = 0;
        let mut work = 0;
        assert!(matches!(
            validate_leaf_component(
                Component {
                    kind: COMPONENT_INTEGER,
                    value: 0,
                    length: 2,
                },
                context,
                &mut scalar_cursor,
                &mut work,
                16,
            ),
            Err(error) if error.message.contains("minimal little-endian")
        ));

        let mut scalar_columns = empty();
        scalar_columns.scalar_bytes = vec![0x80];
        let borrowed = scalar_columns.borrowed();
        let context = ValidationContext {
            columns: &borrowed,
            node_count: 0,
        };
        let mut scalar_cursor = 0;
        let mut work = 0;
        assert!(matches!(
            validate_leaf_component(
                Component {
                    kind: COMPONENT_ENUM,
                    value: 0,
                    length: 1,
                },
                context,
                &mut scalar_cursor,
                &mut work,
                16,
            ),
            Err(error) if error.message.contains("nonempty ASCII")
        ));

        let mut malformed = declaration();
        malformed.field_values = le64(&[0, 5, 0, 2, 0]);
        assert_protocol_contains(&malformed, "one-based and nonzero");
        let mut malformed = declaration();
        malformed.root_ids = le32(&[4]);
        assert_protocol_contains(&malformed, "out of range");
    }
}
