//! Borrowed validation for pyowl-core encoded structural columns schema 1.
//!
//! This module is intentionally Python-free and does not advertise the encoded
//! compiler capability. It validates the frozen eleven-column shape and exact
//! constructor field roles before any future HermiT-specific compilation.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

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

    fn resource(message: impl Into<String>) -> Self {
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
                        validate_leaf_component(
                            item_component,
                            context,
                            &mut work,
                            limits.max_work,
                        )?;
                    }
                }
                _ => {
                    validate_field_role(location, role, component, context)?;
                    validate_leaf_component(component, context, &mut work, limits.max_work)?;
                }
            }
        }
    }

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
    }

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
                work: 20,
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
        let mut work = 0;
        assert!(matches!(
            validate_leaf_component(
                Component {
                    kind: COMPONENT_INTEGER,
                    value: 0,
                    length: 2,
                },
                context,
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
        let mut work = 0;
        assert!(matches!(
            validate_leaf_component(
                Component {
                    kind: COMPONENT_ENUM,
                    value: 0,
                    length: 1,
                },
                context,
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
