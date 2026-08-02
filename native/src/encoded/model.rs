//! Typed, zero-copy access to columns that have passed schema-2 validation.
//!
//! The accessor deliberately retains the caller's [`ByteSource`] rather than
//! materializing Rust collections. It is private compiler substrate: creating
//! one proves the complete encoded-column contract once, after which compiler
//! phases can traverse typed roots and components without decoding Python
//! objects or repeating structural validation.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::ops::Range;

use super::{
    byte_at, node_index, u16_at, u32_at, usize_at, validate_columns, ByteSource, EncodedColumns,
    EncodedLimits, EncodedResult, EncodedValidationError, ValidatedEncodedColumns, COMPONENT_BYTES,
    COMPONENT_ENUM, COMPONENT_INTEGER, COMPONENT_NODE, COMPONENT_NONE, COMPONENT_SEQUENCE,
    COMPONENT_SET, COMPONENT_TEXT, ROOT_AXIOM, ROOT_EXTENSION, ROOT_ONTOLOGY_ANNOTATION,
};

/// The semantic category assigned to a schema-2 root row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RootKind {
    OntologyAnnotation,
    Axiom,
    Extension,
}

impl RootKind {
    fn from_encoded(value: u8) -> EncodedResult<Self> {
        match value {
            ROOT_ONTOLOGY_ANNOTATION => Ok(Self::OntologyAnnotation),
            ROOT_AXIOM => Ok(Self::Axiom),
            ROOT_EXTENSION => Ok(Self::Extension),
            _ => Err(EncodedValidationError::invariant(
                "validated encoded root kind is no longer recognized",
            )),
        }
    }
}

/// The representation category assigned to a schema-2 field or item row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ComponentKind {
    None,
    Node,
    Text,
    Bytes,
    Integer,
    Enum,
    Set,
    Sequence,
}

impl ComponentKind {
    fn from_encoded(value: u8) -> EncodedResult<Self> {
        match value {
            COMPONENT_NONE => Ok(Self::None),
            COMPONENT_NODE => Ok(Self::Node),
            COMPONENT_TEXT => Ok(Self::Text),
            COMPONENT_BYTES => Ok(Self::Bytes),
            COMPONENT_INTEGER => Ok(Self::Integer),
            COMPONENT_ENUM => Ok(Self::Enum),
            COMPONENT_SET => Ok(Self::Set),
            COMPONENT_SEQUENCE => Ok(Self::Sequence),
            _ => Err(EncodedValidationError::invariant(
                "validated encoded component kind is no longer recognized",
            )),
        }
    }
}

/// A one-based dense node identifier from encoded structural schema 2.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeId(u32);

impl NodeId {
    /// Construct a syntactically valid one-based identifier.
    ///
    /// Model bounds are checked when the identifier is used with
    /// [`ValidatedModel::node`].
    #[must_use]
    pub const fn new(value: u32) -> Option<Self> {
        if value == 0 {
            None
        } else {
            Some(Self(value))
        }
    }

    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }

    fn from_index(index: usize) -> EncodedResult<Self> {
        let one_based = index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::invariant("validated encoded node index overflowed")
        })?;
        let value = u32::try_from(one_based).map_err(|_| {
            EncodedValidationError::invariant("validated encoded node ID exceeds u32")
        })?;
        Ok(Self(value))
    }

    fn from_component(value: usize, node_count: usize) -> EncodedResult<Self> {
        let value = u32::try_from(value).map_err(|_| {
            EncodedValidationError::invariant("validated component node ID exceeds u32")
        })?;
        node_index(value, node_count)?;
        Self::new(value).ok_or_else(|| {
            EncodedValidationError::invariant("validated component contains node ID zero")
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RootRef {
    kind: RootKind,
    node: NodeId,
}

impl RootRef {
    #[must_use]
    pub const fn kind(self) -> RootKind {
        self.kind
    }

    #[must_use]
    pub const fn node(self) -> NodeId {
        self.node
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NodeRef {
    id: NodeId,
    tag: u16,
    field_start: usize,
    field_end: usize,
}

impl NodeRef {
    #[must_use]
    pub const fn id(self) -> NodeId {
        self.id
    }

    #[must_use]
    pub const fn tag(self) -> u16 {
        self.tag
    }

    #[must_use]
    pub const fn field_count(self) -> usize {
        self.field_end - self.field_start
    }

    #[must_use]
    pub const fn fields(self) -> Range<usize> {
        self.field_start..self.field_end
    }
}

/// A validated field or item row before its value is resolved.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ComponentRef {
    kind: ComponentKind,
    value: usize,
    length: usize,
}

impl ComponentRef {
    #[must_use]
    pub const fn kind(self) -> ComponentKind {
        self.kind
    }
}

/// A borrowed scalar range in the encoded scalar arena.
#[derive(Clone, Copy)]
pub struct ScalarRef<B: ByteSource> {
    kind: ComponentKind,
    source: B,
    start: usize,
    length: usize,
}

impl<B: ByteSource> ScalarRef<B> {
    #[must_use]
    pub const fn kind(self) -> ComponentKind {
        self.kind
    }

    #[must_use]
    pub const fn len(self) -> usize {
        self.length
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.length == 0
    }

    /// Read one byte relative to this scalar without materializing the range.
    #[must_use]
    pub fn byte(self, offset: usize) -> Option<u8> {
        if offset >= self.length {
            return None;
        }
        self.start
            .checked_add(offset)
            .and_then(|index| self.source.byte(index))
    }

    #[must_use]
    pub fn bytes_equal(self, expected: &[u8]) -> bool {
        expected.len() == self.length
            && expected
                .iter()
                .copied()
                .enumerate()
                .all(|(index, byte)| self.byte(index) == Some(byte))
    }
}

/// A validated range in the shared item columns.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CollectionRef {
    kind: ComponentKind,
    start: usize,
    length: usize,
}

impl CollectionRef {
    #[must_use]
    pub const fn kind(self) -> ComponentKind {
        self.kind
    }

    #[must_use]
    pub const fn len(self) -> usize {
        self.length
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.length == 0
    }

    #[must_use]
    pub const fn items(self) -> Range<usize> {
        self.start..self.start + self.length
    }
}

/// The typed value represented by a validated component row.
#[derive(Clone, Copy)]
pub enum ComponentValue<B: ByteSource> {
    None,
    Node(NodeId),
    Scalar(ScalarRef<B>),
    Collection(CollectionRef),
}

/// An immutable encoded model whose complete column contract has been proven.
#[derive(Clone, Copy)]
pub struct ValidatedModel<B: ByteSource> {
    columns: EncodedColumns<B>,
    summary: ValidatedEncodedColumns,
}

impl<B: ByteSource> ValidatedModel<B> {
    pub fn new(columns: EncodedColumns<B>, limits: EncodedLimits) -> EncodedResult<Self> {
        let summary = validate_columns(columns, limits)?;
        Ok(Self { columns, summary })
    }

    #[must_use]
    pub const fn summary(&self) -> ValidatedEncodedColumns {
        self.summary
    }

    pub fn root(&self, index: usize) -> EncodedResult<Option<RootRef>> {
        if index >= self.summary.root_count {
            return Ok(None);
        }
        let kind = RootKind::from_encoded(byte_at(self.columns.root_kinds, index, "root kind")?)?;
        let raw_node = u32_at(self.columns.root_ids, index, "root ID")?;
        node_index(raw_node, self.summary.node_count)?;
        let node = NodeId::new(raw_node).ok_or_else(|| {
            EncodedValidationError::invariant("validated root contains node ID zero")
        })?;
        Ok(Some(RootRef { kind, node }))
    }

    pub fn node_at(&self, index: usize) -> EncodedResult<Option<NodeRef>> {
        if index >= self.summary.node_count {
            return Ok(None);
        }
        let id = NodeId::from_index(index)?;
        self.node_by_index(id, index).map(Some)
    }

    pub fn node(&self, id: NodeId) -> EncodedResult<NodeRef> {
        let index = node_index(id.get(), self.summary.node_count)?;
        self.node_by_index(id, index)
    }

    pub fn field(&self, index: usize) -> EncodedResult<Option<ComponentRef>> {
        if index >= self.summary.field_count {
            return Ok(None);
        }
        Self::component(
            self.columns.field_kinds,
            self.columns.field_values,
            self.columns.field_lengths,
            index,
            "field kind",
            "field value",
            "field length",
        )
        .map(Some)
    }

    pub fn item(&self, index: usize) -> EncodedResult<Option<ComponentRef>> {
        if index >= self.summary.item_count {
            return Ok(None);
        }
        Self::component(
            self.columns.item_kinds,
            self.columns.item_values,
            self.columns.item_lengths,
            index,
            "item kind",
            "item value",
            "item length",
        )
        .map(Some)
    }

    pub fn resolve(&self, component: ComponentRef) -> EncodedResult<ComponentValue<B>> {
        match component.kind {
            ComponentKind::None => {
                if component.value != 0 || component.length != 0 {
                    return Err(EncodedValidationError::invariant(
                        "validated none component has a payload",
                    ));
                }
                Ok(ComponentValue::None)
            }
            ComponentKind::Node => NodeId::from_component(component.value, self.summary.node_count)
                .map(ComponentValue::Node),
            kind @ (ComponentKind::Text
            | ComponentKind::Bytes
            | ComponentKind::Integer
            | ComponentKind::Enum) => {
                let end = component
                    .value
                    .checked_add(component.length)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant("validated scalar range overflowed")
                    })?;
                if end > self.summary.scalar_bytes {
                    return Err(EncodedValidationError::invariant(
                        "validated scalar range exceeds the scalar arena",
                    ));
                }
                Ok(ComponentValue::Scalar(ScalarRef {
                    kind,
                    source: self.columns.scalar_bytes,
                    start: component.value,
                    length: component.length,
                }))
            }
            kind @ (ComponentKind::Set | ComponentKind::Sequence) => {
                let end = component
                    .value
                    .checked_add(component.length)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant("validated collection range overflowed")
                    })?;
                if end > self.summary.item_count {
                    return Err(EncodedValidationError::invariant(
                        "validated collection range exceeds the item columns",
                    ));
                }
                Ok(ComponentValue::Collection(CollectionRef {
                    kind,
                    start: component.value,
                    length: component.length,
                }))
            }
        }
    }

    fn node_by_index(&self, id: NodeId, index: usize) -> EncodedResult<NodeRef> {
        let tag = u16_at(self.columns.node_tags, index, "node tag")?;
        let field_start = usize_at(self.columns.node_field_offsets, index, "node field offset")?;
        let following = index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::invariant("validated node offset index overflowed")
        })?;
        let field_end = usize_at(
            self.columns.node_field_offsets,
            following,
            "node field offset",
        )?;
        Ok(NodeRef {
            id,
            tag,
            field_start,
            field_end,
        })
    }

    fn component(
        kinds: B,
        values: B,
        lengths: B,
        index: usize,
        kind_name: &str,
        value_name: &str,
        length_name: &str,
    ) -> EncodedResult<ComponentRef> {
        Ok(ComponentRef {
            kind: ComponentKind::from_encoded(byte_at(kinds, index, kind_name)?)?,
            value: usize_at(values, index, value_name)?,
            length: usize_at(lengths, index, length_name)?,
        })
    }
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

    fn required<T>(value: Option<T>, message: &'static str) -> EncodedResult<T> {
        value.ok_or_else(|| EncodedValidationError::invariant(message))
    }

    #[test]
    fn traverses_typed_roots_nodes_scalars_and_collections() -> EncodedResult<()> {
        let owned = equivalent_classes();
        let model = ValidatedModel::new(owned.indexed(), EncodedLimits::default())?;

        assert_eq!(model.summary().root_count, 1);
        assert_eq!(model.summary().node_count, 5);
        assert_eq!(model.summary().field_count, 8);
        assert_eq!(model.summary().item_count, 2);

        let root = required(model.root(0)?, "expected root")?;
        assert_eq!(root.kind(), RootKind::Axiom);
        assert_eq!(root.node().get(), 5);
        assert!(model.root(1)?.is_none());

        let root_node = model.node(root.node())?;
        assert_eq!(root_node.tag(), 62);
        assert_eq!(root_node.field_count(), 2);
        assert_eq!(root_node.fields(), 6..8);

        let iri_node = required(model.node_at(0)?, "expected IRI node")?;
        assert_eq!(iri_node.id().get(), 1);
        assert_eq!(iri_node.tag(), 1);
        let iri_field = required(model.field(0)?, "expected IRI field")?;
        assert_eq!(iri_field.kind(), ComponentKind::Text);
        let ComponentValue::Scalar(iri) = model.resolve(iri_field)? else {
            return Err(EncodedValidationError::invariant(
                "IRI field did not resolve to a scalar",
            ));
        };
        assert_eq!(iri.kind(), ComponentKind::Text);
        assert_eq!(iri.len(), 5);
        assert!(!iri.is_empty());
        assert!(iri.bytes_equal(b"urn:A"));
        assert_eq!(iri.byte(5), None);

        let classes_field = required(model.field(6)?, "expected class set field")?;
        let ComponentValue::Collection(classes) = model.resolve(classes_field)? else {
            return Err(EncodedValidationError::invariant(
                "class set field did not resolve to a collection",
            ));
        };
        assert_eq!(classes.kind(), ComponentKind::Set);
        assert_eq!(classes.len(), 2);
        assert!(!classes.is_empty());
        assert_eq!(classes.items(), 0..2);

        let first_item = required(model.item(0)?, "expected first class item")?;
        let second_item = required(model.item(1)?, "expected second class item")?;
        assert!(model.item(2)?.is_none());
        let ComponentValue::Node(first_class) = model.resolve(first_item)? else {
            return Err(EncodedValidationError::invariant(
                "first class item did not resolve to a node",
            ));
        };
        let ComponentValue::Node(second_class) = model.resolve(second_item)? else {
            return Err(EncodedValidationError::invariant(
                "second class item did not resolve to a node",
            ));
        };
        assert_eq!((first_class.get(), second_class.get()), (3, 4));
        Ok(())
    }

    #[test]
    fn accessor_bounds_fail_closed_after_validation() -> EncodedResult<()> {
        let owned = equivalent_classes();
        let model = ValidatedModel::new(owned.indexed(), EncodedLimits::default())?;

        assert!(NodeId::new(0).is_none());
        assert!(model.node_at(5)?.is_none());
        assert!(model.field(8)?.is_none());
        assert!(model.item(2)?.is_none());
        let outside = required(NodeId::new(6), "expected nonzero node ID")?;
        let error = model.node(outside).err();
        assert!(error.is_some_and(|value| {
            value.code == "NATIVE_ENCODED_VIEW_INVALID" && value.message.contains("out of range")
        }));
        Ok(())
    }
}
