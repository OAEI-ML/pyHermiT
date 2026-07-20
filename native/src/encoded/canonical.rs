//! Bounded canonical source provenance for encoded compiler phases.
//!
//! The encoded structural model is already validated and canonically ordered.
//! This helper reproduces pyowl-core canonical bytes while applying the
//! inner-to-outer anonymous-scope replacement chain owned by a composite slice.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use sha2::{Digest, Sha256};

use super::model::{
    ComponentKind, ComponentRef, ComponentValue, NodeId, ScalarRef, ValidatedModel,
};
use super::{ByteSource, EncodedResult, EncodedValidationError};

const ANONYMOUS_INDIVIDUAL_TAG: u16 = 3;
const ANONYMOUS_SCOPE_BYTES: usize = 32;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AnonymousScopeReplacement {
    pub source: [u8; ANONYMOUS_SCOPE_BYTES],
    pub target: [u8; ANONYMOUS_SCOPE_BYTES],
}

pub type AnonymousScopeMap = Vec<AnonymousScopeReplacement>;

pub(crate) trait CanonicalBudget {
    fn canonical_max_depth(&self) -> usize;

    fn canonical_max_scope_maps(&self) -> usize;

    fn claim_canonical_work(&mut self, amount: usize) -> EncodedResult<()>;

    fn claim_canonical_owned(&mut self, amount: usize) -> EncodedResult<()>;
}

pub(crate) fn validate_scope_maps(
    scope_maps: &[AnonymousScopeMap],
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<()> {
    if scope_maps.len() > budget.canonical_max_scope_maps() {
        return Err(EncodedValidationError::resource(
            "anonymous-scope map count exceeds its limit",
        ));
    }
    budget.claim_canonical_work(scope_maps.len())?;
    for scope_map in scope_maps {
        budget.claim_canonical_work(scope_map.len())?;
        for (index, row) in scope_map.iter().enumerate() {
            if row.source == row.target || (index > 0 && scope_map[index - 1].source >= row.source)
            {
                return Err(EncodedValidationError::invariant(
                    "anonymous-scope replacements are not sorted unique or contain identity rows",
                ));
            }
        }
    }
    Ok(())
}

pub(crate) fn source_axiom_digest<B: ByteSource>(
    model: &ValidatedModel<B>,
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<[u8; 32]> {
    let encoded = canonical_node_bytes(model, root, scope_maps, 0, budget)?;
    budget.claim_canonical_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
}

/// Own the exact canonical key for one validated structural node.
///
/// Compiler symbol phases use this for non-entity domains whose scalar keys are
/// the public core node's canonical bytes. Anonymous scope replacement remains
/// explicit so a caller cannot accidentally assign a source-local key to a
/// composite-owned individual.
pub(crate) fn canonical_node_key<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<Vec<u8>> {
    canonical_node_bytes(model, node, scope_maps, 0, budget)
}

pub(crate) fn annotation_stripped_axiom_digest<B: ByteSource>(
    model: &ValidatedModel<B>,
    root: NodeId,
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<[u8; 32]> {
    let node = model.node(root)?;
    let annotation_index = node.fields().end.checked_sub(1).ok_or_else(|| {
        EncodedValidationError::invariant("encoded axiom root has no annotation field")
    })?;
    let annotation = required_component(
        model.field(annotation_index)?,
        "encoded axiom annotation field",
    )?;
    let ComponentValue::Collection(annotation) = model.resolve(annotation)? else {
        return Err(EncodedValidationError::invariant(
            "encoded axiom annotation field is not a collection",
        ));
    };
    if annotation.kind() != ComponentKind::Set {
        return Err(EncodedValidationError::invariant(
            "encoded axiom annotation field is not a canonical set",
        ));
    }
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(node.tag()), budget)?;
    for field_index in node.fields().start..annotation_index {
        budget.claim_canonical_work(1)?;
        let component = required_component(model.field(field_index)?, "normalized axiom field")?;
        append_canonical_component(
            &mut encoded,
            model,
            model.resolve(component)?,
            &[],
            1,
            false,
            budget,
        )?;
    }
    push_byte(&mut encoded, 6, budget)?;
    push_varint(&mut encoded, 0, budget)?;
    budget.claim_canonical_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
}

fn canonical_node_bytes<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    depth: usize,
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<Vec<u8>> {
    if depth > budget.canonical_max_depth() {
        return Err(EncodedValidationError::resource(
            "encoded provenance canonicalization exceeds its depth limit",
        ));
    }
    budget.claim_canonical_work(1)?;
    let node = model.node(identifier)?;
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(node.tag()), budget)?;
    let child_depth = depth.checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("encoded provenance canonical depth overflowed")
    })?;
    for (position, field_index) in node.fields().enumerate() {
        budget.claim_canonical_work(1)?;
        let component = required_component(model.field(field_index)?, "canonical node field")?;
        append_canonical_component(
            &mut encoded,
            model,
            model.resolve(component)?,
            scope_maps,
            child_depth,
            node.tag() == ANONYMOUS_INDIVIDUAL_TAG && position == 0,
            budget,
        )?;
    }
    Ok(encoded)
}

#[allow(clippy::too_many_arguments)]
fn append_canonical_component<B: ByteSource>(
    target: &mut Vec<u8>,
    model: &ValidatedModel<B>,
    component: ComponentValue<B>,
    scope_maps: &[AnonymousScopeMap],
    depth: usize,
    anonymous_scope: bool,
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<()> {
    match component {
        ComponentValue::None => push_byte(target, 0, budget),
        ComponentValue::Node(identifier) => {
            push_byte(target, 1, budget)?;
            let encoded = canonical_node_bytes(model, identifier, scope_maps, depth, budget)?;
            push_frame(target, &encoded, budget)
        }
        ComponentValue::Scalar(scalar) => {
            append_canonical_scalar(target, scalar, scope_maps, anonymous_scope, budget)
        }
        ComponentValue::Collection(collection) => {
            let marker = match collection.kind() {
                ComponentKind::Set => 6,
                ComponentKind::Sequence => 7,
                _ => {
                    return Err(EncodedValidationError::invariant(
                        "canonical collection has a scalar component kind",
                    ));
                }
            };
            push_byte(target, marker, budget)?;
            push_varint(
                target,
                u64::try_from(collection.len()).map_err(|_| {
                    EncodedValidationError::resource(
                        "encoded provenance collection arity exceeds u64",
                    )
                })?,
                budget,
            )?;
            for item_index in collection.items() {
                budget.claim_canonical_work(1)?;
                let item =
                    required_component(model.item(item_index)?, "canonical collection item")?;
                let item = model.resolve(item)?;
                if collection.kind() == ComponentKind::Set {
                    let ComponentValue::Node(identifier) = item else {
                        return Err(EncodedValidationError::invariant(
                            "canonical set item is not a node",
                        ));
                    };
                    let encoded =
                        canonical_node_bytes(model, identifier, scope_maps, depth, budget)?;
                    push_frame(target, &encoded, budget)?;
                } else {
                    append_canonical_component(
                        target, model, item, scope_maps, depth, false, budget,
                    )?;
                }
            }
            Ok(())
        }
    }
}

fn append_canonical_scalar<B: ByteSource>(
    target: &mut Vec<u8>,
    scalar: ScalarRef<B>,
    scope_maps: &[AnonymousScopeMap],
    anonymous_scope: bool,
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<()> {
    if anonymous_scope {
        if scalar.kind() != ComponentKind::Bytes || scalar.len() != ANONYMOUS_SCOPE_BYTES {
            return Err(EncodedValidationError::invariant(
                "anonymous-individual scope no longer has bytes32 shape",
            ));
        }
        let mut source = [0_u8; ANONYMOUS_SCOPE_BYTES];
        for (index, byte) in source.iter_mut().enumerate() {
            *byte = scalar.byte(index).ok_or_else(|| {
                EncodedValidationError::invariant("anonymous-individual scope disappeared")
            })?;
        }
        let mapped = remap_anonymous_scope(source, scope_maps, budget)?;
        push_byte(target, 3, budget)?;
        return push_frame(target, &mapped, budget);
    }
    let marker = match scalar.kind() {
        ComponentKind::Text => 2,
        ComponentKind::Bytes => 3,
        ComponentKind::Integer => 4,
        ComponentKind::Enum => 5,
        _ => {
            return Err(EncodedValidationError::invariant(
                "canonical scalar has a nonscalar component kind",
            ));
        }
    };
    push_byte(target, marker, budget)?;
    if scalar.kind() == ComponentKind::Integer {
        return push_integer_varint(target, scalar, budget);
    }
    push_varint(
        target,
        u64::try_from(scalar.len()).map_err(|_| {
            EncodedValidationError::resource("encoded provenance scalar length exceeds u64")
        })?,
        budget,
    )?;
    for index in 0..scalar.len() {
        push_byte(
            target,
            scalar.byte(index).ok_or_else(|| {
                EncodedValidationError::invariant("canonical scalar byte disappeared")
            })?,
            budget,
        )?;
    }
    Ok(())
}

fn push_integer_varint<B: ByteSource>(
    target: &mut Vec<u8>,
    scalar: ScalarRef<B>,
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<()> {
    let last = scalar.len().checked_sub(1).ok_or_else(|| {
        EncodedValidationError::invariant("canonical integer has an empty payload")
    })?;
    let high = scalar.byte(last).ok_or_else(|| {
        EncodedValidationError::invariant("canonical integer high byte disappeared")
    })?;
    let lower_bits = last.checked_mul(8).ok_or_else(|| {
        EncodedValidationError::resource("canonical integer bit length overflowed")
    })?;
    let high_bits = usize::try_from(u8::BITS - high.leading_zeros()).map_err(|_| {
        EncodedValidationError::resource("canonical integer bit length exceeds usize")
    })?;
    let width = lower_bits
        .checked_add(high_bits)
        .ok_or_else(|| EncodedValidationError::resource("canonical integer bit length overflowed"))?
        .div_ceil(7)
        .max(1);
    budget.claim_canonical_work(width)?;
    for index in 0..width {
        let bit_offset = index.checked_mul(7).ok_or_else(|| {
            EncodedValidationError::resource("canonical integer bit offset overflowed")
        })?;
        let source_index = bit_offset / 8;
        let shift = u32::try_from(bit_offset % 8).map_err(|_| {
            EncodedValidationError::resource("canonical integer bit shift exceeds u32")
        })?;
        let mut window = u16::from(scalar.byte(source_index).ok_or_else(|| {
            EncodedValidationError::invariant("canonical integer byte disappeared")
        })?) >> shift;
        if shift != 0 && source_index + 1 < scalar.len() {
            window |= u16::from(scalar.byte(source_index + 1).ok_or_else(|| {
                EncodedValidationError::invariant("canonical integer byte disappeared")
            })?) << (8 - shift);
        }
        let mut output = u8::try_from(window & 0x7f)
            .map_err(|_| EncodedValidationError::invariant("canonical integer chunk exceeds u8"))?;
        if index + 1 < width {
            output |= 0x80;
        }
        push_byte(target, output, budget)?;
    }
    Ok(())
}

pub(crate) fn remap_anonymous_scope(
    mut scope: [u8; ANONYMOUS_SCOPE_BYTES],
    scope_maps: &[AnonymousScopeMap],
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<[u8; ANONYMOUS_SCOPE_BYTES]> {
    for scope_map in scope_maps {
        budget.claim_canonical_work(binary_search_work(scope_map.len()))?;
        if let Ok(index) = scope_map.binary_search_by_key(&scope, |row| row.source) {
            scope = scope_map[index].target;
        }
    }
    Ok(scope)
}

fn push_frame(
    target: &mut Vec<u8>,
    value: &[u8],
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<()> {
    let length = u64::try_from(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical frame length exceeds u64"))?;
    push_varint(target, length, budget)?;
    budget.claim_canonical_owned(value.len())?;
    target
        .try_reserve(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical frame allocation failed"))?;
    target.extend_from_slice(value);
    Ok(())
}

fn push_varint(
    target: &mut Vec<u8>,
    mut value: u64,
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<()> {
    loop {
        let mut byte = u8::try_from(value & 0x7f)
            .map_err(|_| EncodedValidationError::invariant("canonical varint chunk exceeds u8"))?;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        push_byte(target, byte, budget)?;
        if value == 0 {
            return Ok(());
        }
    }
}

fn push_byte(
    target: &mut Vec<u8>,
    value: u8,
    budget: &mut impl CanonicalBudget,
) -> EncodedResult<()> {
    budget.claim_canonical_owned(1)?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("canonical byte allocation failed"))?;
    target.push(value);
    Ok(())
}

fn required_component(
    component: Option<ComponentRef>,
    name: &'static str,
) -> EncodedResult<ComponentRef> {
    component.ok_or_else(|| {
        EncodedValidationError::invariant(format!("validated {name} component disappeared"))
    })
}

fn binary_search_work(length: usize) -> usize {
    if length <= 1 {
        1
    } else {
        usize::try_from(usize::BITS - (length - 1).leading_zeros()).unwrap_or(usize::MAX)
    }
}
