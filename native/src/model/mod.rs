//! Primitive language-neutral values shared by the wire reader and state kernel.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::fmt;

use serde::{Deserialize, Serialize};

use crate::error::{NativeError, NativeResult};

/// Stable compiled-IR schema understood by this crate.
pub const IR_SCHEMA_VERSION: u16 = 1;
/// Stable private extension ABI version.
pub const ABI_VERSION: u32 = 1;
/// Exact `pyowl-core` API version compiled into the native handshake.
pub const CORE_API_VERSION: (u16, u16) = (0, 2);
/// Exact `pyowl-core` model schema accepted by this native crate.
pub const CORE_MODEL_SCHEMA_VERSION: u32 = 2;
/// Exact `pyowl-core` flat-wire version accepted by this native crate.
pub const CORE_WIRE_FORMAT_VERSION: (u16, u16) = (1, 2);
/// Exact `pyowl-core` adapter protocol accepted by this native crate.
pub const CORE_ADAPTER_PROTOCOL_VERSION: u32 = 1;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct NodeHandle {
    pub slot: u32,
    pub generation: u32,
}

impl NodeHandle {
    #[must_use]
    pub const fn new(slot: u32, generation: u32) -> Self {
        Self { slot, generation }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum NodeKind {
    Root,
    Tree,
    Ni,
    Concrete,
}

impl NodeKind {
    #[must_use]
    pub const fn sort(self) -> NodeSort {
        match self {
            Self::Concrete => NodeSort::Data,
            Self::Root | Self::Tree | Self::Ni => NodeSort::Object,
        }
    }
}

impl fmt::Display for NodeKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Root => "root",
            Self::Tree => "tree",
            Self::Ni => "ni",
            Self::Concrete => "concrete",
        })
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum NodeSort {
    Object,
    Data,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum NodeLifecycle {
    Active,
    Merged,
    Pruned,
    Retired,
}

/// Immutable canonical branching-level support.
#[derive(Clone, Debug, Default, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct DependencySet(Vec<u32>);

impl DependencySet {
    pub fn new(levels: Vec<u32>) -> NativeResult<Self> {
        if levels.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(NativeError::wire(
                "dependency levels must be ascending and unique",
            ));
        }
        Ok(Self(levels))
    }

    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn as_slice(&self) -> &[u32] {
        &self.0
    }

    #[must_use]
    pub fn maximum(&self) -> Option<u32> {
        self.0.last().copied()
    }

    #[must_use]
    pub fn add(&self, level: u32) -> Self {
        let mut levels = self.0.clone();
        match levels.binary_search(&level) {
            Ok(_) => Self(levels),
            Err(position) => {
                levels.insert(position, level);
                Self(levels)
            }
        }
    }

    #[must_use]
    pub fn without(&self, level: u32) -> Self {
        let mut levels = self.0.clone();
        if let Ok(position) = levels.binary_search(&level) {
            levels.remove(position);
        }
        Self(levels)
    }

    #[must_use]
    pub fn is_subset_of(&self, other: &Self) -> bool {
        self.0
            .iter()
            .all(|level| other.0.binary_search(level).is_ok())
    }

    #[must_use]
    pub fn union(values: &[&Self]) -> Self {
        let mut levels = Vec::new();
        for value in values {
            levels.extend_from_slice(value.as_slice());
        }
        levels.sort_unstable();
        levels.dedup();
        Self(levels)
    }
}

/// Metadata retained at native-session creation without retaining Python memory.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreMetadata {
    pub ontology_fingerprint: [u8; 32],
    pub structural_fingerprint: [u8; 32],
    pub logical_fingerprint: [u8; 32],
    pub signature_fingerprint: [u8; 32],
    pub core_api_version: (u16, u16),
    pub core_model_schema_version: u32,
    pub core_wire_format_version: (u16, u16),
    pub core_adapter_protocol_version: u32,
}

impl CoreMetadata {
    #[must_use]
    pub fn ontology_fingerprint_hex(&self) -> String {
        hex(&self.ontology_fingerprint)
    }
}

#[must_use]
pub fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dependencies_are_canonical_and_union_without_hash_order() -> NativeResult<()> {
        let left = DependencySet::new(vec![0, 3])?;
        let right = DependencySet::new(vec![1, 3, 8])?;
        assert_eq!(
            DependencySet::union(&[&left, &right]).as_slice(),
            &[0, 1, 3, 8]
        );
        assert!(left.is_subset_of(&DependencySet::union(&[&left, &right])));
        assert_eq!(left.add(1).as_slice(), &[0, 1, 3]);
        assert_eq!(left.add(3), left);
        assert_eq!(left.without(0).as_slice(), &[3]);
        assert_eq!(left.without(9), left);
        assert!(DependencySet::new(vec![1, 1]).is_err());
        Ok(())
    }
}
