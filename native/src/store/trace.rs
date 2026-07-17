//! Exact parser and replay adapter for `PYHERMIT-STATE-TRACE` version 1.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde::de::{self, DeserializeSeed, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};
use serde_json::{Map, Number, Value};

use crate::error::{NativeError, NativeResult};
use crate::model::{DependencySet, NodeHandle, NodeKind};

use super::state::TableauKernel;

pub const STATE_TRACE_MAGIC: &str = "PYHERMIT-STATE-TRACE";
pub const STATE_TRACE_VERSION: u32 = 1;
const MAX_TRACE_OPERATIONS: usize = 10_000;
const MAX_SNAPSHOT_BYTES: usize = 128 * 1024 * 1024;

pub fn replay_state_trace(payload: &[u8]) -> NativeResult<Vec<String>> {
    let text = std::str::from_utf8(payload)
        .map_err(|_| NativeError::wire("state trace is not valid UTF-8"))?;
    let mut deserializer = serde_json::Deserializer::from_str(text);
    let UniqueValue(document) = UniqueValue::deserialize(&mut deserializer)?;
    deserializer.end()?;
    TraceRunner::new().run(&document)
}

struct TraceRunner {
    kernel: TableauKernel,
    aliases: BTreeMap<String, NodeHandle>,
}

impl TraceRunner {
    fn new() -> Self {
        Self {
            kernel: TableauKernel::new(),
            aliases: BTreeMap::new(),
        }
    }

    fn run(mut self, document: &Value) -> NativeResult<Vec<String>> {
        let root = exact_object(document, &["magic", "operations", "version"], &[])?;
        if required_string(root, "magic")? != STATE_TRACE_MAGIC {
            return Err(NativeError::version("state trace magic is invalid"));
        }
        if required_u32(root, "version")? != STATE_TRACE_VERSION {
            return Err(NativeError::version("state trace version is unsupported"));
        }
        let operations = required_array(root, "operations")?;
        if operations.len() > MAX_TRACE_OPERATIONS {
            return Err(NativeError::new(
                crate::error::ErrorKind::Resource,
                "NATIVE_TRACE_OPERATION_LIMIT",
                "state trace exceeds the native operation limit",
            )
            .with_context("limit", "state_trace_operations")
            .with_context("observed", operations.len().to_string())
            .with_context("allowed", MAX_TRACE_OPERATIONS.to_string()));
        }
        let mut snapshots = Vec::new();
        snapshots
            .try_reserve_exact(operations.len())
            .map_err(|_| NativeError::wire("state trace snapshot allocation failed"))?;
        let mut snapshot_bytes = 0_usize;
        for operation in operations {
            self.apply(operation)?;
            self.kernel.check_invariants()?;
            let snapshot = self.kernel.canonical_snapshot()?;
            snapshot_bytes = snapshot_bytes
                .checked_add(snapshot.len())
                .ok_or_else(|| NativeError::invariant("state trace snapshot size overflow"))?;
            if snapshot_bytes > MAX_SNAPSHOT_BYTES {
                return Err(NativeError::new(
                    crate::error::ErrorKind::Resource,
                    "NATIVE_TRACE_OUTPUT_LIMIT",
                    "state trace snapshots exceed the native output limit",
                )
                .with_context("limit", "state_trace_snapshot_bytes")
                .with_context("observed", snapshot_bytes.to_string())
                .with_context("allowed", MAX_SNAPSHOT_BYTES.to_string()));
            }
            snapshots.push(snapshot);
        }
        Ok(snapshots)
    }

    fn apply(&mut self, operation: &Value) -> NativeResult<()> {
        let value = exact_object(operation, &["arguments", "kind"], &[])?;
        let kind = required_string(value, "kind")?;
        let arguments = required_object(value, "arguments")?;
        match kind {
            "create_node" => self.create_node(arguments),
            "begin_operation" => {
                exact_fields(arguments, &[], &[])?;
                self.kernel.begin_operation()
            }
            "add_fact" => self.add_fact(arguments),
            "prepare_delta" => {
                exact_fields(arguments, &[], &[])?;
                self.kernel.prepare_next_delta()
            }
            "push_branch" => self.push_branch(arguments),
            "advance_branch" => self.advance_branch(arguments),
            "backtrack" => self.backtrack(arguments),
            "merge" => self.merge(arguments),
            "prune" => self.prune(arguments),
            "add_disjunction" => self.add_disjunction(arguments),
            "take_disjunction" => {
                exact_fields(arguments, &[], &[])?;
                self.kernel.take_disjunction().map(|_| ())
            }
            "install_clash" => self.install_clash(arguments),
            "enqueue" => self.enqueue(arguments),
            "mark_existential" => self.mark_existential(arguments),
            "set_blocked" => self.set_blocked(arguments),
            "check" => {
                exact_fields(arguments, &[], &[])?;
                self.kernel.check_invariants()
            }
            _ => Err(NativeError::version(format!(
                "unknown state operation '{kind}'"
            ))),
        }
    }

    fn create_node(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(
            values,
            &["kind", "name"],
            &[
                "cardinality_tag",
                "is_owl_named_individual",
                "nominal_level",
                "parent",
                "source_individual_id",
            ],
        )?;
        let name = required_string(values, "name")?;
        if self.aliases.contains_key(name) {
            return Err(NativeError::wire("state trace node alias already exists"));
        }
        let kind = match required_string(values, "kind")? {
            "root" => NodeKind::Root,
            "tree" => NodeKind::Tree,
            "ni" => NodeKind::Ni,
            "concrete" => NodeKind::Concrete,
            _ => return Err(NativeError::wire("state trace node kind is unknown")),
        };
        let parent = optional_alias(values.get("parent"), &self.aliases)?;
        let handle = self.kernel.create_node(
            kind,
            parent,
            optional_bool(values, "is_owl_named_individual")?.unwrap_or(false),
            optional_u32(values, "source_individual_id")?,
            optional_u32(values, "nominal_level")?,
            optional_u32(values, "cardinality_tag")?,
        )?;
        self.aliases.insert(name.to_owned(), handle);
        Ok(())
    }

    fn add_fact(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(
            values,
            &["arguments", "dependency", "predicate_id"],
            &["core", "provenance_id"],
        )?;
        let arguments = required_array(values, "arguments")?
            .iter()
            .map(|value| self.alias(value))
            .collect::<NativeResult<Vec<_>>>()?;
        self.kernel
            .add_fact(
                required_u32(values, "predicate_id")?,
                arguments,
                dependency(values)?,
                optional_bool(values, "core")?.unwrap_or(false),
                optional_u32(values, "provenance_id")?,
            )
            .map(|_| ())
    }

    fn push_branch(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(
            values,
            &["alternatives", "choice_kind", "dependency", "source_id"],
            &[],
        )?;
        self.kernel
            .push_branch(
                required_string(values, "choice_kind")?.to_owned(),
                u32_array(required_array(values, "alternatives")?)?,
                required_u32(values, "source_id")?,
                dependency(values)?,
            )
            .map(|_| ())
    }

    fn advance_branch(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(values, &["dependency", "level"], &[])?;
        self.kernel
            .advance_branch(required_u32(values, "level")?, dependency(values)?)
            .map(|_| ())
    }

    fn backtrack(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(values, &["level"], &[])?;
        self.kernel.backtrack_to(required_u32(values, "level")?)
    }

    fn merge(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(values, &["dependency", "left", "right"], &[])?;
        self.kernel
            .merge_nodes(
                self.alias(
                    values
                        .get("left")
                        .ok_or_else(|| NativeError::wire("merge lacks left alias"))?,
                )?,
                self.alias(
                    values
                        .get("right")
                        .ok_or_else(|| NativeError::wire("merge lacks right alias"))?,
                )?,
                dependency(values)?,
            )
            .map(|_| ())
    }

    fn prune(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(values, &["root"], &[])?;
        self.kernel
            .prune_subtree(
                self.alias(
                    values
                        .get("root")
                        .ok_or_else(|| NativeError::wire("prune lacks root alias"))?,
                )?,
            )
            .map(|_| ())
    }

    fn add_disjunction(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(values, &["dependency", "disjunct_ids"], &[])?;
        self.kernel
            .add_disjunction(
                u32_array(required_array(values, "disjunct_ids")?)?,
                dependency(values)?,
            )
            .map(|_| ())
    }

    fn install_clash(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(
            values,
            &["dependency", "kind"],
            &["participants", "provenance_id"],
        )?;
        let participants = values.get("participants").map_or_else(
            || Ok(Vec::new()),
            |value| {
                value.as_array().map_or_else(
                    || Err(NativeError::wire("participants must be an array")),
                    |items| u32_array(items),
                )
            },
        )?;
        self.kernel
            .install_clash(
                required_string(values, "kind")?.to_owned(),
                dependency(values)?,
                participants,
                optional_u32(values, "provenance_id")?,
            )
            .map(|_| ())
    }

    fn enqueue(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(values, &["priority", "queue", "value"], &[])?;
        let queue = required_string(values, "queue")?;
        let priority = i64_array(required_array(values, "priority")?)?;
        let value = values
            .get("value")
            .ok_or_else(|| NativeError::wire("enqueue lacks a value"))?;
        match queue {
            "delta_rows" | "annotated_equalities" | "datatype_components" => self
                .kernel
                .enqueue_integer(queue, value_u32(value, "queue.value")?, priority),
            "existential_candidates" | "blocking_invalidations" => {
                self.kernel
                    .enqueue_node(queue, self.alias(value)?, priority)
            }
            _ => Err(NativeError::wire("state trace queue is unknown")),
        }
    }

    fn mark_existential(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(values, &["existential_id", "node", "pending"], &[])?;
        self.kernel.mark_existential(
            self.alias(
                values
                    .get("node")
                    .ok_or_else(|| NativeError::wire("existential lacks node alias"))?,
            )?,
            required_u32(values, "existential_id")?,
            required_bool(values, "pending")?,
        )
    }

    fn set_blocked(&mut self, values: &Map<String, Value>) -> NativeResult<()> {
        exact_fields(values, &["blocker", "directly", "node"], &[])?;
        let blocker = optional_alias(values.get("blocker"), &self.aliases)?;
        self.kernel.set_blocked(
            self.alias(
                values
                    .get("node")
                    .ok_or_else(|| NativeError::wire("blocking lacks node alias"))?,
            )?,
            blocker,
            required_bool(values, "directly")?,
        )
    }

    fn alias(&self, value: &Value) -> NativeResult<NodeHandle> {
        let name = value
            .as_str()
            .filter(|value| !value.is_empty())
            .ok_or_else(|| NativeError::wire("node alias must be a nonempty string"))?;
        self.aliases
            .get(name)
            .copied()
            .ok_or_else(|| NativeError::wire(format!("unknown node alias '{name}'")))
    }
}

fn exact_object<'a>(
    value: &'a Value,
    required: &[&str],
    optional: &[&str],
) -> NativeResult<&'a Map<String, Value>> {
    let object = value
        .as_object()
        .ok_or_else(|| NativeError::wire("state trace value must be an object"))?;
    exact_fields(object, required, optional)?;
    Ok(object)
}

fn exact_fields(
    object: &Map<String, Value>,
    required: &[&str],
    optional: &[&str],
) -> NativeResult<()> {
    for field in required {
        if !object.contains_key(*field) {
            return Err(NativeError::wire(format!(
                "state trace operation is missing field '{field}'"
            )));
        }
    }
    if object
        .keys()
        .any(|field| !required.contains(&field.as_str()) && !optional.contains(&field.as_str()))
    {
        return Err(NativeError::wire(
            "state trace object contains unknown fields",
        ));
    }
    Ok(())
}

fn required_object<'a>(
    values: &'a Map<String, Value>,
    name: &str,
) -> NativeResult<&'a Map<String, Value>> {
    values
        .get(name)
        .and_then(Value::as_object)
        .ok_or_else(|| NativeError::wire(format!("{name} must be an object")))
}

fn required_array<'a>(values: &'a Map<String, Value>, name: &str) -> NativeResult<&'a [Value]> {
    values
        .get(name)
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| NativeError::wire(format!("{name} must be an array")))
}

fn required_string<'a>(values: &'a Map<String, Value>, name: &str) -> NativeResult<&'a str> {
    values
        .get(name)
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| NativeError::wire(format!("{name} must be a nonempty string")))
}

fn required_u32(values: &Map<String, Value>, name: &str) -> NativeResult<u32> {
    values
        .get(name)
        .ok_or_else(|| NativeError::wire(format!("{name} is required")))
        .and_then(|value| value_u32(value, name))
}

fn value_u32(value: &Value, name: &str) -> NativeResult<u32> {
    value
        .as_u64()
        .and_then(|integer| u32::try_from(integer).ok())
        .ok_or_else(|| NativeError::wire(format!("{name} must be an unsigned 32-bit integer")))
}

fn optional_u32(values: &Map<String, Value>, name: &str) -> NativeResult<Option<u32>> {
    match values.get(name) {
        None | Some(Value::Null) => Ok(None),
        Some(value) => value_u32(value, name).map(Some),
    }
}

fn required_bool(values: &Map<String, Value>, name: &str) -> NativeResult<bool> {
    values
        .get(name)
        .and_then(Value::as_bool)
        .ok_or_else(|| NativeError::wire(format!("{name} must be bool")))
}

fn optional_bool(values: &Map<String, Value>, name: &str) -> NativeResult<Option<bool>> {
    values.get(name).map_or(Ok(None), |value| {
        value
            .as_bool()
            .map(Some)
            .ok_or_else(|| NativeError::wire(format!("{name} must be bool")))
    })
}

fn u32_array(values: &[Value]) -> NativeResult<Vec<u32>> {
    values
        .iter()
        .map(|value| value_u32(value, "array item"))
        .collect()
}

fn i64_array(values: &[Value]) -> NativeResult<Vec<i64>> {
    values
        .iter()
        .map(|value| {
            value
                .as_i64()
                .ok_or_else(|| NativeError::wire("priority items must be signed 64-bit integers"))
        })
        .collect()
}

fn dependency(values: &Map<String, Value>) -> NativeResult<DependencySet> {
    DependencySet::new(u32_array(required_array(values, "dependency")?)?)
}

fn optional_alias(
    value: Option<&Value>,
    aliases: &BTreeMap<String, NodeHandle>,
) -> NativeResult<Option<NodeHandle>> {
    match value {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(name)) if !name.is_empty() => aliases
            .get(name)
            .copied()
            .map(Some)
            .ok_or_else(|| NativeError::wire(format!("unknown node alias '{name}'"))),
        Some(_) => Err(NativeError::wire(
            "optional node alias must be a nonempty string or null",
        )),
    }
}

/// A recursive JSON value that rejects duplicate keys and every floating-point token.
struct UniqueValue(Value);

impl<'de> Deserialize<'de> for UniqueValue {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(UniqueValueVisitor)
    }
}

struct UniqueValueVisitor;

impl<'de> Visitor<'de> for UniqueValueVisitor {
    type Value = UniqueValue;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("JSON without duplicate keys or floating-point values")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Bool(value)))
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Number(Number::from(value))))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Number(Number::from(value))))
    }

    fn visit_f64<E>(self, _value: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Err(E::custom(
            "floating-point values are forbidden in state traces",
        ))
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_string(value.to_owned())
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::String(value)))
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Null))
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Null))
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        UniqueValue::deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut values = Vec::new();
        while let Some(UniqueValue(value)) = sequence.next_element::<UniqueValue>()? {
            values.push(value);
        }
        Ok(UniqueValue(Value::Array(values)))
    }

    fn visit_map<A>(self, mut mapping: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut values = Map::new();
        let mut names = BTreeSet::new();
        while let Some(name) = mapping.next_key::<String>()? {
            if !names.insert(name.clone()) {
                return Err(de::Error::custom(format!("duplicate JSON key '{name}'")));
            }
            let UniqueValue(value) = mapping.next_value_seed(UniqueValueSeed)?;
            values.insert(name, value);
        }
        Ok(UniqueValue(Value::Object(values)))
    }
}

struct UniqueValueSeed;

impl<'de> DeserializeSeed<'de> for UniqueValueSeed {
    type Value = UniqueValue;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        UniqueValue::deserialize(deserializer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_trace_replays_and_malformed_json_is_rejected() -> NativeResult<()> {
        let payload = br#"{"magic":"PYHERMIT-STATE-TRACE","operations":[],"version":1}"#;
        assert!(replay_state_trace(payload)?.is_empty());
        assert!(
            replay_state_trace(br#"{"magic":"x","magic":"y","operations":[],"version":1}"#)
                .is_err()
        );
        assert!(replay_state_trace(br#"{"magic":"PYHERMIT-STATE-TRACE","operations":[{"arguments":{"priority":[1.5],"queue":"delta_rows","value":0},"kind":"enqueue"}],"version":1}"#).is_err());
        Ok(())
    }
}
