//! Versioned compact session-event buffers drained across the `PyO3` boundary.
// SPDX-License-Identifier: LGPL-3.0-or-later

use sha2::{Digest, Sha256};

use crate::error::{NativeError, NativeResult};
use crate::session::{SessionEvent, SessionEventKind, SessionOperationKind};

pub const EVENT_MAGIC: &[u8; 8] = b"PYHMTEV\0";
pub const EVENT_SCHEMA_VERSION: u16 = 1;
pub const EVENT_HEADER_LEN: usize = 64;
pub const EVENT_RECORD_LEN: usize = 80;
pub const MAX_EVENT_WIRE_BYTES: usize = 16 * 1024 * 1024;

const FLAG_QUERY_KEY: u32 = 1;
const FLAG_ERROR_CODE: u32 = 2;

/// Encode one already bounded scheduler drain without exposing Rust objects to Python.
pub fn encode_events(events: &[SessionEvent]) -> NativeResult<Vec<u8>> {
    validate_events(events)?;
    let records_len = events
        .len()
        .checked_mul(EVENT_RECORD_LEN)
        .ok_or_else(|| NativeError::invariant("event record byte length overflow"))?;
    let strings_len = events.iter().try_fold(0_usize, |total, event| {
        total
            .checked_add(event.error_code.map_or(0, str::len))
            .ok_or_else(|| NativeError::invariant("event string table length overflow"))
    })?;
    let payload_len = records_len
        .checked_add(strings_len)
        .ok_or_else(|| NativeError::invariant("event payload byte length overflow"))?;
    let total_len = EVENT_HEADER_LEN
        .checked_add(payload_len)
        .ok_or_else(|| NativeError::invariant("event document byte length overflow"))?;
    if total_len > MAX_EVENT_WIRE_BYTES {
        return Err(NativeError::new(
            crate::error::ErrorKind::Resource,
            "NATIVE_EVENT_SIZE_LIMIT",
            "native event drain exceeds its compact wire limit",
        )
        .with_context("limit", "max_event_wire_bytes")
        .with_context("observed", total_len.to_string())
        .with_context("allowed", MAX_EVENT_WIRE_BYTES.to_string()));
    }

    let mut payload = Vec::new();
    payload
        .try_reserve_exact(payload_len)
        .map_err(|_| NativeError::invariant("event payload allocation failed before encoding"))?;
    let mut strings = Vec::new();
    strings
        .try_reserve_exact(strings_len)
        .map_err(|_| NativeError::invariant("event string allocation failed before encoding"))?;
    for event in events {
        let mut flags = 0_u32;
        let query_key = if let Some(value) = event.query_key {
            flags |= FLAG_QUERY_KEY;
            value.as_bytes()
        } else {
            [0; 32]
        };
        let (error_offset, error_length) = if let Some(code) = event.error_code {
            flags |= FLAG_ERROR_CODE;
            let offset = usize_to_u32(strings.len(), "event error-code offset")?;
            strings.extend_from_slice(code.as_bytes());
            (offset, usize_to_u32(code.len(), "event error-code length")?)
        } else {
            (0, 0)
        };

        payload.extend_from_slice(&event.version.to_le_bytes());
        payload.push(operation_discriminant(event.operation));
        payload.push(kind_discriminant(event.kind));
        payload.extend_from_slice(&flags.to_le_bytes());
        payload.extend_from_slice(&event.sequence.to_le_bytes());
        payload.extend_from_slice(&event.operation_id.to_le_bytes());
        payload.extend_from_slice(&event.completed.to_le_bytes());
        payload.extend_from_slice(&event.total.to_le_bytes());
        payload.extend_from_slice(&query_key);
        payload.push(match event.satisfiable {
            None => 0,
            Some(false) => 1,
            Some(true) => 2,
        });
        payload.extend_from_slice(&[0; 7]);
        payload.extend_from_slice(&error_offset.to_le_bytes());
        payload.extend_from_slice(&error_length.to_le_bytes());
    }
    payload.extend_from_slice(&strings);
    if payload.len() != payload_len {
        return Err(NativeError::invariant(
            "event encoder length accounting diverged",
        ));
    }

    let item_count = usize_to_u32(events.len(), "event record count")?;
    let string_bytes = usize_to_u32(strings_len, "event string table length")?;
    let total_length = u64::try_from(total_len)
        .map_err(|_| NativeError::invariant("event document length cannot fit u64"))?;
    let digest = Sha256::digest(&payload);
    let mut result = Vec::new();
    result
        .try_reserve_exact(total_len)
        .map_err(|_| NativeError::invariant("event document allocation failed before encoding"))?;
    result.extend_from_slice(EVENT_MAGIC);
    result.extend_from_slice(&EVENT_SCHEMA_VERSION.to_le_bytes());
    result.extend_from_slice(
        &u16::try_from(EVENT_RECORD_LEN)
            .map_err(|_| NativeError::invariant("event record length cannot fit u16"))?
            .to_le_bytes(),
    );
    result.extend_from_slice(&0_u32.to_le_bytes());
    result.extend_from_slice(&total_length.to_le_bytes());
    result.extend_from_slice(&item_count.to_le_bytes());
    result.extend_from_slice(&string_bytes.to_le_bytes());
    result.extend_from_slice(&digest);
    result.extend_from_slice(&payload);
    if result.len() != total_len {
        return Err(NativeError::invariant(
            "event document encoder length accounting diverged",
        ));
    }
    Ok(result)
}

fn validate_events(events: &[SessionEvent]) -> NativeResult<()> {
    let mut previous_sequence = 0_u64;
    for event in events {
        if event.version != EVENT_SCHEMA_VERSION {
            return Err(NativeError::invariant(
                "session event version differs from event wire schema",
            ));
        }
        if event.sequence == 0 || event.sequence <= previous_sequence {
            return Err(NativeError::invariant(
                "session event sequences must be strictly increasing and nonzero",
            ));
        }
        previous_sequence = event.sequence;
        if event.operation_id == 0 {
            return Err(NativeError::invariant(
                "session event operation ID must be nonzero",
            ));
        }
        if event.completed > event.total {
            return Err(NativeError::invariant(
                "session event completed count exceeds its total",
            ));
        }
        validate_event_shape(event)?;
        if let Some(code) = event.error_code {
            if code.is_empty()
                || !code
                    .bytes()
                    .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit() || byte == b'_')
            {
                return Err(NativeError::invariant(
                    "session event error code is not a stable ASCII identifier",
                ));
            }
        }
    }
    Ok(())
}

fn validate_event_shape(event: &SessionEvent) -> NativeResult<()> {
    match event.kind {
        SessionEventKind::OperationStarted => {
            if event.completed != 0
                || event.query_key.is_some()
                || event.satisfiable.is_some()
                || event.error_code.is_some()
            {
                return Err(NativeError::invariant(
                    "operation-started event contains terminal fields",
                ));
            }
        }
        SessionEventKind::CheckCompleted => {
            if event.completed == 0 || event.satisfiable.is_none() || event.error_code.is_some() {
                return Err(NativeError::invariant(
                    "check-completed event lacks its canonical answer fields",
                ));
            }
        }
        SessionEventKind::QueryStateReset => {
            if event.query_key.is_some()
                || event.satisfiable.is_some()
                || event.error_code.is_some()
            {
                return Err(NativeError::invariant(
                    "query-state-reset event contains answer fields",
                ));
            }
        }
        SessionEventKind::OperationCompleted => {
            if event.completed != event.total
                || event.query_key.is_some()
                || event.satisfiable.is_some()
                || event.error_code.is_some()
            {
                return Err(NativeError::invariant(
                    "operation-completed event contains noncanonical fields",
                ));
            }
        }
        SessionEventKind::OperationAborted => {
            if event.query_key.is_some()
                || event.satisfiable.is_some()
                || event.error_code.is_none()
            {
                return Err(NativeError::invariant(
                    "operation-aborted event lacks its canonical error fields",
                ));
            }
        }
    }
    Ok(())
}

const fn operation_discriminant(value: SessionOperationKind) -> u8 {
    match value {
        SessionOperationKind::PermanentCheck => 1,
        SessionOperationKind::QueryCheck => 2,
        SessionOperationKind::BatchCheck => 3,
        SessionOperationKind::ResetQueryState => 4,
    }
}

const fn kind_discriminant(value: SessionEventKind) -> u8 {
    match value {
        SessionEventKind::OperationStarted => 1,
        SessionEventKind::CheckCompleted => 2,
        SessionEventKind::QueryStateReset => 3,
        SessionEventKind::OperationCompleted => 4,
        SessionEventKind::OperationAborted => 5,
    }
}

fn usize_to_u32(value: usize, label: &'static str) -> NativeResult<u32> {
    u32::try_from(value).map_err(|_| NativeError::invariant(format!("{label} cannot fit u32")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session::QueryKey;

    fn event(kind: SessionEventKind, sequence: u64) -> SessionEvent {
        SessionEvent {
            version: 1,
            sequence,
            operation_id: 7,
            operation: SessionOperationKind::QueryCheck,
            kind,
            completed: 0,
            total: 1,
            query_key: None,
            satisfiable: None,
            error_code: None,
        }
    }

    #[test]
    fn encodes_empty_and_complete_event_drains_deterministically() -> NativeResult<()> {
        let empty = encode_events(&[])?;
        assert_eq!(&empty[..8], EVENT_MAGIC);
        assert_eq!(empty.len(), EVENT_HEADER_LEN);

        let started = event(SessionEventKind::OperationStarted, 10);
        let mut checked = event(SessionEventKind::CheckCompleted, 11);
        checked.completed = 1;
        checked.query_key = Some(QueryKey::new([9; 32]));
        checked.satisfiable = Some(true);
        let mut completed = event(SessionEventKind::OperationCompleted, 12);
        completed.completed = 1;
        let first = encode_events(&[started.clone(), checked.clone(), completed.clone()])?;
        let second = encode_events(&[started, checked, completed])?;
        assert_eq!(first, second);
        assert_eq!(first.len(), EVENT_HEADER_LEN + 3 * EVENT_RECORD_LEN);
        assert_eq!(&first[24..28], &3_u32.to_le_bytes());
        Ok(())
    }

    #[test]
    fn encodes_abort_code_in_the_trailing_string_table() -> NativeResult<()> {
        let started = event(SessionEventKind::OperationStarted, 1);
        let mut aborted = event(SessionEventKind::OperationAborted, 2);
        aborted.error_code = Some("REASONER_INTERRUPTED");
        let encoded = encode_events(&[started, aborted])?;
        assert!(encoded.ends_with(b"REASONER_INTERRUPTED"));
        Ok(())
    }

    #[test]
    fn rejects_noncanonical_event_shapes_and_sequences() {
        let mut started = event(SessionEventKind::OperationStarted, 1);
        started.satisfiable = Some(true);
        assert!(encode_events(&[started]).is_err());

        let first = event(SessionEventKind::OperationStarted, 2);
        let second = event(SessionEventKind::OperationStarted, 2);
        assert!(encode_events(&[first, second]).is_err());

        let mut aborted = event(SessionEventKind::OperationAborted, 3);
        aborted.error_code = Some("not-stable");
        assert!(encode_events(&[aborted]).is_err());
    }
}
