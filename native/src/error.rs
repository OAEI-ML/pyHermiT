//! Stable internal errors and the single `PyO3` exception-mapping boundary.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyDict;

pub type NativeResult<T> = Result<T, NativeError>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    Wire,
    Version,
    Disposed,
    Busy,
    Cancelled,
    Timeout,
    Resource,
    Profile,
    UnsupportedDatatype,
    Inconsistent,
    Poisoned,
    Fork,
    Feature,
    Invariant,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeError {
    pub kind: ErrorKind,
    pub code: &'static str,
    pub message: String,
    pub context: BTreeMap<String, String>,
}

impl NativeError {
    #[must_use]
    pub fn new(kind: ErrorKind, code: &'static str, message: impl Into<String>) -> Self {
        Self {
            kind,
            code,
            message: message.into(),
            context: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn with_context(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.context.insert(key.into(), value.into());
        self
    }

    #[must_use]
    pub fn wire(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Wire, "NATIVE_WIRE_INVALID", message)
    }

    #[must_use]
    pub fn version(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Version, "NATIVE_WIRE_VERSION", message)
    }

    #[must_use]
    pub fn invariant(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Invariant, "NATIVE_INVARIANT", message)
    }

    #[must_use]
    pub fn unsupported_datatype(
        message: impl Into<String>,
        datatype_iri: impl Into<String>,
    ) -> Self {
        Self::new(
            ErrorKind::UnsupportedDatatype,
            "UNSUPPORTED_DATATYPE",
            message,
        )
        .with_context("datatype_iri", datatype_iri)
    }

    #[must_use]
    pub fn inconsistent(message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Inconsistent, "INCONSISTENT_ONTOLOGY", message)
    }

    #[must_use]
    pub fn feature(feature: &'static str) -> Self {
        Self::new(
            ErrorKind::Feature,
            "FEATURE_NOT_IMPLEMENTED",
            format!("native feature '{feature}' is not implemented by WPR0"),
        )
        .with_context("feature_id", feature)
    }

    #[must_use]
    pub fn into_pyerr(self, py: Python<'_>) -> PyErr {
        match self.build_public_exception(py) {
            Ok(instance) => PyErr::from_value(instance),
            Err(mapping_error) => PyRuntimeError::new_err(format!(
                "native error mapping failed for {}: {mapping_error}",
                self.code
            )),
        }
    }

    fn build_public_exception<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let module = py.import("pyhermit.exceptions")?;
        let class_name = match self.kind {
            ErrorKind::Wire => "BackendMismatchError",
            ErrorKind::Version => "BackendVersionError",
            ErrorKind::Disposed => "DisposedReasonerError",
            ErrorKind::Busy => "ConcurrentMutationError",
            ErrorKind::Cancelled => "ReasonerInterruptedError",
            ErrorKind::Timeout => "ReasonerTimeoutError",
            ErrorKind::Resource => "ResourceLimitError",
            ErrorKind::Profile => "OntologyProfileError",
            ErrorKind::UnsupportedDatatype => "UnsupportedDatatypeError",
            ErrorKind::Inconsistent => "InconsistentOntologyError",
            ErrorKind::Poisoned => "BackendPoisonedError",
            ErrorKind::Fork => "ReasonerStateError",
            ErrorKind::Feature => "FeatureNotImplementedError",
            ErrorKind::Invariant => "InternalInvariantError",
        };
        let class = module.getattr(class_name)?;
        let kwargs = PyDict::new(py);
        match self.kind {
            ErrorKind::Feature => {
                let feature = self.context.get("feature_id").ok_or_else(|| {
                    PyValueError::new_err("native feature error lacks feature_id")
                })?;
                kwargs.set_item("feature_id", feature)?;
            }
            ErrorKind::Resource => {
                if let Some(limit) = self.context.get("limit") {
                    kwargs.set_item("limit", limit)?;
                }
                for field in ["observed", "allowed"] {
                    let hexadecimal = (field == "observed")
                        .then(|| self.context.get("observed_hex"))
                        .flatten();
                    if let Some(value) = hexadecimal {
                        if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                            return Err(PyValueError::new_err(
                                "native resource error has a nonhexadecimal observed_hex value",
                            ));
                        }
                        let integer = py
                            .import("builtins")?
                            .getattr("int")?
                            .call1((value, 16_u8))?;
                        kwargs.set_item(field, integer)?;
                    } else if let Some(value) = self.context.get(field) {
                        let integer = value.parse::<u64>().map_err(|_| {
                            PyValueError::new_err(format!(
                                "native resource error has a noninteger {field} value"
                            ))
                        })?;
                        kwargs.set_item(field, integer)?;
                    }
                }
            }
            ErrorKind::Profile => {
                let issue_count = self
                    .context
                    .get("issue_count")
                    .ok_or_else(|| PyValueError::new_err("native profile error lacks issue_count"))?
                    .parse::<usize>()
                    .map_err(|_| {
                        PyValueError::new_err("native profile error has a noninteger issue_count")
                    })?;
                let context = PyDict::new(py);
                context.set_item("issue_count", issue_count)?;
                context.set_item("rule_ids", self.context.get("rule_ids"))?;
                kwargs.set_item("code", self.code)?;
                kwargs.set_item("context", context)?;
            }
            _ => {
                kwargs.set_item("code", self.code)?;
                if !self.context.is_empty() {
                    kwargs.set_item("context", &self.context)?;
                }
            }
        }
        class.call((self.message.as_str(),), Some(&kwargs))
    }
}

impl fmt::Display for NativeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.code, self.message)
    }
}

impl Error for NativeError {}

impl From<serde_json::Error> for NativeError {
    fn from(error: serde_json::Error) -> Self {
        Self::wire(format!("invalid canonical JSON: {error}"))
    }
}
