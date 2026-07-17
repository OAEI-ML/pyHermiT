//! Exact Python-independent datatype values and constraint machinery.
//!
//! WPR3 consumes the canonical semantic payload emitted by the Python compiler. It
//! never reparses a source literal lexical form and never exposes a Rust value as a
//! public OWL literal. Source IDs remain separate from data identity and comparison.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![allow(
    clippy::missing_errors_doc,
    clippy::module_name_repetitions,
    clippy::too_many_lines
)]

mod solver;
mod value;
mod xsd_regex;
mod xsd_unicode_3_2;

pub use solver::{
    solve_component, CardinalityConstraint, ClashKind, ConstraintComponent, DatatypeClash,
    DatatypeWitness, DomainConstraint, DomainKind, EqualityConstraint, FixedValueConstraint,
    InequalityConstraint, SolveResult, SolverLimits,
};
pub use value::{
    decode_literal_semantic, BinaryKind, ComparisonOrder, ComparisonValue, DataIdentity,
    DatatypeControl, DatatypeError, DatatypeErrorKind, DatatypeLimits, DecodedLiteral,
    ExactRational, IEEECategory, IEEEFormat, NativeLiteral, NeverCancel, OpaqueLiteral,
    SourceLiteral,
};
pub use xsd_regex::{CharSet, RegexLimits, XsdRegex, XSD_REGEX_UNICODE_VERSION};

#[cfg(test)]
mod tests;
