# WPR3 exact semantic-value evidence

This is the independently committable semantic-value foundation of WPR3. Range algebra,
regex, and constraint-component solving remain separate WPR3 work and are not claimed here.

## Boundary and representations

- Rust decodes the canonical `literal_semantic` / `opaque_literal_semantic` JSON emitted by
  Python; it checks exact field sets, schema version, sorted compact JSON bytes, canonical
  signed-hex integers, reduced rationals, fixed-width IEEE bits, and family pairing.
- Every `NativeLiteral` retains its source-literal ID and exact lexical/datatype/language
  record separately from `DataIdentity` and `ComparisonValue`. Lexical aliases are never
  collapsed as source values.
- Exact numeric and date-time values use pinned pure-Rust arbitrary-precision integers;
  neither host float nor fixed-width arithmetic participates in their semantics. The wire
  remains pyHermiT's own language-neutral tokens, not a crate serialization format.
- IEEE float/double identity retains format, signed zero, subnormals, infinities, and one
  canonical XML Schema NaN. Comparison derives an exact rational from bits and keeps NaN
  unordered.
- Strings/plain literals, Boolean, hex/base64, URI, canonical XML, and date-time occupy their
  explicit primitive families. Zoned/unzoned date-time comparison implements the XML Schema
  possible-UTC interval rather than using local timezone state.
- Opaque values preserve the source token but deliberately expose no data identity.
- Payload, numeric-digit, text, and binary limits are checked; validation polls the shared
  cancellation/resource control. `unsafe` remains forbidden.

## Shared differential

`tools/datatypes/build_native_value_fixture.py` compiles 30 values with the authoritative
Python datatype layer. The corpus includes integer/decimal/rational overlap, a very large
integer, IEEE signed zeros/subnormal/NaN/infinities and both formats, Boolean aliases,
string/token/plain-language values, both disjoint binary families, URI, canonical-XML aliases,
zoned/unzoned date-time, and HermiT-compatible end-of-day syntax.

The committed fixture contains all 900 ordered value pairs. For each pair it records exact
data-identity equality and comparison outcome (`less`, `equal`, `greater`, `unordered`, or
cross-family `error`). Rust matches the complete matrix.

Observed gates on 2026-07-17:

- Python 3.10 value/semantic/IEEE/nonnumeric slice: 115 passed in 1.14 s.
- Python 3.12 same slice: 115 passed in 1.27 s.
- Python 3.10 and 3.12 regenerate the shared fixture byte-for-byte.
- Rust datatype value tests: 7 passed, including all 900 pair outcomes.
- Full native crate after this slice: 104/104.
- Ruff and strict mypy pass for the fixture generator/reproducibility test.
- `cargo clippy --all-targets --no-default-features -- -D warnings`: pass.

## Dependency audit note

The lock adds `num-bigint 0.5.1` and `num-integer 0.1.46`; the already-pinned
`num-traits 0.2.19` is now direct. All three are pure Rust, use the existing MSRV, and are
MIT/Apache-2.0 dual licensed. Random, serde, and other optional big-integer features are off;
only `std` is enabled.
