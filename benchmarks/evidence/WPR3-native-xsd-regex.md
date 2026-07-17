# WPR3 native XML Schema regular-language evidence

This tranche ports pyHermiT's XML Schema regular-language algebra to safe Rust. It is
an independent native implementation of the existing pure-Python semantics; it does
not call Java, PCRE, Python's `re`, Rust's `regex`, or any runtime reference engine.

## Implemented semantics

- Patterns are implicitly anchored and parsed as XML Schema regular expressions.
- Supported syntax includes grouping, alternatives, concatenation, `?`, `*`, `+`,
  bounded/unbounded brace quantifiers, dot, positive and negative character classes,
  XML Schema character-class subtraction, escaped metacharacters, `\s`, `\d`, `\w`,
  `\i`, `\c`, their uppercase complements, and Unicode general categories.
- Brzozowski derivatives retain exact intersection, union, complement, membership,
  emptiness, finite cardinality, saturated cardinality, finite enumeration, and
  deterministic shortest/code-point-first witnesses. Symbolic character intervals
  avoid expanding the XML character universe during determinization.
- Membership follows only the derivatives selected by the input and caches them in a
  clone-shared, thread-safe state graph. Whole-language DFA construction is lazy and
  reserved for exact language operations. Cached work is still charged against each
  caller's limits, so a cache populated under broad limits cannot bypass a later
  restrictive call. Bounded quantifiers use a compact nested optional tail rather
  than a flat nullable sequence, avoiding quadratic derivative growth.
- XML characters follow the same five intervals as the Python engine. Unicode general
  categories are pinned to UCD 3.2.0 and encoded as 2,112 generated category runs.
  This deliberately preserves behavior across supported Python and host Unicode
  versions, including code points assigned after UCD 3.2.
- Parsing, derivation, determinization, enumeration, and witness search have explicit
  lexical, state, transition, depth, enumeration, cancellation-poll, and caller memory
  controls. Production Rust is safe code under the crate-wide `unsafe_code = "forbid"`
  gate.

The existing explicit limitation is preserved: `\p{Is...}` Unicode block names are
rejected until the OWL/XSD-normative block inventory is pinned. They are not silently
interpreted using a host library.

## Cross-implementation fixture

`tools/datatypes/build_xsd_regex_fixture.py` derives expectations only from
`src/pyhermit/datatypes/xsd_regex.py`. The versioned fixture contains 14 language
cases with 82 membership points, five Boolean-algebra cases with 28 membership points,
and six invalid-syntax cases. It covers anchoring, quantifiers, class subtraction, XML
name escapes, Unicode category/3.2 drift, control characters, complement,
intersection, emptiness, exact cardinality, and deterministic enumeration.

Both CPython 3.10.11 and 3.12.3 reproduced the checked-in fixture and Unicode table
byte-for-byte. Artifact SHA-256 digests at capture time were:

| artifact | SHA-256 |
|---|---|
| `tests/data/datatypes/xsd-regex-native-v1.json` | `6fa768213be8eb7d24fa338ce91803cfb65bd746d2c16beb6f7b524301c5d882` |
| `native/src/datatypes/xsd_unicode_3_2.rs` | `8ff7a452b5c667574a2bcb508ac6b34bcde2aee8e4ae3cbb8a49245c1a711239` |
| `tools/datatypes/build_xsd_regex_fixture.py` | `b34675ad469eb4f0a0819e42e57535736c7d954d5b893e62fa57d70f654d31eb` |
| `tools/datatypes/build_xsd_unicode_table.py` | `a2fa07bedac870ae787faeaae9083415a7ad9c214b17dddc962ca504550c36b5` |
| `native/src/datatypes/xsd_regex.rs` | `7947559b912af3a0053496708110d3d4db059bf27e393d924b82752f95aaed2a` |
| `native/benches/datatype_kernel.rs` | `591f6cc622e7e6a56a447c83fe18897eef4f34202c0c845e5cc9bcb3dad5fe78` |
| `tests/unit/datatypes/test_native_xsd_regex_fixture.py` | `f78539e8b57a8c03c3eb83b67fa433993922540b9e3b0f61977cfc8cce7d99b7` |

## Correctness and hostile-input gates

The integrated native crate passed all ten focused tests and the complete 119-test
native suite: Python/Rust membership and finite-language parity, Boolean algebra and
emptiness parity, invalid syntax, deterministic witnesses/cardinality saturation,
lexical/state/quantifier/depth limits, determinization transition limits,
cooperative cancellation, pre-growth parser and lazy-cache memory rejection, lazy DFA
materialization, clone-shared cache behavior, and cross-thread membership.

Rust formatting and strict all-target Clippy (`-D warnings`, including the crate's `all`,
`pedantic`, `nursery`, `unwrap_used`, `expect_used`, and `panic` deny policy) passed for
the integrated library and tests with rustc 1.97.1. The crate MSRV remains Rust 1.83;
integration keeps `CharSet::is_empty` non-const because `Vec::is_empty` was not yet
const-stable at that MSRV.

The two fixture generators pass Ruff lint and format checks.

## Performance evidence

Criterion was run against the optimized, Python-independent crate with a one-second
warm-up, two-second measurement, and ten samples. The captured intervals were:

| operation | optimized time |
|---|---:|
| compile `[a-z-[aeiou]]{1,32}` | 27.7–30.0 µs |
| compile `\p{Lu}\p{Ll}{0,31}` | 34.1–37.6 µs |
| cached 32-character ASCII full match | 0.534–0.618 µs |
| cached Unicode-category full match | 0.132–0.181 µs |
| exact emptiness of disjoint infinite languages | 0.120–0.138 µs |
| compile plus first Unicode-category full match | 0.693–0.819 ms |

During integration, eager Unicode DFA construction exceeded 20 seconds and the first
direct derivative design measured 110–115 ms for the same compile-plus-match case.
Lazy selected derivatives plus compact bounded repetition reduced that cold operation
by more than 99%, while subsequent matches use the bounded shared cache.

## Reproduction

```text
PYTHONPATH=../pyOWLCore/src:src .reference/venv310/bin/python \
  tools/datatypes/build_xsd_regex_fixture.py --check
PYTHONPATH=../pyOWLCore/src:src .reference/venv312/bin/python \
  tools/datatypes/build_xsd_regex_fixture.py --check
.reference/venv310/bin/python tools/datatypes/build_xsd_unicode_table.py --check
.reference/venv312/bin/python tools/datatypes/build_xsd_unicode_table.py --check

.reference/venv310/bin/ruff check \
  tools/datatypes/build_xsd_regex_fixture.py \
  tools/datatypes/build_xsd_unicode_table.py
.reference/venv310/bin/ruff format --check \
  tools/datatypes/build_xsd_regex_fixture.py \
  tools/datatypes/build_xsd_unicode_table.py

cargo fmt --manifest-path native/Cargo.toml -- --check
cargo test --manifest-path native/Cargo.toml --no-default-features \
  datatypes::xsd_regex::tests
cargo test --manifest-path native/Cargo.toml --no-default-features
cargo clippy --manifest-path native/Cargo.toml --no-default-features \
  --all-targets -- -D warnings
cargo bench --manifest-path native/Cargo.toml --no-default-features \
  --bench datatype_kernel -- datatype_xsd_regex \
  --warm-up-time 1 --measurement-time 2 --sample-size 10
```
