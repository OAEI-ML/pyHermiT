# Datatypes and concrete-domain reasoning

Datatype behavior follows the OWL 2 datatype map and Direct Semantics, including value
equality rather than Python object equality. The relevant upstream areas are
[`datatypes/`](https://github.com/phillord/hermit-reasoner/tree/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/datatypes)
and
[`tableau/DatatypeManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/DatatypeManager.java).

The W3C source of truth is the
[OWL 2 datatype map](https://www.w3.org/TR/owl2-syntax/#Datatype_Maps).

## 1. Required datatype map

The complete mandatory implementation includes:

- `rdfs:Literal`, `rdf:PlainLiteral`, and `rdf:XMLLiteral`;
- `owl:real` and `owl:rational`;
- `xsd:decimal`, `xsd:integer`, all standard bounded/derived signed and unsigned
  integer types, positive/nonnegative/negative/nonpositive integer;
- `xsd:float` and `xsd:double`;
- `xsd:string`, `xsd:normalizedString`, `xsd:token`, `xsd:language`, `xsd:Name`,
  `xsd:NCName`, and `xsd:NMTOKEN`;
- `xsd:boolean`;
- `xsd:hexBinary` and `xsd:base64Binary`;
- `xsd:anyURI`; and
- `xsd:dateTime` and `xsd:dateTimeStamp`.

If the final W3C/HermiT reference inventory contains an additional required built-in,
it is mandatory and the table in implementation docs must be amended; absence from
this prose is not permission to omit a datatype supported by the pinned core.

Supported facets include every facet normative in the OWL 2 datatype map for the
applicable datatype: inclusive/exclusive bounds, length/minLength/maxLength, pattern,
and langRange. In particular, XML Schema facets that are not in the final OWL 2
datatype map (including `totalDigits` and `fractionDigits`) are not silently accepted
as core OWL 2 semantics. Illegal datatype/facet combinations are profile/input errors
before tableau work; any optional extension needs its own explicit deviation record.

## 2. Literal identity, data-value identity, and facet comparison

A core `Literal` is compiled for datatype reasoning in two steps:

1. validate the lexical form against the datatype's exact lexical space; and
2. map it to an immutable semantic value in the datatype's value space.

Do not delegate correctness to Python `float`, `datetime`, Unicode regex, locale, or an
RDF library's coercion. Required representations include arbitrary-precision integers,
exact decimals/rationals, explicit IEEE-754 bit/category values, byte strings, Unicode
strings, URI lexical values, XML canonical/value records, and date-time interval/order
records.

The implementation MUST keep three relations separate:

1. **Source-literal identity** is the exact source-preserving, standards-canonical
   `pyowl_core.Literal` structural identity. pyHermiT neither lowercases/rebuilds the public
   object nor defines a competing tuple. It controls round trips and which finite explicit
   tokens can be returned. Different core lexical aliases remain different source literals.
2. **Data-value identity** means that two literals denote the same element of the OWL
   data domain. It controls equality/inequality constraints, functional data properties,
   `DataOneOf`, and min/max/exact data cardinality. Overlapping numeric datatypes can
   denote one identical mathematical value. By contrast, IEEE `+0` and `-0` and certain
   timezone-shifted date-times can compare equal while remaining distinct data values;
   they MUST receive different identity tokens and count separately.
3. **Datatype comparison** is the datatype/facet equality or partial order used by
   bounds and range algebra. A comparison result of equal never by itself merges data
   nodes, satisfies functional equality, or reduces cardinality. It may be `UNORDERED`
   (for example for NaN or incomparable date-times).

Each private compiled literal record therefore contains a core source-literal ID, a language-neutral
data-identity token, and the tagged comparison representation required by its datatype
family. There is no single ambiguous `value_id`. The original lexical form remains
available for round trip and answers; language comparison uses core's standards-canonical
language key while source spelling remains preserved. Backend wire/result records carry source literal IDs and identity
tokens even when several source literals denote one identical data value.

## 3. Numeric domains

- Integers, decimals, and rationals are exact and never converted through binary float.
- Decimal scale does not affect value equality; canonical diagnostics use a specified
  minimal decimal form while preserving source lexical form separately.
- `float`/`double` parsing and comparison implement XML Schema/OWL rules for `INF`,
  `-INF`, `NaN`, signed zero, subnormals, rounding, and facets. Python/Rust hardware
  behavior is not assumed identical without bit-level tests.
- Numeric interval intersections retain open/closed endpoints and exclusions exactly.
- Cardinality of a restricted value space is computed or conservatively bounded
  exactly enough to decide the finite distinctness constraints requested by the
  tableau.

## 4. Strings, binaries, URIs, XML, and language tags

String derived types enforce XML Schema whitespace and lexical constraints exactly.
`pattern` uses XML Schema regex semantics, not Python/Rust/PCRE syntax. Compile the
supported regex language to a deterministic automaton or use an equivalently tested
engine; intersection, complement, and emptiness must support datatype reasoning.

The core literal model supplies the standards-defined separation of lexical text,
datatype/language, source spelling, and canonical language comparison. pyHermiT consumes
that representation without rewriting it. `langRange` uses normative basic filtering and
the core case-insensitive canonical tag key; it never applies locale-sensitive casing.
Binary parsers reject invalid padding/alphabet/whitespace and compare decoded octets.
`xsd:anyURI` retains the standards-defined lexical/value behavior without network
resolution. `rdf:XMLLiteral` validation/canonical equality uses a deterministic XML
library/normalization policy matched against HermiT/W3C fixtures and hardened against
external entities.

## 5. Date and time

Date-time parsing covers signed years as supported by the reference, fractional
seconds, timezone offsets, `24:00:00` rules where applicable, leap/calendar validity,
and required timezone for `dateTimeStamp`. Values without a timezone are not naively
assigned the local timezone; comparisons use the XML Schema partial ordering/possible
UTC interval. Bounds and equality follow that model. No result depends on machine
timezone, locale, or platform date range.

## 6. Data ranges

Each normalized range supports:

- `contains(value)`;
- an exact `is_empty_exact()` decision;
- `intersection`, `union`, and `complement` over the data domain;
- finite enumeration when applicable;
- a cardinality lower/upper classification sufficient for distinctness checks; and
- a deterministic witness/certificate operation for tests, not public answers.

Operations may use symbolic unions of intervals, automata, finite exclusions, and
datatype-family partitions. A cheap internal `emptiness_hint()` may return
`EMPTY | NONEMPTY | UNKNOWN`, but `UNKNOWN` MUST be refined by the complete exact path
before deriving a clash or returning SAT/UNSAT; it is never a public logical answer.
Complement is relative to the OWL data domain/range arity, not the host language
universe. Mixed datatype intersections account for overlapping numeric/value spaces
and disjoint families.

Custom datatype definitions are expanded through a validated acyclic dependency graph
or represented as named symbolic aliases. Recursive definitions invalid under OWL 2 DL
are rejected before reasoning.

## 7. Datatype constraint manager

Concrete nodes form constraint components through data-value identity/inequality and
data-role/cardinality requirements. For each dirty component, the manager collects:

- positive and negative data-range assertions with dependencies;
- fixed literal/value assignments;
- equality classes and pairwise inequality edges; and
- minimum distinct-value requirements introduced by data cardinalities.

It decides whether values can be assigned satisfying all constraints. A clash carries
dependencies for a sufficient contradictory subset; it must not include a missing
branch dependency that would make backjumping unsound. A slow exhaustive solver over
small finite generated domains serves as a property-test oracle.

Unknown-datatype compatibility mode treats only the cases justified by pinned HermiT's
unknown restriction semantics. The default is an explicit `UnsupportedDatatypeError`.
Unknown datatypes are never assumed empty, universal, or mutually disjoint without the
configured semantics.

## 8. Python and Rust implementations

The Python datatype library is the readable semantic implementation. Rust may use
specialized crates only after their license, lexical semantics, overflow behavior,
regex language, and date range are verified. Cross-backend fixtures serialize semantic
values in a language-neutral tagged format; neither side exchanges pickles or native
struct layouts.

All Rust arithmetic is checked or mathematically proved bounded. Panics on hostile
lexical forms are bugs. Large integers, regexes, enumerations, and facets honor resource
limits and cooperative cancellation.

## 9. Acceptance matrix

For every datatype/facet combination:

1. valid/invalid lexical boundary tables;
2. source-literal, data-value-identity, and datatype-comparison tables, including cases
   where exactly two of those relations agree;
3. boundary, complement, union, intersection, emptiness, and finite cardinality tests;
4. positive and negative ontology consistency/entailment cases;
5. equality/inequality and data cardinality interactions with backtracking;
6. HermiT black-box fixtures and applicable W3C tests;
7. generated Python/Rust exact parity cases; and
8. hostile size/complexity/cancellation tests.

Locale, timezone, hash seed, CPU floating mode, and supported platform cannot change a
canonical result.
