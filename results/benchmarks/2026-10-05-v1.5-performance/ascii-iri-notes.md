# Restricted ASCII HTTP IRI validation

The existing compact grammar already suppresses unused structural parse-tree
nodes. The remaining candidate targets the full RFC grammar call for every
distinct IRI spelling. It is opt-in with KM_ASCII_IRI_GRAMMAR; the default
validator is unchanged.

The fast predicate accepts only angle-bracketed lowercase HTTP/HTTPS IRIs with
an alphabetic-first, nonempty ASCII-unreserved host; a slash-separated path
of ASCII-unreserved characters; and at most one fragment delimiter with the
same character set plus slashes. Queries, ports, user information, escapes,
Unicode and numeric-leading hosts use the original FullIRI parser.

This is a sufficient subset of the pinned grammar: the scheme matches;
the authority selects RegName; each path segment consists only of IpChar;
and the fragment consists of IpChar or slash. Requiring an alphabetic first
host byte excludes the earlier IPv4 alternative, including its possible
partial-consumption behavior. This optimization preserves the original PEG
acceptance, not just an independent interpretation of RFC-valid IRIs.
Structural parse failures, invalid IRIs and description-graph extensions still
invoke the original validator, preserving refusal text and locations.

The six existing unit tests pass before the change. Seven pass afterward,
including ASCII mutations in host/path/fragment positions, boundary cases,
and exact original/new validation comparisons. The known-prefix grammar
itself is unchanged. All 18 local paired checks agree exactly.

| Input | Cached grammar mean seconds | ASCII subset mean seconds | Repetitions |
| --- | ---: | ---: | ---: |
| 236 | 0.041747 | 0.034794 | 6 |
| 11896 | 0.038223 | 0.026481 | 6 |
| 3250 | 0.000731 | 0.000425 | 6 |

These grammar-only workstation diagnostics use one CPU and alternating arm
order. They do not establish a classification speedup or release readiness.
Job 53341336 compares exact results and errors across all 1,920 frozen inputs
with the original per-arm 240-second, 20-GiB limits. All four production Lean
gates passed with the new flag enabled against a pinned 819-file source
manifest, with no sorryAx. Their receipt rechecks every source hash. This does
not replace the pending corpus equivalence and end-to-end performance checks.
