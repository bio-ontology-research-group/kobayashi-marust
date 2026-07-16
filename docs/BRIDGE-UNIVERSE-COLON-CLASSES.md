# Bridge classification universe: colon-localname classes

Status: fixed. Scope: `engine/src/orchestrate/cb_to_ht.rs` (`is_internal`),
consumed by `engine/src/konclude_ht/bridge.rs::bridged_classify`. No Lean
re-certification (this is bridge bookkeeping over which named classes are
eligible, not CB-calculus logic).

## The mechanism in the bridge

`bridged_classify` builds a `universe` of real named classes:

```rust
let universe: HashSet<usize> = tin.concepts.iter().enumerate()
    .filter(|(_, n)| !is_internal(n) && !is_bottom(n))
    .map(|(i, _)| i).collect();
```

`universe` is the set of classes allowed as subjects (when no explicit query
set is given) and, more importantly, as candidate SUPERS. Every super-position
of the classification is gated on `universe.contains(sup)`:

- `subs.retain(|&c| c == s || universe.contains(&c))` (candidate supers per
  subject),
- `saturation_known_pairs.retain(|(sub, sup)| … && universe.contains(sup))`
  (told/saturation-derived subsumptions),
- the `known_subsumers` emission filter (`c != s && universe.contains(&c)`).

A class excluded from `universe` therefore never appears on the right-hand side
of any emitted subsumption.

The purpose of `is_internal` is to drop two kinds of non-classes: frontend
synthetic markers (`Q_n`, `__…`, `aux_…`, `def_…`) and builtin vocabulary
(`owl:Thing`, `rdfs:Literal`, `xsd:integer`, …). Refuting a marker "candidate"
costs a full SAT search per subject, so the filter is a real performance and
correctness boundary (see the comment at the `universe` construction site).

## The defect

`is_internal` treated ANY name whose `short` form contains a `:` as internal:

```rust
|| (s.contains(':') && s != "Nothing" && s != "owl:Nothing")
```

`short(n)` strips the IRI up to the last `#` or `/`. A real named class can
still carry a colon after that:

- URN class IRIs, e.g. `urn:example:Foo` — `short` finds no `#`/`/`, returns the
  whole string, which contains `:`.
- Colon-bearing fragments, e.g. `http://ex.org/o#Part:Whole` — `short` returns
  `Part:Whole`.

Such a class was silently removed from `universe`. It could still be a subject
(its own supers were computed), but no subsumption `X ⊑ ThatClass` was ever
emitted, and the bridge's own soundness/completeness gate flagged neither an
unsound nor an incomplete result, because the class simply was not in the
classified set. This is a silent under-approximation, which the reasoner's
soundness+completeness contract forbids.

The production Rust orchestrator's mirror predicate (`orchestrate::mod.rs`) and
another `cb_to_ht` call site already guard the same heuristic with
`named.contains(n)` ("a declared class is always a query even when its spelling
resembles an internal frontend symbol"). The bridge's `universe` filter had no
such guard, so it was the one place the drop actually reached output.

## The fix

The colon clause now matches only reserved vocabulary prefixes — exactly the
builtins the heuristic is meant to catch — instead of every colon:

```rust
fn is_reserved_vocabulary_curie(s: &str) -> bool {
    matches!(s.split_once(':'),
             Some(("owl" | "rdf" | "rdfs" | "xsd" | "xml", _)))
}
```

This aligns with the frontend's own internal-name predicate
(`frontend::iri::reserved_internal_prefix`), which is prefix-based and does not
treat a colon as an internal marker (source localnames that look like markers
are escaped to `km_src_…`, never colon-matched).

## Why it preserves soundness and completeness

- **Strict narrowing.** The new predicate is a subset of the old one: fewer
  names are internal, so `universe` can only GROW. No real subsumer is ever
  removed by the change, and no new subsumption verdict is invented — added
  candidates still go through the ordinary saturation/probe path, which returns
  a genuine `true`/`false`.
- **Builtins still excluded.** Every builtin the old clause dropped is written
  with a reserved prefix (`owl`/`rdf`/`rdfs`/`xsd`/`xml`), so it is still
  internal. `owl:Thing`, `rdfs:Literal`, `xsd:*` remain excluded.
  `Nothing`/`owl:Nothing` remain owned by `is_bottom`, unchanged.
- **Corpus byte-identity.** No ORE 2015 class has a non-reserved-prefix colon in
  its localname, so the bridged classification signatures are unchanged on the
  corpus. The fix only changes behaviour on inputs that were previously handled
  incorrectly.
- **Scope.** The change touches only `cb_to_ht`, the HT-bridge feeder. The
  production CB engine output path (`reasoner.rs` → `orchestrate::mod.rs`) is not
  affected.

## Validation

- `cargo test --release --lib is_internal_excludes_markers` — the new unit test
  `is_internal_excludes_markers_and_builtins_but_keeps_colon_localname_classes`
  covers markers, reserved-prefix builtins, `Nothing`/`owl:Nothing`, ordinary
  classes, and the three regression cases (colon fragment, URN IRI, non-reserved
  CURIE).
- Full `konclude_ht` + orchestrate suite — no regression (the change is additive
  and gated on the reserved-prefix set).
