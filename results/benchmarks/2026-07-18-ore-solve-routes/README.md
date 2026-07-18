# ORE 2015 per-ontology KM solve routes

`ontology-solve-routes.tsv` is the actionable route registry for the complete
592-ontology ORE 2015 corpus. It has exactly one row per ontology. For every
gold-exact row it records the route, full environment, copyable invocation,
measured wall time and peak RSS, binary SHA-256 and retained evidence.

All `exact_gold` rows completed under the same outer limits:

- 240 seconds;
- 20 GiB process-group peak RSS;
- 16 CPUs.

## Coverage represented by the TSV

| State | Ontologies | Meaning |
|---|---:|---|
| `exact_gold` | 586 | KM completed within the limits and matched usable gold. The source-IRI fix closes 3524, 13503 and 15703; 7581 also passes a fresh full-IRI regression check. |
| `completed_incorrect` | 1 | KM completes 4669 within the limits, but direct HermiT queries prove its returned UNSAT set unsound. |
| `adjudicated_correct_stale_gold` | 2 | 2669 and 15516 are correctly classified as inconsistent; their stored Konclude signatures are parse-failure artifacts. |
| `no_complete_within_limit_valid_gold` | 1 | 10621 has fresh Konclude gold that matches the current stored signature, but full KM classification exceeds the limits. |
| `unresolved_no_authoritative_gold` | 2 | 10860 and 1194 have neither authoritative full gold nor a retained complete KM run. |

The detailed [`TAIL-EIGHT.md`](TAIL-EIGHT.md) audit records fresh isolated IBEX
runs, independent comparisons, counterexamples, exhausted route history and a
follow-up collision audit and the validated source-IRI repair. It is the
authoritative interpretation of the six ontologies now outside `exact_gold`.

Direct validation leaves 588 correct KM classifications: the 586 gold-exact
rows plus the two adjudicated SWRL parse-failure cases. A route that merely
terminates is not counted. Ontology 4669 remains completed but unsound.

The 586 exact rows are a union over pinned binaries and configurations. They
must not be reported as the coverage of one current KM binary. The base
registry contained 577 distinct local-name-exact ontologies. Direct full-IRI
validation removes 13503, leaving 576 from that base. The 2026-07-18
retained-route rerun adds seven previously missing exact ontologies and
rechecks two existing ones, 10908 and 11745, with improved measurements. The
special-source-IRI fix then restores 13503 and closes 3524 and 15703, while a
fresh run confirms that 7581 remains exact.

## Route selection

For the 573 exact ontologies outside thirteen directly rechecked targets, the TSV
selects the verified `production_all` row. For the targets below it records the
configuration run on IBEX on 2026-07-18:

| Ontology | Selected route | Wall (s) | Peak (MB) |
|---|---|---:|---:|
| 3215 | `kpset_barrier` | 227.8271 | 8445.90 |
| 3524 | fixed `production_all`, full-IRI exact | 27.7082 | 4600.92 |
| 6934 | `htforce_race` | 0.3264 | 67.18 |
| 7499 | `card_race` | 92.8130 | 18512.07 |
| 7581 | fixed `production_all`, full-IRI recheck | 19.4446 | 4318.46 |
| 9540 | `card_race` | 43.5480 | 18487.62 |
| 9635 | `legacy_tab_race` | 0.3548 | 66.56 |
| 10702 | `nomlink_default` | 20.2885 | 512.94 |
| 10908 | `shoq_race` | 0.4138 | 261.46 |
| 11745 | `production_all` | 27.8859 | 3124.53 |
| 13503 | fixed `production_all`, full-IRI exact | 0.0618 | 7.10 |
| 15672 | `shoq_race` | 4.7801 | 831.89 |
| 15703 | fixed `production_all`, full-IRI exact | 24.4224 | 4350.15 |

`other_verified_exact_routes` lists the other route labels that independently
matched gold for that ontology in the frozen all-route registry. The selected
route remains the production route where it works, except for the explicit
retained-route targets above.

The retained routes are per-ontology empirical witnesses. In particular,
`legacy_tab_race` is documented only for ontology 9635 and is not a general
benchmark fallback. A route should not be generalized to a different ontology
without the normal soundness and completeness validation.

## Evidence and provenance

The frozen all-route source registry is archive member
`results/benchmarks/2026-07-16-routing-complete592/ontology-routes.tsv` in:

```text
ibex:/ibex/scratch/hohndor/km/routing_20260715/candidates/feb0cc6/source.tar.gz
```

Its SHA-256 is:

```text
90eff8539618605b1ccdef5b367518ea8cbc5f6a19d14deabe909abef86e64ea
```

Nine retained-route exact result rows are under
`evidence/retained-route-rerun/`. Fresh direct-validation metadata for the tail
and the source-IRI fix is under `evidence/direct-validation/`; the older
completion-only rows remain under `evidence/completed-no-gold/` as historical
records. The final rebased binary SHA-256 is
`6dd3a33c62018b177c01967af5784303c7b18f2657f730ec60643d1fb4e227df`.
The TSV's `binary_locator` field points to the exact retained IBEX executable,
and `binary_sha256` prevents a path from being mistaken for a stable binary
identity.

Failure diagnoses and the distinction between completed, adjudicated and
gold-exact results are documented in [`TAIL-EIGHT.md`](TAIL-EIGHT.md).

## Regeneration and checks

After extracting the frozen source registry, regenerate the TSV with:

```bash
python3 build_ontology_solve_routes.py \
  --base-registry /path/to/ontology-routes.tsv \
  --retained-evidence evidence/retained-route-rerun \
  --direct-validation evidence/direct-validation \
  --output ontology-solve-routes.tsv
```

The builder fails unless all of the following hold:

- the frozen registry hash matches;
- all 592 ontology names occur exactly once in the output;
- the state counts are 586, 1, 2, 1 and 2 as listed above;
- every `exact_gold` row has a complete route, binary, gold, signature and
  evidence record;
- every `exact_gold` measurement is within 240 seconds and 20 GiB;
- all nine retained-route JSON rows are `status=ok`, `verdict=match`, use 16
  CPUs and report zero signature differences.
- direct evidence proves the fixed 3524 and 15703 outputs preserve all 123,310
  strict told subsumptions and match Konclude's full-IRI taxonomy;
- direct evidence proves fixed 13503 emits the legal `daml+oil#Nothing` source
  class as UNSAT, matching Konclude and HermiT;
- 7581's fixed KM output and Konclude full-IRI taxonomy match exactly over a
  shared source declaration universe;
- the remaining 4669 output has retained HermiT counterexamples.
