# KM 1.6.3 release notes

Released 2026-11-13 (tag `v1.6.3`).

## What changes

KM 1.6.3 extends the proved OWL reference procedure of v1.6.2 from OWL EL
and OWL ALC to SHI: ALC with inverse roles, role hierarchies and
transitive roles. It also makes the Protégé plugin installable from
Protégé's plugin list, with km bundled for five platforms. No theorem of
v1.6.0 to v1.6.2 changes. Plan: `docs/V1.6.3-HT-PLAN.md`.

- **Normal form and translation.** `translateSRI` turns an OWL ontology
  into the SRI normal form (inverses and role chains);
  `translateSRI_correct` shows that subsumption between named classes is
  the same before and after.
- **A procedure that finishes on large inputs.** v1.6.2 decided ALC by
  type elimination, which is exponential in the number of concept names,
  so it declined inputs above 16 names. v1.6.3 builds only the candidate
  types the rules can reach from the requested names, closes them under
  the rules and then eliminates (`classify_spec`). The executable version
  (`classifyF`, sorted-list types, a seed cache, per-role tables) has the
  same statement (`classifyF_spec`). Transitive roles are removed first by
  `encTrans` (`encTrans_correct`).
- **The capstone.** `owlSRIReference_sound`: every answer of the SHI route
  is exact for `OWL.EntailsSub`. `owlSRIReference_complete`: it publishes
  on every OWL SHI ontology (`OWL.Ontology.isSHI`: role chains only as
  inclusions `r ⊑ s` or transitivity `r ∘ r ⊑ r`). `owlReferenceSHI`
  tries the EL route first, then SHI; it is sound, and complete on OWL EL
  and OWL SHI, which includes OWL ALC.
- **`km-owl-reference`.** New `--procedure sri` and `el-then-sri`; the
  default is `el-then-sri` with no concept budget. It declines inputs with
  other role chains and names the first such axiom.
- **`KM_FRONTEND_CHECK=1`** compares km's answer with the `el-then-sri`
  route. Off by default.
- **Protégé plugin.** One jar per Protégé line
  (`kobayashi-marust-protege5-1.6.3.jar`, `kobayashi-marust-protege6-1.6.3.jar`),
  each with km for linux-x86_64, linux-aarch64, macos-x86_64,
  macos-aarch64 and windows-x86_64. The plugin unpacks the matching km to
  a per-user cache on first use and checks its SHA-256 sum; `km.bin` and
  `KM_BIN` still take precedence. The engine gained `cfg` gates so it
  compiles on macOS and Windows; Linux behaviour is unchanged.

## Coverage

`km-sri-probe` (the Lean executable of the SHI route), 60 s per input on
the workstation:

| set | finished | timed out | declined (other chains) |
|---|---:|---:|---:|
| the 84 suite inputs v1.6.2 declined as neither EL nor ALC | 68 | 12 | 4 |
| the 25 inputs over the v1.6.2 ALC budget | 22 | 3 | 0 |

The 12 timeouts all have many disjunctions. Role chains beyond
transitivity stay outside the proved route.

## Checks for this release

The engine's production routes did not change since v1.6.2 (the only
Linux change is the procedure that the off-by-default `KM_FRONTEND_CHECK`
calls), so the v1.6.2 speed and correctness records stand. Run for this
release: the engine library tests, the routing gate's `km-owl-reference`
checks, and the Protégé CI on all five platforms (km built and run on
each; both jars built with 86 tests passing; installation tested in
Protégé 5.6.9 and 6.0.0-alpha-1 with the bundled km). The Ibex
`KM_FRONTEND_CHECK` suite with the SHI route follows as a separate record.

## Known issues

- Issue #5: v1.6.2 and later time out on an ontology with many negated
  quality classes (the `production_all` race); the same ontology without
  the negations classifies in about 1 s.
- macOS and Windows: km runs on both (CI), but the plugin has been tested
  inside Protégé on Linux only. The macOS binaries are not signed.

## Assets

`kobayashi-marust-protege5-1.6.3.jar`, `kobayashi-marust-protege6-1.6.3.jar`
(attached by CI), and the km executables built by CI for the five
platforms (release profile, not PGO).
