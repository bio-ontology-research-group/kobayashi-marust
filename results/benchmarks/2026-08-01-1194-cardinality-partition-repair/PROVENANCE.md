# Provenance of this evidence, and what landed

Every log and table in this directory was produced on 2026-08-01 by an
experimental binary built from a branch rooted at `4faad8a` ("Report residual
clause shape and repair-round cost for ORE 1194"), which is not an ancestor of
this branch. That binary carried two changes together:

1. **Cardinality-aware partition assignment**: the pinned-witness recogniser,
   the qualified at-most recogniser, the identification-legality filter on
   merges, and the demotion of a locally unsatisfiable partition side.
2. **A rotated residual scan** with an environment-exposed violation cap
   (`KM_ELC_VIOL_CAP`).

**Only the first landed on this branch**, as "Guide certificate repair with
qualified-cardinality shapes". The rotated scan is a separate enumeration-order
change and was not ported: this branch instead carries the certificate index
reuse of `e05b35c`, which attacks the same per-round scan cost by keeping the
join's enumeration index across rounds, and whose correctness argument rests on
the enumeration order being byte-identical to a full rebuild.

Consequences for reading the tables below:

- The **conflict and restart counts** are attributable to the cardinality half
  alone. The README says so directly: `card_demoted` is 0 on 1194, and what
  removes the conflicts is the identification-legality filter. The
  "partition assignment only" row (7 restarts to 0, scan unchanged at 1.7 to
  12.5 s) isolates it.
- The **per-round scan times** in the "plus rotated scan" row, the
  `KM_ELC_VIOL_CAP` rows, and `gate-cap1m-240s.log` measure the half that did
  not land. They do not describe this branch.
- The **phase accounting** (96.2 s of parse and EL saturation, 1.8 s to fork,
  one incomplete round applying a role-bridge clause family) is a property of
  the ontology and the model scale, not of either search change, and still
  describes where the 1194 budget goes.

Nothing here was re-measured on current HEAD. The 1194 gate remains a timeout
and the automatic route for 1194 is `nominals`, which sets `KM_NO_ELC=1`, so no
certificate worker runs on the production row either way.
