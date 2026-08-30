# v1.3 automatic bridge acceptance

This gate validates the two ORE 2015 profiles selected by the automatic
`ht_bridge` route and exercises source-axiom explanation extraction through
that route. It runs on IBEX compute nodes, not on a login node.

## Provenance

- Source commit: `5c981fd` (`development/v1.3`).
- IBEX-native build job: `51003931`.
- Acceptance job: `51003988`.
- Binary SHA-256:
  `586ee9db68ecf50fb54be44b877c64220dea66de271cf52c33ce84abf02f651c`.
- Remote evidence root:
  `/ibex/scratch/hohndor/km/v13-bridge-acceptance-20260830`.

The build verifies the source-archive checksum, uses `cargo build --release
--locked --bin km`, records `ldd`, records the route inventory, and installs
the resulting binary only after a successful build.

## Incremental results

For both `ore_ont_9944.owl` and `ore_ont_11311.owl`, the gate:

1. opens one complete-source session and requires `route=ht_bridge` and
   `retained_backend=true`;
2. inserts one named-class inclusion while preserving the automatic route;
3. compares consistency, dropped count, unsatisfiable classes, and the set of
   subsumption pairs with a fresh `km classify` process;
4. removes the inclusion and requires the original canonical result exactly.

Both ontologies pass. The changed-result digests are:

- 9944: `acd277fc6a45dd0d50e3c13d1b72da1108606494969ef6698fc720e3c6f0b7e0`
- 11311: `6e67a93e258b7c2a0f09ac0b745add49d2b28365905c0cd1544425918036a1ba`

Both source graphs form one dependency component, so the tested edits
correctly report `exact_rebuild`, zero retained query rows, and no route
migration. Meaningful bridge reuse is separately covered by
`bridge_disconnected_changes_reuse_unaffected_subject_rows` and
`bridge_concept_replacement_reuses_a_disconnected_subject_component`, which
compare retained results with fresh bridge classifications for addition,
removal, and replacement.

## Explanation result

The automatic route explains
`CHEBI_15355 SubClassOf CHEBI_35287` in ORE 9944. The result contains the exact
source axiom as a one-axiom support, reclassifies it successfully, proves it
subset-minimal, and uses 25 classification checks. The one-justification bound
is reached, so the report correctly sets `enumerationComplete=false`; it does
not claim that no alternative support exists.

## Soundness regression found by the gate

Job `51003818` found nine extra subsumptions before the final fix. The
complete-source constructor allowed an automatic `ht_bridge` profile to enter
the ordinary typed-HT adapter before the exact bridge supervisor. Commit
`5c981fd` prevents both ordinary HT and quasi-order adapters from intercepting
`ht_bridge` initialization or fallback. The final job proves zero missing and
zero extra pairs against fresh classification after this fix.
