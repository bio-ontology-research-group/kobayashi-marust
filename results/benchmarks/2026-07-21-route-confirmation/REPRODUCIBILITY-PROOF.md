# Reproduced ORE route ledger proof

*2026-07-21T23:01:21Z by Showboat 0.6.1*
<!-- showboat-id: 97de580b-d5f0-412c-8b00-122e746c6763 -->

This document verifies the committed 592-ontology ledger against the external SHA-256 values from the successful IBEX receipt. The expensive reasoner replays are hash-bound in each ledger row; these local checks are reasoner-free and safe to rerun.

```bash
sha256sum reproduced-route-ledger.tsv reproduced-route-ledger-receipt.json
```

```output
7db5b5b3c645cb2f37e515d215808ef3de499249c7a2d3fd22ec50771e64f354  reproduced-route-ledger.tsv
859614e066d0d7c890adf7c9d8d3cd4220276ae9bccf9608f24b3a6ac6e49a02  reproduced-route-ledger-receipt.json
```

The verifier independently checks row uniqueness, state and evidence-origin counts, route observation identities, commands, limits, source and runtime hashes, fresh oracle hashes, and exact-source receipts.

```bash
python3 verify_reproduced_route_ledger.py --ledger reproduced-route-ledger.tsv --receipt reproduced-route-ledger-receipt.json --expected-ledger-sha256 7db5b5b3c645cb2f37e515d215808ef3de499249c7a2d3fd22ec50771e64f354 --expected-receipt-sha256 859614e066d0d7c890adf7c9d8d3cd4220276ae9bccf9608f24b3a6ac6e49a02
```

```output
{"ledger_sha256": "7db5b5b3c645cb2f37e515d215808ef3de499249c7a2d3fd22ec50771e64f354", "nonclaims": ["ore_ont_10860.owl", "ore_ont_1194.owl", "ore_ont_4669.owl"], "origins": {"current_alternative_route": 3, "current_selected_route": 578, "exact_source_candidate_route": 3, "exact_source_historical_route": 5, "none": 3}, "reproduced_claims": 589, "rows": 592, "states": {"not_a_documented_solve_claim": 3, "reproduced_adjudicated_inconsistent": 2, "reproduced_exact_full_iri": 579, "reproduced_exact_source_candidate_full_iri": 3, "reproduced_exact_source_historical_full_iri": 5}, "status": "verified"}
```
