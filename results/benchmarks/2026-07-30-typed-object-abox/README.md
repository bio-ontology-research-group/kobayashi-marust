# Typed object-ABox bridge routing

This experiment broadens only the source-side candidate gate for the existing
`certified_nominals` portfolio. Object ABoxes without data assertions,
`SameIndividual`, complex role chains, self restrictions, imports, rules, or
the universal role may try the exact Konclude-derived completion bridge.

The source gate never certifies a result. The bridge independently checks the
normalized clauses, RBox, object-ABox, and nominal payload and either returns a
complete classification or defers. On defer, the nominal-aware CB worker
remains authoritative. No ontology identifier is inspected.

Local release validation at commit `2062501`:

- all 1,827 tests pass (1,794 library and 33 integration), with eight ignored;
- automatic 5107 matches Konclude exactly in 0.83 seconds;
- automatic 15672 matches Konclude exactly in 0.25 seconds;
- automatic 5184 matches Konclude exactly in 0.29 seconds.

The first IBEX submission, build `49638992` and dependent gate `49638993`,
did not run because the source archive had an extra directory level. Build
`49639796` corrected that packaging error. Its focused array `49639797` then
failed before invoking KM because `ore_canon.py` was absent from the deployed
harness. These are infrastructure failures and provide no reasoner evidence.

The repaired gate checks the selected route, demands an exact gold match for
5107, 15672, and 5184, and keeps 1481 as a terminal fail-closed resource
control.

Array `49641738` exposed a second missing runner dependency,
`tree_watchdog.py`, before KM classification began. The next submission
deploys both Python dependencies and performs an explicit import preflight.
That preflight passed before repaired array `49641798` was submitted. Results
are recorded only after all four tasks emit validated terminal rows.
