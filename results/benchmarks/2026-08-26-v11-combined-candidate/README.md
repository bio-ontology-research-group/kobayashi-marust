# v11 combined source-bound candidate

This candidate combines the v10 feature-selected general-HT routes with the
proved positive empty-source projection promoted after the complete source
census and exact three-arm panel. It is not a release until its own exact
panel, complete 592-ontology sweep, strict correctness audit, and external
aggregate gates pass.

The frozen source archive is `v11-source-20260826.tar.gz`, SHA-256
`02f38c0f33ff5dee64f258ba6739394d7c3478da30bad99a6d94c569137d4d29`.
Before freezing it, all 15 release-mode flat-source tests passed. The routing
suite had already passed all 45 tests before the default promotion; promotion
changes only the source-screen activation condition.

Source-bound build job `50865608` completed in 4 minutes 15 seconds. The v11
binary SHA-256 is
`decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c`.

Sanity job `50865813` passed one positive-source hit, retained HT routing on
ORE148, and the large ORE3377 miss control. Full exact panel `50865832` then
passed all 19 rows with byte-identical v10/v11 answers and no errors. Exactly
15 traces select `positive_empty_source`, both ORE148 and ORE7499 retain
`ht_general`, and ORE3377/ORE7246 retain their prior routes. Across the panel,
wall total falls from 65.00 to 42.54 seconds and summed process-tree peak RSS
falls from 7,766.0 to 4,032.9 MiB.
