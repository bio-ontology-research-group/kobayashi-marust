# Completed IRI-cache diagnostic sweep 53332943

All 60 chunks completed, retaining all 1,920 frozen inputs: 1,708 admitted and
212 invalid. The pinned diagnostic-profile binary verified 1,620 solves, with
arithmetic mean 7.365632 seconds and median 0.401102 seconds. It produced 1,622
outputs; admitted failures were 27 process errors and 59 timeouts. All 212
invalid inputs were refused. One output, 10689, retains its original audit
failure; a later artifact does not replace the failed audit outcome.

Against v1.4.5, this candidate gains 33 verified solves and loses four, a net
29. On the 1,587 shared verified cases, its mean/median is 6.165/0.376 seconds
versus 10.480/0.690 seconds for v1.4.5. It remains behind Konclude: on 1,609
shared cases, 6.420/0.393 seconds versus 2.863/0.263 seconds. It has 46 losses
and 11 gains against Konclude, a net deficit of 35; exceeding Konclude needs
36 additional net verified solves from this candidate's total.

The candidate uses no LTO and 16 codegen units and predates classifier snapshot
reuse. It does not isolate the effect of IRI caching relative to production
builds. Production-profile sweep 53334551 and graph-output sweep 53338465 remain
the relevant pending measurements. No release requirement is declared met.

The final summary validates frozen inputs, artifact and runner hashes, flags,
chunk positions, and recorded comparison outcomes. It preserves every failure.
