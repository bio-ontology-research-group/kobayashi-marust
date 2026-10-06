# Completed finite-role-index diagnostic sweep

Job 53329459 completed all 1,920 frozen inputs at 240 seconds, 20 GiB and one CPU. It produced 1,622 complete outputs on admitted inputs, of which 1,621 have independent corroboration. The remaining output is ore_ont_4669. Admitted failures comprise 26 process errors and 60 timeouts. All 212 invalid inputs remain refusals. There are zero audit errors.

Verified-success mean wall time is 8.312185 seconds and median wall time is 0.442573 seconds. These are descriptive results for the pinned diagnostic binary. The earlier single-worker baseline was built with production LTO/codegen settings; see build-profile-comparison-notes.md. Neither source-only regression attribution nor release performance approval follows from this comparison.

Relative to the complete single-worker sweep, 12898 and 13799 gain verified results while 1123 loses one, for a net gain of one. The candidate needs 35 additional net verified results to exceed Konclude's recorded 1,655. It does not meet v1.5.0 acceptance. The IRI-cache full sweep and a production-profile build remain active; incremental acceptance is unchanged.
