# Classification analysis phase diagnostic

Job 53332023 completed its three instrumented attempts. Ontology 13242 produced an independently corroborated answer; 13276 and 16680 timed out. All required timer groups are present, but this does not establish an unbiased performance comparison.

The seven inner analyser phases account for only part of the outer analysis timer. Per-event stderr logging and container destruction can contribute to the difference. Do not attribute that difference to a single algorithm or sum nested timer groups. The two timeout outcomes remain failures, and this experiment changes no release solved count.

The original job 53331735 is retained separately as an observability failure because worker logs were not forwarded. The corrected runner enables forwarding with KM_HT_STATS.
