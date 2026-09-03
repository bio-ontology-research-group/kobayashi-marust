# Stack-polarity NNF experiment

Commit `4994c254d1ff3d7cd648abe063d8b21e67c1eb0a` replaced the frontend's
clone-based negation-normal-form recursion with a polarity bit carried on the
call stack. A differential unit test retained the prior implementation as an
oracle and compared positive and negated forms of every concept constructor.
The focused test and all 169 frontend tests passed.

IBEX build job `51279755` produced binary SHA-256
`be0d5bb1a5043470f26455e0cb6b167fffcadc488e545c015e9790b2b0bb7e54`
from source archive SHA-256
`cc01274c7e0b0c0597676520bbfc45e1acef9d735fa58604c15bf3bf207ee5bc`.
Frontend job `51282081` compared that binary with parent binary
`420d607931b0d72c8e2c712b19ca33efc53f831c7ac3c14a5e42c034c0f2bf72`
over all 64 current performance residuals, interleaved with three repetitions
per arm.

The corrected job produced 192/192 paired records and ended with
`PANEL_COMPLETE`. Every pair had byte-identical normalized clauses and metadata.
Among the 52 ontologies whose parent median frontend wall time was at least
0.05 seconds, both the median wall ratio and median peak-RSS ratio were 1.000.
The apparent per-ontology changes were at timer-noise scale and were not
consistent across the panel. The result ledger SHA-256 is
`1157b6eb74f082ad9ab3d0cfbae6d6c0d6e7cfc3d046ec7bf6e14a3e4277e252`;
the completion log SHA-256 is
`79200d9ad78a618dbda3d2d469783d112278d35fb8595ddd4dcc62d478db0f85`.

The optimization was therefore rejected and reverted by commit `558da33`.
KM retains the simpler NNF implementation and the strict score remains
525/589.

An initial attempt, job `51279770`, was cancelled after live monitoring caught
a harness quoting error that made `sha256sum` receive literal quote characters.
Its partial output was deleted and is not evidence. Job `51282081` uses direct,
fail-fast hash assignments and is the only accepted panel.
