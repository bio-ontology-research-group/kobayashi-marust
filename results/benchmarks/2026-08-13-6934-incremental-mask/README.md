# ORE6934 incremental label-mask candidate

This experiment added two incrementally maintained 64-bit masks per tableau
node as a necessary-condition filter before the exact subset check. Concept
insertions updated the masks in constant time; backtracking rebuilt only the
label actually shrunk. Mask collisions could only cause an exact check and
could not change blocking decisions.

IBEX build job `50437174` produced binary
`04078554e13769bbc132634e186482e25cd5966e3154a4fe4e22cd6ec0ecf4f9`.
Same-node exact-gold panel `50437283` measured:

| Arm | Wall | Peak RSS | Verdict |
|---|---:|---:|---:|
| v0.2.11 | 116.4807 s | 3053.98 MiB | exact match |
| incremental-mask candidate | 148.6096 s | 3045.44 MiB | exact match |

The candidate saved 8.54 MiB but regressed wall time by 27.58%. The masks did
not reject enough candidates to repay their maintenance and hot-loop checks.
The candidate was rejected and fully removed.
