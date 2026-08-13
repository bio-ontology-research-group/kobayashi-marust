# ORE6934 persistent-index candidate

This experiment followed the ORE6934 blocking profile in
`../2026-08-13-6934-tail/`. It combined suffix-only status recomputation with
the existing persistent all-node literal posting index. Consulting blocked
nodes as blocker candidates is result-identical because each such node has an
earlier unblocked label superset, which is transitively also a blocker.

IBEX build job `50436942` produced binary
`59444c8a7473d6ce950468f9a7a0ff85be87d1acf8f9664cf74280e109701685`.
Same-node exact-gold panel `50437030` measured:

| Arm | Wall | Peak RSS | Verdict |
|---|---:|---:|---:|
| v0.2.11 | 116.9666 s | 3052.32 MiB | exact match |
| persistent-index candidate | 123.6060 s | 3047.50 MiB | exact match |

The candidate saved 4.82 MiB but regressed wall time by 5.68%. Avoiding
posting-list rebuilds did not compensate for scanning longer lists that also
contained blocked nodes. The candidate was rejected and removed. Future work
should reduce blocking-pass frequency or dirty-suffix width while retaining
the shorter unblocked-only candidate lists.
