# Exact Hyper narrowing on ORE 1194

This gate evaluates commit `1ef8ee1`, which combines the exact Hyper
candidate narrowing from `7902085` with the dense CB subsumption screen and
staged local Pred join from `1ef8ee1`.

The Hyper change performs a semijoin reduction over body-position postings and
uses an exact-predicate index when the current substitution determines a body
atom. It leaves every surviving branch to the existing unifier and preserves
candidate order. Differential tests compare complete ordered resolvent traces
against the generic join, including grounded substitutions, and a saturation
test compares final classifications with the optimization enabled and disabled.

## Local workstation gates

Host: `leechuck-office`. Input: `/tmp/1194.clauses.json`, 1,062,240 clauses.
Command shape: single-threaded CB worker with no named query roots,
`KM_THREADS=1 KM_QUERIES=__none__`, under a 245-second wall cap.

| tree | wall | peak RSS | result |
|---|---:|---:|---|
| Hyper narrowing only (`7902085`) | 245.18 s | 2,171,400 KiB | timeout, no output |
| Hyper + ClauseSig + staged Pred (`1ef8ee1`) | 245.17 s | 2,470,112 KiB | timeout, no output |

A trace-enabled diagnostic confirmed that the narrowing fires on the target
qualified-cardinality clauses. Representative raw products of 4,320,000 and
2,784,800 candidates became 145,200 and 80,000 candidates respectively. The
trace was stopped and the timing gates were rerun without tracing so diagnostic
I/O could not affect the reported wall times.

The optimization therefore removes the identified Cartesian Hyper blow-up but
does not recover ORE 1194 by itself or in combination at the benchmark limit.
The complete combined release suite passed 1,950 library tests and every
integration suite with zero failures.
