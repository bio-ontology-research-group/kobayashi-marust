# Round-23 re-closure: what it costs, and why the NF4 index fix does not help

The gate on ORE 1194 is consumed by one repair round: round 23 applies the first
of 14 inverse role bridges and re-closes under the EL rules. This document
measures that closure, records a fixpoint-preserving optimization of the rule it
is dominated by, and reports that the optimization buys nothing.

## The closure is convergent, and NF4 dominates it

`KM_ELC_CLOSE_TRACE=N` reports the rule counters every N worklist items. On the
pre-optimization binary, round 23's re-closure gives
(`round23-close-trace-300s.log`):

```
t=13.1s  popped=20000000  queued=15880616 | nf2=269042094 nf4_sub=297194265  nf4_edge=58722373
t=30.4s  popped=40000000  queued=17983781 | nf2=386403074 nf4_sub=802389474  nf4_edge=269232921
t=50.3s  popped=60000000  queued=16679183 | nf2=476460743 nf4_sub=1406207893 nf4_edge=622678369
t=70.4s  popped=80000000  queued=15042665 | nf2=514590090 nf4_sub=2116375356 nf4_edge=1100493220
t=88.2s  popped=100000000 queued=9777266  | nf2=529435347 nf4_sub=2774678153 nf4_edge=1587468555
t=102.2s popped=120000000 queued=778147   | nf2=543733158 nf4_sub=3320505443 nf4_edge=2043321446
```

Two things to read off it.

The queue drains: 15.9M, 18.0M, 16.7M, 15.0M, 9.8M, 0.78M. The closure is
converging, not diverging, and it takes about 105 s.

The rule mix at the last sample:

| rule | scans | share |
| --- | --- | --- |
| `nf4_sub` | 3,320,505,443 | 55.5% |
| `nf4_edge` | 2,043,321,446 | 34.2% |
| `nf2` | 543,733,158 | 9.1% |
| `nf1` | 47,167,302 | 0.8% |
| `nf3` | 26,238,605 | 0.4% |
| `nf7`, `botback` | 0 | 0% |

NF4 is 89.7% of all rule scans.

## The optimization

The Sub-NF4 rule fires an axiom `∃s.d ⊑ e` at a backward link `(parent, role)`
into `c` when `role == s`. It was scanning every axiom on the filler for every
backward link and discarding the mismatches:

```rust
while k < st.in_edges[c].len() {
    let (parent, role) = st.in_edges[c][k];
    for &(s, e) in axs {                 // every axiom, every in-edge
        if role == s { st.add_sub(parent, e); }
    }
    k += 1;
}
```

so the probe count is `|in_edges[c]| × |axs|`, and on 1194 the bridged roles
carry 144,130 `∃R.C ⊑ D` axioms. Sorting `nf4_by_filler` by role at index-build
time makes the axioms for one role a contiguous range, which binary search takes
directly:

```rust
let lo = axs.partition_point(|&(s, _)| s < role);
let hi = axs.partition_point(|&(s, _)| s <= role);
for &(_, e) in &axs[lo..hi] { st.add_sub(parent, e); }
```

**Why the derived fixpoint is unchanged.** The rule's conclusions are exactly
`{ add_sub(parent, e) : (parent, role) ∈ in_edges[c], (s, e) ∈ axs, role == s }`.
Sorting `axs` reorders a set without adding or removing members, and the
equal-range `axs[lo..hi]` is precisely the subset with `s == role`, since the
sequence is sorted on `s`. So the same axioms fire at the same backward links,
and only the probes that the `role == s` test used to reject are skipped. The
order in which they fire differs, which does not matter: EL saturation is
monotone and confluent, `add_sub` is idempotent, and the loop runs to a fixpoint
over the worklist. The `prop` registration loop above still walks every axiom,
so the propagation store is filled identically; reordering the pushes into
`prop[(c,s)]` does not change the set of conclusions the Edge rule later draws
from it.

## Result: 77% fewer probes, no time saved

The same run with the sorted-role index, matched at identical worklist
positions:

| popped | wall pre | wall with fix | `nf4_sub` pre | `nf4_sub` with fix | `nf4_edge` (both) |
| --- | --- | --- | --- | --- | --- |
| 20,000,000 | 13.1 s | 14.3 s | 297,194,265 | 72,347,642 | 58,722,373 |
| 40,000,000 | 30.4 s | 30.3 s | 802,389,474 | 193,388,888 | 269,232,921 |
| 60,000,000 | 50.3 s | 48.4 s | 1,406,207,893 | 340,588,224 | 622,678,369 |
| 80,000,000 | 70.4 s | 68.7 s | 2,116,375,356 | 508,286,337 | 1,100,493,220 |
| 100,000,000 | 88.2 s | 87.3 s | 2,774,678,153 | 652,858,051 | 1,587,468,555 |
| 120,000,000 | 102.2 s | **102.3 s** | 3,320,505,443 | **758,834,718** | 2,043,321,446 |

The fix removes 2,561,670,725 probes, 77% of them, and the closure reaches the
same point at the same time. The probes it removed were sequential comparisons
over a contiguous `Vec`, which the hardware predicts and prefetches; they were
never the cost. The counter was a bad proxy for time, and reading it as one is
the mistake this measurement corrects.

## Where the time actually is, and why it is not reducible here

What remains at the same point is the work the fixpoint itself requires:

- 120,000,000 worklist items popped, about 1.18M items/s;
- 2,043,321,446 `nf4_edge` propagation firings, each an `add_sub` hash probe,
  which at 20 ns is about 41 s on its own;
- 543,733,158 NF2 scans.

The `nf4_edge` count is the ELK backward-link join, already a single hashmap
lookup per edge. Its total is `Σ over new edges of |prop[(d,r)]|`, so on a
structure with 43,891,310 edges it is a property of the model, not of the
implementation. Every one of those firings is a conclusion the fixpoint has to
consider; firing fewer of them means deriving less, which is exactly what may
not change.

That is the wall. One bridge costs about 105 s of re-closure, and the residual
holds 14 of them at indices 177 through 190:

```
96.2 s base saturation + 1.8 s fork + 42.3 s covers + 14 × ~105 s ≈ 1,610 s
```

against a 240 s gate, about 6.7 times over.

## Gate

| run | budget | status | wall | peak RSS | output bytes | taxonomy |
| --- | --- | --- | --- | --- | --- | --- |
| sorted-role NF4 candidate | 240 s / 20 GiB | 124, timeout | 240.77 s | 8,949,092 KiB | 0 | none |

22 rounds completed, 0 conflicts, 0 restarts, round 23 incomplete. The output is
0 bytes and does not parse. **1194 does not close, so this candidate is not
proposed for integration.**

Serial release suite on this candidate: 1,883 passed, 0 failed, 8 intentional
ignores, rc=0, across the library and every integration target. The change is
green; it is simply not a speedup.

Binary SHA-256 `d98316966431045d9bbdbc5ec117872a12aa7e2cebefe4959893cddeb615fede`,
working-tree diff SHA-256
`2a2e379a6f616d6b7e4b4d3e8a0899380eb94cbcbe7be5b0015019a4b0d94906`.

Peak RSS is below the previous candidate's 11,404,928 KiB at the same budget,
but the two runs were killed at different points inside round 23's closure, so
that difference is not attributable to the change. Neither approaches the cap.

## Status of the change

The sorted-role index is correct and strictly reduces probe count, and the
fixpoint argument above holds. It is measured-neutral on 1194 and is left in the
working tree unintegrated. It should not be adopted on its own evidence: the
binary search replaces a linear scan that is faster for the small axiom lists
most ontologies have, so adopting it would need a corpus-wide timing case that
this measurement does not provide.
