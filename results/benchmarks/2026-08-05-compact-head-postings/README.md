# Rejected 16-byte compact head-index postings

This experiment replaced `SmallVec<[u32; 2]>` head-index postings with a
16-byte representation containing two inline `u32` identifiers and an optional
boxed `Vec<u32>` spill. Posting order, removal order, and all slice consumers
were preserved. A focused inline/spill/compaction test and release check passed.

The profile-backed ORE9944 gate showed why the common-case layout is valuable.
Two alternating production-route pairs were output-identical (SHA-256
`97a95bbfc29dd4c7228f20740a5c0d886ee196a113b1154d785759ca5d90168f`).
Candidate peak RSS was 6,030,880 and 6,154,316 KiB versus baseline 6,532,624
and 6,488,564 KiB, saving 326–490 MiB. Wall time was neutral to slightly
better: 9.30/9.46 seconds versus 9.71/9.51 seconds.

The ORE1194 production gate rejected this implementation. The candidate failed
closed at 19,050,596 KiB after 34.98 seconds versus 18,923,964 KiB after 32.98
seconds for current `main`. The boxed `Vec` spill needs a separate allocation
for its header and data, which penalises workloads with many postings wider
than two entries. No source code was merged and no IBEX job was submitted.

The measurements support a follow-up implementation only if it retains the
16-byte common case with a one-allocation spill representation. That design
must preserve the ORE9944 saving without reducing ORE1194 headroom.
