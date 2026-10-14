# Borrow the frontend clause snapshot

The bridge source backend no longer owns a duplicate normalized-clause vector.
Every previous constructor copied the current frontend clauses into that
vector; every successful update replaced both together. Delta construction
now borrows the frontend snapshot directly. The borrow ends before publication.
Failed preparation, failed bridge updates and route migration retain their
existing transactional behavior. The bridge classifier still owns the clauses
needed by its independent API. No inference, invalidation, query ordering,
source coverage or proof rule changed.

Verification brackets the change: the deletion-support baseline passed the
same 26 source-session and 14 typed incremental tests. The new source passes
26 source-session tests both normally and with experimental source/module/
deletion reuse enabled, plus all 14 typed tests. The source manifest and
certification receipt pin the exact candidate and its production Lean gates.

A paired workstation diagnostic uses the same five revisions of ORE9944,
including the one-axiom and 32-axiom deletion/restoration sequences. Each arm
uses source locality, source modules and deletion reproof. Repetition zero
runs old then new; repetition one reverses that order. Both binaries use one
CPU and identical limits. Every answer and every reuse receipt is identical
across binaries, and every retained answer also matches fresh classification.

The new binary beats the old on 7/8 update measurements. Publication takes
61–101 ms versus 105–233 ms before the change, improving all eight measurements.
These are only two repetitions on one ontology; timings include noise and
must not be generalized to the release panel. Initialization also avoids the
duplicate storage, but the update comparison is the intended acceptance test.

The new binary beats fresh reasoning on 5/8 updates. The large deletion takes
1.508–1.733 seconds versus 1.674–1.710 seconds fresh; the large restoration
still takes 1.953–2.034 seconds versus 1.702 seconds fresh. The v1.5.1 requirement
remains unmet. The latter update still probes 2,180 query rows through a
7,887-axiom module, spending about 0.74 seconds in module classification.
A previously solved exact revision could avoid this work when a source is
restored, but any such cache needs complete source/background identity and
honest reuse accounting. General additions also need better maintained state.
