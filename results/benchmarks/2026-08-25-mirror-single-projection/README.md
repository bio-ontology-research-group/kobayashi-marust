# Theorem-backed single mirror projection

The v1 mirror route classifies a proxy-free base projection and then a richer
fresh-proxy slice projection sequentially. It compares their old-signature
taxonomies before reconstruction. The second classification is redundant:
`MirrorProxyConservativeExtension.oldEntails_iff_sliceEntails` proves that the
fresh one-way proxies, including the selected exact proxies, conservatively
extend every old ontology for every old-concept subsumption.

The new default classifies only the slice and uses its old-signature rows as
the base taxonomy. `KM_MIRROR_DOUBLE_CHECK=1` retains the previous two-run
cross-check for same-binary differential evidence. Every other reconstruction
check remains active, including consistency, proxy-to-base exclusion, selected
proxy publication, declared-name validation, and exact mirror reconstruction.

The standalone Lean module builds without `sorryAx`; `#print axioms` reports no
axioms. Release-mode Rust checking passes, and all 47 focused mirror tests pass.
An order-balanced ORE4669 pair is still required before integration.

The pinned combined-candidate sweep supplies a useful phase trace even though
its AMD EPYC timing is not release-comparable. ORE4669 spends 31.43 seconds on
the base projection and 203.41 seconds on the slice, then reconstructs the
exact independent-oracle fingerprint `a482e066a22110d...`. This directly
confirms that eliminating the base run removes real work. Gold-6248 paired
evidence remains binding for the performance claim.

Source-bound IBEX build job `50848204` was cancelled while still pending after
the integrated cyclic-flat candidate subsumed its source and test coverage.
Integrated build job `50848755` independently reruns the
47 mirror tests and the direct-route tests before installing binary
`55e606f6cd500d12…`. Integrated Gold-6248 pair `50849594` is dependency-gated
on corrected functional array `50849592`; the initial dependency pair never
allocated after its harness-packaging preflight failed.
