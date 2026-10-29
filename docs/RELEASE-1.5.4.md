# KM 1.5.4 release notes

Version 1.5.4 replaces the v1.5.3 route selector, whose numeric bands were
fitted to known ORE ontologies, with a general routing policy, and fixes
every soundness and completeness defect found in a two-day differential
campaign against HermiT 1.4.3 on generated ALCHIQ, nominal and data-property
inputs and on five Protégé bug reports. It adds exact realization
(`km classify --realize`), exact data-range reasoning for empty and
universal ranges, and a nominal-safe regime of the Sequoia literal ordering
with a Lean theorem for the ground-level exchange between differently
ordered contexts. The acceptance contract is `docs/V1.5.4-ACCEPTANCE.md`;
its three approved amendments are listed in `docs/V1.5.4-STATUS.md`.

## Routing

`KM_ROUTING_POLICY=general` is the default. The policy uses semantic,
certificate and construct evidence only; an audit test rejects numeric
thresholds in the general rules, and metamorphic tests check route
stability under renaming and axiom reordering. The old selector remains as
`KM_ROUTING_POLICY=v153` for paired evaluation. Forced routes
(`KM_ROUTE=<name>`, `--route`) fail closed: a route that would drop or
approximate exits 3 with the reason, and `KM_ALLOW_APPROXIMATE=1` publishes
with an `APPROXIMATE` line (`docs/ROUTING.md`).

Design-half evaluation (1,123 ORE inputs, paired on the same binary, Ibex,
single core, 300 s): run 9 from the frozen head verified 1,099 inputs under
the general policy against 1,094 under v1.5.3's policy, 0 wrong, 0 lost,
mean time ratio 1.081, median 1.088 on the 1,094 inputs both solve
(`results/benchmarks/2026-10-26-v154-routing/RUNS.md`).

Held-out half (585 inputs, run once on the PGO binary built from this tag)
and the G8 comparison against the v1.5.3 PGO release binary on the same
node type (contract: mean and median ratio at most 1.10) are measured after
the tag is cut; their tables are in `BENCHMARKS.md` among the release
assets and in `results/benchmarks/2026-10-26-v154-routing/RUNS.md` on the
release branch.

## Wrong answers fixed

The changelog lists every item with its commits. In summary:

- **Nominal mode sorts.** Object and data elements are separate sorts; the
  encoding now also runs when a data property or range appears without a
  literal (`⊤ ⊑ {a}` with `⊤ ⊑ ≥2 u` was answered inconsistent). The
  native bridge defers on such inputs, forced one-sorted routes refuse both
  verdicts beside a TBox nominal, and the DL-safe rule checker publishes no
  inconsistency from a one-sorted stream.
- **Konclude bridge.** Negated `≤n` polarity, the `≥0` trigger,
  insufficiency propagation, resolved definer markers on the clause path,
  and `≤0 R.C` built as `∀R.¬C` because the ported saturation did not count
  a predecessor reached over the inverse role.
- **CB engine.** Shared-closure clauses now enter every context's r-Succ
  pool (backward roles under `⊤ ⊑ D` missed subsumptions on every CB
  route); a retained incremental insertion that enables r-Succ rebuilds.
- **CB to HT conversion and native hypertableau.** The complementary-definer
  fold kept its contrapositive; subset blocking admits a pair only without
  relevant gain (it had published `CONSISTENT` for an inconsistent ontology
  on the automatic route through the card arm).
- **Sequoia ordering under nominals.** The plain ordering and the unordered
  regime are both incomplete with the nominal ground context. Nominal mode
  uses the context regime (`docs/PER-CONTEXT-ORDERING.md`), which answers
  both counterexamples, agrees with HermiT on every differential run, and
  recovers ORE 10874 and 15655.
- **Frontend.** Regular role inclusions through the Horrocks, Kutz and
  Sattler automaton (ORE 14101); `owl:topObjectProperty` rewritten exactly;
  IRI spellings identified; empty and universal data ranges decided; one
  definer for equal cardinality and existential restrictions; HasKey as
  DL-safe rules; legacy incremental sessions classify revisions with
  uncarried data assertions exactly.

Differential coverage at the freeze (60 s cap unless noted): 700 ALCHIQ
seeds on auto, the pure CB route and the bridge routes; 300 fresh seeds
with inverse roles; 400 generated nominal-plus-data inputs and 200 fresh
ones on the nominal routes; 33 sorts fixtures; 20 at-most predecessor
probes; 14 rule probes. No wrong answer remains on any route. Timeouts are
reported as timeouts; the known performance items are listed in
`docs/V1.5.4-STATUS.md` for v1.5.5.

## Lean boundary

The proved boundary is unchanged from v1.5.3 and stated in
`docs/history/LEAN-BOUNDARY-AUDIT-2026-10-27.md`: a checker's acceptance of
an evidence document proves the answer exact for the normalised clauses in
that document; the frontend is unmodelled; procedure completeness is a
theorem premise; no checker runs on the default route. New in 1.5.4 is
`lean/ContextCalculus/CompletenessExchange.lean`, which proves, at the
ground level and without `sorry`, that a server context satisfying the
downward-closed interface condition is complete for every consumer order
(`downward_server_complete`, `exchange_refutation_complete`), and that the
condition is necessary. The mapping from KM's announcement guard to the
theorem is argued, not mechanised (`docs/PER-CONTEXT-ORDERING.md` section 6).
The CB certificate checker models the unordered regime, so runs with
`KM_CB_LEAN_REQUIRED` keep it.

All four production Lean certification gates (`elc`, `routing`, `ht`, `cb`)
are executed from the exact tagged commit with zero `sorryAx`, alongside the
serial Rust CI suite (the 22 checker-bound tests run inside the gates) and
the 76-test Maven Java suite. The gate receipts, test logs and tool
bindings are in `build-completion.json` among the release assets.

## Reproducing and inspecting the release

Build the tagged source with `cargo build --locked --release --features
mimalloc --bin km` in `engine/` (with `RUSTFLAGS="-Cprofile-use=merged.profdata
-Cllvm-args=-pgo-warn-missing-function"` for the profile-guided build, pipeline
receipts under the release assets). Reproduce the JAR with `mvn package` in
`protege/`.

The release attaches:
- `km-v1.5.4-linux-x86_64`: the measured native executable.
- `kobayashi-marust-protege-1.5.4.jar`: the Protégé / OWLAPI package.
- `km-v1.5.4-certified-source.tar.gz`: the exact final source archive.
- `BENCHMARKS.md`: design and held-out tables and the G8 comparison.
- `build-completion.json`: machine-readable results and certification bindings.
- `SHA256SUMS`: checksums of the other five files.
