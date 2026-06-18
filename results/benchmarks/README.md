# Versioned benchmark snapshots

Each `YYYY-MM-DD-<topic>.md` here is a **point-in-time** snapshot of a full
benchmark table. We keep every version (never overwrite) so changes can be
compared across time. When a sweep finishes, append a new dated file rather than
editing an old one.

Every snapshot must report the full panel for each measure (standing rule):
**passrate (ok) / MATCH / sound / complete / unsound / incomplete /
avg + median wall / avg + median peak-mem** — no single metric defines
success/failure.

Gold = Konclude with the `ore_canon` `Thing≡Nothing` fix; SWRL/`DLSafeRule`
ontologies use HermiT (Konclude cannot parse them). See
[`../../docs/CONTESTED-GOLD.md`](../../docs/CONTESTED-GOLD.md) for which oracle is
correct where.

## Index

- `2026-06-17-ht-matrix.md` — HT 9-arm version matrix (after the cb_to_ht
  query-set incompleteness fix) + proactive-router sim. Adds the `ht-modelprune`
  arm (HermiT QuasiOrder multi-model pruning). NOTE: its in-run "+1" for
  modelprune was not reproducible — see the correction banner and the file
  below.
- `2026-06-17-emelim.md` — complementary-definer excluded-middle elimination
  (`B≡¬A`), HT + CB. HT `KM_HT_EMELIM` +14 MATCH (folds the disjunction family
  to HermiT's exact model size; 3 unsound all gold/engine artifacts). CB
  `KM_EMELIM` +2 ok gold-CLEAN (recovers 16444 memout + 6212), lower memory,
  0 regressions. Both gated default-off. HEAD `28597d4`.
- `2026-06-17-ht-fullcorpus-panel.md` — fresh full-corpus 10-arm panel on
  committed `190fe53`. Best HT arm = `ht-default` (454 ok, 0 unsound). Shows
  `ht-modelprune` is a net −7 (447 ok) and overturns the earlier sample result;
  modelprune stays gated OFF. Soundness invariant (unsound=0) holds across all
  arms; only incompleteness is ont 7216 (non-disjunction gap).
- `2026-06-18-km-cb-ht-ablation.md` — KM-only CB+HT optimization ablation, full
  587 corpus, faithful `ore_canon` (HEAD `6207bae`). `ht_emelim` is the global
  winner (565 gold-clean / 0 unsound / 1 incomplete=5303 / 21 timeout, +7 vs base
  558). Blanket-`ALL` (561) is *worse* than `ht_emelim` alone — `elcport` regresses
  2 giants; a router beats blanket-on. `absorb`/`tabrace` now +0 (subsumed by base);
  `KM_HT_CONTRA` neutral. Union 568. Deployable: `base + ht_emelim` + giant-excluded
  `elcport`.
