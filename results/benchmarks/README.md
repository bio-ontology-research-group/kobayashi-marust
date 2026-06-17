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
- `2026-06-17-ht-fullcorpus-panel.md` — fresh full-corpus 10-arm panel on
  committed `190fe53`. Best HT arm = `ht-default` (454 ok, 0 unsound). Shows
  `ht-modelprune` is a net −7 (447 ok) and overturns the earlier sample result;
  modelprune stays gated OFF. Soundness invariant (unsound=0) holds across all
  arms; only incompleteness is ont 7216 (non-disjunction gap).
