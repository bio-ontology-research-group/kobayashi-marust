# Heap profiling harness

Heap profiling for the CB engine (`kobayashi-marust`) and the hypertableau
(`tableau_cli`), using [`dhat-rs`](https://docs.rs/dhat). The instrumentation is
behind the `dhat-heap` Cargo feature, so the normal release build is unaffected.

## Build the instrumented binaries

```sh
cd engine
CARGO_TARGET_DIR=target-dhat RUSTFLAGS="-C debuginfo=1" \
    cargo build --release --features dhat-heap --bins
```

`RUSTFLAGS="-C debuginfo=1"` keeps line/symbol tables so dhat backtraces resolve
to function names (the default release profile has `lto = true`, which strips
them). Output lands in `target-dhat/release/` so it never clobbers the real
binaries in `target/release/`.

## Run

Each instrumented binary prints a `dhat: Total / At t-gmax / At t-end` summary to
stderr and writes `dhat-heap.json` (full per-allocation-site backtraces) to the
cwd.

```sh
# Tableau, on a live-disjunction stress with a clash trap (forces backtracking):
python3 prof/gen_disjunction_stress.py 12 8 > /tmp/s.ofn      # K disjunctions, P parallel roles
python3 prof/ofn_to_tin.py /tmp/s.ofn > /tmp/s.tin.json
target-dhat/release/tableau_cli < /tmp/s.tin.json > /dev/null
python3 prof/parse_dhat.py dhat-heap.json

# CB engine, on any .ofn:
python3 prof/ofn_to_clauses.py examples/ontologies/kinship.ofn > /tmp/k.cl.json
target-dhat/release/kobayashi-marust < /tmp/k.cl.json > /dev/null
python3 prof/parse_dhat.py dhat-heap.json
```

`parse_dhat.py` ranks allocation sites two ways: by **peak live bytes** (`gb`,
what is resident at the global high-water mark) and by **total bytes allocated**
(`tb`, churn / allocator traffic over the whole run).

## Findings (2026-06-08, tableau K=12 P=8 stress)

- Peak live 268 MB: **~92 % is `Graph::clone`** — the per-branch whole-graph copy.
  Target of the trail-based-backtracking rewrite.
- Total churn 3.85 GB / 18.5 M allocations: **~80 % is `Tableau::match_rec`** —
  `Subst = HashMap<Var, Node>` for 1–3-variable maps, plus `match_body`
  materialising `Vec<Subst>` with a `subst.clone()` per solution. A separate,
  larger-traffic hotspot; fixed by a small-inline `Subst` + a visitor callback
  instead of collecting.

## After trail-based backtracking (2026-06-08)

Replaced the per-branch `g.clone()` in `expand` with a trail of reversible undo
records (`checkpoint` / `rollback_to`); see `Undo` / `MergeUndo` in `tableau.rs`.
Same stress (K=12 P=8), validated identical (`consistent=true`, 16/16 oracle
fixtures still MATCH HermiT):

- **Peak live: 268 MB -> 0.98 MB (274x).** `Graph::clone` is gone from the peak;
  it is now the live graph itself (`new_node` / `add_concept`).
- Churn: 3.85 GB -> 3.56 GB (~unchanged) and wall-clock ~neutral (+5%), both
  expected — CPU/allocator traffic is dominated by `match_rec`, not clone. That
  is the next fix (small-inline `Subst` + visitor).

## After the match_rec / Subst fix (2026-06-08)

Replaced `Subst = HashMap<Var,Node>` with an inline `SmallVec<[(Var,Node);4]>`
newtype (clauses have 1–4 variables, so `clone` is allocation-free for the common
case), and turned `match_rec` into an early-exit visitor so `find_disjunctive`
stops at the first usable match instead of materialising every solution. Same
stress, identical verdicts, 16/16 oracle fixtures MATCH:

- **Allocation count: 18.5 M -> 1.77 M blocks (10.5x)** — the 14 M tiny per-solution
  HashMap allocations are gone. malloc/free *call count* (not byte volume) is the
  CPU cost, so:
- **Wall-clock: K=12/P=8 5.37 s -> 2.30 s (2.3x), K=14/P=10 16.7 s -> 10.3 s.**
- Peak unchanged (~0.89 MB). Total bytes ~flat (the remaining churn is
  `horn_saturate` materialising solution sets before it mutates the graph — it
  cannot apply during the match because a Role-body clause iterates `g.edges`
  while the head would mutate it).

Net vs the original clone+HashMap baseline: **peak 300x lower, allocations 10x
fewer, ~2.3x faster**, verdicts identical.
