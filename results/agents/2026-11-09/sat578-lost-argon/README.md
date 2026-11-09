# sat578-lost-argon: recovering the 12 lost answers of the sat578 fix

Branch `fix/v155-sat578-lost-argon` from `development/v1.5.5` at `4bf690c8`,
worktree `.work/worktrees/fix-sat578-lost-argon`. Scratch directory:
`.work/agent-scratch/sat578-lost-argon/`. Release flags for every measurement:
`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`.

Binaries (`.work/agent-scratch/sat578-lost-argon/bin/`):

| name | source | sha256 |
|---|---|---|
| `km-4bf690c8` (`km-base`) | base `4bf690c8` (`development/v1.5.5`, byte-identical to `km-b1fcbb93`) | `1caca2fa5cd53765d3ffcec206acb95a55750e2e19811561bca1634e949ce035` |
| `km-fix` | branch head (`u08.rs` and `u19.rs` changes; later commit adds fixture, docs, and results) | `930835f332cf6cedc7dacbb39d69cce2f0a559f7a0164cf072b5b2990df361c3` |

The full argument for the change is in `docs/HYBRID-CB-HT.md` section 25.7.

## Cause and Konclude comparison

Line numbers refer to
`~/konclude-build/Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.

1. **Why B4a `atmost` (`nominal_bound_counts_copy`) lost `s578_1486`, and what the port lacked in `applySOMERule` (`u08.rs`, cpp 14440–14452, 20368–20403, 4670–4734).**
   In `s578_1486`, the earlier probe `A ⊓ ¬E` creates a probe root `w' = 1000`
   linked to the nominal `b` (`p(b, b)` and `p(b, w')`). Because `b` carries no
   at-most restriction on `p` in `A ⊓ ¬E`, `nominal_bound_counts_copy(b, w')`
   returns `false` and `w'` blocks its successor `w = 1002`. When `apply_some_rule`
   (`u08.rs`, `applySOMERule`, cpp 14313–14453) expands `w'`'s existential
   `∃p⁻.{b}`, `has_role_neighbour_with_concepts` (cpp 14382) finds the existing
   neighbour `already_exist = b`. In Konclude, when `applySOMERule` reuses an
   existing neighbour, the `else` branch (cpp 14440–14452) records a backward
   dependency and calls
   `propagateIndividualNodeNominalConnectionStatusToAncestors(indi, alreadyExist, calcAlgContext)`
   (cpp 14449; ported in `u16.rs` lines 782–850 from cpp 20368–20403), and
   Konclude's VALUE shortcut for `∃R.{o}` (cpp 14316–14380) also propagates
   `PRF_SUCCESSORNOMINALCONNECTION` to `indi` and its ancestors (cpp 14375).
   Because the port omits the VALUE shortcut and its `else` branch in
   `apply_some_rule` (`u08.rs` line 750) was empty, reusing the existing link
   to `b` never set `PRF_SUCCESSORNOMINALCONNECTION` on `w' = 1000`. When
   `A ⊓ ¬E` finished, `test_all_successors_processed_and_write_satisfiable_cache`
   (`u21.rs` lines 1026–1035, cpp 4676:
   `!indiNode->hasPartialProcessingRestrictionFlags(PRFINVALIDATEBLOCKERFLAGSCOMPINATION | PRFSUCCESSORNOMINALCONNECTION)`)
   cached `w'`'s label in the global satisfiable expander cache as context-free
   satisfiable, and the later probe `Q5 ⊓ ¬Q1` absorbed that cached result and
   missed `Q5 ⊑ Q1`. Porting `propagate_individual_node_nominal_connection_status_to_ancestors`
   into the `else` branch of `apply_some_rule` (`u08.rs` lines 750–782,
   cpp 14449) sets `PRF_SUCCESSORNOMINALCONNECTION` on `process_indi` and its
   ancestors whenever `already_exist` is a nominal or carries
   `PRF_SUCCESSORNOMINALCONNECTION`, keeping `s578_1486` right under
   `nominal_bound_counts_copy` while recovering `s578_171`, `s578_733`,
   `s578_908`, and `nn969`.

2. **Why `b6_redirect_collides` lost `nn1881`, `s578_1288`, `s578_1026`, and `nn969`, and how B6 couples with B4a (`u19.rs`, cpp 18716–18803, 19376–19442).**
   In Konclude's `isLabelConceptOptimizedBlocking` (cpp 18716–18745), when B3
   and B5 hold and `w ∈ C` for every `¬(≤n R.C)` at `v`, `cBlocked` stays
   `true` and the function returns `true` at `if (cBlocked) return true;`
   (cpp 18743) without running B4 (cpp 18747–18803). When two siblings `w₁, w₂`
   share a blocker `w'` so that C-block edge redirects would collide at `v`,
   standard unravelling can instantiate `w₂` as a fresh tree copy of `w'`
   (A-blocking) without merging the two `R`-edges from `v`, provided no
   restriction of `w'` relies on a witness that tree unravelling cannot copy.
   For non-nominal restrictions of `w'`, blocking runs at priority 3
   (`check_for_blocking`, `u02.rs`) before `w'` has popped its priority-4
   `SOME` or priority-5 `ATLEAST` queues (`nn1881`), or when `w'`'s non-nominal
   witness is its tree parent (`s578_1288` on `con=79`, `s578_1026` on `con=74`).
   When `b1fcbb93` cleared `c_blocked = false` on `b6_redirect_collides`, B4a
   rejected `w'` before `w'` expanded its priority-4/5 queue, and
   `getAnywhereBlockingIndividualNodeCanidateHashed` (`u20.rs` line 636,
   cpp 19412) updated `w`'s `concept_label_set_modification_tag`, causing
   `is_individual_node_concept_label_set_modified(w')` (cpp 19415) to skip `w'`
   permanently after `w'` expanded its `SOME`/`ATLEAST` edges (`nn1881`). By
   contrast, unravelling `w` as a copy of `w'` fails when `w'` satisfies an
   existential or at-least restriction in B4a only through a nominal `o` (or a
   ghost link to a node merged into `o`) that the B4a nominal guard rejects
   (`sat578`, its eight reductions, `fx279`, `s578_96`, and `s578_1288` on
   `con=83`). Keeping `c_blocked` distinct from `b6_collide_only` and, when
   `c_blocked && b6_collide_only`, rejecting in B4a only when
   `min_role_cardinality < cardinality && nominal_guard_rejected` (`u19.rs`
   line 913) refuses the block whenever copying `w'` would duplicate an
   uncounted nominal link while preserving Konclude's `if (cBlocked) return true;`
   acceptance on non-nominal restrictions.

## Hand derivation of `nn1881_red` (`engine/tests/fixtures/sat578/nn1881_red.ofn`)

Axioms (8): `Q2 ≡ ≤1 s.(∃r.{a})`, `F ⊑ ∀s⁻.{b}`, `≥3 s.(≥2 p.¬E) ⊑ B`,
`Functional(r)`, `Inverse(s, p)`, `Reflexive(p)`, `Q4 ≡ ≤1 p⁻`, and
`Q4 ≡ ≤2 r⁻.(∃r.F)`.

- *Subsumption `Q4 ⊑ Q2`.* By `Reflexive(p)` and `Inverse(s, p)`, every element
  `x ∈ Δ` satisfies `p(x, x)` and `s(x, x)`. For any `x ∈ Q4 = ≤1 p⁻`, `x` has
  at most one `p⁻`-successor, and since `p(x, x)` holds, `{y ∈ Δ | p(y, x)} = {x}`.
  Because `s ≡ p⁻`, `{y ∈ Δ | s(x, y)} = {x}`, so `x` has at most one
  `s`-successor in total and therefore at most one `s`-successor in `∃r.{a}`.
  Hence `x ∈ ≤1 s.(∃r.{a}) = Q2`, proving `Q4 ⊑ Q2`.
- *Consistency and absence of other subsumptions.* In the one-element interpretation
  `Δ = {b}` with `aᴵ = bᴵ = b`, `pᴵ = sᴵ = {(b, b)}`, and `rᴵ = ∅`,
  `Functional(r)`, `Reflexive(p)`, and `Inverse(s, p)` hold; `(∃r.F)ᴵ = ∅` and
  `(∃r.{a})ᴵ = ∅`, so `(≤2 r⁻.(∃r.F))ᴵ = (≤1 p⁻)ᴵ = Q4ᴵ = Q2ᴵ = Δ`;
  `(≥3 s.(≥2 p.¬E))ᴵ = ∅`; and `(∀s⁻.{b})ᴵ = Δ`. Choosing `Bᴵ, Eᴵ, Fᴵ ⊆ {b}`
  independently separates `B, E, F` from one another and shows `Q2, Q4 ⋢ B, E, F`.
  To separate `Q2 ⋢ Q4` and `B, E, F ⋢ Q2, Q4`, take `Δ = {b, u, v}` with
  `aᴵ = b`, `pᴵ = {(x, x) | x ∈ Δ} ∪ {(u, b), (v, b)}`, `sᴵ = (pᴵ)⁻`, and
  `rᴵ = {(u, b), (v, b)}` (functional): `b` has three `p⁻`/`s`-neighbours
  (`b, u, v`), of which two (`u, v`) lie in `∃r.{a}`, whereas `b`'s only
  `s⁻`-neighbour (`p`-successor) is `b` itself (`p(b, y) ⟺ y = b`). Consequently,
  `b ∈ ∀s⁻.{b}` and `b ∉ Q4, Q2`, so setting `Bᴵ = Eᴵ = Fᴵ = {b}` (with
  `u, v` having only one `s`-successor each, so `(≥3 s.(≥2 p.¬E))ᴵ = ∅`) shows
  `B, E, F ⋢ Q2, Q4`; shrinking `rᴵ` to `{(u, b)}` leaves `b` with only one
  `s`-successor in `∃r.{a}` (`u`) while keeping three `p⁻`-neighbours, so
  `b ∈ Q2 \ Q4` and `Q2 ⋢ Q4`. Confirmed by HermiT 1.4 and Konclude 0.7.0 `-w 2`.

## Validation summary

| check | result | data |
|---|---|---|
| 1. 12 lost seed-route rows of `lost-answers-base.tsv`, 3 runs | 36/36 `ok` on `km-fix`, all within `max(3 * base_time, 60 s)` | `data/lost-answers-fix.tsv`, `data/lost-answers-base.tsv`, `data/lost-answers-4bf690c8.tsv` |
| 2. 10 fixtures (`sat578`, 8 reductions, `fx279`, `nn1881_red`), both routes, 20 runs | 400/400 `ok` (`tests/sat578.rs` 5/5 pass) | `data/fx-final.tsv` |
| 3. 27 families and pools (`pools.sh` + `families.txt`), 55,330 seed-route runs | 0 new `WRONG`, 0 `ok -> TIMEOUT/ERR` flips; 12 lost seed-routes + `s578_908` (`auto`) recovered | `data/pools/final-table.txt`, `data/pools/final-diff.tsv`, `data/pools/flips-3runs.tsv` |
| 3b. `regressions-of-fbd1932c.txt`, 35 rows, 3 runs | 105/105 `ok` (including `nn969` `ht_bridge` 3/3 `ok`) | `data/reg-final.tsv` |
| 4. Library + 95 integration targets (`KM_THREADS=1`, `--test-threads=1`, clean env) | Library: 3,121 passed, exact 21 baseline failures; 95/95 integration targets pass (`rc=0`) | `data/tests/summary.txt`, `data/tests/lib-failures.txt`, `data/tests/lib-results.txt` |
| 5a. 16 held-out ORE inputs (240 s cap) | 15/15 answered inputs match reference agreement identically on `km-base` and `km-fix` | `data/heldout/summary.tsv` |
| 5b. 112 nominal ORE design-half inputs (300 s cap) | 109 answered by both, 109 identical signatures, 0 status/route changes, mean ratio 0.988, median 0.981 | `data/nominal/pair.txt`, `data/nominal/times-before.tsv`, `data/nominal/times-after.tsv` |

### Item 1: 12 lost seed-routes (`data/lost-answers-fix.tsv`, 3 runs per row)

| pool | seed | route | `274faa6a` (3 runs, s) | `km-4bf690c8` (3 runs) | `km-fix` (3 runs, s) |
|---|---|---|---|---|---|
| `bridge-nn-rule-fam` | `nn1881` | `auto` | `ok` (0.03, 0.03, 0.03) | `TIMEOUT` 3/3 | `ok` 3/3 (0.03, 0.03, 0.03) |
| `bridge-nn-rule-fam` | `nn1881` | `ht_bridge` | `ok` (0.03, 0.03, 0.02) | `ERR` 3/3 | `ok` 3/3 (0.03, 0.02, 0.02) |
| `bridge-nn-rule-fam` | `nn969` | `ht_bridge` | `ok` (30.90, 29.87, 30.69) | `TIMEOUT` 3/3 | `ok` 3/3 (36.04, 34.64, 33.92) |
| `sat578-fam` | `s578_1026` | `auto` | `ok` (36.00, 35.96, 37.54) | `TIMEOUT` 3/3 | `ok` 3/3 (41.58, 39.86, 39.57) |
| `sat578-fam` | `s578_1026` | `ht_bridge` | `ok` (27.94, 28.81, 28.19) | `TIMEOUT` 3/3 | `ok` 3/3 (31.46, 31.40, 31.66) |
| `sat578-fam` | `s578_1288` | `auto` | `ok` (0.06, 0.06, 0.06) | `TIMEOUT` 3/3 | `ok` 3/3 (0.06, 0.06, 0.06) |
| `sat578-fam` | `s578_1288` | `ht_bridge` | `ok` (0.05, 0.05, 0.06) | `TIMEOUT` 3/3 | `ok` 3/3 (0.06, 0.06, 0.06) |
| `sat578-fam` | `s578_171` | `auto` | `ok` (0.96, 0.98, 0.96) | `TIMEOUT` 3/3 | `ok` 3/3 (1.41, 1.39, 1.34) |
| `sat578-fam` | `s578_171` | `ht_bridge` | `ok` (0.92, 0.97, 1.00) | `ERR` 3/3 | `ok` 3/3 (1.46, 1.32, 1.37) |
| `sat578-fam` | `s578_733` | `auto` | `ok` (0.17, 0.14, 0.14) | `TIMEOUT` 3/3 | `ok` 3/3 (0.16, 0.18, 0.16) |
| `sat578-fam` | `s578_733` | `ht_bridge` | `ok` (0.13, 0.16, 0.16) | `ERR` 3/3 | `ok` 3/3 (0.18, 0.16, 0.17) |
| `sat578-fam` | `s578_908` | `ht_bridge` | `ok` (25.98, 26.13, 26.37) | `TIMEOUT` 3/3 | `ok` 3/3 (28.75, 29.00, 28.25) |
