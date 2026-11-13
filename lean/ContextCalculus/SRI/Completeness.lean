import ContextCalculus.SRI.Procedure

/-!
# Completeness of the v1.6.3 procedure (plan, section 2b, core lemma)

If a good type contains `a` and not `b`, and `a` is requested, an alive
record contains `a` and not `b`.

Proof. Fix a self-realising `G ∋ t0` and witnesses `w`. Unravel `G` from
`t0` into paths of demands (`tp`). Build, by recursion on the stage `k`
and then on the path, types `m k x ⊆ tp x`:

- `m 0 [] = guided (tp []) {a}`,
  `m 0 (d :: p) = guided (tp (d :: p)) (K 0 (d :: p))`;
- `m (k+1) x = guided (tp x) (K (k+1) x ∪ B k x)`,

with the context `K k (d :: p) = insert d.b (fwd (m k p) d.R)` (the
parent at the same stage), `K k [] = {a}`, and the back set `B k x`, the
union of `back (m k (d :: x)) d.R` over the demands `d` of `m k x`, taken
only when `x` is active at stage `k`. A path is active at stage `k` when
every step is a demand of `m k` of its parent. `m` and activity increase
with `k`; each `m · x` stops at `M x`.

1. `sim`: an active path at stage `k` has a `Gstar` record with context
   `K k x` and type `m k x` (child rule, then augment with the children's
   back sets stage by stage from the stage the path became active).
2. `selfReal`: the records whose type is some `M x` of an eventually
   active `x` are witnessed among themselves.
3. `subset_alive` puts them into `alive`; the root record has `a` and not
   `b` because `M [] ⊆ tp [] = t0`.
-/

namespace ContextCalculus.SRI.Proc

open ContextCalculus.SRI

variable {n m : Nat} {O : Ontology (Fin n) (Fin m)}

/-- A demand: `exRight a R b`. -/
abbrev Dm (n m : Nat) := Fin n × RT m × Fin n

section Unravel

variable (O) (G : Finset (Ty n)) (hG : SelfReal O G)

/-- A witness for every demand of every member of `G` (arbitrary outside). -/
noncomputable def wit (t : Ty n) (d : Dm n m) : Ty n := by
  classical
  exact if h : t ∈ G ∧ Clause.exRight d.1 d.2.1 d.2.2 ∈ O ∧ d.1 ∈ t then
    Classical.choose ((hG t h.1).2 d.1 d.2.1 d.2.2 h.2.1 h.2.2) else t

theorem wit_spec {t : Ty n} (ht : t ∈ G) {d : Dm n m}
    (hd : Clause.exRight d.1 d.2.1 d.2.2 ∈ O) (ha : d.1 ∈ t) :
    wit O G hG t d ∈ G ∧ d.2.2 ∈ wit O G hG t d ∧ Compat O d.2.1 t (wit O G hG t d) := by
  sorry

/-- The type at a path (the head of the list is the last step). -/
noncomputable def tp (t0 : Ty n) : List (Dm n m) → Ty n
  | [] => t0
  | d :: p => wit O G hG (tp t0 p) d

theorem tp_mem {t0 : Ty n} (h0 : t0 ∈ G) (x : List (Dm n m)) : tp O G hG t0 x ∈ G := by
  sorry

end Unravel

section Stages

variable (O) (T : List (Dm n m) → Ty n) (a : Fin n)

/-- Stage `k` types (`T` is the unravelled `tp`). Mutual recursion on the
stage and the path; the activity test and the back sets use stage `k`. -/
noncomputable def stage : Nat → List (Dm n m) → Ty n
  | 0, [] => guided O (T []) {a}
  | 0, d :: p => guided O (T (d :: p)) (insert d.2.2 (fwd O (stage 0 p) d.2.1))
  | k + 1, x =>
      guided O (T x) (ctx (k + 1) x ∪ backs k x)
where
  ctx : Nat → List (Dm n m) → Ty n
    | _, [] => {a}
    | j, d :: p => insert d.2.2 (fwd O (stage j p) d.2.1)
  active : Nat → List (Dm n m) → Prop
    | _, [] => True
    | j, d :: p => d ∈ demands O (stage j p) ∧ active j p
  backs : Nat → List (Dm n m) → Ty n
    | j, x => by
        classical
        exact if active j x then
          ((demands O (stage j x)).map fun d => back O (stage j (d :: x)) d.2.1).foldr (· ∪ ·) ∅
        else ∅

end Stages

/-! The lemmas of the proof, in order. Each is stated for `T = tp …` with
`t0 ∈ G`, `SelfReal O G`, `IsALCHI O`. -/

-- (a) `stage k x ⊆ T x`, and every seed is inside `T x` (compat of `w`).
-- (b) `stage k x ⊆ stage (k+1) x` and `active k x → active (k+1) x`.
-- (c) eventual value `M x` and `∀ k, stage k x ⊆ M x`.
-- (d) `sim`: `active k x → ∃ A, ⟨ctx k x, A, stage k x⟩ ∈ Gstar O req`
--     (with `a ∈ req`); by induction on `k`, then on `x`.
-- (e) `selfReal` of the records whose type is `M x` for an eventually
--     active `x`.

/-- **P4, completeness.** -/
theorem complete (hA : IsALCHI O) {req : List (Fin n)} {a b : Fin n} (ha : a ∈ req)
    {t0 : Ty n} (hgood : Good O t0) (hat : a ∈ t0) (hbt : b ∉ t0) :
    ∃ r ∈ alive O req, a ∈ r.t ∧ b ∉ r.t := by
  sorry

/-- **Exactness of the procedure on requested names.** -/
theorem entails_iff (hA : IsALCHI O) {req : List (Fin n)} {a : Fin n} (ha : a ∈ req)
    (b : Fin n) : entails O req a b = true ↔ EntailsSub O a b := by
  sorry

end ContextCalculus.SRI.Proc
