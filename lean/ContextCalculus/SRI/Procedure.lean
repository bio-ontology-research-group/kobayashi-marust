import ContextCalculus.SRI.GoodTypes
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-!
# The v1.6.3 decision procedure for ALCHI (plan, section 2b, Steps 2 and 3)

Concepts are `Fin n`, roles `Fin m`. A record `(K, A, t)` is a context
seed `K`, an augment set `A` and a closed type `t` from
`branches (K ∪ A)`. `Gstar` is the least set of records closed under the
root, child and augment rules; `alive` is its greatest self-realising
part. `a ⊑ b` holds iff every alive type that contains `a` contains `b`.

This file gives a direct, unoptimised computation: `Gstar` iterates all
rules until nothing new appears. Soundness and completeness use only
that `Gstar` is closed under the rules and that its types are closed, so
a faster worklist can replace `Gstar` later with a proof of those two
facts.
-/

namespace ContextCalculus.SRI.Proc

open ContextCalculus.SRI

variable {n m : Nat}

abbrev Ty (n : Nat) := Finset (Fin n)
abbrev RT (m : Nat) := RoleT (Fin m)

section Defs

variable (O : Ontology (Fin n) (Fin m))

/-! ## Role closure -/

/-- Inclusion steps `R ⊑ S` from chains of length one, and their flips. -/
def stepPairs : List (RT m × RT m) :=
  let base := O.filterMap fun
    | .chain [R] S => some (R, S)
    | _ => none
  base ++ base.map fun p => (p.1.flip, p.2.flip)

def upStep (L : List (RT m)) : List (RT m) :=
  (L ++ (stepPairs O).filterMap fun p => if p.1 ∈ L then some p.2 else none).dedup

/-- The super-roles of `R` (there are at most `2m` role terms). -/
def roleUp (R : RT m) : List (RT m) :=
  (upStep O)^[2 * m + 1] [R]

/-! ## Universal propagation -/

def alls : List (Fin n × RT m × Fin n) :=
  O.filterMap fun
    | .allRight a S c => some (a, S, c)
    | _ => none

/-- Names an `R`-successor of `t` must contain. -/
def fwd (t : Ty n) (R : RT m) : Ty n :=
  (((alls O).filter fun q => decide (q.1 ∈ t) && decide (q.2.1 ∈ roleUp O R)).map
    fun q => q.2.2).toFinset

/-- Names an `R`-predecessor of `s` must contain. -/
def back (s : Ty n) (R : RT m) : Ty n :=
  (((alls O).filter fun q => decide (q.1 ∈ s) && decide (q.2.1 ∈ roleUp O R.flip)).map
    fun q => q.2.2).toFinset

def exs : List (Fin n × RT m × Fin n) :=
  O.filterMap fun
    | .exRight a R b => some (a, R, b)
    | _ => none

/-- The existential demands a type triggers. -/
def demands (t : Ty n) : List (Fin n × RT m × Fin n) :=
  (exs O).filter fun d => decide (d.1 ∈ t)

/-! ## Branches -/

def gcis : List (List (Fin n) × List (Fin n)) :=
  O.filterMap fun
    | .gci body head => some (body, head)
    | _ => none

/-- The head parts a processed gci may add: subsets `Y` of the head with
`Y ∪ (head ∩ cur)` nonempty. An empty head gives no choice (a clash). -/
def choices (head : List (Fin n)) (cur : Ty n) : List (Ty n) :=
  ((head.sublists.map List.toFinset).filter fun Y =>
    decide (Y ∪ (head.toFinset ∩ cur)).Nonempty).dedup

/-- Process the first unprocessed gci whose body holds, branching over
`choices`; stop when none is left. `fuel` bounds the number of gcis. -/
def branchesAux : Nat → Ty n → List Nat → List (Ty n)
  | 0, cur, _ => [cur]
  | fuel + 1, cur, done =>
      match ((gcis O).zipIdx).find? (fun q =>
          decide (q.2 ∉ done) && q.1.1.all (fun a => decide (a ∈ cur))) with
      | none => [cur]
      | some q => (choices q.1.2 cur).flatMap fun Y =>
          branchesAux fuel (cur ∪ Y) (q.2 :: done)

def branches (σ : Ty n) : List (Ty n) :=
  branchesAux O ((gcis O).length + 1) σ []

/-! ## Records and the candidate set -/

structure Rec (n : Nat) where
  K : Ty n
  A : Ty n
  t : Ty n
deriving DecidableEq

def rootRecs (req : List (Fin n)) : Finset (Rec n) :=
  (req.flatMap fun a => (branches O {a}).map fun t => (⟨{a}, ∅, t⟩ : Rec n)).toFinset

def childRecs (G : Finset (Rec n)) : Finset (Rec n) :=
  G.biUnion fun r => ((demands O r.t).flatMap fun d =>
    let K := insert d.2.2 (fwd O r.t d.2.1)
    (branches O K).map fun s => (⟨K, ∅, s⟩ : Rec n)).toFinset

def augRecs (G : Finset (Rec n)) : Finset (Rec n) :=
  G.biUnion fun r => (demands O r.t).toFinset.biUnion fun d =>
    (G.filter fun r' => d.2.2 ∈ r'.K ∧ r'.K ⊆ insert d.2.2 (fwd O r.t d.2.1)).biUnion
      fun r' =>
        let A := r.A ∪ back O r'.t d.2.1
        ((branches O (r.K ∪ A)).map fun t' => (⟨r.K, A, t'⟩ : Rec n)).toFinset

def step (req : List (Fin n)) (G : Finset (Rec n)) : Finset (Rec n) :=
  G ∪ rootRecs O req ∪ childRecs O G ∪ augRecs O G

/-- Records form a finite type (three subsets of `Fin n`). -/
def recEquiv : Rec n ≃ Ty n × Ty n × Ty n where
  toFun r := (r.K, r.A, r.t)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv r := by cases r; rfl
  right_inv p := by rfl

instance : Fintype (Rec n) := Fintype.ofEquiv _ recEquiv.symm

/-- Iterate `step` until it adds nothing. -/
def saturate (req : List (Fin n)) (G : Finset (Rec n)) : Finset (Rec n) :=
  let G' := step O req G
  if h : G' ⊆ G then G else saturate req G'
termination_by (Finset.univ \ G).card
decreasing_by
  sorry

def Gstar (req : List (Fin n)) : Finset (Rec n) :=
  saturate O req ∅

/-! ## Elimination and the answer -/

def witnessed (G : Finset (Rec n)) (r : Rec n) : Prop :=
  ∀ d ∈ demands O r.t, ∃ r' ∈ G, d.2.2 ∈ r'.t ∧
    fwd O r.t d.2.1 ⊆ r'.t ∧ back O r'.t d.2.1 ⊆ r.t

instance (G : Finset (Rec n)) (r : Rec n) : Decidable (witnessed O G r) := by
  unfold witnessed; infer_instance

def prune (G : Finset (Rec n)) : Finset (Rec n) :=
  G.filter (witnessed O G)

/-- Remove unwitnessed records until stable. -/
def eliminate (G : Finset (Rec n)) : Finset (Rec n) :=
  let G' := prune O G
  if h : G' = G then G else eliminate G'
termination_by G.card
decreasing_by
  sorry

def alive (req : List (Fin n)) : Finset (Rec n) :=
  eliminate O (Gstar O req)

/-- The procedure's verdict on `a ⊑ b`. -/
def entails (req : List (Fin n)) (a b : Fin n) : Bool :=
  decide (∀ r ∈ alive O req, a ∈ r.t → b ∈ r.t)

end Defs

/-! ## Facts the proofs of soundness and completeness use (P2, P3) -/

section Facts

variable {O : Ontology (Fin n) (Fin m)}

theorem mem_roleUp {R S : RT m} : S ∈ roleUp O R ↔ RoleLe O R S := by
  sorry

theorem compat_iff (R : RT m) (t s : Ty n) :
    Compat O R t s ↔ fwd O t R ⊆ s ∧ back O s R ⊆ t := by
  sorry

theorem mem_demands {t : Ty n} {a b : Fin n} {R : RT m} :
    (a, R, b) ∈ demands O t ↔ Clause.exRight a R b ∈ O ∧ a ∈ t := by
  sorry

theorem branches_closed {σ t : Ty n} (h : t ∈ branches O σ) : Closed O t ∧ σ ⊆ t := by
  sorry

/-- The least superset of `σ` that adds `head ∩ T` whenever a gci body
is contained in it (the `C_T` of the plan). -/
noncomputable def guided (O : Ontology (Fin n) (Fin m)) (T σ : Ty n) : Ty n := by
  classical
  exact Finset.univ.filter fun x => ∀ U : Ty n, (σ ⊆ U ∧ ∀ body head,
    Clause.gci body head ∈ O → (∀ a ∈ body, a ∈ U) → head.toFinset ∩ T ⊆ U) → x ∈ U

theorem guided_mem_branches {T σ : Ty n} (hT : Closed O T) (hσ : σ ⊆ T) :
    guided O T σ ∈ branches O σ := by
  sorry

theorem guided_subset {T σ : Ty n} (hT : Closed O T) (hσ : σ ⊆ T) : guided O T σ ⊆ T := by
  sorry

theorem guided_mono {T σ σ' : Ty n} (h : σ ⊆ σ') : guided O T σ ⊆ guided O T σ' := by
  sorry

theorem subset_guided {T σ : Ty n} : σ ⊆ guided O T σ := by
  sorry

theorem fwd_mono {t t' : Ty n} (R : RT m) (h : t ⊆ t') : fwd O t R ⊆ fwd O t' R := by
  sorry

theorem back_mono {s s' : Ty n} (R : RT m) (h : s ⊆ s') : back O s R ⊆ back O s' R := by
  sorry

variable {req : List (Fin n)}

theorem Gstar_root {a : Fin n} (ha : a ∈ req) {t : Ty n} (ht : t ∈ branches O {a}) :
    (⟨{a}, ∅, t⟩ : Rec n) ∈ Gstar O req := by
  sorry

theorem Gstar_child {r : Rec n} (hr : r ∈ Gstar O req) {a b : Fin n} {R : RT m}
    (hd : (a, R, b) ∈ demands O r.t) {s : Ty n}
    (hs : s ∈ branches O (insert b (fwd O r.t R))) :
    (⟨insert b (fwd O r.t R), ∅, s⟩ : Rec n) ∈ Gstar O req := by
  sorry

theorem Gstar_augment {r r' : Rec n} (hr : r ∈ Gstar O req) (hr' : r' ∈ Gstar O req)
    {a b : Fin n} {R : RT m} (hd : (a, R, b) ∈ demands O r.t)
    (hb : b ∈ r'.K) (hK : r'.K ⊆ insert b (fwd O r.t R)) {t' : Ty n}
    (ht' : t' ∈ branches O (r.K ∪ (r.A ∪ back O r'.t R))) :
    (⟨r.K, r.A ∪ back O r'.t R, t'⟩ : Rec n) ∈ Gstar O req := by
  sorry

theorem Gstar_closed {r : Rec n} (hr : r ∈ Gstar O req) : Closed O r.t := by
  sorry

theorem alive_subset : alive O req ⊆ Gstar O req := by
  sorry

theorem alive_witnessed {r : Rec n} (hr : r ∈ alive O req) : witnessed O (alive O req) r := by
  sorry

/-- Every set of `Gstar` records whose members are witnessed inside it
survives elimination. -/
theorem subset_alive {S : Finset (Rec n)} (hS : S ⊆ Gstar O req)
    (hw : ∀ r ∈ S, witnessed O S r) : S ⊆ alive O req := by
  sorry

/-- **P3, soundness.** Alive types are good. -/
theorem alive_good {r : Rec n} (hr : r ∈ alive O req) : Good O r.t := by
  sorry

end Facts

end ContextCalculus.SRI.Proc
