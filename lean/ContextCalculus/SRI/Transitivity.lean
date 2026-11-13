import ContextCalculus.SRI.Procedure

/-!
# Transitivity by universal propagation (v1.6.3 plan, section 2d)

SHI clauses have role chains of two shapes: inclusions `[R] ⊑ S` and
transitivity `[T, T] ⊑ T`. `encTrans` drops the transitivity clauses and
adds, for every `allRight a S c` and every transitive role term `T` (or
the flip of one) with `T ⊑* S`, a fresh name `q` with

- `allRight a T q`, `gci [q] [c]`, `allRight q T q`.

The result is ALCHI and has the same subsumptions between old names.
-/

namespace ContextCalculus.SRI.Proc

open ContextCalculus.SRI

variable {n m : Nat}

/-- Chains are inclusions or transitivity. -/
def IsSHI (O : Ontology (Fin n) (Fin m)) : Prop :=
  ∀ body S, Clause.chain body S ∈ O → body.length = 1 ∨ body = [S, S]

section Enc

variable (O : Ontology (Fin n) (Fin m))

/-- The transitive role terms, closed under flip. -/
def transTerms : List (RT m) :=
  let base := O.filterMap fun
    | .chain [R, S] T => if R = T ∧ S = T then some T else none
    | _ => none
  (base ++ base.map RoleT.flip).dedup

/-- One fresh name per universal restriction and transitive sub-role. -/
def transPairs : List ((Fin n × RT m × Fin n) × RT m) :=
  (alls O).flatMap fun q =>
    ((transTerms O).filter fun T => decide (q.2.1 ∈ roleUp O T)).map fun T => (q, T)

def liftClause (k : Nat) : Clause (Fin n) (Fin m) → Option (Clause (Fin (n + k)) (Fin m))
  | .gci body head => some (.gci (body.map (Fin.castAdd k)) (head.map (Fin.castAdd k)))
  | .exRight a R b => some (.exRight (Fin.castAdd k a) R (Fin.castAdd k b))
  | .allRight a R b => some (.allRight (Fin.castAdd k a) R (Fin.castAdd k b))
  | .chain [R] S => some (.chain [R] S)
  | .chain _ _ => none

/-- The encoding. -/
def encTrans : Σ k, Ontology (Fin (n + k)) (Fin m) :=
  let P := transPairs O
  ⟨P.length,
    O.filterMap (liftClause P.length) ++
      (P.zipIdx.flatMap fun ⟨⟨⟨a, _, c⟩, T⟩, i⟩ =>
        if h : i < P.length then
          let q : Fin (n + P.length) := Fin.natAdd n ⟨i, h⟩
          [.allRight (Fin.castAdd _ a) T q, .gci [q] [Fin.castAdd _ c], .allRight q T q]
        else [])⟩

end Enc

theorem encTrans_isALCHI (O : Ontology (Fin n) (Fin m)) : IsALCHI (encTrans O).2 := by
  sorry

/-- **P5.** The encoding keeps subsumption between the old names. -/
theorem encTrans_correct {O : Ontology (Fin n) (Fin m)} (h : IsSHI O) (a b : Fin n) :
    EntailsSub O a b ↔
      EntailsSub (encTrans O).2 (Fin.castAdd _ a) (Fin.castAdd _ b) := by
  sorry

end ContextCalculus.SRI.Proc
