import ContextCalculus.SRI.Transitivity

/-!
# Tests for the transitivity encoding

Each `#guard` runs `entails` from `Procedure.lean` on `encTrans` of a tiny
SHI ontology, with and without the transitivity clause, and checks that
transitivity changes the answer. Old names keep their index under
`Fin.castAdd`; `old O i` names old concept `i` in the encoding of `O`.
-/

namespace ContextCalculus.SRI.TransitivityTests

open ContextCalculus.SRI Proc

/-- Old concept `i` as a name of the encoding. -/
abbrev old {n m : Nat} (O : Ontology (Fin n) (Fin m)) (i : Fin n) :
    Fin (n + (encTrans O).1) :=
  Fin.castAdd _ i

/-- Ask `a ⊑ b` of the encoding, with `a` as the only required name. -/
def ask {n m : Nat} (O : Ontology (Fin n) (Fin m)) (a b : Fin n) : Bool :=
  entails (encTrans O).2 [old O a] (old O a) (old O b)

/-- Names: `A = 0`, `B = 1`, `D = 2`, `E = 3`.
`A ⊑ ∀r.B`, `A ⊑ ∃r.D`, `D ⊑ ∃r.E`, `E ⊓ B ⊑ ⊥`. -/
def base1 : Ontology (Fin 4) (Fin 1) :=
  [.allRight 0 (.pos 0) 1, .exRight 0 (.pos 0) 2, .exRight 2 (.pos 0) 3, .gci [3, 1] []]

/-- `base1` with `Trans(r)`. -/
def O1 : Ontology (Fin 4) (Fin 1) := .chain [.pos 0, .pos 0] (.pos 0) :: base1

-- With `Trans(r)`, the `E` two steps away is an `r`-successor of `A`, so it
-- is a `B` and clashes: `A` is unsatisfiable and entails `D`.
#guard ask O1 0 2
-- Without it, `A` is satisfiable and `A ⊑ D` fails.
#guard !ask base1 0 2
-- `D` stays satisfiable in both.
#guard !ask O1 2 1

/-- Names: `A = 0`, `B = 1`, `C = 2`, `D = 3`.
`A ⊑ ∃r.B`, `B ⊑ ∃r.C`, `C ⊑ ∀r⁻.D`: the universal runs along the inverse
of the transitive role, so the flipped term carries it. -/
def base2 : Ontology (Fin 4) (Fin 1) :=
  [.exRight 0 (.pos 0) 1, .exRight 1 (.pos 0) 2, .allRight 2 (.inv 0) 3]

def O2 : Ontology (Fin 4) (Fin 1) := .chain [.pos 0, .pos 0] (.pos 0) :: base2

-- With `Trans(r)`, `A` is an `r⁻`-successor of the `C`, so `A ⊑ D`.
#guard ask O2 0 3
#guard !ask base2 0 3
-- `B ⊑ D` holds in both (one step).
#guard ask O2 1 3
#guard ask base2 1 3

/-- Names: `A = 0`, `B = 1`, `C = 2`, `E = 3`.
`r ⊑ s`, `A ⊑ ∀s.B`, `A ⊑ ∃r.C`, `C ⊑ ∃r.E`: the transitive `r` sits below
the role of the universal. -/
def base3 : Ontology (Fin 4) (Fin 2) :=
  [.chain [.pos 0] (.pos 1), .allRight 0 (.pos 1) 1, .exRight 0 (.pos 0) 2,
   .exRight 2 (.pos 0) 3]

def O3 : Ontology (Fin 4) (Fin 2) := .chain [.pos 0, .pos 0] (.pos 0) :: base3

-- With `E ⊓ B ⊑ ⊥`, `A` is unsatisfiable only with `Trans(r)`, so it
-- entails `C`.
#guard ask (O3 ++ [.gci [3, 1] []]) 0 2
#guard !ask (base3 ++ [.gci [3, 1] []]) 0 2
-- `Trans(s)` also works: the `r`-edges are `s`-edges, so `E` is an
-- `s`-successor of `A`.
#guard ask (.chain [.pos 1, .pos 1] (.pos 1) :: base3 ++ [.gci [3, 1] []]) 0 2

end ContextCalculus.SRI.TransitivityTests
