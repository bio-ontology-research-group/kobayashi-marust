import ContextCalculus.SRIQ.Procedure

/-!
# Tests for the ALCHIQ elimination procedure

Roles are `Fin 1` (`R = 0`). Each ontology has a top name `T` with
`⊤ ⊑ T` (`gci [] [T]`), so `≤k R.⊤` is written `≤k R.T`. `satQ` answers
satisfiability of a name, `entailsQ` subsumption.
-/

namespace ContextCalculus.SRIQ.ProcedureTests

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ

/-- Functionality forces a clash: `A ⊑ ∃R.B`, `A ⊑ ∃R.C`, `B ⊓ C ⊑ ⊥`,
`A ⊑ ≤1 R.T` (`A = 0`, `B = 1`, `C = 2`, `T = 3`). -/
def F1 : Ontology (Fin 4) (Fin 1) :=
  [.gci [] [3], .exRight 0 (.pos 0) 1, .exRight 0 (.pos 0) 2, .gci [1, 2] [],
    .atMost 0 1 (.pos 0) 3]

#guard !Proc.satQ F1 0
#guard Proc.satQ F1 1
-- Without the at-most clause `A` is satisfiable.
#guard Proc.satQ (F1.take 4) 0
-- With `≤2` it is satisfiable too.
#guard Proc.satQ ((F1.take 4) ++ [.atMost 0 2 (.pos 0) 3]) 0

/-- `≥2` against `≤1`: `A ⊑ ≥2 R.B`, `A ⊑ ≤1 R.T` (`A = 0`, `B = 1`, `T = 2`). -/
def F2 : Ontology (Fin 3) (Fin 1) :=
  [.gci [] [2], .atLeast 0 2 (.pos 0) 1, .atMost 0 1 (.pos 0) 2]

#guard !Proc.satQ F2 0
#guard Proc.entailsQ F2 0 1
-- `≥2` against `≤2` is satisfiable, and `A ⊑ B` fails.
#guard Proc.satQ ([.gci [] [2], .atLeast 0 2 (.pos 0) 1, .atMost 0 2 (.pos 0) 2] :
  Ontology (Fin 3) (Fin 1)) 0
#guard !Proc.entailsQ ([.gci [] [2], .atLeast 0 2 (.pos 0) 1, .atMost 0 2 (.pos 0) 2] :
  Ontology (Fin 3) (Fin 1)) 0 1

/-- Counting through an inverse role: `A ⊑ ∃R⁻.B`, `A ⊑ ∃R⁻.C`,
`B ⊓ C ⊑ ⊥`, `A ⊑ ≤1 R⁻.T`. -/
def F3 : Ontology (Fin 4) (Fin 1) :=
  [.gci [] [3], .exRight 0 (.inv 0) 1, .exRight 0 (.inv 0) 2, .gci [1, 2] [],
    .atMost 0 1 (.inv 0) 3]

#guard !Proc.satQ F3 0
-- `≤1 R.T` does not restrict the `R⁻`-neighbours.
#guard Proc.satQ ([.gci [] [3], .exRight 0 (.inv 0) 1, .exRight 0 (.inv 0) 2, .gci [1, 2] [],
    .atMost 0 1 (.pos 0) 3] : Ontology (Fin 4) (Fin 1)) 0

/-- A parent counts toward an at-most: `A ⊑ ∃R.B`, `B ⊑ ∃R⁻.C`,
`B ⊑ ≤1 R⁻.T`. The `R`-predecessor `A` is the only `R⁻`-neighbour of
`B`, so it is `C`. -/
def F4 : Ontology (Fin 4) (Fin 1) :=
  [.gci [] [3], .exRight 0 (.pos 0) 1, .exRight 1 (.inv 0) 2, .atMost 1 1 (.inv 0) 3]

#guard Proc.entailsQ F4 0 2
#guard Proc.satQ F4 0
-- Without the at-most clause, `A ⊑ C` fails.
#guard !Proc.entailsQ (F4.take 3) 0 2
#guard Proc.classifyQ F4 [0, 1] == [(0, [0, 2, 3]), (1, [1, 3])]

/-- Only infinite models: `Z ⊑ A`, `A ⊑ ∃R.A`, `T ⊑ ≤1 R⁻.T`, and
`Z ⊑ ∀R⁻.E` with `E ⊑ ⊥` (no `R`-predecessor at `Z`) (`Z = 0`, `A = 1`,
`E = 2`, `T = 3`). `Z` is satisfiable, by an infinite chain only. -/
def F5 : Ontology (Fin 4) (Fin 1) :=
  [.gci [] [3], .gci [0] [1], .exRight 1 (.pos 0) 1, .atMost 3 1 (.inv 0) 3,
    .allRight 0 (.inv 0) 2, .gci [2] []]

#guard Proc.satQ F5 0
#guard !Proc.satQ F5 2
#guard Proc.entailsQ F5 0 1
#guard !Proc.entailsQ F5 1 0

/-- An element can be its own successor: `A ⊑ ∃R.A` with `R` functional
and inverse functional has a one-element model with a loop; the
procedure finds `A` satisfiable (its stars unravel the loop into a
chain), and `A ⊑ ∀R.B` gives `A ⊑ B` only through the successor. -/
def F6 : Ontology (Fin 3) (Fin 1) :=
  [.gci [] [2], .exRight 0 (.pos 0) 0, .atMost 2 1 (.pos 0) 2, .atMost 2 1 (.inv 0) 2,
    .allRight 0 (.pos 0) 1]

#guard Proc.satQ F6 0
#guard !Proc.entailsQ F6 0 1

end ContextCalculus.SRIQ.ProcedureTests
