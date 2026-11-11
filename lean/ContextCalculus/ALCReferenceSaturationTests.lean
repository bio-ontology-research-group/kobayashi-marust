import ContextCalculus.ALCReferenceSaturation

/-!
# Unit tests for `ALCReferenceSaturation`

Executable checks (`#eval` and `by decide`) for the computable ALC
type-elimination saturation `saturateC` and the subsumption decision bit
`alcBit`.
-/

namespace ContextCalculus.ALCReferenceSaturationTests

open ContextCalculus.Ctx
open ContextCalculus.ALCReference

/-- Disjunctive GCI ontology over four concepts `A = 0, B = 1, C = 2, D = 3`:
`A ⊑ B ⊔ C`, `B ⊑ D`, `C ⊑ D`. -/
def disjunctiveOntology : Ontology (Fin 4) (Fin 0) :=
  [ .gci [0] [1, 2]
  , .gci [1] [3]
  , .gci [2] [3] ]

#eval (saturateC disjunctiveOntology).card
#eval alcBit disjunctiveOntology 0 3
#eval alcBit disjunctiveOntology 0 1
#eval alcBit disjunctiveOntology 0 2

example : alcBit disjunctiveOntology 0 3 = true := by decide
example : alcBit disjunctiveOntology 0 1 = false := by decide
example : alcBit disjunctiveOntology 0 2 = false := by decide

/-- Existential plus universal interaction over five concepts
`A = 0, B = 1, C = 2, BC = 3, D = 4` and one role `r = 0`:
`A ⊑ ∃r.B`, `A ⊑ ∀r.C`, `B ⊓ C ⊑ BC`, `∃r.BC ⊑ D` entails `A ⊑ D`. -/
def exAllOntology : Ontology (Fin 5) (Fin 1) :=
  [ .exRight 0 0 1
  , .allRight 0 0 2
  , .gci [1, 2] [3]
  , .exLeft 0 3 4 ]

#eval (candC exAllOntology).card
#eval (saturateC exAllOntology).card
#eval alcBit exAllOntology 0 4
#eval alcBit exAllOntology 4 0
#eval alcBit exAllOntology 0 1

example : alcBit exAllOntology 0 4 = true := by decide
example : alcBit exAllOntology 4 0 = false := by decide
example : alcBit exAllOntology 0 1 = false := by decide

/-- Unsatisfiable concept via an empty-head GCI (`B ⊑ ⊥`) and propagation
across an existential restriction (`A ⊑ ∃r.B`) over three concepts
`A = 0, B = 1, C = 2` and one role `r = 0`. -/
def unsatOntology : Ontology (Fin 3) (Fin 1) :=
  [ .gci [1] []
  , .exRight 0 0 1 ]

#eval (candC unsatOntology).card
#eval (saturateC unsatOntology).card
#eval alcBit unsatOntology 1 2
#eval alcBit unsatOntology 0 2
#eval alcBit unsatOntology 2 0

example : alcBit unsatOntology 1 2 = true := by decide
example : alcBit unsatOntology 0 2 = true := by decide
example : alcBit unsatOntology 2 0 = false := by decide

end ContextCalculus.ALCReferenceSaturationTests
