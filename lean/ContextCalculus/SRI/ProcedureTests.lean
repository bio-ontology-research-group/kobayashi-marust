import ContextCalculus.SRI.Procedure

/-!
# Tests for the ALCHI decision procedure

The ontologies of `GoodTypesTests.lean` with roles over `Fin 1` or
`Fin 2`, and one with a disjunction. Concept names are `Fin 3` or `Fin 4`
(`A = 0`, `B = 1`, `C = 2`, `D = 3`). Each `#guard` runs `entails` with
`A` as the only required name.
-/

namespace ContextCalculus.SRI.ProcedureTests

open ContextCalculus.SRI

/-- `A ⊑ ∃r.B` and `B ⊑ ∀r⁻.C`. -/
def O1 : Ontology (Fin 3) (Fin 1) :=
  [.exRight 0 (.pos 0) 1, .allRight 1 (.inv 0) 2]

-- The witness of `A` sends `C` back along the inverse role.
#guard Proc.entails O1 [0] 0 2
#guard !Proc.entails O1 [0] 0 1

/-- `r ⊑ s`, `A ⊑ ∃r.B` and `B ⊑ ∀s⁻.C`. -/
def O2 : Ontology (Fin 3) (Fin 2) :=
  [.chain [.pos 0] (.pos 1), .exRight 0 (.pos 0) 1, .allRight 1 (.inv 1) 2]

-- The inclusion `r ⊑ s` gives `r⁻ ⊑* s⁻`, so `A ⊑ C` holds.
#guard Proc.entails O2 [0] 0 2

-- Without the inclusion, `A ⊑ C` fails.
#guard !Proc.entails ([.exRight 0 (.pos 0) 1, .allRight 1 (.inv 1) 2] :
  Ontology (Fin 3) (Fin 2)) [0] 0 2

/-- `A ⊑ ∃r.B` alone does not entail `A ⊑ C`. -/
def O3 : Ontology (Fin 3) (Fin 1) :=
  [.exRight 0 (.pos 0) 1]

#guard !Proc.entails O3 [0] 0 2
#guard Proc.entails O3 [0] 0 0

/-- `A ⊑ B ⊔ C`, `B ⊑ D` and `C ⊑ D`. -/
def O4 : Ontology (Fin 4) (Fin 1) :=
  [.gci [0] [1, 2], .gci [1] [3], .gci [2] [3]]

-- Both branches reach `D`, so `A ⊑ D`; neither `B` nor `C` is forced.
#guard Proc.entails O4 [0] 0 3
#guard !Proc.entails O4 [0] 0 1
#guard !Proc.entails O4 [0] 0 2

-- An unsatisfiable name entails everything: `A ⊑ ∃r.B`, `B ⊑ ⊥`.
#guard Proc.entails ([.exRight 0 (.pos 0) 1, .gci [1] []] : Ontology (Fin 3) (Fin 1)) [0] 0 2

end ContextCalculus.SRI.ProcedureTests
