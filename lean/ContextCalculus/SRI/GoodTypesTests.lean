import ContextCalculus.SRI.GoodTypes

/-!
# Tests for the ALCHI good types

Small ontologies over `Fin 3` concept names (`A = 0`, `B = 1`, `C = 2`).
Each example derives a subsumption, or refutes one, through
`entailsSub_iff_good`: the proof works on good types, never on models.
-/

namespace ContextCalculus.SRI.GoodTypesTests

open ContextCalculus.SRI

/-- `A ⊑ ∃r.B` and `B ⊑ ∀r⁻.C`. -/
def O1 : Ontology (Fin 3) Unit :=
  [.exRight 0 (.pos ()) 1, .allRight 1 (.inv ()) 2]

theorem O1_alchi : IsALCHI O1 := by
  intro body S h
  simp [O1] at h

/-- `A ⊑ ∃r.B`, `B ⊑ ∀r⁻.C` entail `A ⊑ C`: the witness of `A` sends
`C` back along the inverse role. -/
example : EntailsSub O1 0 2 := by
  rw [entailsSub_iff_good O1 O1_alchi]
  rintro t ⟨G, htG, hG⟩ ha
  obtain ⟨s, -, hbs, hc⟩ := (hG t htG).2 0 (.pos ()) 1 (by simp [O1]) ha
  exact hc.2 1 (.inv ()) 2 (by simp [O1]) Relation.ReflTransGen.refl hbs

/-- `r ⊑ s`, `A ⊑ ∃r.B` and `B ⊑ ∀s⁻.C`. -/
def O2 : Ontology (Fin 3) (Fin 2) :=
  [.chain [.pos 0] (.pos 1), .exRight 0 (.pos 0) 1, .allRight 1 (.inv 1) 2]

theorem O2_alchi : IsALCHI O2 := by
  intro body S h
  simp [O2] at h
  obtain ⟨rfl, -⟩ := h
  rfl

/-- The role inclusion `r ⊑ s` gives `r⁻ ⊑* s⁻`, so `A ⊑ C` holds. -/
example : EntailsSub O2 0 2 := by
  rw [entailsSub_iff_good O2 O2_alchi]
  rintro t ⟨G, htG, hG⟩ ha
  obtain ⟨s, -, hbs, hc⟩ := (hG t htG).2 0 (.pos 0) 1 (by simp [O2]) ha
  have hle : RoleLe O2 (RoleT.pos (0 : Fin 2)).flip (.inv 1) :=
    Relation.ReflTransGen.single (Or.inr (by simp [O2, RoleT.flip]))
  exact hc.2 1 (.inv 1) 2 (by simp [O2]) hle hbs

/-- `A ⊑ ∃r.B` alone does not entail `A ⊑ C`: the good type `{A, B}`
contains `A` and not `C`. -/
example : ¬ EntailsSub (([.exRight 0 (.pos ()) 1] : Ontology (Fin 3) Unit)) 0 2 := by
  rw [entailsSub_iff_good _ (by intro body S h; simp at h)]
  intro h
  have hgood : Good ([.exRight 0 (.pos ()) 1] : Ontology (Fin 3) Unit) {0, 1} := by
    refine ⟨{{0, 1}}, Finset.mem_singleton_self _, ?_⟩
    intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    refine ⟨fun body head hcl _ => by simp at hcl, ?_⟩
    intro a R b hcl _
    simp only [List.mem_singleton, Clause.exRight.injEq] at hcl
    obtain ⟨rfl, rfl, rfl⟩ := hcl
    refine ⟨{0, 1}, Finset.mem_singleton_self _, by decide, ?_, ?_⟩
    · intro a S c hcl; simp at hcl
    · intro a S c hcl; simp at hcl
  exact absurd (h _ hgood (by decide)) (by decide)

end ContextCalculus.SRI.GoodTypesTests
