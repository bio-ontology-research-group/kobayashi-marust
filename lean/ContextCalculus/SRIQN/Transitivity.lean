import ContextCalculus.SRIQN.Rows
import ContextCalculus.SRIQ.ABox

/-!
# Transitivity with nominals (stage C2, design section 8)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. `encTransN` applies the SHIQ
transitivity encoding `SRIQ.Proc.encTransQ` to the base part and keeps the
nominal clauses on the old names. Both model maps of the SHIQ encoding
(`SRI.Proc.upI`, `SRI.Proc.downI`) leave the extensions of the old names
unchanged, so nominal clauses hold on one side iff they hold on the other
(`consistentN_encTransN`, `entailsSubN_encTransN`). The encoding is ALCHOIQ
(`isALCHOIQ_encTransN`).
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)

variable {n m : Nat}

/-- SHOIQ: the base part is SHIQ (inclusions and transitivity, simple
roles in counting clauses). -/
def IsSHOIQ (O : Ontology (Fin n) (Fin m)) : Prop := SRIQ.Proc.IsSHIQ (basePart O)

/-- The number of names the encoding adds. -/
abbrev encK (O : Ontology (Fin n) (Fin m)) : Nat :=
  (SRIQ.Proc.encTransQ (basePart O)).1

/-- **The transitivity encoding with nominals.** -/
def encTransN (O : Ontology (Fin n) (Fin m)) : Ontology (Fin (n + encK O)) (Fin m) :=
  ofSRIQ (SRIQ.Proc.encTransQ (basePart O)).2 ++ (noms O).map fun a => .nom (Fin.castAdd (encK O) a)

theorem basePart_ofSRIQ_noms {C C' Role : Type} (X : SRIQ.Ontology C Role) (L : List C')
    (f : C' → C) : basePart (ofSRIQ X ++ L.map fun a => .nom (f a)) = X := by
  rw [basePart_append, basePart_ofSRIQ]
  simp [basePart, List.filterMap_map]

theorem basePart_encTransN (O : Ontology (Fin n) (Fin m)) :
    basePart (encTransN O) = (SRIQ.Proc.encTransQ (basePart O)).2 :=
  basePart_ofSRIQ_noms _ _ _

theorem noms_encTransN (O : Ontology (Fin n) (Fin m)) :
    noms (encTransN O) = (noms O).map (Fin.castAdd _) := by
  simp only [encTransN, noms, ofSRIQ, List.filterMap_append, List.filterMap_map]
  simp [List.map_filterMap]

theorem isALCHOIQ_encTransN (O : Ontology (Fin n) (Fin m)) : IsALCHOIQ (encTransN O) := by
  have h := SRIQ.Proc.encTransQ_isALCHIQ (basePart O)
  rw [← basePart_encTransN] at h
  exact h

theorem models_encTransN_up {D : Type} {O : Ontology (Fin n) (Fin m)}
    {I : Interp D (Fin n) (Fin m)} (hI : models I O) :
    models (SRI.Proc.upI (SRIQ.sriPart (basePart O)) I) (encTransN O) := by
  obtain ⟨hb, hn⟩ := models_iff.1 hI
  refine models_iff.2 ⟨?_, ?_⟩
  · have h := SRIQ.Proc.models_upI hb
    rw [← basePart_encTransN] at h
    exact h
  · intro a' ha'
    have ha'' : a' ∈ noms (encTransN O) := ha'
    rw [noms_encTransN] at ha''
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha''
    obtain ⟨x, hx⟩ := hn a ha
    exact ⟨x, fun y => (SRI.Proc.upI_old I a y).trans (hx y)⟩

theorem models_encTransN_down {D : Type} {O : Ontology (Fin n) (Fin m)} (h : IsSHOIQ O)
    {J : Interp D (Fin (n + encK O)) (Fin m)} (hJ : models J (encTransN O)) :
    models (SRI.Proc.downI (SRIQ.sriPart (basePart O)) J) O := by
  obtain ⟨hb, hn⟩ := models_iff.1 hJ
  have hb' : SRIQ.models J (SRIQ.Proc.encTransQ (basePart O)).2 := by
    rw [← basePart_encTransN]
    exact hb
  refine models_iff.2 ⟨SRIQ.Proc.models_downI h hb', fun a ha => ?_⟩
  have := hn (Fin.castAdd _ a) (by rw [noms_encTransN]; exact List.mem_map_of_mem ha)
  exact this

/-- **Transitivity removal keeps consistency.** -/
theorem consistentN_encTransN {O : Ontology (Fin n) (Fin m)} (h : IsSHOIQ O) :
    ConsistentN O ↔ ConsistentN (encTransN O) := by
  constructor
  · rintro ⟨D, hD, I, hI⟩
    exact ⟨D, hD, _, models_encTransN_up hI⟩
  · rintro ⟨D, hD, J, hJ⟩
    exact ⟨D, hD, _, models_encTransN_down h hJ⟩

/-- **Transitivity removal keeps subsumption** between old names. -/
theorem entailsSubN_encTransN {O : Ontology (Fin n) (Fin m)} (h : IsSHOIQ O) (a b : Fin n) :
    EntailsSubN O a b ↔ EntailsSubN (encTransN O) (Fin.castAdd _ a) (Fin.castAdd _ b) := by
  constructor
  · intro hO D _ J hJ x hx
    exact hO D _ (models_encTransN_down h hJ) x hx
  · intro hE D _ I hI x hx
    have := hE D _ (models_encTransN_up hI) x ((SRI.Proc.upI_old I a x).2 hx)
    exact (SRI.Proc.upI_old I b x).1 this

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.consistentN_encTransN
#print axioms ContextCalculus.SRIQN.entailsSubN_encTransN
#print axioms ContextCalculus.SRIQN.isALCHOIQ_encTransN
