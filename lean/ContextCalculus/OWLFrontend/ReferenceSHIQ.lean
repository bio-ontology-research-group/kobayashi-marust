import ContextCalculus.OWLFrontend.ReferenceSHI
import ContextCalculus.OWLFrontend.SRIQComplete

/-!
# The v1.7.0 OWL reference procedure: EL, then SHI, then SHIQ

`owlReferenceSHIQ O requested` runs the v1.6.3 procedure
`owlReferenceSHI` (the EL route, then the SHI route) and, when neither
applies, the SHIQ route (`owlSHIQReference`). The two theorems are stated
on the OWL 2 direct semantics of the ontology alone, as for
`owlReferenceSHI`:

- `owlReferenceSHIQ_sound`: every published row is exact for
  `OWL.EntailsSub`;
- `owlReferenceSHIQ_complete`: on OWL EL, on the SHI part, and on the
  SHIQ part with the simple-role check passed (`SHIQSimple`) the procedure
  publishes.

`owlReferenceSHI` and its theorems stay as they are.
-/

namespace ContextCalculus.OWLFrontend

/-- The v1.7.0 OWL reference procedure: EL, then SHI, then SHIQ. -/
def owlReferenceSHIQ (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match owlReferenceSHI O requested with
  | some a => some a
  | none => owlSHIQReference O requested

/-- Every answer of `owlReferenceSHIQ` is exact under the OWL 2 direct
semantics, for every requested pair. -/
theorem owlReferenceSHIQ_sound {O : OWL.Ontology} {requested : List OWL.IRI}
    {a : OWLAnswer} (h : owlReferenceSHIQ O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlReferenceSHIQ at h
  split at h
  · next a' hSHI =>
      cases h
      exact owlReferenceSHI_sound hSHI
  · exact owlSHIQReference_sound h

/-- On OWL EL, on the SHI part (so on OWL ALC too), and on the SHIQ part
with the simple-role check passed, `owlReferenceSHIQ` publishes, for every
requested list. -/
theorem owlReferenceSHIQ_complete {O : OWL.Ontology} (requested : List OWL.IRI)
    (h : O.isEL = true ∨ O.isSHI = true ∨ (O.isSHIQ = true ∧ SHIQSimple O requested)) :
    (owlReferenceSHIQ O requested).isSome = true := by
  unfold owlReferenceSHIQ
  rcases h with hEL | hSHI | ⟨hQ, hs⟩
  · have := owlReferenceSHI_complete requested (Or.inl hEL)
    split
    · rfl
    · next hnone => rw [hnone] at this; exact absurd this (by simp)
  · have := owlReferenceSHI_complete requested (Or.inr hSHI)
    split
    · rfl
    · next hnone => rw [hnone] at this; exact absurd this (by simp)
  · split
    · rfl
    · exact owlSHIQReference_complete requested hQ hs

#print axioms owlReferenceSHIQ_sound
#print axioms owlReferenceSHIQ_complete

end ContextCalculus.OWLFrontend
