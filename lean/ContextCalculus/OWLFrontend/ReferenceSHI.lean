import ContextCalculus.OWLFrontend.Reference
import ContextCalculus.OWLFrontend.SRIComplete

/-!
# The v1.6.3 OWL reference procedure: EL, then SHI

`owlReferenceSHI O requested` runs the EL route (`owlELReference`) and, when
it does not apply, the SHI route (`owlSRIReference`). The two theorems are
stated on the OWL 2 direct semantics of the ontology alone, as for
`owlReference`:

- `owlReferenceSHI_sound`: every published row is exact for
  `OWL.EntailsSub`;
- `owlReferenceSHI_complete`: on OWL EL and on the SHI part
  (`OWL.Ontology.isSHI`, which contains OWL ALC) the procedure publishes.

The SHI route has no concept budget: it does not build all types of the
signature, unlike the ALC route of `owlReference`. `owlReference` and its
theorems stay as they are.
-/

namespace ContextCalculus.OWLFrontend

/-- The v1.6.3 OWL reference procedure: EL first, then SHI. -/
def owlReferenceSHI (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match owlELReference O requested with
  | some a => some a
  | none => owlSRIReference O requested

/-- Every answer of `owlReferenceSHI` is exact under the OWL 2 direct
semantics, for every requested pair. -/
theorem owlReferenceSHI_sound {O : OWL.Ontology} {requested : List OWL.IRI}
    {a : OWLAnswer} (h : owlReferenceSHI O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlReferenceSHI at h
  split at h
  · next a' hEL =>
      cases h
      exact owlELReference_sound hEL
  · exact owlSRIReference_sound h

/-- On OWL EL and on the SHI part (so on OWL ALC too) `owlReferenceSHI`
publishes, for every requested list. -/
theorem owlReferenceSHI_complete {O : OWL.Ontology} (requested : List OWL.IRI)
    (h : O.isEL = true ∨ O.isSHI = true) :
    (owlReferenceSHI O requested).isSome = true := by
  unfold owlReferenceSHI
  rcases h with hEL | hSHI
  · have hs := translateEL_isSome (requested := requested) hEL
    split
    · rfl
    · next hnone =>
        simp [owlELReference, Option.map_eq_none_iff] at hnone
        rw [hnone] at hs
        exact absurd hs (by simp)
  · split
    · rfl
    · exact owlSRIReference_complete requested hSHI

/-- The procedure publishes on OWL ALC, which is part of SHI. -/
theorem owlReferenceSHI_complete_of_isALC {O : OWL.Ontology} (requested : List OWL.IRI)
    (h : O.isALC = true) : (owlReferenceSHI O requested).isSome = true :=
  owlReferenceSHI_complete requested (Or.inr (OWL.Ontology.isSHI_of_isALC h))

#print axioms owlReferenceSHI_sound
#print axioms owlReferenceSHI_complete
#print axioms owlReferenceSHI_complete_of_isALC

end ContextCalculus.OWLFrontend
