import ContextCalculus.OWLFrontend.SRITranslateCorrect
import ContextCalculus.OWLFrontend.Reference
import ContextCalculus.SRI.Fast
import ContextCalculus.SRI.Transitivity

/-!
# The v1.6.3 OWL route: SHI through the SRI normal form

`docs/V1.6.3-HT-PLAN.md`. `owlSRIReference` translates the ontology to the
SRI normal form (`translateSRI`), checks that every role chain is an
inclusion or a transitivity axiom, removes transitivity (`encTrans`),
classifies the requested names with the fast procedure (`classify`) and
reads out one sparse row per requested IRI, in the format of the EL and
ALC routes. `owlSRIReference_sound`: every published row is exact for
`OWL.EntailsSub`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy
open ContextCalculus.SRI
open ContextCalculus.SRI.Proc

/-- Chains are inclusions or transitivity (`IsSHI`), as a Boolean. -/
def chainOK {n m : Nat} : SRI.Clause (Fin n) (Fin m) → Bool
  | .chain body S => body.length == 1 || body == [S, S]
  | _ => true

def isSHIB {n m : Nat} (O : SRI.Ontology (Fin n) (Fin m)) : Bool :=
  O.all chainOK

theorem isSHI_of_isSHIB {n m : Nat} {O : SRI.Ontology (Fin n) (Fin m)}
    (h : isSHIB O = true) : IsSHI O := by
  intro body S hc
  have := List.all_eq_true.1 h _ hc
  simp only [chainOK, Bool.or_eq_true, beq_iff_eq] at this
  exact this

/-- The requested indices `0 .. named.length - 1`, as names of the
encoding. -/
def sriRequest (T : SRITranslation) (k : Nat) : List (Fin (T.conceptCount + k)) :=
  (List.range T.named.length).filterMap fun i =>
    if h : i < T.conceptCount then some (Fin.castAdd k ⟨i, h⟩) else none

/-- One row per requested index: its subsumers among the requested indices. -/
def sriRows (T : SRITranslation) {k m : Nat}
    (cls : List (Fin (T.conceptCount + k) × List (Fin (T.conceptCount + k)))) :
    List SparseRow :=
  cls.map fun p =>
    { sub := p.1.val, unsat := false,
      sups := (p.2.map Fin.val).filter (· < T.named.length) }

/-- The SHI route. -/
def owlSRIReference (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match translateSRI O requested with
  | none => none
  | some T =>
      if isSHIB T.ontology then
        let E := encTrans T.ontology
        some { named := T.named,
               rows := sriRows T (m := T.roleCount) (classify E.2 (sriRequest T E.1)) }
      else none

end ContextCalculus.OWLFrontend
