import ContextCalculus.KMCommonRoutingSource
import ContextCalculus.CertifiedRouting

/-!
# Concrete common taxonomy publications for KM workers

Routing composes workers only after their route-specific payload has been
converted to this one finite matrix.  Coordinates are required to be exactly
the row-major square of the named source concepts, and each Boolean is tied to
the common proper-term source semantics.
-/

namespace ContextCalculus.KMConcreteWorkerAdapters

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.KMCommonRoutingSource

structure TaxonomyCell where
  sub : Nat
  sup : Nat
  answer : Bool
deriving DecidableEq, Repr

structure TaxonomyAnswer where
  named : List Nat
  cells : List TaxonomyCell
deriving DecidableEq, Repr

def TaxonomyCell.coordinate (cell : TaxonomyCell) : Nat × Nat :=
  (cell.sub, cell.sup)

def coordinates (named : List Nat) : List (Nat × Nat) :=
  named.flatMap fun sub => named.map fun sup => (sub, sup)

/-- A complete finite taxonomy answer over the exact routed source. -/
def Correct (ontology : List FCL) (answer : TaxonomyAnswer) : Prop :=
  answer.named.Nodup ∧
  answer.cells.map TaxonomyCell.coordinate = coordinates answer.named ∧
  ∀ cell ∈ answer.cells,
    cell.answer = true ↔ Entails ontology cell.sub cell.sup

def matrixCells (named : List Nat) (answer : Nat → Nat → Bool) :
    List TaxonomyCell :=
  named.flatMap fun sub => named.map fun sup => { sub, sup, answer := answer sub sup }

def matrixAnswer (named : List Nat) (answer : Nat → Nat → Bool) :
    TaxonomyAnswer := { named, cells := matrixCells named answer }

@[simp] theorem matrixCells_coordinates (named : List Nat)
    (answer : Nat → Nat → Bool) :
    (matrixCells named answer).map TaxonomyCell.coordinate = coordinates named := by
  unfold matrixCells coordinates
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro sub _hsub
  rw [List.map_map]
  apply List.map_congr_left
  intro sup _hsup
  rfl

theorem matrixAnswer_correct (ontology : List FCL) (named : List Nat)
    (answer : Nat → Nat → Bool) (hnodup : named.Nodup)
    (hexact : ∀ sub ∈ named, ∀ sup ∈ named,
      answer sub sup = true ↔ Entails ontology sub sup) :
    Correct ontology (matrixAnswer named answer) := by
  refine ⟨hnodup, by simp [matrixAnswer], ?_⟩
  intro cell hcell
  simp only [matrixAnswer, matrixCells, List.mem_flatMap, List.mem_map] at hcell
  rcases hcell with ⟨sub, hsub, sup, hsup, rfl⟩
  exact hexact sub hsub sup hsup

def cbAnswer
    (decoded :
      CBLiveExactTaxonomyPublication.DecodedLiveExactTaxonomyPublication) :
    TaxonomyAnswer where
  named := decoded.named
  cells := decoded.cells.map fun cell => {
    sub := cell.sub
    sup := cell.sup
    answer := cell.answer
  }

theorem cbAnswer_correct
    (decoded :
      CBLiveExactTaxonomyPublication.DecodedLiveExactTaxonomyPublication) :
    Correct (cbPublicationOntology decoded) (cbAnswer decoded) := by
  refine ⟨decoded.named_nodup, ?_, ?_⟩
  · simpa [cbAnswer, TaxonomyCell.coordinate, coordinates,
      CBLiveExactTaxonomyPublication.coordinates] using decoded.coordinates_exact
  · intro cell hcell
    simp only [cbAnswer, List.mem_map] at hcell
    rcases hcell with ⟨source, _hsource, rfl⟩
    exact source.exact.trans
      (cbExactEntails_iff_common decoded.live source.sub source.sup)

/-- An accepted CB matrix produces one exact common taxonomy answer. -/
theorem cbCheck_correct
    (wire : CBLiveExactTaxonomyPublication.WireLiveExactTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    ∃ decoded :
        CBLiveExactTaxonomyPublication.DecodedLiveExactTaxonomyPublication,
      wire.decode = .ok decoded ∧
      Correct (cbPublicationOntology decoded) (cbAnswer decoded) := by
  rcases cbCheck_common_routing_source_sound wire hcheck with
    ⟨decoded, hdecode, _⟩
  exact ⟨decoded, hdecode, cbAnswer_correct decoded⟩

structure CBEvidence where
  document : CBLiveExactTaxonomyPublication.WireLiveExactTaxonomyPublication

/-- Fail-closed CB adapter acceptance.  The checker derives both source and
answer from the decoded document and compares them extensionally with the
values proposed to the router. -/
def cbAccept (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : CBEvidence) : Bool :=
  match evidence.document.decode with
  | .error _ => false
  | .ok decoded =>
      decide (ontology = cbPublicationOntology decoded ∧
        answer = cbAnswer decoded)

theorem cbAccept_sound (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : CBEvidence) (haccept : cbAccept ontology answer evidence = true) :
    Correct ontology answer := by
  cases hdecode : evidence.document.decode with
  | error message => simp [cbAccept, hdecode] at haccept
  | ok decoded =>
      simp only [cbAccept, hdecode, decide_eq_true_eq] at haccept
      rcases haccept with ⟨rfl, rfl⟩
      exact cbAnswer_correct decoded

/-- Execution evidence supplied by the native supervisor boundary.  Unlike a
route tag, publication requires the concrete CB checker above to accept the
exact source and answer returned by the process. -/
structure CBExecution where
  run : List FCL →
    Certification.Outcome
      (CertifiedRouting.Publication (List FCL) TaxonomyAnswer CBEvidence)
  sourceExact : ∀ ontology publication,
    run ontology = .publish publication → publication.source = ontology
  accepted : ∀ ontology publication,
    run ontology = .publish publication →
      cbAccept ontology publication.answer publication.evidence = true

def CBExecution.worker (execution : CBExecution) :
    CertifiedRouting.SourceBoundWorker (List FCL) TaxonomyAnswer CBEvidence Correct where
  run := execution.run
  accept := cbAccept
  run_source_exact := execution.sourceExact
  run_accepted := execution.accepted
  accept_sound := cbAccept_sound

theorem CBExecution.worker_soundAt (execution : CBExecution)
    (ontology : List FCL) :
    Certification.SoundAt Correct execution.worker.erase ontology :=
  execution.worker.erase_soundAt ontology

def elcBit (decoded : ELCompletion.DecodedCertificate n)
    (sub sup : Fin n) : Bool :=
  if sub = sup then true
  else if (sub, decoded.bottom) ∈ decoded.public_subsumptions then true
  else decide ((sub, sup) ∈ decoded.public_subsumptions)

theorem elc_entails_of_bottom
    (decoded : ELCompletion.DecodedCertificate n) (sub sup : Fin n)
    (hbottom : ELCompletion.EntailsSubWithResidual decoded.ontology
      decoded.sourceResidualTheory sub decoded.bottom) :
    ELCompletion.EntailsSubWithResidual decoded.ontology
      decoded.sourceResidualTheory sub sup := by
  intro Domain interpretation hmodels value hsub
  have hfalse := hbottom interpretation hmodels value hsub
  exact (interpretation.bottom_false value hfalse).elim

theorem elcBit_exact
    (decoded : ELCompletion.DecodedCertificate n)
    (publication : ELCompletion.PublicationSemantics decoded)
    (sub sup : Fin n)
    (hactive : sub ∈ decoded.active_concepts)
    (hsubTop : sub ≠ decoded.top)
    (hsubBottom : sub ≠ decoded.bottom)
    (hsupTop : sup ≠ decoded.top) :
    elcBit decoded sub sup = true ↔
      ELCompletion.EntailsSubWithResidual decoded.ontology
        decoded.sourceResidualTheory sub sup := by
  by_cases heq : sub = sup
  · subst sup
    simp only [elcBit]
    constructor
    · intro _ Domain interpretation _hmodels value hsub
      exact hsub
    · intro _
      trivial
  · have hbottomNeSub : decoded.bottom ≠ sub := hsubBottom.symm
    have hbottomNeTop : decoded.bottom ≠ decoded.top :=
      decoded.top_ne_bottom.symm
    have hbottomExact := publication.id_taxonomy_exact hactive hsubTop
      hsubBottom hbottomNeSub hbottomNeTop (Or.inl rfl)
    by_cases hbottomPublic :
        (sub, decoded.bottom) ∈ decoded.public_subsumptions
    · have hbottomEntails :
          ELCompletion.EntailsSubWithResidual decoded.ontology
            decoded.sourceResidualTheory sub decoded.bottom :=
        hbottomExact.mp hbottomPublic
      constructor
      · intro _
        exact elc_entails_of_bottom decoded sub sup hbottomEntails
      · intro _
        simp [elcBit, heq, hbottomPublic]
    · have hnotBottom : ¬ ELCompletion.EntailsSubWithResidual decoded.ontology
          decoded.sourceResidualTheory sub decoded.bottom := by
        intro hentails
        exact hbottomPublic (hbottomExact.mpr hentails)
      have hexact := publication.id_taxonomy_exact hactive hsubTop hsubBottom
        (fun h => heq h.symm) hsupTop (Or.inr hnotBottom)
      simpa [elcBit, heq, hbottomPublic] using hexact

def elcNamedFin (decoded : ELCompletion.DecodedCertificate n) : List (Fin n) :=
  (List.finRange n).filter fun concept =>
    decide (concept ∈ decoded.active_concepts ∧
      concept ≠ decoded.top ∧ concept ≠ decoded.bottom)

def elcNamed (decoded : ELCompletion.DecodedCertificate n) : List Nat :=
  (elcNamedFin decoded).map Fin.val

theorem elcNamed_nodup (decoded : ELCompletion.DecodedCertificate n) :
    (elcNamed decoded).Nodup := by
  apply List.Nodup.map
    (fun left right hval => Fin.ext hval)
  exact (List.nodup_finRange n).filter _

def elcNatBit (decoded : ELCompletion.DecodedCertificate n)
    (sub sup : Nat) : Bool :=
  if hsub : sub < n then
    if hsup : sup < n then elcBit decoded ⟨sub, hsub⟩ ⟨sup, hsup⟩
    else false
  else false

def elcAnswer (decoded : ELCompletion.DecodedCertificate n) : TaxonomyAnswer :=
  matrixAnswer (elcNamed decoded) (elcNatBit decoded)

theorem elcAnswer_correct
    (decoded : ELCompletion.DecodedCertificate n)
    (publication : ELCompletion.PublicationSemantics decoded) :
    Correct (elcWireOntology decoded) (elcAnswer decoded) := by
  apply matrixAnswer_correct _ _ _ (elcNamed_nodup decoded)
  intro sub hsub sup hsup
  rcases List.mem_map.mp hsub with ⟨subFin, hsubFin, rfl⟩
  rcases List.mem_map.mp hsup with ⟨supFin, hsupFin, rfl⟩
  have hsubProperties := (List.mem_filter.mp hsubFin).2
  have hsupProperties := (List.mem_filter.mp hsupFin).2
  simp only [decide_eq_true_eq] at hsubProperties hsupProperties
  rw [elcWireEntails_iff decoded subFin supFin]
  simpa [elcNatBit, subFin.isLt, supFin.isLt] using
    elcBit_exact decoded publication subFin supFin hsubProperties.1
      hsubProperties.2.1 hsubProperties.2.2 hsupProperties.2.1

theorem elcCheck_correct (wire : ELCompletion.WireCertificate)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : ELCompletion.DecodedCertificate wire.symbol_count,
      wire.decode = .ok decoded ∧
      Correct (elcWireOntology decoded) (elcAnswer decoded) := by
  rcases ELCompletion.WireCertificate.check_common_routing_source_sound
      wire hcheck with
    ⟨decoded, hdecode, publication, _⟩
  exact ⟨decoded, hdecode, elcAnswer_correct decoded publication⟩

structure ELCEvidence where
  document : ELCompletion.WireCertificate

/-- Fail-closed ELC adapter acceptance.  Both the executable V5 checker and
the exact decode must succeed before the source and answer are compared with
the values proposed to the router. -/
def elcAccept (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : ELCEvidence) : Bool :=
  match evidence.document.check with
  | .error _ => false
  | .ok false => false
  | .ok true =>
      match evidence.document.decode with
      | .error _ => false
      | .ok decoded =>
          decide (ontology = elcWireOntology decoded ∧
            answer = elcAnswer decoded)

theorem elcAccept_sound (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : ELCEvidence)
    (haccept : elcAccept ontology answer evidence = true) :
    Correct ontology answer := by
  cases hcheck : evidence.document.check with
  | error message => simp [elcAccept, hcheck] at haccept
  | ok checked =>
      cases checked with
      | false => simp [elcAccept, hcheck] at haccept
      | true =>
          cases hdecode : evidence.document.decode with
          | error message => simp [elcAccept, hcheck, hdecode] at haccept
          | ok decoded =>
              simp only [elcAccept, hcheck, hdecode, decide_eq_true_eq] at haccept
              rcases haccept with ⟨rfl, rfl⟩
              rcases elcCheck_correct evidence.document hcheck with
                ⟨checkedDecoded, checkedDecode, correct⟩
              rw [hdecode] at checkedDecode
              cases checkedDecode
              exact correct

structure ELCExecution where
  run : List FCL →
    Certification.Outcome
      (CertifiedRouting.Publication (List FCL) TaxonomyAnswer ELCEvidence)
  sourceExact : ∀ ontology publication,
    run ontology = .publish publication → publication.source = ontology
  accepted : ∀ ontology publication,
    run ontology = .publish publication →
      elcAccept ontology publication.answer publication.evidence = true

def ELCExecution.worker (execution : ELCExecution) :
    CertifiedRouting.SourceBoundWorker
      (List FCL) TaxonomyAnswer ELCEvidence Correct where
  run := execution.run
  accept := elcAccept
  run_source_exact := execution.sourceExact
  run_accepted := execution.accepted
  accept_sound := elcAccept_sound

theorem ELCExecution.worker_soundAt (execution : ELCExecution)
    (ontology : List FCL) :
    Certification.SoundAt Correct execution.worker.erase ontology :=
  execution.worker.erase_soundAt ontology

#print axioms cbAnswer_correct
#print axioms cbCheck_correct
#print axioms cbAccept_sound
#print axioms CBExecution.worker_soundAt
#print axioms elcBit_exact
#print axioms elcAnswer_correct
#print axioms elcCheck_correct
#print axioms elcAccept_sound
#print axioms ELCExecution.worker_soundAt

end ContextCalculus.KMConcreteWorkerAdapters
