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

#print axioms cbAnswer_correct
#print axioms cbCheck_correct
#print axioms cbAccept_sound
#print axioms CBExecution.worker_soundAt

end ContextCalculus.KMConcreteWorkerAdapters
