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

def finNamed (named : List (Fin n)) : List Nat :=
  named.map Fin.val

def finNatBit (bit : Fin n → Fin n → Bool) (sub sup : Nat) : Bool :=
  if hsub : sub < n then
    if hsup : sup < n then bit ⟨sub, hsub⟩ ⟨sup, hsup⟩
    else false
  else false

def finBooleanAnswer (named : List (Fin n))
    (bit : Fin n → Fin n → Bool) : TaxonomyAnswer :=
  matrixAnswer (finNamed named)
    (finNatBit bit)

def finTaxonomyAnswer (named : List (Fin n))
    (subsumptions : List (Fin n × Fin n)) : TaxonomyAnswer :=
  finBooleanAnswer named fun sub sup => decide ((sub, sup) ∈ subsumptions)

theorem finNamed_nodup (named : List (Fin n)) (hnodup : named.Nodup) :
    (finNamed named).Nodup := by
  apply List.Nodup.map (fun _ _ equality => Fin.ext equality)
  exact hnodup

theorem finTaxonomyAnswer_correct (ontology : List FCL)
    (named : List (Fin n)) (hnodup : named.Nodup)
    (subsumptions : List (Fin n × Fin n))
    (hexact : ∀ sub sup, sub ∈ named → sup ∈ named →
      ((sub, sup) ∈ subsumptions ↔ Entails ontology sub.val sup.val)) :
    Correct ontology (finTaxonomyAnswer named subsumptions) := by
  apply matrixAnswer_correct ontology _ _ (finNamed_nodup named hnodup)
  intro sub hsub sup hsup
  rcases List.mem_map.mp hsub with ⟨subFin, hsubFin, rfl⟩
  rcases List.mem_map.mp hsup with ⟨supFin, hsupFin, rfl⟩
  simpa [finTaxonomyAnswer, finBooleanAnswer, finNatBit,
    subFin.isLt, supFin.isLt] using
    hexact subFin supFin hsubFin hsupFin

theorem finBooleanAnswer_correct (ontology : List FCL)
    (named : List (Fin n)) (hnodup : named.Nodup)
    (bit : Fin n → Fin n → Bool)
    (hexact : ∀ sub sup, sub ∈ named → sup ∈ named →
      (bit sub sup = true ↔ Entails ontology sub.val sup.val)) :
    Correct ontology (finBooleanAnswer named bit) := by
  apply matrixAnswer_correct ontology _ _ (finNamed_nodup named hnodup)
  intro sub hsub sup hsup
  rcases List.mem_map.mp hsub with ⟨subFin, hsubFin, rfl⟩
  rcases List.mem_map.mp hsup with ⟨supFin, hsupFin, rfl⟩
  simpa [finBooleanAnswer, finNatBit, subFin.isLt, supFin.isLt] using
    hexact subFin supFin hsubFin hsupFin

def selectedFin (n : Nat) (predicate : Fin n → Bool) : List (Fin n) :=
  (List.finRange n).filter fun concept => predicate concept

theorem selectedFin_nodup (n : Nat) (predicate : Fin n → Bool) :
    (selectedFin n predicate).Nodup :=
  (List.nodup_finRange n).filter _

theorem mem_selectedFin_iff (concept : Fin n) (predicate : Fin n → Bool) :
    concept ∈ selectedFin n predicate ↔ predicate concept = true := by
  simp [selectedFin]

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

def directHTAnswer :
    HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication →
      TaxonomyAnswer
  | .plain decoded _ =>
      finTaxonomyAnswer decoded.target.named decoded.semantic.subsumptions
  | .mixed decoded _ =>
      finTaxonomyAnswer decoded.target.named decoded.semantic.subsumptions

theorem directHTAnswer_correct
    (decoded :
      HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication) :
    Correct (directHTPublicationOntology decoded) (directHTAnswer decoded) := by
  have semantics := directHTRoutingSemantics decoded
  cases decoded with
  | plain publication direct =>
      apply finTaxonomyAnswer_correct _ _ publication.target.namedNodup _
      exact semantics.2
  | mixed publication direct =>
      apply finTaxonomyAnswer_correct _ _ publication.target.namedNodup _
      exact semantics.2

theorem directHTCheck_correct
    (wire : HTDirectTaxonomyCommonPublication.WireDirectTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    ∃ decoded :
        HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication,
      wire.decode = .ok decoded ∧
      Correct (directHTPublicationOntology decoded) (directHTAnswer decoded) := by
  rcases directHTCheck_common_routing_source_sound wire hcheck with
    ⟨_, _, decoded, hdecode, _⟩
  exact ⟨decoded, hdecode, directHTAnswer_correct decoded⟩

structure DirectHTEvidence where
  document : HTDirectTaxonomyCommonPublication.WireDirectTaxonomyPublication

def directHTAccept (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : DirectHTEvidence) : Bool :=
  match evidence.document.check with
  | .error _ => false
  | .ok false => false
  | .ok true =>
      match evidence.document.decode with
      | .error _ => false
      | .ok decoded =>
          decide (ontology = directHTPublicationOntology decoded ∧
            answer = directHTAnswer decoded)

theorem directHTAccept_sound (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : DirectHTEvidence)
    (haccept : directHTAccept ontology answer evidence = true) :
    Correct ontology answer := by
  cases hcheck : evidence.document.check with
  | error message => simp [directHTAccept, hcheck] at haccept
  | ok checked =>
      cases checked with
      | false => simp [directHTAccept, hcheck] at haccept
      | true =>
          cases hdecode : evidence.document.decode with
          | error message => simp [directHTAccept, hcheck, hdecode] at haccept
          | ok decoded =>
              simp only [directHTAccept, hcheck, hdecode,
                decide_eq_true_eq] at haccept
              rcases haccept with ⟨rfl, rfl⟩
              rcases directHTCheck_correct evidence.document hcheck with
                ⟨checkedDecoded, checkedDecode, correct⟩
              rw [hdecode] at checkedDecode
              cases checkedDecode
              exact correct

structure DirectHTExecution where
  run : List FCL →
    Certification.Outcome
      (CertifiedRouting.Publication
        (List FCL) TaxonomyAnswer DirectHTEvidence)
  sourceExact : ∀ ontology publication,
    run ontology = .publish publication → publication.source = ontology
  accepted : ∀ ontology publication,
    run ontology = .publish publication →
      directHTAccept ontology publication.answer publication.evidence = true

def DirectHTExecution.worker (execution : DirectHTExecution) :
    CertifiedRouting.SourceBoundWorker
      (List FCL) TaxonomyAnswer DirectHTEvidence Correct where
  run := execution.run
  accept := directHTAccept
  run_source_exact := execution.sourceExact
  run_accepted := execution.accepted
  accept_sound := directHTAccept_sound

theorem DirectHTExecution.worker_soundAt (execution : DirectHTExecution)
    (ontology : List FCL) :
    Certification.SoundAt Correct execution.worker.erase ontology :=
  execution.worker.erase_soundAt ontology

def mixedHTAnswer :
    HTMixedTaxonomyCommonPublication.DecodedMixedTaxonomyPublication →
      TaxonomyAnswer
  | .plain common taxonomy _ conceptCount _ _ =>
      finBooleanAnswer
        (selectedFin common.projection.concepts.length fun concept =>
          decide (Fin.cast conceptCount concept ∈ taxonomy.target.named))
        fun sub sup => decide
          ((Fin.cast conceptCount sub, Fin.cast conceptCount sup) ∈
            taxonomy.semantic.subsumptions)
  | .mixed common taxonomy _ conceptCount _ _ =>
      finBooleanAnswer
        (selectedFin common.projection.concepts.length fun concept =>
          decide (Fin.cast conceptCount concept ∈ taxonomy.target.named))
        fun sub sup => decide
          ((Fin.cast conceptCount sub, Fin.cast conceptCount sup) ∈
            taxonomy.semantic.subsumptions)

theorem mixedHTAnswer_correct
    (decoded :
      HTMixedTaxonomyCommonPublication.DecodedMixedTaxonomyPublication) :
    Correct (mixedHTPublicationOntology decoded) (mixedHTAnswer decoded) := by
  have semantics := mixedHTRoutingSemantics decoded
  cases decoded with
  | plain common taxonomy variableCount conceptCount roleCount sourceExact =>
      apply finBooleanAnswer_correct _ _ (selectedFin_nodup _ _) _
      intro sub sup hsub hsup
      rw [mem_selectedFin_iff] at hsub hsup
      simp only [decide_eq_true_eq] at hsub hsup
      simpa using semantics.2 sub sup hsub hsup
  | mixed common taxonomy variableCount conceptCount roleCount sourceExact =>
      apply finBooleanAnswer_correct _ _ (selectedFin_nodup _ _) _
      intro sub sup hsub hsup
      rw [mem_selectedFin_iff] at hsub hsup
      simp only [decide_eq_true_eq] at hsub hsup
      simpa using semantics.2 sub sup hsub hsup

theorem mixedHTCheck_correct
    (wire : HTMixedTaxonomyCommonPublication.WireMixedTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    ∃ decoded :
        HTMixedTaxonomyCommonPublication.DecodedMixedTaxonomyPublication,
      wire.decode = .ok decoded ∧
      Correct (mixedHTPublicationOntology decoded) (mixedHTAnswer decoded) := by
  rcases mixedHTCheck_common_routing_source_sound wire hcheck with
    ⟨_, _, decoded, hdecode, _⟩
  exact ⟨decoded, hdecode, mixedHTAnswer_correct decoded⟩

structure MixedHTEvidence where
  document : HTMixedTaxonomyCommonPublication.WireMixedTaxonomyPublication

def mixedHTAccept (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : MixedHTEvidence) : Bool :=
  match evidence.document.check with
  | .error _ => false
  | .ok false => false
  | .ok true =>
      match evidence.document.decode with
      | .error _ => false
      | .ok decoded =>
          decide (ontology = mixedHTPublicationOntology decoded ∧
            answer = mixedHTAnswer decoded)

theorem mixedHTAccept_sound (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : MixedHTEvidence)
    (haccept : mixedHTAccept ontology answer evidence = true) :
    Correct ontology answer := by
  cases hcheck : evidence.document.check with
  | error message => simp [mixedHTAccept, hcheck] at haccept
  | ok checked =>
      cases checked with
      | false => simp [mixedHTAccept, hcheck] at haccept
      | true =>
          cases hdecode : evidence.document.decode with
          | error message => simp [mixedHTAccept, hcheck, hdecode] at haccept
          | ok decoded =>
              simp only [mixedHTAccept, hcheck, hdecode,
                decide_eq_true_eq] at haccept
              rcases haccept with ⟨rfl, rfl⟩
              rcases mixedHTCheck_correct evidence.document hcheck with
                ⟨checkedDecoded, checkedDecode, correct⟩
              rw [hdecode] at checkedDecode
              cases checkedDecode
              exact correct

structure MixedHTExecution where
  run : List FCL →
    Certification.Outcome
      (CertifiedRouting.Publication
        (List FCL) TaxonomyAnswer MixedHTEvidence)
  sourceExact : ∀ ontology publication,
    run ontology = .publish publication → publication.source = ontology
  accepted : ∀ ontology publication,
    run ontology = .publish publication →
      mixedHTAccept ontology publication.answer publication.evidence = true

def MixedHTExecution.worker (execution : MixedHTExecution) :
    CertifiedRouting.SourceBoundWorker
      (List FCL) TaxonomyAnswer MixedHTEvidence Correct where
  run := execution.run
  accept := mixedHTAccept
  run_source_exact := execution.sourceExact
  run_accepted := execution.accepted
  accept_sound := mixedHTAccept_sound

theorem MixedHTExecution.worker_soundAt (execution : MixedHTExecution)
    (ontology : List FCL) :
    Certification.SoundAt Correct execution.worker.erase ontology :=
  execution.worker.erase_soundAt ontology

def bundleHTAnswer :
    HTBundleTaxonomyCommonPublication.DecodedBundleTaxonomyPublication →
      TaxonomyAnswer
  | .plain common taxonomy conceptCount _ _ =>
      finBooleanAnswer
        (selectedFin common.projection.sourceConcepts.length fun concept =>
          decide (Fin.cast conceptCount (common.projection.sourceTargets concept) ∈
            taxonomy.target.named))
        fun sub sup => decide
          ((Fin.cast conceptCount (common.projection.sourceTargets sub),
              Fin.cast conceptCount (common.projection.sourceTargets sup)) ∈
            taxonomy.semantic.subsumptions)
  | .mixed common taxonomy conceptCount _ _ =>
      finBooleanAnswer
        (selectedFin common.projection.sourceConcepts.length fun concept =>
          decide (Fin.cast conceptCount (common.projection.sourceTargets concept) ∈
            taxonomy.target.named))
        fun sub sup => decide
          ((Fin.cast conceptCount (common.projection.sourceTargets sub),
              Fin.cast conceptCount (common.projection.sourceTargets sup)) ∈
            taxonomy.semantic.subsumptions)

theorem bundleHTAnswer_correct
    (decoded :
      HTBundleTaxonomyCommonPublication.DecodedBundleTaxonomyPublication) :
    Correct (bundleHTPublicationOntology decoded) (bundleHTAnswer decoded) := by
  have semantics := bundleHTRoutingSemantics decoded
  cases decoded with
  | plain common taxonomy conceptCount roleCount sourceExact =>
      apply finBooleanAnswer_correct _ _ (selectedFin_nodup _ _) _
      intro sub sup hsub hsup
      rw [mem_selectedFin_iff] at hsub hsup
      simp only [decide_eq_true_eq] at hsub hsup
      simpa using semantics.2 sub sup hsub hsup
  | mixed common taxonomy conceptCount roleCount sourceExact =>
      apply finBooleanAnswer_correct _ _ (selectedFin_nodup _ _) _
      intro sub sup hsub hsup
      rw [mem_selectedFin_iff] at hsub hsup
      simp only [decide_eq_true_eq] at hsub hsup
      simpa using semantics.2 sub sup hsub hsup

theorem bundleHTCheck_correct
    (wire : HTBundleTaxonomyCommonPublication.WireBundleTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    ∃ decoded :
        HTBundleTaxonomyCommonPublication.DecodedBundleTaxonomyPublication,
      wire.decode = .ok decoded ∧
      Correct (bundleHTPublicationOntology decoded) (bundleHTAnswer decoded) := by
  rcases bundleHTCheck_common_routing_source_sound wire hcheck with
    ⟨_, _, decoded, hdecode, _⟩
  exact ⟨decoded, hdecode, bundleHTAnswer_correct decoded⟩

structure BundleHTEvidence where
  document : HTBundleTaxonomyCommonPublication.WireBundleTaxonomyPublication

def bundleHTAccept (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : BundleHTEvidence) : Bool :=
  match evidence.document.check with
  | .error _ => false
  | .ok false => false
  | .ok true =>
      match evidence.document.decode with
      | .error _ => false
      | .ok decoded =>
          decide (ontology = bundleHTPublicationOntology decoded ∧
            answer = bundleHTAnswer decoded)

theorem bundleHTAccept_sound (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : BundleHTEvidence)
    (haccept : bundleHTAccept ontology answer evidence = true) :
    Correct ontology answer := by
  cases hcheck : evidence.document.check with
  | error message => simp [bundleHTAccept, hcheck] at haccept
  | ok checked =>
      cases checked with
      | false => simp [bundleHTAccept, hcheck] at haccept
      | true =>
          cases hdecode : evidence.document.decode with
          | error message => simp [bundleHTAccept, hcheck, hdecode] at haccept
          | ok decoded =>
              simp only [bundleHTAccept, hcheck, hdecode,
                decide_eq_true_eq] at haccept
              rcases haccept with ⟨rfl, rfl⟩
              rcases bundleHTCheck_correct evidence.document hcheck with
                ⟨checkedDecoded, checkedDecode, correct⟩
              rw [hdecode] at checkedDecode
              cases checkedDecode
              exact correct

structure BundleHTExecution where
  run : List FCL →
    Certification.Outcome
      (CertifiedRouting.Publication
        (List FCL) TaxonomyAnswer BundleHTEvidence)
  sourceExact : ∀ ontology publication,
    run ontology = .publish publication → publication.source = ontology
  accepted : ∀ ontology publication,
    run ontology = .publish publication →
      bundleHTAccept ontology publication.answer publication.evidence = true

def BundleHTExecution.worker (execution : BundleHTExecution) :
    CertifiedRouting.SourceBoundWorker
      (List FCL) TaxonomyAnswer BundleHTEvidence Correct where
  run := execution.run
  accept := bundleHTAccept
  run_source_exact := execution.sourceExact
  run_accepted := execution.accepted
  accept_sound := bundleHTAccept_sound

theorem BundleHTExecution.worker_soundAt (execution : BundleHTExecution)
    (ontology : List FCL) :
    Certification.SoundAt Correct execution.worker.erase ontology :=
  execution.worker.erase_soundAt ontology

def exactCardinalityCoordinate (sub sup : Nat)
    (entry : Hypertableau.ExactCardinalitySubsumptionEntry) : Bool :=
  decide (entry.sub = sub ∧ entry.sup = sup)

def exactCardinalityBit
    (entries : List Hypertableau.ExactCardinalitySubsumptionEntry)
    (sub sup : Nat) : Bool :=
  match entries.find? (exactCardinalityCoordinate sub sup) with
  | none => false
  | some entry => entry.natDecision.answer

theorem exactCardinalityBit_exact (ontology : List FCL)
    (entries : List Hypertableau.ExactCardinalitySubsumptionEntry)
    (coordinateSub coordinateSup sub sup : Nat)
    (hcovered : ∃ entry ∈ entries,
      entry.sub = coordinateSub ∧ entry.sup = coordinateSup)
    (hexact : ∀ entry ∈ entries,
      entry.sub = coordinateSub → entry.sup = coordinateSup →
      (entry.natDecision.answer = true ↔ Entails ontology sub sup)) :
    exactCardinalityBit entries coordinateSub coordinateSup = true ↔
      Entails ontology sub sup := by
  rcases hcovered with ⟨witness, hwitness, hwsub, hwsup⟩
  cases hfind : entries.find?
      (exactCardinalityCoordinate coordinateSub coordinateSup) with
  | none =>
      have hreject := (List.find?_eq_none.mp hfind) witness hwitness
      exact (hreject (by
        simp [exactCardinalityCoordinate, hwsub, hwsup])).elim
  | some entry =>
      have hcoordinate := List.find?_some hfind
      simp only [exactCardinalityCoordinate, decide_eq_true_eq] at hcoordinate
      have hentry : entry ∈ entries := by
        rcases (List.find?_eq_some_iff_append.mp hfind).2 with
          ⟨pre, suffix, hentries, _⟩
        rw [hentries]
        simp
      rw [exactCardinalityBit, hfind]
      exact hexact entry hentry hcoordinate.1 hcoordinate.2

def directCardinalityHTAnswer
    (decoded :
      HTDirectCardinalityTaxonomyCommonPublication.DecodedDirectCardinalityTaxonomyPublication) :
    TaxonomyAnswer :=
  finBooleanAnswer
    (selectedFin decoded.common.projection.concepts.length fun concept =>
      decide (concept.val ∈ decoded.exact.namedNats))
    fun sub sup => exactCardinalityBit decoded.exact.covered.subsumptions
      sub.val sup.val

theorem directCardinalityHTAnswer_correct
    (decoded :
      HTDirectCardinalityTaxonomyCommonPublication.DecodedDirectCardinalityTaxonomyPublication) :
    Correct decoded.common.commonOntology (directCardinalityHTAnswer decoded) := by
  have semantics := directCardinalityHTRoutingSemantics decoded
  apply finBooleanAnswer_correct _ _ (selectedFin_nodup _ _) _
  intro sub sup hsub hsup
  rw [mem_selectedFin_iff] at hsub hsup
  simp only [decide_eq_true_eq] at hsub hsup
  apply exactCardinalityBit_exact
  · rcases semantics.1.2 sub sup hsub hsup with
      ⟨entry, hentry, hentrySub, hentrySup, _⟩
    exact ⟨entry, hentry, hentrySub, hentrySup⟩
  · intro entry hentry hentrySub hentrySup
    exact (decoded.subsumption_answer_iff_common entry hentry sub sup
      hentrySub hentrySup).trans (semantics.2.1 sub sup)

theorem directCardinalityHTCheck_correct
    (wire :
      HTDirectCardinalityTaxonomyCommonPublication.WireDirectCardinalityTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    ∃ decoded :
        HTDirectCardinalityTaxonomyCommonPublication.DecodedDirectCardinalityTaxonomyPublication,
      wire.decode = .ok decoded ∧
      Correct decoded.common.commonOntology
        (directCardinalityHTAnswer decoded) := by
  rcases directCardinalityHTCheck_common_routing_source_sound wire hcheck with
    ⟨decoded, hdecode, _⟩
  exact ⟨decoded, hdecode, directCardinalityHTAnswer_correct decoded⟩

structure DirectCardinalityHTEvidence where
  document :
    HTDirectCardinalityTaxonomyCommonPublication.WireDirectCardinalityTaxonomyPublication

def directCardinalityHTAccept (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : DirectCardinalityHTEvidence) : Bool :=
  match evidence.document.check with
  | .error _ => false
  | .ok false => false
  | .ok true =>
      match evidence.document.decode with
      | .error _ => false
      | .ok decoded =>
          decide (ontology = decoded.common.commonOntology ∧
            answer = directCardinalityHTAnswer decoded)

theorem directCardinalityHTAccept_sound
    (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : DirectCardinalityHTEvidence)
    (haccept : directCardinalityHTAccept ontology answer evidence = true) :
    Correct ontology answer := by
  cases hcheck : evidence.document.check with
  | error message => simp [directCardinalityHTAccept, hcheck] at haccept
  | ok checked =>
      cases checked with
      | false => simp [directCardinalityHTAccept, hcheck] at haccept
      | true =>
          cases hdecode : evidence.document.decode with
          | error message =>
              simp [directCardinalityHTAccept, hcheck, hdecode] at haccept
          | ok decoded =>
              simp only [directCardinalityHTAccept, hcheck, hdecode,
                decide_eq_true_eq] at haccept
              rcases haccept with ⟨rfl, rfl⟩
              rcases directCardinalityHTCheck_correct evidence.document hcheck with
                ⟨checkedDecoded, checkedDecode, correct⟩
              rw [hdecode] at checkedDecode
              cases checkedDecode
              exact correct

structure DirectCardinalityHTExecution where
  run : List FCL →
    Certification.Outcome
      (CertifiedRouting.Publication
        (List FCL) TaxonomyAnswer DirectCardinalityHTEvidence)
  sourceExact : ∀ ontology publication,
    run ontology = .publish publication → publication.source = ontology
  accepted : ∀ ontology publication,
    run ontology = .publish publication →
      directCardinalityHTAccept ontology publication.answer
        publication.evidence = true

def DirectCardinalityHTExecution.worker
    (execution : DirectCardinalityHTExecution) :
    CertifiedRouting.SourceBoundWorker
      (List FCL) TaxonomyAnswer DirectCardinalityHTEvidence Correct where
  run := execution.run
  accept := directCardinalityHTAccept
  run_source_exact := execution.sourceExact
  run_accepted := execution.accepted
  accept_sound := directCardinalityHTAccept_sound

theorem DirectCardinalityHTExecution.worker_soundAt
    (execution : DirectCardinalityHTExecution) (ontology : List FCL) :
    Certification.SoundAt Correct execution.worker.erase ontology :=
  execution.worker.erase_soundAt ontology

def mixedCardinalityHTAnswer
    (decoded :
      HTMixedCardinalityTaxonomyCommonPublication.DecodedMixedCardinalityTaxonomyPublication) :
    TaxonomyAnswer :=
  finBooleanAnswer
    (selectedFin decoded.common.projection.mixed.concepts.length fun concept =>
      decide (concept.val ∈ decoded.exact.namedNats))
    fun sub sup => exactCardinalityBit decoded.exact.covered.subsumptions
      sub.val sup.val

theorem mixedCardinalityHTAnswer_correct
    (decoded :
      HTMixedCardinalityTaxonomyCommonPublication.DecodedMixedCardinalityTaxonomyPublication) :
    Correct decoded.common.commonOntology (mixedCardinalityHTAnswer decoded) := by
  have semantics := mixedCardinalityHTRoutingSemantics decoded
  apply finBooleanAnswer_correct _ _ (selectedFin_nodup _ _) _
  intro sub sup hsub hsup
  rw [mem_selectedFin_iff] at hsub hsup
  simp only [decide_eq_true_eq] at hsub hsup
  apply exactCardinalityBit_exact
  · rcases semantics.1.2 sub sup hsub hsup with
      ⟨entry, hentry, hentrySub, hentrySup, _⟩
    exact ⟨entry, hentry, hentrySub, hentrySup⟩
  · intro entry hentry hentrySub hentrySup
    exact (decoded.subsumption_answer_iff_common entry hentry sub sup
      hentrySub hentrySup).trans (semantics.2.1 sub sup)

theorem mixedCardinalityHTCheck_correct
    (wire :
      HTMixedCardinalityTaxonomyCommonPublication.WireMixedCardinalityTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    ∃ decoded :
        HTMixedCardinalityTaxonomyCommonPublication.DecodedMixedCardinalityTaxonomyPublication,
      wire.decode = .ok decoded ∧
      Correct decoded.common.commonOntology
        (mixedCardinalityHTAnswer decoded) := by
  rcases mixedCardinalityHTCheck_common_routing_source_sound wire hcheck with
    ⟨decoded, hdecode, _⟩
  exact ⟨decoded, hdecode, mixedCardinalityHTAnswer_correct decoded⟩

structure MixedCardinalityHTEvidence where
  document :
    HTMixedCardinalityTaxonomyCommonPublication.WireMixedCardinalityTaxonomyPublication

def mixedCardinalityHTAccept (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : MixedCardinalityHTEvidence) : Bool :=
  match evidence.document.check with
  | .error _ => false
  | .ok false => false
  | .ok true =>
      match evidence.document.decode with
      | .error _ => false
      | .ok decoded =>
          decide (ontology = decoded.common.commonOntology ∧
            answer = mixedCardinalityHTAnswer decoded)

theorem mixedCardinalityHTAccept_sound
    (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : MixedCardinalityHTEvidence)
    (haccept : mixedCardinalityHTAccept ontology answer evidence = true) :
    Correct ontology answer := by
  cases hcheck : evidence.document.check with
  | error message => simp [mixedCardinalityHTAccept, hcheck] at haccept
  | ok checked =>
      cases checked with
      | false => simp [mixedCardinalityHTAccept, hcheck] at haccept
      | true =>
          cases hdecode : evidence.document.decode with
          | error message =>
              simp [mixedCardinalityHTAccept, hcheck, hdecode] at haccept
          | ok decoded =>
              simp only [mixedCardinalityHTAccept, hcheck, hdecode,
                decide_eq_true_eq] at haccept
              rcases haccept with ⟨rfl, rfl⟩
              rcases mixedCardinalityHTCheck_correct evidence.document hcheck with
                ⟨checkedDecoded, checkedDecode, correct⟩
              rw [hdecode] at checkedDecode
              cases checkedDecode
              exact correct

structure MixedCardinalityHTExecution where
  run : List FCL →
    Certification.Outcome
      (CertifiedRouting.Publication
        (List FCL) TaxonomyAnswer MixedCardinalityHTEvidence)
  sourceExact : ∀ ontology publication,
    run ontology = .publish publication → publication.source = ontology
  accepted : ∀ ontology publication,
    run ontology = .publish publication →
      mixedCardinalityHTAccept ontology publication.answer
        publication.evidence = true

def MixedCardinalityHTExecution.worker
    (execution : MixedCardinalityHTExecution) :
    CertifiedRouting.SourceBoundWorker
      (List FCL) TaxonomyAnswer MixedCardinalityHTEvidence Correct where
  run := execution.run
  accept := mixedCardinalityHTAccept
  run_source_exact := execution.sourceExact
  run_accepted := execution.accepted
  accept_sound := mixedCardinalityHTAccept_sound

theorem MixedCardinalityHTExecution.worker_soundAt
    (execution : MixedCardinalityHTExecution) (ontology : List FCL) :
    Certification.SoundAt Correct execution.worker.erase ontology :=
  execution.worker.erase_soundAt ontology

def bundleCardinalityHTAnswer
    (decoded :
      HTBundleCardinalityTaxonomyCommonPublication.DecodedBundleCardinalityTaxonomyPublication) :
    TaxonomyAnswer :=
  finBooleanAnswer
    (selectedFin decoded.common.projection.bundle.sourceConcepts.length
      fun concept => decide
        ((decoded.common.projection.bundle.sourceTargets concept).val ∈
          decoded.exact.namedNats))
    fun sub sup => exactCardinalityBit decoded.exact.covered.subsumptions
      (decoded.common.projection.bundle.sourceTargets sub).val
      (decoded.common.projection.bundle.sourceTargets sup).val

theorem bundleCardinalityHTAnswer_correct
    (decoded :
      HTBundleCardinalityTaxonomyCommonPublication.DecodedBundleCardinalityTaxonomyPublication) :
    Correct decoded.common.commonOntology (bundleCardinalityHTAnswer decoded) := by
  have semantics := bundleCardinalityHTRoutingSemantics decoded
  apply finBooleanAnswer_correct _ _ (selectedFin_nodup _ _) _
  intro sub sup hsub hsup
  rw [mem_selectedFin_iff] at hsub hsup
  simp only [decide_eq_true_eq] at hsub hsup
  apply exactCardinalityBit_exact
  · rcases semantics.1.2 sub sup hsub hsup with
      ⟨entry, hentry, hentrySub, hentrySup, _⟩
    exact ⟨entry, hentry, hentrySub, hentrySup⟩
  · intro entry hentry hentrySub hentrySup
    exact (decoded.subsumption_answer_iff_common entry hentry sub sup
      hentrySub hentrySup).trans (semantics.2.1 sub sup)

theorem bundleCardinalityHTCheck_correct
    (wire :
      HTBundleCardinalityTaxonomyCommonPublication.WireBundleCardinalityTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    ∃ decoded :
        HTBundleCardinalityTaxonomyCommonPublication.DecodedBundleCardinalityTaxonomyPublication,
      wire.decode = .ok decoded ∧
      Correct decoded.common.commonOntology
        (bundleCardinalityHTAnswer decoded) := by
  rcases bundleCardinalityHTCheck_common_routing_source_sound wire hcheck with
    ⟨decoded, hdecode, _⟩
  exact ⟨decoded, hdecode, bundleCardinalityHTAnswer_correct decoded⟩

structure BundleCardinalityHTEvidence where
  document :
    HTBundleCardinalityTaxonomyCommonPublication.WireBundleCardinalityTaxonomyPublication

def bundleCardinalityHTAccept (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : BundleCardinalityHTEvidence) : Bool :=
  match evidence.document.check with
  | .error _ => false
  | .ok false => false
  | .ok true =>
      match evidence.document.decode with
      | .error _ => false
      | .ok decoded =>
          decide (ontology = decoded.common.commonOntology ∧
            answer = bundleCardinalityHTAnswer decoded)

theorem bundleCardinalityHTAccept_sound
    (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : BundleCardinalityHTEvidence)
    (haccept : bundleCardinalityHTAccept ontology answer evidence = true) :
    Correct ontology answer := by
  cases hcheck : evidence.document.check with
  | error message => simp [bundleCardinalityHTAccept, hcheck] at haccept
  | ok checked =>
      cases checked with
      | false => simp [bundleCardinalityHTAccept, hcheck] at haccept
      | true =>
          cases hdecode : evidence.document.decode with
          | error message =>
              simp [bundleCardinalityHTAccept, hcheck, hdecode] at haccept
          | ok decoded =>
              simp only [bundleCardinalityHTAccept, hcheck, hdecode,
                decide_eq_true_eq] at haccept
              rcases haccept with ⟨rfl, rfl⟩
              rcases bundleCardinalityHTCheck_correct evidence.document hcheck with
                ⟨checkedDecoded, checkedDecode, correct⟩
              rw [hdecode] at checkedDecode
              cases checkedDecode
              exact correct

structure BundleCardinalityHTExecution where
  run : List FCL →
    Certification.Outcome
      (CertifiedRouting.Publication
        (List FCL) TaxonomyAnswer BundleCardinalityHTEvidence)
  sourceExact : ∀ ontology publication,
    run ontology = .publish publication → publication.source = ontology
  accepted : ∀ ontology publication,
    run ontology = .publish publication →
      bundleCardinalityHTAccept ontology publication.answer
        publication.evidence = true

def BundleCardinalityHTExecution.worker
    (execution : BundleCardinalityHTExecution) :
    CertifiedRouting.SourceBoundWorker
      (List FCL) TaxonomyAnswer BundleCardinalityHTEvidence Correct where
  run := execution.run
  accept := bundleCardinalityHTAccept
  run_source_exact := execution.sourceExact
  run_accepted := execution.accepted
  accept_sound := bundleCardinalityHTAccept_sound

theorem BundleCardinalityHTExecution.worker_soundAt
    (execution : BundleCardinalityHTExecution) (ontology : List FCL) :
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
#print axioms finTaxonomyAnswer_correct
#print axioms directHTAnswer_correct
#print axioms directHTCheck_correct
#print axioms directHTAccept_sound
#print axioms DirectHTExecution.worker_soundAt
#print axioms finBooleanAnswer_correct
#print axioms mixedHTAnswer_correct
#print axioms mixedHTCheck_correct
#print axioms mixedHTAccept_sound
#print axioms MixedHTExecution.worker_soundAt
#print axioms bundleHTAnswer_correct
#print axioms bundleHTCheck_correct
#print axioms bundleHTAccept_sound
#print axioms BundleHTExecution.worker_soundAt
#print axioms exactCardinalityBit_exact
#print axioms directCardinalityHTAnswer_correct
#print axioms directCardinalityHTCheck_correct
#print axioms directCardinalityHTAccept_sound
#print axioms DirectCardinalityHTExecution.worker_soundAt
#print axioms mixedCardinalityHTAnswer_correct
#print axioms mixedCardinalityHTCheck_correct
#print axioms mixedCardinalityHTAccept_sound
#print axioms MixedCardinalityHTExecution.worker_soundAt
#print axioms bundleCardinalityHTAnswer_correct
#print axioms bundleCardinalityHTCheck_correct
#print axioms bundleCardinalityHTAccept_sound
#print axioms BundleCardinalityHTExecution.worker_soundAt

end ContextCalculus.KMConcreteWorkerAdapters
