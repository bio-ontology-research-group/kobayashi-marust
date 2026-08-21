import ContextCalculus.HypertableauNativeABoxTaxonomyWire
import ContextCalculus.HypertableauNativeABoxModelWire

/-!
# Native-ABox cardinality taxonomy certificates

Each decision is interpreted in one shared model of the normalized ontology,
the first-class cardinality definitions, the complete native ABox, and the
query literals.  Negative decisions start from the exact joint ABox/query seed,
including every explicit different-individual fact.
-/

namespace ContextCalculus.Hypertableau

open Lean

def NativeABox.SatisfiableWithCardinalityQuery
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (query : List (Lit Concept)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain) (element : Domain),
    Nonempty Domain ∧ I.models ontology ∧ I.modelsCardinalityDefs definitions ∧
      abox.models I value ∧ I.RealizesLiterals query element

def NativeABox.UnsatisfiableConceptWithCardinality
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (concept : Concept) : Prop :=
  ¬abox.SatisfiableWithCardinalityQuery ontology definitions [.pos concept]

def NativeABox.EntailsSubWithCardinality
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (sub sup : Concept) : Prop :=
  ¬abox.SatisfiableWithCardinalityQuery ontology definitions
    [.pos sub, .negated sup]

inductive NativeABoxCardinalityConceptDecision
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (concept : Concept) : Type where
  | unsatisfiable
      (proof : abox.UnsatisfiableConceptWithCardinality ontology definitions concept)
  | satisfiable
      (counterexample :
        ¬abox.UnsatisfiableConceptWithCardinality ontology definitions concept)

inductive NativeABoxCardinalitySubsumptionDecision
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (sub sup : Concept) : Type where
  | entailed
      (proof : abox.EntailsSubWithCardinality ontology definitions sub sup)
  | notEntailed
      (counterexample : ¬abox.EntailsSubWithCardinality ontology definitions sub sup)

def NativeABoxCardinalityConceptDecision.answer :
    NativeABoxCardinalityConceptDecision abox ontology definitions concept → Bool
  | .unsatisfiable _ => true
  | .satisfiable _ => false

theorem NativeABoxCardinalityConceptDecision.answer_eq_true_iff
    (decision : NativeABoxCardinalityConceptDecision
      abox ontology definitions concept) :
    decision.answer = true ↔
      abox.UnsatisfiableConceptWithCardinality ontology definitions concept := by
  cases decision with
  | unsatisfiable proof =>
      simp [NativeABoxCardinalityConceptDecision.answer, proof]
  | satisfiable counterexample =>
      simp [NativeABoxCardinalityConceptDecision.answer, counterexample]

def NativeABoxCardinalitySubsumptionDecision.answer :
    NativeABoxCardinalitySubsumptionDecision abox ontology definitions sub sup → Bool
  | .entailed _ => true
  | .notEntailed _ => false

theorem NativeABoxCardinalitySubsumptionDecision.answer_eq_true_iff
    (decision : NativeABoxCardinalitySubsumptionDecision
      abox ontology definitions sub sup) :
    decision.answer = true ↔
      abox.EntailsSubWithCardinality ontology definitions sub sup := by
  cases decision with
  | entailed proof =>
      simp [NativeABoxCardinalitySubsumptionDecision.answer, proof]
  | notEntailed counterexample =>
      simp [NativeABoxCardinalitySubsumptionDecision.answer, counterexample]

structure CompleteNativeABoxCardinalityTaxonomyCertificate
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) (named : List Concept) where
  concept : ∀ candidate, candidate ∈ named →
    NativeABoxCardinalityConceptDecision abox ontology definitions candidate
  subsumption : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    NativeABoxCardinalitySubsumptionDecision abox ontology definitions sub sup

def CompleteNativeABoxCardinalityTaxonomyCertificate.unsatisfiable
    [DecidableEq Concept]
    (certificate : CompleteNativeABoxCardinalityTaxonomyCertificate
      (abox : NativeABox Individual Concept Role)
      (ontology : List (Clause Variable Concept Role)) definitions named) : List Concept :=
  named.filter fun concept =>
    if h : concept ∈ named then (certificate.concept concept h).answer else false

def CompleteNativeABoxCardinalityTaxonomyCertificate.subsumptions
    [DecidableEq Concept]
    (certificate : CompleteNativeABoxCardinalityTaxonomyCertificate
      (abox : NativeABox Individual Concept Role)
      (ontology : List (Clause Variable Concept Role)) definitions named) :
    List (Concept × Concept) :=
  named.flatMap fun sub =>
    if hsub : sub ∈ named then
      (named.filter fun sup =>
        if hsup : sup ∈ named
        then (certificate.subsumption sub hsub sup hsup).answer
        else false).map fun sup => (sub, sup)
    else []

theorem CompleteNativeABoxCardinalityTaxonomyCertificate.unsatisfiable_exact
    [DecidableEq Concept]
    (certificate : CompleteNativeABoxCardinalityTaxonomyCertificate
      (abox : NativeABox Individual Concept Role)
      (ontology : List (Clause Variable Concept Role)) definitions named)
    (concept : Concept) (hnamed : concept ∈ named) :
    concept ∈ certificate.unsatisfiable ↔
      abox.UnsatisfiableConceptWithCardinality ontology definitions concept := by
  simp [CompleteNativeABoxCardinalityTaxonomyCertificate.unsatisfiable, hnamed,
    (certificate.concept concept hnamed).answer_eq_true_iff]

theorem CompleteNativeABoxCardinalityTaxonomyCertificate.subsumptions_exact
    [DecidableEq Concept]
    (certificate : CompleteNativeABoxCardinalityTaxonomyCertificate
      (abox : NativeABox Individual Concept Role)
      (ontology : List (Clause Variable Concept Role)) definitions named)
    (sub sup : Concept) (hsub : sub ∈ named) (hsup : sup ∈ named) :
    (sub, sup) ∈ certificate.subsumptions ↔
      abox.EntailsSubWithCardinality ontology definitions sub sup := by
  simp [CompleteNativeABoxCardinalityTaxonomyCertificate.subsumptions, hsub, hsup,
    (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff]

def NativeABox.InitializesDistinctQueryState
    (abox : NativeABox Individual Concept Role)
    (query : List (Lit Concept))
    (state : DistinctEqState Node Concept Role) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Concept Role)
      [Nonempty Domain] (value : Individual → Domain) (element : Domain),
    abox.models I value → I.RealizesLiterals query element →
      ∃ nodeValue : Node → Domain, state.RealizedBy I nodeValue

def NativeABox.ExactDistinctQuerySeed
    (abox : NativeABox Individual Concept Role)
    (query : List (Lit Concept))
    (state : DistinctEqState Node Concept Role)
    (root : Individual → Node) (queryRoot : Node) : Prop :=
  abox.ExactEqQuerySeed query state.base root queryRoot ∧
  ∀ left right, state.apart left right →
    ∃ pair ∈ abox.different,
      (left = root pair.1 ∧ right = root pair.2) ∨
      (left = root pair.2 ∧ right = root pair.1)

theorem NativeABox.ExactDistinctQuerySeed.initializes
    (abox : NativeABox Individual Concept Role)
    (query : List (Lit Concept))
    (state : DistinctEqState Node Concept Role)
    (root : Individual → Node) (queryRoot : Node)
    (hroot : Function.Injective root)
    (hqueryRoot : ∀ individual, queryRoot ≠ root individual)
    (hexact : abox.ExactDistinctQuerySeed query state root queryRoot) :
    abox.InitializesDistinctQueryState query state := by
  intro Domain I _ value element habox hquery
  classical
  let taggedRoot : Option Individual → Node
    | none => queryRoot
    | some individual => root individual
  have htagged : Function.Injective taggedRoot := by
    intro left right hequal
    cases left with
    | none =>
        cases right with
        | none => rfl
        | some individual => exact False.elim (hqueryRoot individual hequal)
    | some leftIndividual =>
        cases right with
        | none => exact False.elim (hqueryRoot leftIndividual hequal.symm)
        | some rightIndividual => exact congrArg some (hroot hequal)
  let taggedValue : Option Individual → Domain
    | none => element
    | some individual => value individual
  let fallback : Domain := Classical.choice (inferInstance : Nonempty Domain)
  let nodeValue : Node → Domain :=
    Function.extend taggedRoot taggedValue (fun _ => fallback)
  have htaggedValue : ∀ tagged,
      nodeValue (taggedRoot tagged) = taggedValue tagged :=
    fun tagged => htagged.extend_apply taggedValue (fun _ => fallback) tagged
  have hnativeValue : ∀ individual,
      nodeValue (root individual) = value individual := by
    intro individual
    exact htaggedValue (some individual)
  have hqueryValue : nodeValue queryRoot = element := htaggedValue none
  have hbase : state.base.RealizedBy I nodeValue := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro node literal hlabel
      rcases (hexact.1.1 node literal).1 hlabel with
        ⟨individual, concept, rfl, hconcept, rfl⟩ | ⟨rfl, hliteral⟩
      · rcases List.mem_append.mp hconcept with hproxy | hassertion
        · rw [hnativeValue]
          simpa [Interp.satLit] using
            (habox.1 individual concept hproxy (value individual)).2 rfl
        · rw [hnativeValue]
          simpa [Interp.satLit] using habox.2.1 individual concept hassertion
      · rw [hqueryValue]
        exact hquery literal hliteral
    · intro role source target hedge
      rcases (hexact.1.2.1 role source target).1 hedge with
        ⟨assertion, hassertion, rfl, rfl, rfl⟩
      rw [hnativeValue, hnativeValue]
      exact habox.2.2.2.1 assertion hassertion
    · intro role filler node hobligation
      exact (hexact.1.2.2.1 role filler node hobligation).elim
    · intro left right hequivalent
      exact congrArg nodeValue ((hexact.1.2.2.2 left right).1 hequivalent)
  refine ⟨nodeValue, hbase, ?_⟩
  intro left right hapart hequal
  rcases hexact.2 left right hapart with ⟨pair, hpair, horientation⟩
  have hdifferent := habox.2.2.1 pair hpair
  rcases horientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hdifferent (by simpa [hnativeValue] using hequal)
  · exact hdifferent (by simpa [hnativeValue] using hequal.symm)

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_native_abox_query_unsatisfiable
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (query : List (Lit (Fin conceptCount)))
    (hinitial : abox.InitializesDistinctQueryState query certificate.state)
    (hcheck : tree.checkClosed definitions certificate = true) :
    ¬abox.SatisfiableWithCardinalityQuery certificate.base.base.ontology
      definitions query := by
  rintro ⟨Domain, I, value, element, hdomain, hmodels, hcardinality, habox,
    hquery⟩
  letI : Nonempty Domain := hdomain
  rcases hinitial Domain I value element habox hquery with ⟨nodeValue, hrealized⟩
  exact tree.checkClosed_unsatisfiable definitions certificate hcheck
    ⟨Domain, I, nodeValue, hmodels, hcardinality, hrealized⟩

theorem DecodedNativeABoxCardinalitySatCertificate.satisfiable_with_query
    (decoded : DecodedNativeABoxCardinalitySatCertificate)
    (root : Fin decoded.seed.nodeCount)
    (query : List (Lit (Fin decoded.seed.abox.concepts.length)))
    (hquery : ∀ literal ∈ query,
      (root, literal) ∈ decoded.seed.state.base.base.labels) :
    decoded.seed.abox.abox.SatisfiableWithCardinalityQuery
      decoded.seed.state.base.base.ontology decoded.definitions query := by
  rcases decoded.canonical_model with
    ⟨value, hdomain, hontology, hdefinitions, habox⟩
  let I := decoded.seed.state.base.state.quotientCanonical
  let nodeValue : Fin decoded.seed.nodeCount →
      decoded.seed.state.base.state.QuotientDomain :=
    fun node => Quotient.mk decoded.seed.state.base.state.nodeSetoid node
  have hparts := decoded.cardinality
  simp only [FiniteEqCertificate.checkEqSatWithCardinality,
    Bool.and_eq_true] at hparts
  have hrealized : decoded.seed.state.base.state.RealizedBy I nodeValue :=
    decoded.seed.state.base.checkEqSat_realizes hparts.1
  have hroot : I.RealizesLiterals query (nodeValue root) := by
    intro literal hliteral
    exact hrealized.1.1 root literal (hquery literal hliteral)
  exact ⟨decoded.seed.state.base.state.QuotientDomain, I, value, nodeValue root,
    hdomain, hontology, hdefinitions, habox, hroot⟩

def DecodedNativeABox.exactDistinctQuerySeedB
    (decoded : DecodedNativeABox)
    (state : FiniteDistinctEqCertificate nodeCount decoded.concepts.length
      decoded.roles.length variableCount)
    (root : Fin decoded.individuals.length → Fin nodeCount)
    (query : DecodedNativeABoxTaxonomyQuery nodeCount decoded.concepts.length) : Bool :=
  decoded.exactEqQuerySeedB state.base root query &&
    decoded.apartJustifiedB state root

theorem DecodedNativeABox.exactDistinctQuerySeedB_sound
    (decoded : DecodedNativeABox)
    (state : FiniteDistinctEqCertificate nodeCount decoded.concepts.length
      decoded.roles.length variableCount)
    (root : Fin decoded.individuals.length → Fin nodeCount)
    (query : DecodedNativeABoxTaxonomyQuery nodeCount decoded.concepts.length)
    (hcheck : decoded.exactDistinctQuerySeedB state root query = true) :
    decoded.abox.ExactDistinctQuerySeed query.literals state.state root query.root := by
  simp only [DecodedNativeABox.exactDistinctQuerySeedB, Bool.and_eq_true] at hcheck
  exact ⟨decoded.exactEqQuerySeedB_sound state.base root query hcheck.1,
    decoded.apartJustifiedB_sound state root hcheck.2⟩

inductive WireNativeABoxCardinalityTaxonomyEvidence where
  | sat (certificate : WireNativeABoxCardinalitySatCertificate)
  | unsat (initial : WireNativeABoxSeed)
      (definitions : List WireCardinalityDef) (depth : Nat)
      (tree : WireDistinctCardinalityRefutationTree)
deriving FromJson, ToJson, Repr

structure WireNativeABoxCardinalityTaxonomyDecision where
  version : Nat
  query : WireNativeABoxTaxonomyQuery
  evidence : WireNativeABoxCardinalityTaxonomyEvidence
deriving FromJson, ToJson, Repr

structure DecodedNativeABoxCardinalityTaxonomySat where
  certificate : DecodedNativeABoxCardinalitySatCertificate
  query : DecodedNativeABoxTaxonomyQuery certificate.seed.nodeCount
    certificate.seed.abox.concepts.length
  wireQuery : WireNativeABoxTaxonomyQuery
  exactCoordinates : DecodedNativeABoxTaxonomyQuery.MatchesWire query wireQuery
  query_present : ∀ literal ∈ query.literals,
    (query.root, literal) ∈ certificate.seed.state.base.base.labels

structure DecodedNativeABoxCardinalityTaxonomyUnsat where
  initial : DecodedNativeABoxSeed
  query : DecodedNativeABoxTaxonomyQuery initial.nodeCount
    initial.abox.concepts.length
  wireQuery : WireNativeABoxTaxonomyQuery
  exactCoordinates : DecodedNativeABoxTaxonomyQuery.MatchesWire query wireQuery
  query_root_disjoint : ∀ individual, query.root ≠ initial.roots individual
  exact_initial : initial.abox.abox.ExactDistinctQuerySeed query.literals
    initial.state.state initial.roots query.root
  definitions : List (CardinalityDef (Fin initial.abox.concepts.length)
    (Fin initial.abox.roles.length))
  depth : Nat
  tree : FiniteDistinctCardinalityRefutationTree initial.nodeCount
    initial.abox.concepts.length initial.abox.roles.length initial.variableCount depth
  checked : tree.checkClosed definitions initial.state = true

inductive DecodedNativeABoxCardinalityTaxonomyDecision where
  | sat (decoded : DecodedNativeABoxCardinalityTaxonomySat)
  | unsat (decoded : DecodedNativeABoxCardinalityTaxonomyUnsat)

def DecodedNativeABoxCardinalityTaxonomyDecision.wireQuery :
    DecodedNativeABoxCardinalityTaxonomyDecision → WireNativeABoxTaxonomyQuery
  | .sat decoded => decoded.wireQuery
  | .unsat decoded => decoded.wireQuery

def DecodedNativeABoxCardinalityTaxonomyDecision.CoordinatesExact
    (expected : WireNativeABoxTaxonomyQuery) :
    DecodedNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      DecodedNativeABoxTaxonomyQuery.MatchesWire decoded.query expected
  | .unsat decoded =>
      DecodedNativeABoxTaxonomyQuery.MatchesWire decoded.query expected

theorem DecodedNativeABoxCardinalityTaxonomyDecision.coordinates_exact
    (decoded : DecodedNativeABoxCardinalityTaxonomyDecision)
    {expected : WireNativeABoxTaxonomyQuery}
    (haligned : decoded.wireQuery = expected) :
    decoded.CoordinatesExact expected := by
  cases decoded with
  | sat result => exact haligned ▸ result.exactCoordinates
  | unsat result => exact haligned ▸ result.exactCoordinates

def WireNativeABoxCardinalityTaxonomyDecision.decodeExact
    (wire : WireNativeABoxCardinalityTaxonomyDecision) :
    Except String { decoded : DecodedNativeABoxCardinalityTaxonomyDecision //
      decoded.wireQuery = wire.query } := do
  if wire.version != 1 then
    throw s!"unsupported native ABox cardinality taxonomy decision version {wire.version}"
  match wire.evidence with
  | .sat certificateWire =>
      let certificate ← certificateWire.decode
      let exactQuery ← wire.query.decodeExact certificate.seed.nodeCount
        certificate.seed.abox.concepts.length
      let query := exactQuery.query
      if hquery : query.labelsPresentB certificate.seed.state.base.base.labels = true then
        return ⟨.sat {
          certificate
          query
          wireQuery := wire.query
          exactCoordinates := exactQuery.exactCoordinates
          query_present := query.labelsPresentB_sound _ hquery
        }, rfl⟩
      else throw "native ABox cardinality taxonomy countermodel omits its query literals"
  | .unsat initialWire definitionWires depth treeWire =>
      let expectedRoots := (List.range initialWire.abox.individuals.length).map (· + 1)
      unless initialWire.roots == expectedRoots do
        throw "native ABox cardinality taxonomy roots must be ordered nodes 1 through N"
      let initial ← initialWire.decode
      let exactQuery ← wire.query.decodeExact initial.nodeCount
        initial.abox.concepts.length
      let query := exactQuery.query
      let queryZero : Fin initial.nodeCount :=
        ⟨0, Nat.pos_of_ne_zero initial.node_nonzero⟩
      if _hqueryRoot : query.root = queryZero then
        if hdisjoint : ∀ individual, query.root ≠ initial.roots individual then
          if hexact : initial.abox.exactDistinctQuerySeedB initial.state
              initial.roots query = true then
            let definitions ← definitionWires.mapM
              (WireCardinalityDef.decode initial.abox.concepts.length
                initial.abox.roles.length)
            let decodedTree ← treeWire.decode initial.nodeCount
              initial.abox.concepts.length initial.abox.roles.length
              initial.variableCount depth initial.ontology definitions
            if htree : decodedTree.tree.checkClosed definitions initial.state = true then
              return ⟨.unsat {
                initial
                query
                wireQuery := wire.query
                exactCoordinates := exactQuery.exactCoordinates
                query_root_disjoint := hdisjoint
                exact_initial := initial.abox.exactDistinctQuerySeedB_sound
                  initial.state initial.roots query hexact
                definitions
                depth := decodedTree.depth
                tree := decodedTree.tree
                checked := htree
              }, rfl⟩
            else throw "native ABox cardinality taxonomy refutation did not close"
          else throw "native ABox cardinality taxonomy root is not the exact joint query seed"
        else throw "native ABox cardinality taxonomy query root overlaps a named-individual root"
      else throw "native ABox cardinality taxonomy query root must be node zero"

def WireNativeABoxCardinalityTaxonomyDecision.decode
    (wire : WireNativeABoxCardinalityTaxonomyDecision) :
    Except String DecodedNativeABoxCardinalityTaxonomyDecision := do
  return (← wire.decodeExact).val

def WireNativeABoxCardinalityTaxonomyDecision.check
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedNativeABoxCardinalityTaxonomyUnsat.unsatisfiable
    (decoded : DecodedNativeABoxCardinalityTaxonomyUnsat) :
    ¬decoded.initial.abox.abox.SatisfiableWithCardinalityQuery
      decoded.initial.state.base.base.ontology decoded.definitions
      decoded.query.literals :=
  decoded.tree.checkClosed_native_abox_query_unsatisfiable decoded.definitions
    decoded.initial.state decoded.initial.abox.abox decoded.query.literals
    (decoded.exact_initial.initializes decoded.initial.abox.abox
      decoded.query.literals decoded.initial.state.state decoded.initial.roots
      decoded.query.root decoded.initial.roots_injective decoded.query_root_disjoint)
    decoded.checked

def DecodedNativeABoxCardinalityTaxonomyDecision.SemanticallyValid :
    DecodedNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      decoded.certificate.seed.abox.abox.SatisfiableWithCardinalityQuery
        decoded.certificate.seed.state.base.base.ontology
        decoded.certificate.definitions decoded.query.literals
  | .unsat decoded =>
      ¬decoded.initial.abox.abox.SatisfiableWithCardinalityQuery
        decoded.initial.state.base.base.ontology decoded.definitions
        decoded.query.literals

theorem DecodedNativeABoxCardinalityTaxonomyDecision.semantic_valid
    (decoded : DecodedNativeABoxCardinalityTaxonomyDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat result =>
      exact result.certificate.satisfiable_with_query result.query.root
        result.query.literals result.query_present
  | unsat result => exact result.unsatisfiable

def DecodedNativeABoxCardinalityTaxonomyDecision.positive :
    DecodedNativeABoxCardinalityTaxonomyDecision → Bool
  | .sat _ => false
  | .unsat _ => true

def DecodedNativeABoxCardinalityTaxonomyDecision.QueryEntailed :
    DecodedNativeABoxCardinalityTaxonomyDecision → Prop
  | .sat decoded =>
      ¬decoded.certificate.seed.abox.abox.SatisfiableWithCardinalityQuery
        decoded.certificate.seed.state.base.base.ontology
        decoded.certificate.definitions decoded.query.literals
  | .unsat decoded =>
      ¬decoded.initial.abox.abox.SatisfiableWithCardinalityQuery
        decoded.initial.state.base.base.ontology decoded.definitions
        decoded.query.literals

theorem DecodedNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    (decision : DecodedNativeABoxCardinalityTaxonomyDecision) :
    decision.positive = true ↔ decision.QueryEntailed := by
  cases decision with
  | sat decoded =>
      have hsemantic :=
        (DecodedNativeABoxCardinalityTaxonomyDecision.sat decoded).semantic_valid
      change decoded.certificate.seed.abox.abox.SatisfiableWithCardinalityQuery
        decoded.certificate.seed.state.base.base.ontology
        decoded.certificate.definitions decoded.query.literals at hsemantic
      change (false = true ↔
        ¬decoded.certificate.seed.abox.abox.SatisfiableWithCardinalityQuery
          decoded.certificate.seed.state.base.base.ontology
          decoded.certificate.definitions decoded.query.literals)
      constructor
      · intro hfalse
        contradiction
      · intro hnot
        exact False.elim (hnot hsemantic)
  | unsat decoded =>
      have hsemantic :=
        (DecodedNativeABoxCardinalityTaxonomyDecision.unsat decoded).semantic_valid
      change ¬decoded.initial.abox.abox.SatisfiableWithCardinalityQuery
        decoded.initial.state.base.base.ontology decoded.definitions
        decoded.query.literals at hsemantic
      change (true = true ↔
        ¬decoded.initial.abox.abox.SatisfiableWithCardinalityQuery
          decoded.initial.state.base.base.ontology decoded.definitions
          decoded.query.literals)
      constructor
      · intro _
        exact hsemantic
      · intro _
        rfl

structure WireNativeABoxCardinalityTaxonomyMatrix where
  version : Nat
  named : List Nat
  concepts : List WireNativeABoxCardinalityTaxonomyDecision
  subsumptions : List (List WireNativeABoxCardinalityTaxonomyDecision)
deriving FromJson, ToJson, Repr

def WireNativeABoxCardinalityTaxonomyDecision.problemJson
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : Json :=
  let (seed, definitions) := match wire.evidence with
    | .sat certificate => (certificate.seed, certificate.definitions)
    | .unsat initial definitions _ _ => (initial, definitions)
  Json.mkObj [
    ("abox", toJson seed.abox),
    ("variable_count", toJson seed.variable_count),
    ("ontology", toJson seed.ontology),
    ("definitions", toJson definitions)]

def WireNativeABoxCardinalityTaxonomyDecision.sameProblemB
    (left right : WireNativeABoxCardinalityTaxonomyDecision) : Bool :=
  left.problemJson == right.problemJson

def WireNativeABoxCardinalityTaxonomyDecision.matchesConceptB
    (wire : WireNativeABoxCardinalityTaxonomyDecision) (concept : Nat) : Bool :=
  match wire.query with
  | .concept root candidate => root == 0 && candidate == concept
  | .subsumption .. => false

def WireNativeABoxCardinalityTaxonomyDecision.matchesSubsumptionB
    (wire : WireNativeABoxCardinalityTaxonomyDecision) (sub sup : Nat) : Bool :=
  match wire.query with
  | .concept .. => false
  | .subsumption root candidateSub candidateSup =>
      root == 0 && candidateSub == sub && candidateSup == sup

def WireNativeABoxCardinalityTaxonomyMatrix.shapeB
    (wire : WireNativeABoxCardinalityTaxonomyMatrix) : Bool :=
  wire.concepts.length == wire.named.length &&
  wire.subsumptions.length == wire.named.length &&
  wire.subsumptions.all fun row => row.length == wire.named.length

def WireNativeABoxCardinalityTaxonomyMatrix.queriesB
    (wire : WireNativeABoxCardinalityTaxonomyMatrix) : Bool :=
  ((wire.named.zip wire.concepts).all fun pair =>
      pair.2.matchesConceptB pair.1) &&
  (wire.named.zip wire.subsumptions).all fun subRow =>
    (wire.named.zip subRow.2).all fun supCell =>
      supCell.2.matchesSubsumptionB subRow.1 supCell.1

def WireNativeABoxCardinalityTaxonomyMatrix.allCells
    (wire : WireNativeABoxCardinalityTaxonomyMatrix) :
    List WireNativeABoxCardinalityTaxonomyDecision :=
  wire.concepts ++ wire.subsumptions.flatten

def WireNativeABoxCardinalityTaxonomyMatrix.sharedProblemB
    (wire : WireNativeABoxCardinalityTaxonomyMatrix) : Bool :=
  match wire.concepts.head? with
  | none => false
  | some baseline => wire.allCells.all (baseline.sameProblemB ·)

structure DecodedNativeABoxCardinalityTaxonomyMatrix where
  wire : WireNativeABoxCardinalityTaxonomyMatrix
  named : List Nat
  concepts : List DecodedNativeABoxCardinalityTaxonomyDecision
  subsumptions : List (List DecodedNativeABoxCardinalityTaxonomyDecision)
  concepts_exact : List.Forall₂
    (fun concept decoded => decoded.wireQuery = .concept 0 concept) named concepts
  subsumptions_exact : List.Forall₂
    (fun sub row => List.Forall₂
      (fun sup decoded => decoded.wireQuery = .subsumption 0 sub sup) named row)
    named subsumptions
  named_nodup : named.Nodup
  complete_shape : wire.shapeB = true
  exact_queries : wire.queriesB = true
  shared_problem : wire.sharedProblemB = true

private def decodeNativeCardinalityTaxonomyDecisionAt
    (expected : WireNativeABoxTaxonomyQuery)
    (wire : WireNativeABoxCardinalityTaxonomyDecision) :
    Except String { decoded : DecodedNativeABoxCardinalityTaxonomyDecision //
      decoded.wireQuery = expected } := do
  if hquery : wire.query = expected then
    let decoded ← wire.decodeExact
    return ⟨decoded.val, decoded.property.trans hquery⟩
  else throw "native ABox cardinality taxonomy cell is in the wrong matrix position"

private def decodeNativeCardinalityTaxonomyConceptsExact :
    (named : List Nat) → (wires : List WireNativeABoxCardinalityTaxonomyDecision) →
    Except String { decoded : List DecodedNativeABoxCardinalityTaxonomyDecision //
      List.Forall₂
        (fun concept decision => decision.wireQuery = .concept 0 concept)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | concept :: named, wire :: wires => do
      let decision ← decodeNativeCardinalityTaxonomyDecisionAt (.concept 0 concept) wire
      let tail ← decodeNativeCardinalityTaxonomyConceptsExact named wires
      return ⟨decision.val :: tail.val, .cons decision.property tail.property⟩
  | _, _ => .error "native ABox cardinality taxonomy concept row is incomplete"

private def decodeNativeCardinalityTaxonomySubsumptionRowExact (sub : Nat) :
    (named : List Nat) → (wires : List WireNativeABoxCardinalityTaxonomyDecision) →
    Except String { decoded : List DecodedNativeABoxCardinalityTaxonomyDecision //
      List.Forall₂
        (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | sup :: named, wire :: wires => do
      let decision ← decodeNativeCardinalityTaxonomyDecisionAt
        (.subsumption 0 sub sup) wire
      let tail ← decodeNativeCardinalityTaxonomySubsumptionRowExact sub named wires
      return ⟨decision.val :: tail.val, .cons decision.property tail.property⟩
  | _, _ => .error "native ABox cardinality taxonomy subsumption row is incomplete"

private def decodeNativeCardinalityTaxonomyRowsExact (allNamed : List Nat) :
    (named : List Nat) →
    (rows : List (List WireNativeABoxCardinalityTaxonomyDecision)) →
    Except String { decoded : List (List DecodedNativeABoxCardinalityTaxonomyDecision) //
      List.Forall₂
        (fun sub row => List.Forall₂
          (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
          allNamed row)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | sub :: named, row :: rows => do
      let decodedRow ← decodeNativeCardinalityTaxonomySubsumptionRowExact
        sub allNamed row
      let decodedRows ← decodeNativeCardinalityTaxonomyRowsExact allNamed named rows
      return ⟨decodedRow.val :: decodedRows.val,
        .cons decodedRow.property decodedRows.property⟩
  | _, _ => .error "native ABox cardinality taxonomy subsumption matrix is incomplete"

def WireNativeABoxCardinalityTaxonomyMatrix.decode
    (wire : WireNativeABoxCardinalityTaxonomyMatrix) :
    Except String DecodedNativeABoxCardinalityTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported complete native ABox cardinality taxonomy version {wire.version}"
  if hnamed : wire.named.Nodup then
    if hshape : wire.shapeB = true then
      if hqueries : wire.queriesB = true then
        if hshared : wire.sharedProblemB = true then
          let concepts ← decodeNativeCardinalityTaxonomyConceptsExact
            wire.named wire.concepts
          let subsumptions ← decodeNativeCardinalityTaxonomyRowsExact wire.named
            wire.named wire.subsumptions
          return {
            wire
            named := wire.named
            concepts := concepts.val
            subsumptions := subsumptions.val
            concepts_exact := concepts.property
            subsumptions_exact := subsumptions.property
            named_nodup := hnamed
            complete_shape := hshape
            exact_queries := hqueries
            shared_problem := hshared
          }
        else throw "native ABox cardinality taxonomy cells describe different problems"
      else throw "native ABox cardinality taxonomy cell is in the wrong matrix position"
    else throw "native ABox cardinality taxonomy matrix is incomplete"
  else throw "complete native ABox cardinality taxonomy repeats a named concept"

def WireNativeABoxCardinalityTaxonomyMatrix.check
    (wire : WireNativeABoxCardinalityTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedNativeABoxCardinalityTaxonomyMatrix.allDecisions
    (decoded : DecodedNativeABoxCardinalityTaxonomyMatrix) :
    List DecodedNativeABoxCardinalityTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedNativeABoxCardinalityTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedNativeABoxCardinalityTaxonomyMatrix) : Prop :=
  decoded.wire.shapeB = true ∧ decoded.wire.queriesB = true ∧
  decoded.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

private theorem nativeCardinalityConceptAlignment_coordinates_exact
    {named : List Nat}
    {decisions : List DecodedNativeABoxCardinalityTaxonomyDecision}
    (haligned : List.Forall₂
      (fun concept decision => decision.wireQuery = .concept 0 concept)
      named decisions) :
    List.Forall₂
      (fun concept decision =>
        decision.CoordinatesExact (.concept 0 concept))
      named decisions := by
  induction haligned with
  | nil => exact .nil
  | cons haligned _ ih =>
      exact .cons
        (DecodedNativeABoxCardinalityTaxonomyDecision.coordinates_exact _ haligned) ih

private theorem nativeCardinalitySubsumptionRowAlignment_coordinates_exact
    (sub : Nat) {named : List Nat}
    {decisions : List DecodedNativeABoxCardinalityTaxonomyDecision}
    (haligned : List.Forall₂
      (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
      named decisions) :
    List.Forall₂
      (fun sup decision =>
        decision.CoordinatesExact (.subsumption 0 sub sup))
      named decisions := by
  induction haligned with
  | nil => exact .nil
  | cons haligned _ ih =>
      exact .cons
        (DecodedNativeABoxCardinalityTaxonomyDecision.coordinates_exact _ haligned) ih

private theorem nativeCardinalitySubsumptionAlignment_coordinates_exact
    (allNamed : List Nat) {named : List Nat}
    {rows : List (List DecodedNativeABoxCardinalityTaxonomyDecision)}
    (haligned : List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
        allNamed row)
      named rows) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision =>
          decision.CoordinatesExact (.subsumption 0 sub sup))
        allNamed row)
      named rows := by
  induction haligned with
  | nil => exact .nil
  | cons hrow _ ih =>
      exact .cons
        (nativeCardinalitySubsumptionRowAlignment_coordinates_exact _ hrow) ih

theorem DecodedNativeABoxCardinalityTaxonomyMatrix.concept_coordinates_exact
    (decoded : DecodedNativeABoxCardinalityTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision =>
        decision.CoordinatesExact (.concept 0 concept))
      decoded.named decoded.concepts :=
  nativeCardinalityConceptAlignment_coordinates_exact decoded.concepts_exact

theorem DecodedNativeABoxCardinalityTaxonomyMatrix.subsumption_coordinates_exact
    (decoded : DecodedNativeABoxCardinalityTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision =>
          decision.CoordinatesExact (.subsumption 0 sub sup))
        decoded.named row)
      decoded.named decoded.subsumptions :=
  nativeCardinalitySubsumptionAlignment_coordinates_exact decoded.named
    decoded.subsumptions_exact

theorem DecodedNativeABoxCardinalityTaxonomyMatrix.semantic_valid
    (decoded : DecodedNativeABoxCardinalityTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.complete_shape, decoded.exact_queries,
    decoded.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

#print axioms NativeABox.ExactDistinctQuerySeed.initializes
#print axioms FiniteDistinctCardinalityRefutationTree.checkClosed_native_abox_query_unsatisfiable
#print axioms DecodedNativeABoxCardinalityTaxonomyDecision.semantic_valid
#print axioms DecodedNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
#print axioms DecodedNativeABoxCardinalityTaxonomyMatrix.concept_coordinates_exact
#print axioms DecodedNativeABoxCardinalityTaxonomyMatrix.subsumption_coordinates_exact
#print axioms DecodedNativeABoxCardinalityTaxonomyMatrix.semantic_valid
#print axioms CompleteNativeABoxCardinalityTaxonomyCertificate.unsatisfiable_exact
#print axioms CompleteNativeABoxCardinalityTaxonomyCertificate.subsumptions_exact

end ContextCalculus.Hypertableau
