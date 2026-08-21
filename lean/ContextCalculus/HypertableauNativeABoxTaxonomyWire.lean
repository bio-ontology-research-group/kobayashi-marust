import ContextCalculus.HypertableauNativeABoxTaxonomy

/-!
# Executable native-ABox taxonomy query wire

Each cell binds one query to either a checked terminal native-ABox model or an
exact joint initial state and finite equality refutation.  The query root must
be disjoint from every named-individual root.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireNativeABoxTaxonomyQuery where
  | concept (root concept : Nat)
  | subsumption (root sub sup : Nat)
deriving FromJson, ToJson, Repr

inductive DecodedNativeABoxTaxonomyQuery (nodeCount conceptCount : Nat) where
  | concept (root : Fin nodeCount) (concept : Fin conceptCount)
  | subsumption (root : Fin nodeCount) (sub sup : Fin conceptCount)

def WireNativeABoxTaxonomyQuery.decode
    (wire : WireNativeABoxTaxonomyQuery) (nodeCount conceptCount : Nat) :
    Except String (DecodedNativeABoxTaxonomyQuery nodeCount conceptCount) :=
  match wire with
  | WireNativeABoxTaxonomyQuery.concept root conceptId => do
      return DecodedNativeABoxTaxonomyQuery.concept
        (← checkedFin "taxonomy query root" nodeCount root)
        (← checkedFin "taxonomy concept" conceptCount conceptId)
  | WireNativeABoxTaxonomyQuery.subsumption root sub sup => do
      return DecodedNativeABoxTaxonomyQuery.subsumption
        (← checkedFin "taxonomy query root" nodeCount root)
        (← checkedFin "taxonomy subclass" conceptCount sub)
        (← checkedFin "taxonomy superclass" conceptCount sup)

def DecodedNativeABoxTaxonomyQuery.root :
    DecodedNativeABoxTaxonomyQuery nodeCount conceptCount → Fin nodeCount
  | DecodedNativeABoxTaxonomyQuery.concept root _ => root
  | DecodedNativeABoxTaxonomyQuery.subsumption root _ _ => root

def DecodedNativeABoxTaxonomyQuery.literals :
    DecodedNativeABoxTaxonomyQuery nodeCount conceptCount → List (Lit (Fin conceptCount))
  | DecodedNativeABoxTaxonomyQuery.concept _ conceptId => [.pos conceptId]
  | DecodedNativeABoxTaxonomyQuery.subsumption _ sub sup =>
      [.pos sub, .negated sup]

def DecodedNativeABoxTaxonomyQuery.queryLabels
    (query : DecodedNativeABoxTaxonomyQuery nodeCount conceptCount) :
    List (Fin nodeCount × Lit (Fin conceptCount)) :=
  query.literals.map (query.root, ·)

def DecodedNativeABoxTaxonomyQuery.labelsPresentB
    (query : DecodedNativeABoxTaxonomyQuery nodeCount conceptCount)
    (labels : List (Fin nodeCount × Lit (Fin conceptCount))) : Bool :=
  query.literals.all fun literal => decide ((query.root, literal) ∈ labels)

theorem DecodedNativeABoxTaxonomyQuery.labelsPresentB_sound
    (query : DecodedNativeABoxTaxonomyQuery nodeCount conceptCount)
    (labels : List (Fin nodeCount × Lit (Fin conceptCount)))
    (hcheck : query.labelsPresentB labels = true) :
    ∀ literal ∈ query.literals, (query.root, literal) ∈ labels := by
  simpa only [DecodedNativeABoxTaxonomyQuery.labelsPresentB,
    List.all_eq_true, decide_eq_true_eq] using hcheck

def DecodedNativeABox.exactEqQuerySeedB
    (decoded : DecodedNativeABox)
    (state : FiniteEqCertificate nodeCount decoded.concepts.length
      decoded.roles.length variableCount)
    (root : Fin decoded.individuals.length → Fin nodeCount)
    (query : DecodedNativeABoxTaxonomyQuery nodeCount decoded.concepts.length) : Bool :=
  decide (state.base.labels = decoded.initialLabels root ++ query.queryLabels) &&
  decide (state.base.edges = decoded.initialEdges root) &&
  decide (state.base.obligations = []) && decide (state.equalities = [])

theorem DecodedNativeABox.exactEqQuerySeedB_sound
    (decoded : DecodedNativeABox)
    (state : FiniteEqCertificate nodeCount decoded.concepts.length
      decoded.roles.length variableCount)
    (root : Fin decoded.individuals.length → Fin nodeCount)
    (query : DecodedNativeABoxTaxonomyQuery nodeCount decoded.concepts.length)
    (hcheck : decoded.exactEqQuerySeedB state root query = true) :
    decoded.abox.ExactEqQuerySeed query.literals state.state root query.root := by
  simp only [DecodedNativeABox.exactEqQuerySeedB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hlabels, hedges⟩, hobligations⟩, hequalities⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro node literal
    rw [FiniteEqCertificate.state, FiniteSatCertificate.state, hlabels]
    simp only [List.mem_append, DecodedNativeABox.initialLabels,
      List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
      DecodedNativeABoxTaxonomyQuery.queryLabels]
    constructor
    · intro hmem
      rcases hmem with hnative | hquery
      · rcases hnative with ⟨individual, concept, hconcept, hequal⟩
        injection hequal with hnode hliteral
        exact Or.inl ⟨individual, concept, hnode.symm, hconcept, hliteral.symm⟩
      · rcases hquery with ⟨queryLiteral, hqueryLiteral, hequal⟩
        injection hequal with hnode hliteral
        exact Or.inr ⟨hnode.symm, hliteral ▸ hqueryLiteral⟩
    · intro hsource
      rcases hsource with
        ⟨individual, concept, rfl, hconcept, rfl⟩ | ⟨rfl, hqueryLiteral⟩
      · exact Or.inl ⟨individual, concept, hconcept, rfl⟩
      · exact Or.inr ⟨literal, hqueryLiteral, rfl⟩
  · intro role source target
    rw [FiniteEqCertificate.state, FiniteSatCertificate.state, hedges]
    simp only [DecodedNativeABox.initialEdges, List.mem_map]
    constructor
    · rintro ⟨assertion, hassertion, hequal⟩
      have hrole := congrArg Prod.fst hequal
      have hrest := congrArg Prod.snd hequal
      have hsource := congrArg Prod.fst hrest
      have htarget := congrArg Prod.snd hrest
      exact ⟨assertion, hassertion, hrole.symm, hsource.symm, htarget.symm⟩
    · rintro ⟨assertion, hassertion, rfl, rfl, rfl⟩
      exact ⟨assertion, hassertion, rfl⟩
  · simpa [FiniteEqCertificate.state, FiniteSatCertificate.state, hobligations]
  · simp only [FiniteEqCertificate.state, hequalities, List.not_mem_nil]
    intro left right
    constructor
    · intro hequiv
      induction hequiv with
      | rel _ _ hfalse => exact False.elim hfalse
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · intro hequal
      subst right
      exact Relation.EqvGen.refl left

inductive WireNativeABoxTaxonomyEvidence where
  | sat (certificate : WireNativeABoxSatCertificate)
  | unsat (initial : WireNativeABoxSeed) (tree : WireEqRefutationTree)
deriving FromJson, ToJson, Repr

structure WireNativeABoxTaxonomyDecision where
  version : Nat
  query : WireNativeABoxTaxonomyQuery
  evidence : WireNativeABoxTaxonomyEvidence
deriving FromJson, ToJson, Repr

structure DecodedNativeABoxTaxonomySat where
  certificate : DecodedNativeABoxSatCertificate
  query : DecodedNativeABoxTaxonomyQuery certificate.seed.nodeCount
    certificate.seed.abox.concepts.length
  query_present : ∀ literal ∈ query.literals,
    (query.root, literal) ∈ certificate.seed.state.base.base.labels

structure DecodedNativeABoxTaxonomyUnsat where
  initial : DecodedNativeABoxSeed
  query : DecodedNativeABoxTaxonomyQuery initial.nodeCount
    initial.abox.concepts.length
  query_root_disjoint : ∀ individual, query.root ≠ initial.roots individual
  exact_initial : initial.abox.abox.ExactEqQuerySeed query.literals
    initial.state.base.state initial.roots query.root
  tree : FiniteEqRefutationTree initial.nodeCount initial.abox.concepts.length
    initial.abox.roles.length initial.variableCount
  checked : tree.check initial.state.base = true

inductive DecodedNativeABoxTaxonomyDecision where
  | sat (decoded : DecodedNativeABoxTaxonomySat)
  | unsat (decoded : DecodedNativeABoxTaxonomyUnsat)

def WireNativeABoxTaxonomyDecision.decode
    (wire : WireNativeABoxTaxonomyDecision) :
    Except String DecodedNativeABoxTaxonomyDecision := do
  if wire.version != 1 then
    throw s!"unsupported native ABox taxonomy decision version {wire.version}"
  match wire.evidence with
  | .sat certificateWire =>
      let certificate ← certificateWire.decode
      let query ← wire.query.decode certificate.seed.nodeCount
        certificate.seed.abox.concepts.length
      if hquery : query.labelsPresentB certificate.seed.state.base.base.labels = true then
        return .sat {
          certificate
          query
          query_present := query.labelsPresentB_sound _ hquery
        }
      else throw "native ABox taxonomy countermodel omits its query literals"
  | .unsat initialWire treeWire =>
      let expectedRoots := (List.range initialWire.abox.individuals.length).map (· + 1)
      unless initialWire.roots == expectedRoots do
        throw "native ABox taxonomy roots must be ordered nodes 1 through N"
      let initial ← initialWire.decode
      let query ← wire.query.decode initial.nodeCount initial.abox.concepts.length
      let queryZero : Fin initial.nodeCount :=
        ⟨0, Nat.pos_of_ne_zero initial.node_nonzero⟩
      if hqueryRoot : query.root = queryZero then
        if hdisjoint : ∀ individual, query.root ≠ initial.roots individual then
          if hexact : initial.abox.exactEqQuerySeedB initial.state.base
              initial.roots query = true then
            let tree ← treeWire.decode initial.nodeCount initial.abox.concepts.length
              initial.abox.roles.length initial.variableCount initial.ontology
            if htree : tree.check initial.state.base = true then
              return .unsat {
                initial
                query
                query_root_disjoint := hdisjoint
                exact_initial := initial.abox.exactEqQuerySeedB_sound
                  initial.state.base initial.roots query hexact
                tree
                checked := htree
              }
            else throw "native ABox taxonomy equality refutation did not close"
          else throw "native ABox taxonomy refutation root is not the exact joint query seed"
        else throw "native ABox taxonomy query root overlaps a named-individual root"
      else throw "native ABox taxonomy query root must be node zero"

def WireNativeABoxTaxonomyDecision.check
    (wire : WireNativeABoxTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedNativeABoxTaxonomyUnsat.unsatisfiable
    (decoded : DecodedNativeABoxTaxonomyUnsat) :
    ¬decoded.initial.abox.abox.SatisfiableWithQuery
      decoded.initial.state.base.base.ontology decoded.query.literals :=
  decoded.tree.check_native_abox_query_unsatisfiable decoded.initial.state.base
    decoded.initial.abox.abox decoded.query.literals
    (decoded.exact_initial.initializes decoded.initial.abox.abox
      decoded.query.literals decoded.initial.state.base.state decoded.initial.roots
      decoded.query.root decoded.initial.roots_injective decoded.query_root_disjoint)
    decoded.checked

def DecodedNativeABoxTaxonomyDecision.SemanticallyValid :
    DecodedNativeABoxTaxonomyDecision → Prop
  | .sat decoded => decoded.certificate.seed.abox.abox.SatisfiableWithQuery
      decoded.certificate.seed.state.base.base.ontology decoded.query.literals
  | .unsat decoded => ¬decoded.initial.abox.abox.SatisfiableWithQuery
      decoded.initial.state.base.base.ontology decoded.query.literals

theorem DecodedNativeABoxTaxonomyDecision.semantic_valid
    (decoded : DecodedNativeABoxTaxonomyDecision) : decoded.SemanticallyValid := by
  cases decoded with
  | sat result =>
      change result.certificate.seed.abox.abox.SatisfiableWithQuery
        result.certificate.seed.state.base.base.ontology result.query.literals
      exact result.certificate.satisfiable_with_query result.query.root
        result.query.literals result.query_present
  | unsat result =>
      change ¬result.initial.abox.abox.SatisfiableWithQuery
        result.initial.state.base.base.ontology result.query.literals
      exact result.unsatisfiable

/-- The Boolean polarity consumed by KM's taxonomy readout.  `true` denotes a
closed query, hence an unsatisfiable concept or an entailed subsumption. -/
def DecodedNativeABoxTaxonomyDecision.positive :
    DecodedNativeABoxTaxonomyDecision → Bool
  | .sat _ => false
  | .unsat _ => true

def DecodedNativeABoxTaxonomyDecision.QueryEntailed :
    DecodedNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      ¬decoded.certificate.seed.abox.abox.SatisfiableWithQuery
        decoded.certificate.seed.state.base.base.ontology decoded.query.literals
  | .unsat decoded =>
      ¬decoded.initial.abox.abox.SatisfiableWithQuery
        decoded.initial.state.base.base.ontology decoded.query.literals

theorem DecodedNativeABoxTaxonomyDecision.positive_eq_true_iff
    (decision : DecodedNativeABoxTaxonomyDecision) :
    decision.positive = true ↔ decision.QueryEntailed := by
  cases decision with
  | sat decoded =>
      have hsemantic := (DecodedNativeABoxTaxonomyDecision.sat decoded).semantic_valid
      change decoded.certificate.seed.abox.abox.SatisfiableWithQuery
        decoded.certificate.seed.state.base.base.ontology
        decoded.query.literals at hsemantic
      change (false = true ↔
        ¬decoded.certificate.seed.abox.abox.SatisfiableWithQuery
          decoded.certificate.seed.state.base.base.ontology decoded.query.literals)
      constructor
      · intro hfalse
        contradiction
      · intro hnot
        exact False.elim (hnot hsemantic)
  | unsat decoded =>
      have hsemantic := (DecodedNativeABoxTaxonomyDecision.unsat decoded).semantic_valid
      change ¬decoded.initial.abox.abox.SatisfiableWithQuery
        decoded.initial.state.base.base.ontology decoded.query.literals at hsemantic
      change (true = true ↔
        ¬decoded.initial.abox.abox.SatisfiableWithQuery
          decoded.initial.state.base.base.ontology decoded.query.literals)
      constructor
      · intro _
        exact hsemantic
      · intro _
        rfl

#print axioms DecodedNativeABox.exactEqQuerySeedB_sound
#print axioms DecodedNativeABoxTaxonomyUnsat.unsatisfiable
#print axioms DecodedNativeABoxTaxonomyDecision.semantic_valid
#print axioms DecodedNativeABoxTaxonomyDecision.positive_eq_true_iff

end ContextCalculus.Hypertableau
