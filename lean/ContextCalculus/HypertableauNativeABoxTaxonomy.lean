import ContextCalculus.HypertableauNativeABoxModelWire

/-!
# Native-ABox hypertableau taxonomy semantics

A taxonomy query is interpreted together with the complete native ABox.  Its
fresh root realizes either one positive concept literal or the positive
subclass and negative superclass pair.  This module states the joint semantic
target and proves the model and refutation interfaces needed by a finite wire.
-/

namespace ContextCalculus.Hypertableau

def Interp.RealizesLiterals
    (I : Interp Domain Concept Role) (literals : List (Lit Concept))
    (element : Domain) : Prop :=
  ∀ literal ∈ literals, I.satLit literal element

def NativeABox.SatisfiableWithQuery
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (query : List (Lit Concept)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain) (element : Domain),
    Nonempty Domain ∧ I.models ontology ∧ abox.models I value ∧
      I.RealizesLiterals query element

def NativeABox.UnsatisfiableConceptWith
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (concept : Concept) : Prop :=
  ¬abox.SatisfiableWithQuery ontology [.pos concept]

def NativeABox.EntailsSubWith
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (sub sup : Concept) : Prop :=
  ¬abox.SatisfiableWithQuery ontology [.pos sub, .negated sup]

/-- Semantic initialization contract for a native ABox plus a fresh taxonomy
query root.  Every joint source model extends to a realization of the exact
finite refutation root. -/
def NativeABox.InitializesEqQueryState
    (abox : NativeABox Individual Concept Role)
    (query : List (Lit Concept))
    (state : EqState Node Concept Role) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Concept Role)
      [Nonempty Domain] (value : Individual → Domain) (element : Domain),
    abox.models I value → I.RealizesLiterals query element →
      ∃ nodeValue : Node → Domain, state.RealizedBy I nodeValue

def NativeABox.ExactEqQuerySeed
    (abox : NativeABox Individual Concept Role)
    (query : List (Lit Concept))
    (state : EqState Node Concept Role)
    (root : Individual → Node) (queryRoot : Node) : Prop :=
  (∀ node literal, state.base.label node literal ↔
    (∃ individual concept,
      node = root individual ∧
      concept ∈ abox.proxies individual ++ abox.assertions individual ∧
      literal = .pos concept) ∨
    (node = queryRoot ∧ literal ∈ query)) ∧
  (∀ role source target, state.base.edge role source target ↔
    ∃ assertion ∈ abox.roleAssertions,
      role = assertion.1 ∧ source = root assertion.2.1 ∧
        target = root assertion.2.2) ∧
  (∀ role filler node, ¬state.base.obligation role filler node) ∧
  (∀ left right, state.equiv left right ↔ left = right)

theorem NativeABox.ExactEqQuerySeed.initializes
    (abox : NativeABox Individual Concept Role)
    (query : List (Lit Concept))
    (state : EqState Node Concept Role)
    (root : Individual → Node) (queryRoot : Node)
    (hroot : Function.Injective root)
    (hqueryRoot : ∀ individual, queryRoot ≠ root individual)
    (hexact : abox.ExactEqQuerySeed query state root queryRoot) :
    abox.InitializesEqQueryState query state := by
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
        | some rightIndividual =>
            exact congrArg some (hroot hequal)
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
  have hqueryValue : nodeValue queryRoot = element :=
    htaggedValue none
  refine ⟨nodeValue, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · intro node literal hlabel
    rcases (hexact.1 node literal).1 hlabel with
      ⟨individual, concept, rfl, hconcept, rfl⟩ | ⟨rfl, hliteral⟩
    · rcases List.mem_append.mp hconcept with hproxy | hassertion
      · rw [hnativeValue]
        simpa [Interp.satLit] using
          (habox.1 individual concept hproxy (value individual)).2 rfl
      · rw [hnativeValue]
        simpa [Interp.satLit] using
          habox.2.1 individual concept hassertion
    · rw [hqueryValue]
      exact hquery literal hliteral
  · intro role source target hedge
    rcases (hexact.2.1 role source target).1 hedge with
      ⟨assertion, hassertion, rfl, rfl, rfl⟩
    rw [hnativeValue, hnativeValue]
    exact habox.2.2.2.1 assertion hassertion
  · intro role filler node hobligation
    exact (hexact.2.2.1 role filler node hobligation).elim
  · intro left right hequivalent
    exact congrArg nodeValue ((hexact.2.2.2 left right).1 hequivalent)

theorem FiniteEqRefutationTree.check_native_abox_query_unsatisfiable
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (query : List (Lit (Fin conceptCount)))
    (hinitial : abox.InitializesEqQueryState query certificate.state)
    (hcheck : tree.check certificate = true) :
    ¬abox.SatisfiableWithQuery certificate.base.ontology query := by
  rintro ⟨Domain, I, value, element, hdomain, hmodels, habox, hquery⟩
  letI : Nonempty Domain := hdomain
  rcases hinitial Domain I value element habox hquery with ⟨nodeValue, hrealized⟩
  exact tree.check_unsatisfiable certificate hcheck
    ⟨Domain, I, nodeValue, hmodels, hrealized⟩

/-- A checked native-ABox quotient that retains every query literal at one
finite node is a joint source model and query counterexample. -/
theorem DecodedNativeABoxSatCertificate.satisfiable_with_query
    (decoded : DecodedNativeABoxSatCertificate)
    (root : Fin decoded.seed.nodeCount)
    (query : List (Lit (Fin decoded.seed.abox.concepts.length)))
    (hquery : ∀ literal ∈ query,
      (root, literal) ∈ decoded.seed.state.base.base.labels) :
    decoded.seed.abox.abox.SatisfiableWithQuery
      decoded.seed.state.base.base.ontology query := by
  rcases decoded.canonical_model with ⟨value, hdomain, hontology, habox⟩
  let I := decoded.seed.state.base.state.quotientCanonical
  let nodeValue : Fin decoded.seed.nodeCount →
      decoded.seed.state.base.state.QuotientDomain :=
    fun node ↦ Quotient.mk decoded.seed.state.base.state.nodeSetoid node
  have hrealized : decoded.seed.state.base.state.RealizedBy I nodeValue :=
    decoded.seed.state.base.checkEqSat_realizes decoded.sat
  have hroot : I.RealizesLiterals query (nodeValue root) := by
    intro literal hliteral
    exact hrealized.1.1 root literal (hquery literal hliteral)
  exact ⟨decoded.seed.state.base.state.QuotientDomain, I, value,
    nodeValue root, hdomain, hontology, habox, hroot⟩

theorem DecodedNativeABoxSatCertificate.concept_satisfiable
    (decoded : DecodedNativeABoxSatCertificate)
    (root : Fin decoded.seed.nodeCount)
    (concept : Fin decoded.seed.abox.concepts.length)
    (hquery : (root, .pos concept) ∈ decoded.seed.state.base.base.labels) :
    ¬decoded.seed.abox.abox.UnsatisfiableConceptWith
      decoded.seed.state.base.base.ontology concept := by
  intro hunsat
  exact hunsat (decoded.satisfiable_with_query root [.pos concept]
    (by simpa using hquery))

theorem DecodedNativeABoxSatCertificate.non_subsumption
    (decoded : DecodedNativeABoxSatCertificate)
    (root : Fin decoded.seed.nodeCount)
    (sub sup : Fin decoded.seed.abox.concepts.length)
    (hsub : (root, .pos sub) ∈ decoded.seed.state.base.base.labels)
    (hnotSup : (root, .negated sup) ∈ decoded.seed.state.base.base.labels) :
    ¬decoded.seed.abox.abox.EntailsSubWith
      decoded.seed.state.base.base.ontology sub sup := by
  intro hentails
  exact hentails (decoded.satisfiable_with_query root [.pos sub, .negated sup]
    (by
      intro literal hliteral
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
      rcases hliteral with rfl | rfl
      · exact hsub
      · exact hnotSup))

#print axioms FiniteEqRefutationTree.check_native_abox_query_unsatisfiable
#print axioms NativeABox.ExactEqQuerySeed.initializes
#print axioms DecodedNativeABoxSatCertificate.satisfiable_with_query
#print axioms DecodedNativeABoxSatCertificate.concept_satisfiable
#print axioms DecodedNativeABoxSatCertificate.non_subsumption

end ContextCalculus.Hypertableau
