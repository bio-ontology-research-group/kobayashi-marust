import ContextCalculus.HypertableauNativeABoxTaxonomy

/-!
# Consistent ABox projection by model amalgamation

This module isolates the semantic theorem used by KM's ABox/TBox projection.
The executable source screen must separately prove that its accepted TBox
fragment has `NativeABox.ModelAmalgamation`. No consistency assumption is
hidden in that closure property: a concrete full-ontology model is required as
a separate premise and is supplied only by the exact global HT publication.
-/

namespace ContextCalculus.Hypertableau

/-- The complete TBox and native ABox have a model. This is the semantic fact
provided by an accepted exact global-consistency certificate. -/
def NativeABox.FullSatisfiable
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain),
    Nonempty Domain ∧ I.models ontology ∧ abox.models I value

/-- Every full-ontology witness can be amalgamated with an arbitrary TBox
model. The resulting model retains the complete ABox in the witness component
and preserves every requested public concept predicate on the arbitrary-model
component.

The public predicate is essential for native ABoxes. Their proxy concepts are
internal singleton names, so the combined model must keep them false outside
the witness component. Taxonomy projection never asks for those internal
proxies; the executable source binding must prove that every requested named
class is public.

For nominal-free, universal-role-free SROIQ TBoxes this is witnessed by the
ordinary disjoint union. Keeping the interface semantic makes the exact
property needed by taxonomy projection explicit; the source-fragment checker
is responsible for constructing this witness. -/
def NativeABox.ModelAmalgamationFor
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (requested : Concept → Prop) : Prop :=
  ∀ (WitnessDomain : Type) (witness : Interp WitnessDomain Concept Role)
      (individual : Individual → WitnessDomain),
    witness.models ontology → abox.models witness individual →
    ∀ (OtherDomain : Type) (other : Interp OtherDomain Concept Role),
      other.models ontology →
      ∃ (CombinedDomain : Type) (combined : Interp CombinedDomain Concept Role)
          (includeWitness : WitnessDomain → CombinedDomain)
          (includeOther : OtherDomain → CombinedDomain),
        combined.models ontology ∧
        abox.models combined (includeWitness ∘ individual) ∧
        ∀ concept, requested concept → ∀ value,
          combined.concept concept (includeOther value) ↔
            other.concept concept value

/-- The stronger special case that preserves every concept, retained as a
compatibility interface for callers whose concept signature has no internal
singleton proxies. -/
def NativeABox.ModelAmalgamation
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  abox.ModelAmalgamationFor ontology (fun _ => True)

/-- A concept is private exactly when the native ABox constrains it as a
singleton proxy for at least one individual. -/
def NativeABox.ProxyConcept
    (abox : NativeABox Individual Concept Role) (concept : Concept) : Prop :=
  ∃ individual, concept ∈ abox.proxies individual

/-- Disjoint union of two interpretations, with selected private concepts
masked from the right component. Native ABox singleton proxies use this mask;
ordinary concepts and all roles retain the standard disjoint-union meaning. -/
def Interp.maskedDisjointUnion
    (privateConcept : Concept → Prop)
    (left : Interp LeftDomain Concept Role)
    (right : Interp RightDomain Concept Role) :
    Interp (Sum LeftDomain RightDomain) Concept Role where
  concept concept value := match value with
    | .inl leftValue => left.concept concept leftValue
    | .inr rightValue => ¬privateConcept concept ∧
        right.concept concept rightValue
  role role source target := match source, target with
    | .inl leftSource, .inl leftTarget =>
        left.role role leftSource leftTarget
    | .inr rightSource, .inr rightTarget =>
        right.role role rightSource rightTarget
    | _, _ => False

/-- Exact TBox closure property needed by native-ABox projection. It is stated
independently of the witness ABox: combining any two TBox models and masking
the supplied private concepts must remain a TBox model. A source checker can
establish this by proving that the TBox is nominal-free, universal-role-free,
component-local, and contains none of the generated private proxies. -/
def Interp.MaskedDisjointUnionClosed
    (ontology : List (Clause Variable Concept Role))
    (privateConcept : Concept → Prop) : Prop :=
  ∀ (LeftDomain RightDomain : Type)
      (left : Interp LeftDomain Concept Role)
      (right : Interp RightDomain Concept Role),
    left.models ontology → right.models ontology →
      (Interp.maskedDisjointUnion privateConcept left right).models ontology

/-- Clause-local form of masked disjoint-union closure. This is the executable
checker boundary: the normalized source screen can certify clauses one at a
time, while the theorem below lifts those certificates to the whole TBox. -/
def Clause.MaskedDisjointUnionClosed
    (clause : Clause Variable Concept Role)
    (privateConcept : Concept → Prop) : Prop :=
  ∀ (LeftDomain RightDomain : Type)
      (left : Interp LeftDomain Concept Role)
      (right : Interp RightDomain Concept Role),
    left.modelsClause clause → right.modelsClause clause →
      (Interp.maskedDisjointUnion privateConcept left right).modelsClause clause

/-- Every concept mentioned by an atom is public with respect to the mask. -/
def Atom.AvoidsPrivate
    (privateConcept : Concept → Prop) :
    Atom Variable Concept Role → Prop
  | .concept lit _ => ¬privateConcept lit.concept
  | .exists_ _ filler _ => ¬privateConcept filler.concept
  | .role _ _ _ | .eq _ _ => True

/-- A variable occurs in an atom, including the source of an existential. -/
def Atom.Mentions (candidate : Variable) :
    Atom Variable Concept Role → Prop
  | .concept _ node | .exists_ _ _ node => candidate = node
  | .role _ source target | .eq source target =>
      candidate = source ∨ candidate = target

/-- Reachability in the undirected body role/equality graph. Concept and
existential atoms do not connect distinct variables. -/
inductive Clause.BodyLinked (clause : Clause Variable Concept Role)
    (root : Variable) : Variable → Prop
  | refl : clause.BodyLinked root root
  | roleFwd (source target : Variable) (role : Role) :
      clause.BodyLinked root source →
      Atom.role role source target ∈ clause.body →
      clause.BodyLinked root target
  | roleBwd (source target : Variable) (role : Role) :
      clause.BodyLinked root target →
      Atom.role role source target ∈ clause.body →
      clause.BodyLinked root source
  | eqFwd (source target : Variable) :
      clause.BodyLinked root source →
      Atom.eq source target ∈ clause.body →
      clause.BodyLinked root target
  | eqBwd (source target : Variable) :
      clause.BodyLinked root target →
      Atom.eq source target ∈ clause.body →
      clause.BodyLinked root source

/-- The executable clause-shape contract: no masked concept occurs and every
variable in the clause is connected to one root by body roles/equalities. -/
def Clause.MaskedComponentLocal
    (clause : Clause Variable Concept Role)
    (privateConcept : Concept → Prop) : Prop :=
  (∀ atom ∈ clause.body ++ clause.head, atom.AvoidsPrivate privateConcept) ∧
  ∃ root, ∀ atom ∈ clause.body ++ clause.head, ∀ candidate,
    atom.Mentions candidate → clause.BodyLinked root candidate

private theorem Interp.maskedDisjointUnion_satLit_left
    (privateConcept : Concept → Prop)
    (left : Interp LeftDomain Concept Role)
    (right : Interp RightDomain Concept Role)
    (lit : Lit Concept) (value : LeftDomain) :
    (Interp.maskedDisjointUnion privateConcept left right).satLit lit (.inl value) ↔
      left.satLit lit value := by
  cases lit with
  | mk concept neg => cases neg <;> simp [Interp.satLit, Interp.maskedDisjointUnion]

private theorem Interp.maskedDisjointUnion_satLit_right
    (privateConcept : Concept → Prop)
    (left : Interp LeftDomain Concept Role)
    (right : Interp RightDomain Concept Role)
    (lit : Lit Concept) (value : RightDomain)
    (hpublic : ¬privateConcept lit.concept) :
    (Interp.maskedDisjointUnion privateConcept left right).satLit lit (.inr value) ↔
      right.satLit lit value := by
  cases lit with
  | mk concept neg => cases neg <;>
      simp [Interp.satLit, Interp.maskedDisjointUnion, hpublic]

private theorem Clause.bodyLinked_same_component
    (clause : Clause Variable Concept Role) (root candidate : Variable)
    (privateConcept : Concept → Prop)
    (left : Interp LeftDomain Concept Role)
    (right : Interp RightDomain Concept Role)
    (assignment : Variable → Sum LeftDomain RightDomain)
    (hbody : ∀ atom ∈ clause.body,
      (Interp.maskedDisjointUnion privateConcept left right).satAtom assignment atom)
    (hlinked : clause.BodyLinked root candidate) :
    (∃ rootValue candidateValue,
      assignment root = .inl rootValue ∧ assignment candidate = .inl candidateValue) ∨
    (∃ rootValue candidateValue,
      assignment root = .inr rootValue ∧ assignment candidate = .inr candidateValue) := by
  induction hlinked with
  | refl =>
      cases hroot : assignment root with
      | inl value => exact Or.inl ⟨value, value, by simpa using hroot, rfl⟩
      | inr value => exact Or.inr ⟨value, value, by simpa using hroot, rfl⟩
  | roleFwd source target role _ hmember ih =>
      rcases ih with ⟨rv, sv, hr, hs⟩ | ⟨rv, sv, hr, hs⟩
      · cases ht : assignment target with
        | inl tv => exact Or.inl ⟨rv, tv, by simpa using hr, rfl⟩
        | inr tv => simpa [Interp.satAtom, Interp.maskedDisjointUnion, hs, ht]
            using hbody (.role role source target) hmember
      · cases ht : assignment target with
        | inl tv => simpa [Interp.satAtom, Interp.maskedDisjointUnion, hs, ht]
            using hbody (.role role source target) hmember
        | inr tv => exact Or.inr ⟨rv, tv, by simpa using hr, rfl⟩
  | roleBwd source target role _ hmember ih =>
      rcases ih with ⟨rv, tv, hr, ht⟩ | ⟨rv, tv, hr, ht⟩
      · cases hs : assignment source with
        | inl sv => exact Or.inl ⟨rv, sv, by simpa using hr, rfl⟩
        | inr sv => simpa [Interp.satAtom, Interp.maskedDisjointUnion, hs, ht]
            using hbody (.role role source target) hmember
      · cases hs : assignment source with
        | inl sv => simpa [Interp.satAtom, Interp.maskedDisjointUnion, hs, ht]
            using hbody (.role role source target) hmember
        | inr sv => exact Or.inr ⟨rv, sv, by simpa using hr, rfl⟩
  | eqFwd source target _ hmember ih =>
      rcases ih with ⟨rv, sv, hr, hs⟩ | ⟨rv, sv, hr, hs⟩
      · have heq := hbody (.eq source target) hmember
        rw [Interp.satAtom, hs] at heq
        cases ht : assignment target with
        | inl tv => exact Or.inl ⟨rv, tv, by simpa using hr, rfl⟩
        | inr tv => cases heq.trans ht
      · have heq := hbody (.eq source target) hmember
        rw [Interp.satAtom, hs] at heq
        cases ht : assignment target with
        | inl tv => cases heq.trans ht
        | inr tv => exact Or.inr ⟨rv, tv, by simpa using hr, rfl⟩
  | eqBwd source target _ hmember ih =>
      rcases ih with ⟨rv, tv, hr, ht⟩ | ⟨rv, tv, hr, ht⟩
      · have heq := hbody (.eq source target) hmember
        rw [Interp.satAtom, ht] at heq
        cases hs : assignment source with
        | inl sv => exact Or.inl ⟨rv, sv, by simpa using hr, rfl⟩
        | inr sv => cases hs.symm.trans heq
      · have heq := hbody (.eq source target) hmember
        rw [Interp.satAtom, ht] at heq
        cases hs : assignment source with
        | inl sv => cases hs.symm.trans heq
        | inr sv => exact Or.inr ⟨rv, sv, by simpa using hr, rfl⟩

private theorem Interp.maskedDisjointUnion_satAtom_left_iff
    (privateConcept : Concept → Prop)
    (left : Interp LeftDomain Concept Role)
    (right : Interp RightDomain Concept Role)
    (assignment : Variable → Sum LeftDomain RightDomain)
    (fallback : LeftDomain) (atom : Atom Variable Concept Role)
    (hpublic : atom.AvoidsPrivate privateConcept)
    (hleft : ∀ candidate, atom.Mentions candidate →
      ∃ value, assignment candidate = .inl value) :
    (Interp.maskedDisjointUnion privateConcept left right).satAtom assignment atom ↔
      left.satAtom (fun candidate => match assignment candidate with
        | .inl value => value | .inr _ => fallback) atom := by
  cases atom with
  | concept lit node =>
      rcases hleft node rfl with ⟨value, hvalue⟩
      simpa [Interp.satAtom, hvalue] using
        (Interp.maskedDisjointUnion_satLit_left
          privateConcept left right lit value)
  | role role source target =>
      rcases hleft source (Or.inl rfl) with ⟨sourceValue, hsource⟩
      rcases hleft target (Or.inr rfl) with ⟨targetValue, htarget⟩
      simp [Interp.satAtom, Interp.maskedDisjointUnion, hsource, htarget]
  | exists_ role filler node =>
      rcases hleft node rfl with ⟨nodeValue, hnode⟩
      constructor
      · rintro ⟨witness, hedge, hfiller⟩
        cases witness with
        | inl witnessValue =>
            refine ⟨witnessValue, ?_, ?_⟩
            · simpa [Interp.maskedDisjointUnion, hnode] using hedge
            · exact (Interp.maskedDisjointUnion_satLit_left
                privateConcept left right filler witnessValue).1 hfiller
        | inr witnessValue =>
            simp [Interp.maskedDisjointUnion, hnode] at hedge
      · rintro ⟨witness, hedge, hfiller⟩
        refine ⟨Sum.inl witness, ?_, ?_⟩
        · simpa [Interp.satAtom, Interp.maskedDisjointUnion, hnode] using hedge
        · exact (Interp.maskedDisjointUnion_satLit_left
            privateConcept left right filler witness).2 hfiller
  | eq source target =>
      rcases hleft source (Or.inl rfl) with ⟨sourceValue, hsource⟩
      rcases hleft target (Or.inr rfl) with ⟨targetValue, htarget⟩
      simp [Interp.satAtom, hsource, htarget]

private theorem Interp.maskedDisjointUnion_satAtom_right_iff
    (privateConcept : Concept → Prop)
    (left : Interp LeftDomain Concept Role)
    (right : Interp RightDomain Concept Role)
    (assignment : Variable → Sum LeftDomain RightDomain)
    (fallback : RightDomain) (atom : Atom Variable Concept Role)
    (hpublic : atom.AvoidsPrivate privateConcept)
    (hright : ∀ candidate, atom.Mentions candidate →
      ∃ value, assignment candidate = .inr value) :
    (Interp.maskedDisjointUnion privateConcept left right).satAtom assignment atom ↔
      right.satAtom (fun candidate => match assignment candidate with
        | .inl _ => fallback | .inr value => value) atom := by
  cases atom with
  | concept lit node =>
      rcases hright node rfl with ⟨value, hvalue⟩
      simpa [Interp.satAtom, hvalue] using
        (Interp.maskedDisjointUnion_satLit_right
          privateConcept left right lit value hpublic)
  | role role source target =>
      rcases hright source (Or.inl rfl) with ⟨sourceValue, hsource⟩
      rcases hright target (Or.inr rfl) with ⟨targetValue, htarget⟩
      simp [Interp.satAtom, Interp.maskedDisjointUnion, hsource, htarget]
  | exists_ role filler node =>
      rcases hright node rfl with ⟨nodeValue, hnode⟩
      constructor
      · rintro ⟨witness, hedge, hfiller⟩
        cases witness with
        | inl witnessValue =>
            simp [Interp.maskedDisjointUnion, hnode] at hedge
        | inr witnessValue =>
            refine ⟨witnessValue, ?_, ?_⟩
            · simpa [Interp.maskedDisjointUnion, hnode] using hedge
            · exact (Interp.maskedDisjointUnion_satLit_right
                privateConcept left right filler witnessValue hpublic).1 hfiller
      · rintro ⟨witness, hedge, hfiller⟩
        refine ⟨Sum.inr witness, ?_, ?_⟩
        · simpa [Interp.satAtom, Interp.maskedDisjointUnion, hnode] using hedge
        · exact (Interp.maskedDisjointUnion_satLit_right
            privateConcept left right filler witness hpublic).2 hfiller
  | eq source target =>
      rcases hright source (Or.inl rfl) with ⟨sourceValue, hsource⟩
      rcases hright target (Or.inr rfl) with ⟨targetValue, htarget⟩
      simp [Interp.satAtom, hsource, htarget]

/-- The executable connected-clause screen is sufficient for semantic masked
disjoint-union closure. This is the source theorem behind KM's fast ABox/TBox
projection route: a true body forces every clause variable into one summand,
and absence of private concepts makes every atom componentwise exact. -/
theorem Clause.maskedDisjointUnionClosed_of_maskedComponentLocal
    (clause : Clause Variable Concept Role)
    (privateConcept : Concept → Prop)
    (hlocal : clause.MaskedComponentLocal privateConcept) :
    clause.MaskedDisjointUnionClosed privateConcept := by
  intro LeftDomain RightDomain left right hleftModel hrightModel assignment hbody
  rcases hlocal with ⟨hpublic, root, hconnected⟩
  cases hroot : assignment root with
  | inl rootValue =>
      let componentAssignment : Variable → LeftDomain := fun candidate =>
        match assignment candidate with
        | .inl value => value
        | .inr _ => rootValue
      have allLeft : ∀ atom ∈ clause.body ++ clause.head, ∀ candidate,
          atom.Mentions candidate → ∃ value, assignment candidate = .inl value := by
        intro atom hatom candidate hmentions
        have hlinked := hconnected atom hatom candidate hmentions
        rcases clause.bodyLinked_same_component root candidate privateConcept
            left right assignment hbody hlinked with hsame | hopposite
        · rcases hsame with ⟨_, value, _, hvalue⟩
          exact ⟨value, hvalue⟩
        · rcases hopposite with ⟨oppositeRoot, _, hoppositeRoot, _⟩
          cases hroot.symm.trans hoppositeRoot
      have componentBody : ∀ atom ∈ clause.body,
          left.satAtom componentAssignment atom := by
        intro atom hatom
        apply (Interp.maskedDisjointUnion_satAtom_left_iff
          privateConcept left right assignment rootValue atom
          (hpublic atom (List.mem_append_left clause.head hatom))
          (allLeft atom (List.mem_append_left clause.head hatom))).1
        exact hbody atom hatom
      rcases hleftModel componentAssignment componentBody with
        ⟨atom, hatom, hsatisfied⟩
      refine ⟨atom, hatom, ?_⟩
      apply (Interp.maskedDisjointUnion_satAtom_left_iff
        privateConcept left right assignment rootValue atom
        (hpublic atom (List.mem_append_right clause.body hatom))
        (allLeft atom (List.mem_append_right clause.body hatom))).2
      exact hsatisfied
  | inr rootValue =>
      let componentAssignment : Variable → RightDomain := fun candidate =>
        match assignment candidate with
        | .inl _ => rootValue
        | .inr value => value
      have allRight : ∀ atom ∈ clause.body ++ clause.head, ∀ candidate,
          atom.Mentions candidate → ∃ value, assignment candidate = .inr value := by
        intro atom hatom candidate hmentions
        have hlinked := hconnected atom hatom candidate hmentions
        rcases clause.bodyLinked_same_component root candidate privateConcept
            left right assignment hbody hlinked with hopposite | hsame
        · rcases hopposite with ⟨oppositeRoot, _, hoppositeRoot, _⟩
          cases hroot.symm.trans hoppositeRoot
        · rcases hsame with ⟨_, value, _, hvalue⟩
          exact ⟨value, hvalue⟩
      have componentBody : ∀ atom ∈ clause.body,
          right.satAtom componentAssignment atom := by
        intro atom hatom
        apply (Interp.maskedDisjointUnion_satAtom_right_iff
          privateConcept left right assignment rootValue atom
          (hpublic atom (List.mem_append_left clause.head hatom))
          (allRight atom (List.mem_append_left clause.head hatom))).1
        exact hbody atom hatom
      rcases hrightModel componentAssignment componentBody with
        ⟨atom, hatom, hsatisfied⟩
      refine ⟨atom, hatom, ?_⟩
      apply (Interp.maskedDisjointUnion_satAtom_right_iff
        privateConcept left right assignment rootValue atom
        (hpublic atom (List.mem_append_right clause.body hatom))
        (allRight atom (List.mem_append_right clause.body hatom))).2
      exact hsatisfied

/-- Per-clause closure is sufficient for closure of the complete normalized
ontology. This removes a whole-ontology semantic assumption from the eventual
source gate: every accepted clause must carry its own local certificate. -/
theorem Interp.maskedDisjointUnionClosed_of_all_clauses
    (ontology : List (Clause Variable Concept Role))
    (privateConcept : Concept → Prop)
    (hclauses : ∀ clause ∈ ontology,
      clause.MaskedDisjointUnionClosed privateConcept) :
    Interp.MaskedDisjointUnionClosed ontology privateConcept := by
  intro LeftDomain RightDomain left right hleft hright clause hclause
  exact hclauses clause hclause LeftDomain RightDomain left right
    (hleft clause hclause) (hright clause hclause)

/-- A complete normalized ontology accepted by the executable connected-clause
screen is closed under the masked disjoint union used by native-ABox
projection. -/
theorem Interp.maskedDisjointUnionClosed_of_maskedComponentLocal
    (ontology : List (Clause Variable Concept Role))
    (privateConcept : Concept → Prop)
    (hlocal : ∀ clause ∈ ontology,
      clause.MaskedComponentLocal privateConcept) :
    Interp.MaskedDisjointUnionClosed ontology privateConcept := by
  apply Interp.maskedDisjointUnionClosed_of_all_clauses
  intro clause hclause
  exact clause.maskedDisjointUnionClosed_of_maskedComponentLocal
    privateConcept (hlocal clause hclause)

/-- Whole-ontology closure is also necessary clause by clause when the clause
is considered as a singleton ontology. Kept as a small normalization lemma for
checker-facing proofs. -/
theorem Clause.maskedDisjointUnionClosed_iff_singleton
    (clause : Clause Variable Concept Role)
    (privateConcept : Concept → Prop) :
    clause.MaskedDisjointUnionClosed privateConcept ↔
      Interp.MaskedDisjointUnionClosed [clause] privateConcept := by
  constructor
  · intro hclause LeftDomain RightDomain left right hleft hright
    exact Interp.maskedDisjointUnionClosed_of_all_clauses [clause]
      privateConcept (by
        intro current hcurrent
        simp only [List.mem_singleton] at hcurrent
        subst current
        exact hclause)
      LeftDomain RightDomain left right hleft hright
  · intro hclosed LeftDomain RightDomain left right hleft hright
    have hleftList : left.models [clause] := by
      intro current hcurrent
      simp only [List.mem_singleton] at hcurrent
      subst current
      exact hleft
    have hrightList : right.models [clause] := by
      intro current hcurrent
      simp only [List.mem_singleton] at hcurrent
      subst current
      exact hright
    exact hclosed LeftDomain RightDomain left right hleftList hrightList
      clause (by simp)

/-- Masked disjoint-union closure constructs the semantic amalgamation needed
for taxonomy projection. Public requested concepts must not be singleton
proxies; this is the precise executable signature-separation check. -/
theorem NativeABox.modelAmalgamationFor_of_maskedDisjointUnionClosed
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (requested : Concept → Prop)
    (hclosed : Interp.MaskedDisjointUnionClosed ontology abox.ProxyConcept)
    (hrequested : ∀ concept, requested concept → ¬abox.ProxyConcept concept) :
    abox.ModelAmalgamationFor ontology requested := by
  intro WitnessDomain witness individual hwitness habox
    OtherDomain other hother
  classical
  let combined := Interp.maskedDisjointUnion abox.ProxyConcept witness other
  refine ⟨Sum WitnessDomain OtherDomain, combined, Sum.inl, Sum.inr,
    hclosed WitnessDomain OtherDomain witness other hwitness hother, ?_, ?_⟩
  · rcases habox with ⟨hproxy, hassertion, hdifferent, hrole, hnegative⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro source proxy hproxyMember candidate
      cases candidate with
      | inl candidate =>
          simpa [combined, Interp.maskedDisjointUnion] using
            hproxy source proxy hproxyMember candidate
      | inr candidate =>
          have hprivate : abox.ProxyConcept proxy := ⟨source, hproxyMember⟩
          simp [combined, Interp.maskedDisjointUnion, hprivate]
    · intro source concept hasserted
      simpa [combined, Interp.maskedDisjointUnion] using
        hassertion source concept hasserted
    · intro pair hpair hequal
      exact hdifferent pair hpair (Sum.inl_injective hequal)
    · intro assertion hassertionMember
      simpa [combined, Interp.maskedDisjointUnion] using
        hrole assertion hassertionMember
    · intro assertion hassertionMember
      simpa [combined, Interp.maskedDisjointUnion] using
        hnegative assertion hassertionMember
  · intro concept hconcept value
    have hnotPrivate := hrequested concept hconcept
    simp [combined, Interp.maskedDisjointUnion, hnotPrivate]

/-- Once the full ontology is consistent and its TBox admits public-concept
amalgamation, adding the ABox changes no subsumption between public concepts. -/
theorem NativeABox.entailsSubWith_iff_entailsSub_of_modelAmalgamationFor
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (requested : Concept → Prop)
    (hfull : abox.FullSatisfiable ontology)
    (hamalgamate : abox.ModelAmalgamationFor ontology requested)
    (sub sup : Concept) (hsubPublic : requested sub) (hsupPublic : requested sup) :
    abox.EntailsSubWith ontology sub sup ↔ EntailsSub ontology sub sup := by
  constructor
  · intro haboxEntails OtherDomain other hother value hsub
    by_contra hsup
    rcases hfull with
      ⟨WitnessDomain, witness, individual, ⟨witnessValue⟩, hwitness, habox⟩
    rcases hamalgamate WitnessDomain witness individual hwitness habox
        OtherDomain other hother with
      ⟨CombinedDomain, combined, includeWitness, includeOther,
        hcombined, haboxCombined, hconcept⟩
    letI : Nonempty CombinedDomain := ⟨includeWitness witnessValue⟩
    apply haboxEntails
    refine ⟨CombinedDomain, combined, includeWitness ∘ individual,
      includeOther value, inferInstance, hcombined, haboxCombined, ?_⟩
    intro literal hliteral
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
    rcases hliteral with rfl | rfl
    · simpa [Interp.satLit, Lit.pos] using
        (hconcept sub hsubPublic value).2 hsub
    · simpa [Interp.satLit, Lit.negated] using
        (show ¬combined.concept sup (includeOther value) from
          fun h => hsup ((hconcept sup hsupPublic value).1 h))
  · intro htboxEntails hquery
    rcases hquery with
      ⟨Domain, interpretation, individual, value, _, hmodels, _, hrealizes⟩
    have hsub : interpretation.concept sub value := by
      simpa [Interp.satLit, Lit.pos] using
        hrealizes (.pos sub) (by simp)
    have hnotSup : ¬interpretation.concept sup value := by
      simpa [Interp.satLit, Lit.negated] using
        hrealizes (.negated sup) (by simp)
    exact hnotSup (htboxEntails Domain interpretation hmodels value hsub)

/-- Once the full ontology is consistent and its TBox admits the disjoint-union
amalgamation, adding the ABox changes no concept subsumption. -/
theorem NativeABox.entailsSubWith_iff_entailsSub_of_modelAmalgamation
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (hfull : abox.FullSatisfiable ontology)
    (hamalgamate : abox.ModelAmalgamation ontology)
    (sub sup : Concept) :
    abox.EntailsSubWith ontology sub sup ↔ EntailsSub ontology sub sup := by
  exact abox.entailsSubWith_iff_entailsSub_of_modelAmalgamationFor ontology
    (fun _ => True) hfull hamalgamate sub sup trivial trivial

#print axioms NativeABox.modelAmalgamationFor_of_maskedDisjointUnionClosed
#print axioms Clause.maskedDisjointUnionClosed_of_maskedComponentLocal
#print axioms Interp.maskedDisjointUnionClosed_of_maskedComponentLocal
#print axioms Interp.maskedDisjointUnionClosed_of_all_clauses
#print axioms Clause.maskedDisjointUnionClosed_iff_singleton
#print axioms NativeABox.entailsSubWith_iff_entailsSub_of_modelAmalgamationFor
#print axioms NativeABox.entailsSubWith_iff_entailsSub_of_modelAmalgamation

end ContextCalculus.Hypertableau
