import ContextCalculus.HypertableauCardinalityDistinct

/-!
# Native named-individual ABox projection

KM seeds one non-blockable root per named individual. Proxy and asserted
concepts become positive labels, object-property assertions become edges, and
`DifferentIndividuals` becomes the explicit `apart` relation. Negative object
property assertions are checked as guarded clash clauses and are represented
semantically here by absence of the corresponding role edge.
-/

namespace ContextCalculus.Hypertableau

structure NativeABox (Individual Concept Role : Type) where
  proxies : Individual → List Concept
  assertions : Individual → List Concept
  different : List (Individual × Individual)
  roleAssertions : List (Role × Individual × Individual)
  negativeRoleAssertions : List (Role × Individual × Individual)

def NativeABox.models (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain) : Prop :=
  (∀ individual proxy, proxy ∈ abox.proxies individual →
      ∀ candidate, I.concept proxy candidate ↔ candidate = value individual) ∧
  (∀ individual concept, concept ∈ abox.assertions individual →
      I.concept concept (value individual)) ∧
  (∀ pair ∈ abox.different, value pair.1 ≠ value pair.2) ∧
  (∀ assertion ∈ abox.roleAssertions,
      I.role assertion.1 (value assertion.2.1) (value assertion.2.2)) ∧
  (∀ assertion ∈ abox.negativeRoleAssertions,
      ¬I.role assertion.1 (value assertion.2.1) (value assertion.2.2))

def NativeABox.mapConcepts (f : TargetConcept → SourceConcept)
    (abox : NativeABox Individual TargetConcept Role) :
    NativeABox Individual SourceConcept Role where
  proxies individual := (abox.proxies individual).map f
  assertions individual := (abox.assertions individual).map f
  different := abox.different
  roleAssertions := abox.roleAssertions
  negativeRoleAssertions := abox.negativeRoleAssertions

/-- Transport a native ABox model across a concept-signature extension. Only
concepts actually occurring in the ABox require agreement; role and individual
semantics are preserved exactly. -/
theorem NativeABox.models_of_mapConcepts
    (abox : NativeABox Individual TargetConcept Role)
    (f : TargetConcept → SourceConcept)
    (source : Interp Domain SourceConcept Role)
    (target : Interp Domain TargetConcept Role)
    (value : Individual → Domain)
    (hconcept : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      target.concept concept = source.concept (f concept))
    (hrole : target.role = source.role)
    (hmodels : (abox.mapConcepts f).models source value) :
    abox.models target value := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro individual proxy hproxy candidate
    have hmapped : f proxy ∈ (abox.mapConcepts f).proxies individual :=
      List.mem_map.mpr ⟨proxy, hproxy, rfl⟩
    rw [hconcept individual proxy (List.mem_append_left _ hproxy)]
    exact hmodels.1 individual (f proxy) hmapped candidate
  · intro individual concept hassertion
    have hmapped : f concept ∈ (abox.mapConcepts f).assertions individual :=
      List.mem_map.mpr ⟨concept, hassertion, rfl⟩
    rw [hconcept individual concept (List.mem_append_right _ hassertion)]
    exact hmodels.2.1 individual (f concept) hmapped
  · simpa [NativeABox.mapConcepts] using hmodels.2.2.1
  · intro assertion hassertion
    rw [hrole]
    exact hmodels.2.2.2.1 assertion hassertion
  · intro assertion hassertion
    rw [hrole]
    exact hmodels.2.2.2.2 assertion hassertion

/-- Pull a target native-ABox model back along a concept map.  This is the
converse preservation direction needed when a checked HT quotient model is
decoded back through a source projection.  The map need only preserve concepts
that actually occur in the ABox. -/
theorem NativeABox.mapConcepts_models_of
    (abox : NativeABox Individual TargetConcept Role)
    (f : TargetConcept → SourceConcept)
    (source : Interp Domain SourceConcept Role)
    (target : Interp Domain TargetConcept Role)
    (value : Individual → Domain)
    (hconcept : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      target.concept concept = source.concept (f concept))
    (hrole : target.role = source.role)
    (hmodels : abox.models target value) :
    (abox.mapConcepts f).models source value := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro individual proxy hproxy candidate
    rcases List.mem_map.mp hproxy with ⟨targetProxy, htargetProxy, rfl⟩
    rw [← hconcept individual targetProxy
      (List.mem_append_left _ htargetProxy)]
    exact hmodels.1 individual targetProxy htargetProxy candidate
  · intro individual concept hassertion
    rcases List.mem_map.mp hassertion with
      ⟨targetConcept, htargetAssertion, rfl⟩
    rw [← hconcept individual targetConcept
      (List.mem_append_right _ htargetAssertion)]
    exact hmodels.2.1 individual targetConcept htargetAssertion
  · simpa [NativeABox.mapConcepts] using hmodels.2.2.1
  · intro assertion hassertion
    rw [← hrole]
    exact hmodels.2.2.2.1 assertion hassertion
  · intro assertion hassertion
    rw [← hrole]
    exact hmodels.2.2.2.2 assertion hassertion

def nativeABoxSeed (abox : NativeABox Individual Concept Role) :
    DistinctEqState Individual Concept Role where
  base := {
    base := {
      label := fun individual literal => ∃ concept,
        concept ∈ abox.proxies individual ++ abox.assertions individual ∧
          literal = .pos concept
      edge := fun role source target => (role, source, target) ∈ abox.roleAssertions
      obligation := fun _ _ _ => False
    }
    equiv := fun left right => left = right
    equiv_equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }
  apart := fun left right =>
    (left, right) ∈ abox.different ∨ (right, left) ∈ abox.different

def NativeABox.ProxySingletons
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain) : Prop :=
  ∀ individual proxy, proxy ∈ abox.proxies individual →
    ∀ candidate, I.concept proxy candidate ↔ candidate = value individual

def NativeABox.NegativeRoles
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain) : Prop :=
  ∀ assertion ∈ abox.negativeRoleAssertions,
    ¬I.role assertion.1 (value assertion.2.1) (value assertion.2.2)

/-- The concrete completion state contains every positive fact installed by
KM's native named-root initializer. Additional derived facts are allowed. -/
def NativeABox.SeededIn (abox : NativeABox Individual Concept Role)
    (state : DistinctEqState Node Concept Role) (root : Individual → Node) : Prop :=
  (∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
        state.base.base.label (root individual) (.pos concept)) ∧
  (∀ assertion ∈ abox.roleAssertions,
      state.base.base.edge assertion.1
        (root assertion.2.1) (root assertion.2.2)) ∧
  (∀ pair ∈ abox.different, state.apart (root pair.1) (root pair.2))

theorem nativeABoxSeed_realized_of_seeded
    (abox : NativeABox Individual Concept Role)
    (state : DistinctEqState Node Concept Role) (root : Individual → Node)
    (I : Interp Domain Concept Role) (nodeValue : Node → Domain)
    (hseeded : abox.SeededIn state root)
    (hrealized : state.RealizedBy I nodeValue) :
    (nativeABoxSeed abox).RealizedBy I (nodeValue ∘ root) := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro individual literal hlabel
    rcases hlabel with ⟨concept, hconcept, rfl⟩
    exact hrealized.1.1.1 (root individual) (.pos concept)
      (hseeded.1 individual concept hconcept)
  · intro role source target hedge
    exact hrealized.1.1.2.1 role (root source) (root target)
      (hseeded.2.1 (role, source, target) hedge)
  · intro _ _ _ hfalse
    exact hfalse.elim
  · intro left right hequal
    subst right
    exact hrealized.1.2 (root left) (root left)
      (state.base.equiv_equivalence.1 (root left))
  · intro left right hapart
    rcases hapart with hdirect | hreverse
    · exact hrealized.2 (root left) (root right)
        (hseeded.2.2 (left, right) hdirect)
    · exact (hrealized.2 (root right) (root left)
        (hseeded.2.2 (right, left) hreverse)).symm

def negativeRoleAssertionClause (sourceProxy targetProxy : Concept)
    (role : Role) (source target : Variable) : Clause Variable Concept Role := {
  body := [
    .concept (.pos sourceProxy) source,
    .role role source target,
    .concept (.pos targetProxy) target
  ]
  head := []
}

theorem models_negativeRoleAssertionClause_iff
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain)
    (hsingletons : abox.ProxySingletons I value)
    (left right : Individual) (sourceProxy targetProxy : Concept)
    (hsourceProxy : sourceProxy ∈ abox.proxies left)
    (htargetProxy : targetProxy ∈ abox.proxies right)
    (role : Role) (source target : Variable) (hne : source ≠ target) :
    I.modelsClause
        (negativeRoleAssertionClause sourceProxy targetProxy role source target) ↔
      ¬I.role role (value left) (value right) := by
  classical
  constructor
  · intro hmodels hedge
    let assignment : Variable → Domain := fun candidateVariable =>
      if candidateVariable = target then value right else value left
    have hsource : assignment source = value left := by simp [assignment, hne]
    have htarget : assignment target = value right := by simp [assignment]
    have hbody : ∀ atom ∈
        (negativeRoleAssertionClause sourceProxy targetProxy role source target).body,
        I.satAtom assignment atom := by
      intro atom hatom
      simp only [negativeRoleAssertionClause, List.mem_cons, List.not_mem_nil,
        or_false] at hatom
      rcases hatom with rfl | rfl | rfl
      · simpa [Interp.satAtom, Interp.satLit, hsource] using
          (hsingletons left sourceProxy hsourceProxy (value left)).2 rfl
      · simpa [Interp.satAtom, hsource, htarget] using hedge
      · simpa [Interp.satAtom, Interp.satLit, htarget] using
          (hsingletons right targetProxy htargetProxy (value right)).2 rfl
    rcases hmodels assignment hbody with ⟨atom, hatom, _⟩
    simp [negativeRoleAssertionClause] at hatom
  · intro hnegative assignment hbody
    have hsourceSat := hbody (.concept (.pos sourceProxy) source)
      (by simp [negativeRoleAssertionClause])
    have htargetSat := hbody (.concept (.pos targetProxy) target)
      (by simp [negativeRoleAssertionClause])
    have hrole := hbody (.role role source target)
      (by simp [negativeRoleAssertionClause])
    have hsource : assignment source = value left :=
      (hsingletons left sourceProxy hsourceProxy (assignment source)).1
        (by simpa [Interp.satAtom, Interp.satLit] using hsourceSat)
    have htarget : assignment target = value right :=
      (hsingletons right targetProxy htargetProxy (assignment target)).1
        (by simpa [Interp.satAtom, Interp.satLit] using htargetSat)
    exact (hnegative (by simpa [Interp.satAtom, hsource, htarget] using hrole)).elim

theorem nativeABoxSeed_realized_iff
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain) :
    ((nativeABoxSeed abox).RealizedBy I value ∧
        abox.ProxySingletons I value ∧ abox.NegativeRoles I value) ↔
      abox.models I value := by
  constructor
  · rintro ⟨hseed, hsingletons, hnegative⟩
    refine ⟨hsingletons, ?_, ?_, ?_, hnegative⟩
    · intro individual concept hconcept
      have hlabel : (nativeABoxSeed abox).base.base.label individual (.pos concept) :=
        ⟨concept, List.mem_append_right _ hconcept, rfl⟩
      simpa [Interp.satLit] using hseed.1.1.1 individual (.pos concept) hlabel
    · intro pair hpair
      exact hseed.2 pair.1 pair.2 (Or.inl hpair)
    · intro assertion hassertion
      exact hseed.1.1.2.1 assertion.1 assertion.2.1 assertion.2.2 hassertion
  · rintro ⟨hsingletons, hassertions, hdifferent, hroles, hnegative⟩
    refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, hsingletons, hnegative⟩
    · intro individual literal hlabel
      rcases hlabel with ⟨concept, hconcept, rfl⟩
      rcases List.mem_append.mp hconcept with hproxy | hassertion
      · simpa [Interp.satLit] using
          (hsingletons individual concept hproxy (value individual)).2 rfl
      · simpa [Interp.satLit] using hassertions individual concept hassertion
    · intro role source target hedge
      exact hroles (role, source, target) hedge
    · intro _ _ _ hfalse
      exact hfalse.elim
    · intro left right hequal
      exact congrArg value hequal
    · intro left right hapart
      rcases hapart with hdirect | hreverse
      · exact hdifferent (left, right) hdirect
      · exact (hdifferent (right, left) hreverse).symm

theorem NativeABox.models_of_seeded
    (abox : NativeABox Individual Concept Role)
    (state : DistinctEqState Node Concept Role) (root : Individual → Node)
    (I : Interp Domain Concept Role) (nodeValue : Node → Domain)
    (hseeded : abox.SeededIn state root)
    (hrealized : state.RealizedBy I nodeValue)
    (hsingletons : abox.ProxySingletons I (nodeValue ∘ root))
    (hnegative : abox.NegativeRoles I (nodeValue ∘ root)) :
    abox.models I (nodeValue ∘ root) := by
  exact (nativeABoxSeed_realized_iff abox I (nodeValue ∘ root)).1
    ⟨nativeABoxSeed_realized_of_seeded abox state root I nodeValue hseeded hrealized,
      hsingletons, hnegative⟩

#print axioms nativeABoxSeed_realized_iff
#print axioms NativeABox.models_of_mapConcepts
#print axioms NativeABox.mapConcepts_models_of
#print axioms nativeABoxSeed_realized_of_seeded
#print axioms NativeABox.models_of_seeded
#print axioms models_negativeRoleAssertionClause_iff

end ContextCalculus.Hypertableau
