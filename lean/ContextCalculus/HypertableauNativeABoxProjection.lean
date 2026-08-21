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

#print axioms nativeABoxSeed_realized_iff
#print axioms models_negativeRoleAssertionClause_iff

end ContextCalculus.Hypertableau
