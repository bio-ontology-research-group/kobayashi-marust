import ContextCalculus.HypertableauSkolemProjection

/-!
# Domain consequences emitted beside projected existentials

The Rust adapter materializes a concept consequence for every domain on the
existential role or one of its super-roles.  These clauses are redundant, not
approximations.  This module proves that fact and connects the semantic role
conditions to their ordinary two-variable HT clauses.
-/

namespace ContextCalculus.Hypertableau

def RoleIncluded (I : Interp Domain Concept Role) (sub sup : Role) : Prop :=
  ∀ source target, I.role sub source target → I.role sup source target

def RoleDomain (I : Interp Domain Concept Role) (role : Role) (domain : Lit Concept) : Prop :=
  ∀ source target, I.role role source target → I.satLit domain source

def roleInclusionClause (sub sup : Role) (source target : Variable) :
    Clause Variable Concept Role := {
  body := [.role sub source target]
  head := [.role sup source target]
}

def roleDomainClause (role : Role) (domain : Lit Concept)
    (source target : Variable) : Clause Variable Concept Role := {
  body := [.role role source target]
  head := [.concept domain source]
}

def roleInclusionPathClauses (start : Role) (steps : List Role)
    (source target : Variable) : List (Clause Variable Concept Role) :=
  match steps with
  | [] => []
  | next :: rest =>
      roleInclusionClause start next source target ::
        roleInclusionPathClauses next rest source target

def roleInclusionPathTarget (start : Role) (steps : List Role) : Role :=
  match steps with
  | [] => start
  | next :: rest => roleInclusionPathTarget next rest

theorem roleIncluded_refl (I : Interp Domain Concept Role) (role : Role) :
    RoleIncluded I role role := by
  intro source target hedge
  exact hedge

theorem roleIncluded_trans (I : Interp Domain Concept Role) (left middle right : Role)
    (hleft : RoleIncluded I left middle) (hright : RoleIncluded I middle right) :
    RoleIncluded I left right := by
  intro source target hedge
  exact hright source target (hleft source target hedge)

theorem models_roleInclusionClause_iff [DecidableEq Variable]
    (I : Interp Domain Concept Role) (sub sup : Role) (source target : Variable)
    (hne : source ≠ target) :
    I.modelsClause (roleInclusionClause sub sup source target) ↔
      RoleIncluded I sub sup := by
  constructor
  · intro hmodels left right hedge
    let assignment : Variable → Domain := fun candidate =>
      if candidate = source then left else right
    have hsource : assignment source = left := by simp [assignment]
    have htarget : assignment target = right := by simp [assignment, Ne.symm hne]
    have hbody : ∀ atom ∈ (roleInclusionClause sub sup source target).body,
        I.satAtom assignment atom := by
      intro atom hatom
      simp only [roleInclusionClause, List.mem_singleton] at hatom
      subst atom
      simpa [Interp.satAtom, hsource, htarget] using hedge
    rcases hmodels assignment hbody with ⟨atom, hatom, hsat⟩
    simp only [roleInclusionClause, List.mem_singleton] at hatom
    subst atom
    simpa [Interp.satAtom, hsource, htarget] using hsat
  · intro hincluded assignment hbody
    have hedge := hbody (.role sub source target) (by simp [roleInclusionClause])
    exact ⟨.role sup source target, by simp [roleInclusionClause],
      hincluded (assignment source) (assignment target) hedge⟩

theorem models_roleDomainClause_iff [DecidableEq Variable]
    (I : Interp Domain Concept Role) (role : Role) (domain : Lit Concept)
    (source target : Variable) (hne : source ≠ target) :
    I.modelsClause (roleDomainClause role domain source target) ↔
      RoleDomain I role domain := by
  constructor
  · intro hmodels left right hedge
    let assignment : Variable → Domain := fun candidate =>
      if candidate = source then left else right
    have hsource : assignment source = left := by simp [assignment]
    have htarget : assignment target = right := by simp [assignment, Ne.symm hne]
    have hbody : ∀ atom ∈ (roleDomainClause role domain source target).body,
        I.satAtom assignment atom := by
      intro atom hatom
      simp only [roleDomainClause, List.mem_singleton] at hatom
      subst atom
      simpa [Interp.satAtom, hsource, htarget] using hedge
    rcases hmodels assignment hbody with ⟨atom, hatom, hsat⟩
    simp only [roleDomainClause, List.mem_singleton] at hatom
    subst atom
    simpa [Interp.satAtom, hsource] using hsat
  · intro hdomain assignment hbody
    have hedge := hbody (.role role source target) (by simp [roleDomainClause])
    exact ⟨.concept domain source, by simp [roleDomainClause],
      hdomain (assignment source) (assignment target) hedge⟩

theorem models_roleInclusionPathClauses_implies [DecidableEq Variable]
    (I : Interp Domain Concept Role) (start : Role) (steps : List Role)
    (source target : Variable) (hne : source ≠ target)
    (hmodels : I.models (roleInclusionPathClauses start steps source target)) :
    RoleIncluded I start (roleInclusionPathTarget start steps) := by
  induction steps generalizing start with
  | nil =>
      exact roleIncluded_refl I start
  | cons next rest ih =>
      have hfirst : I.modelsClause (roleInclusionClause start next source target) := by
        apply hmodels
        simp [roleInclusionPathClauses]
      have htail : I.models (roleInclusionPathClauses next rest source target) := by
        intro clause hclause
        apply hmodels clause
        simp only [roleInclusionPathClauses, List.mem_cons]
        exact Or.inr hclause
      have hstep : RoleIncluded I start next :=
        (models_roleInclusionClause_iff I start next source target hne).1 hfirst
      have hrest := ih next htail
      exact roleIncluded_trans I start next
        (roleInclusionPathTarget next rest) hstep hrest

def domainConsequenceClause
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (domain : Lit Concept) : Clause Variable Concept Role := {
  body
  head := [.concept domain source]
}

theorem domainConsequence_sound
    (I : Interp Domain Concept Role)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (role superRole : Role) (filler domain : Lit Concept)
    (hexist : I.modelsClause (existentialProjectionClause body source role filler))
    (hincluded : RoleIncluded I role superRole)
    (hdomain : RoleDomain I superRole domain) :
    I.modelsClause (domainConsequenceClause body source domain) := by
  intro assignment hbody
  rcases hexist assignment hbody with ⟨atom, hatom, hsat⟩
  simp only [existentialProjectionClause, List.mem_singleton] at hatom
  subst atom
  rcases hsat with ⟨witness, hedge, _hfiller⟩
  refine ⟨.concept domain source, by simp [domainConsequenceClause], ?_⟩
  exact hdomain (assignment source) witness
    (hincluded (assignment source) witness hedge)

structure DomainConsequenceSpec (Concept Role : Type*) where
  superRole : Role
  domain : Lit Concept

def domainConsequenceOntology
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (specs : List (DomainConsequenceSpec Concept Role)) :
    List (Clause Variable Concept Role) :=
  specs.map fun spec => domainConsequenceClause body source spec.domain

theorem domainConsequences_sound
    (I : Interp Domain Concept Role)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (role : Role) (filler : Lit Concept)
    (specs : List (DomainConsequenceSpec Concept Role))
    (hexist : I.modelsClause (existentialProjectionClause body source role filler))
    (hincluded : ∀ spec ∈ specs, RoleIncluded I role spec.superRole)
    (hdomains : ∀ spec ∈ specs, RoleDomain I spec.superRole spec.domain) :
    I.models (domainConsequenceOntology body source specs) := by
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨spec, hspec, rfl⟩
  exact domainConsequence_sound I body source role spec.superRole filler spec.domain
    hexist (hincluded spec hspec) (hdomains spec hspec)

theorem add_domainConsequences_iff
    (I : Interp Domain Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (role : Role) (filler : Lit Concept)
    (specs : List (DomainConsequenceSpec Concept Role))
    (hexist : I.modelsClause (existentialProjectionClause body source role filler))
    (hincluded : ∀ spec ∈ specs, RoleIncluded I role spec.superRole)
    (hdomains : ∀ spec ∈ specs, RoleDomain I spec.superRole spec.domain) :
    I.models (ontology ++ domainConsequenceOntology body source specs) ↔
      I.models ontology := by
  constructor
  · intro hmodels clause hclause
    exact hmodels clause (List.mem_append_left _ hclause)
  · intro hmodels clause hclause
    rcases List.mem_append.mp hclause with hclause | hclause
    · exact hmodels clause hclause
    · exact domainConsequences_sound I body source role filler specs hexist hincluded hdomains
        clause hclause

#print axioms models_roleInclusionClause_iff
#print axioms models_roleDomainClause_iff
#print axioms models_roleInclusionPathClauses_implies
#print axioms domainConsequence_sound
#print axioms domainConsequences_sound
#print axioms add_domainConsequences_iff

end ContextCalculus.Hypertableau
