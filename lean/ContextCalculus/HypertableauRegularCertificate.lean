import ContextCalculus.HypertableauUnravelling
import ContextCalculus.HypertableauCertificate

/-!
# Finite regular-unravelling certificates

This module turns the finite semantic boundary from
`HypertableauUnravelling` into certificate data. The role cover is an untrusted
list. Local closure checks prove that it contains every direct, subrole,
inverse, chain, transitive, and reflexive endpoint edge. Residual clauses are
then discharged over finite endpoint assignments.
-/

namespace ContextCalculus.Hypertableau

structure FiniteRegularCertificate
    (nodeCount conceptCount roleCount variableCount : Nat) where
  labels : List (Fin nodeCount × Lit (Fin conceptCount))
  edges : List (Fin roleCount × Fin nodeCount × Fin nodeCount)
  obligations : List (Fin roleCount × Lit (Fin conceptCount) × Fin nodeCount)
  redirect : Fin nodeCount → Fin nodeCount
  cover : List (Fin roleCount × Fin nodeCount × Fin nodeCount)
  subRoles : List (Fin roleCount × Fin roleCount)
  inverseRoles : List (Fin roleCount × Fin roleCount)
  chains : List (Fin roleCount × Fin roleCount × Fin roleCount)
  reflexiveRoles : List (Fin roleCount)
  roleClauses : List (NormalizedRoleClause (Fin variableCount) (Fin roleCount))
  residual : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))

def FiniteRegularCertificate.state
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    State (Fin nodeCount) (Fin conceptCount) (Fin roleCount) where
  label node lit := (node, lit) ∈ certificate.labels
  edge role source target := (role, source, target) ∈ certificate.edges
  obligation role filler node :=
    (role, filler, node) ∈ certificate.obligations

def FiniteRegularCertificate.rules
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    UnravellingRoleRules (Fin roleCount) where
  subRole premise conclusion := (premise, conclusion) ∈ certificate.subRoles
  inverseRole premise conclusion :=
    (premise, conclusion) ∈ certificate.inverseRoles
  chain first second conclusion :=
    (first, second, conclusion) ∈ certificate.chains
  reflexive role := role ∈ certificate.reflexiveRoles

def FiniteRegularCertificate.coverRelation
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    Fin roleCount → Fin nodeCount → Fin nodeCount → Prop :=
  fun role source target => (role, source, target) ∈ certificate.cover

/-- Local finite closure conditions sufficient to cover the inductively
generated endpoint relation. -/
def FiniteRegularCertificate.CoverClosed
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) : Prop :=
  (∀ role source target,
    certificate.state.edge role (certificate.redirect source) target →
      certificate.coverRelation role source target) ∧
  (∀ premise conclusion, certificate.rules.subRole premise conclusion →
    ∀ source target, certificate.coverRelation premise source target →
      certificate.coverRelation conclusion source target) ∧
  (∀ premise conclusion, certificate.rules.inverseRole premise conclusion →
    ∀ source target, certificate.coverRelation premise source target →
      certificate.coverRelation conclusion target source) ∧
  (∀ first second conclusion,
    certificate.rules.chain first second conclusion →
    ∀ source middle target,
      certificate.coverRelation first source middle →
      certificate.coverRelation second middle target →
      certificate.coverRelation conclusion source target) ∧
  (∀ role, certificate.rules.reflexive role →
    ∀ source, certificate.coverRelation role source source)

theorem FiniteRegularCertificate.coverClosed_covers
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hclosed : certificate.CoverClosed) :
    EndpointRoleCovered certificate.state certificate.redirect
      certificate.rules certificate.coverRelation := by
  intro role source target edge
  induction edge with
  | direct edge => exact hclosed.1 _ _ _ edge
  | sub rule edge ih => exact hclosed.2.1 _ _ rule _ _ ih
  | inverse rule edge ih => exact hclosed.2.2.1 _ _ rule _ _ ih
  | chain rule left right ihLeft ihRight =>
      exact hclosed.2.2.2.1 _ _ _ rule _ _ _ ihLeft ihRight
  | refl rule => exact hclosed.2.2.2.2 _ rule _

def FiniteRegularCertificate.Valid
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) : Prop :=
  (∀ rule ∈ certificate.roleClauses,
    rule.Authorized certificate.rules) ∧
  (∀ clause ∈ certificate.residual, clause.GuardedBody) ∧
  (∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
    PathLiftableHead atom) ∧
  certificate.state.ClashFree ∧
  certificate.state.WitnessComplete ∧
  (∀ node role filler, certificate.state.obligation role filler node →
    certificate.state.obligation role filler (certificate.redirect node)) ∧
  certificate.CoverClosed ∧
  (∀ clause ∈ certificate.residual,
    certificate.state.CoverDischarges certificate.coverRelation clause)

def FiniteRegularCertificate.authorizedB
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    NormalizedRoleClause (Fin variableCount) (Fin roleCount) → Bool
  | .subRole premise conclusion .. =>
      decide ((premise, conclusion) ∈ certificate.subRoles)
  | .inverseRole premise conclusion .. =>
      decide ((premise, conclusion) ∈ certificate.inverseRoles)
  | .chain first second conclusion .. =>
      decide ((first, second, conclusion) ∈ certificate.chains)
  | .reflexive role .. => decide (role ∈ certificate.reflexiveRoles)

def pathLiftableHeadB : Atom V C R → Bool
  | .concept .. => true
  | .exists_ .. => true
  | .role .. => false
  | .eq .. => false

def FiniteRegularCertificate.coverHoldsAtomB
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount) :
    Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount) → Bool
  | .concept lit node => decide ((assignment node, lit) ∈ certificate.labels)
  | .role role source target =>
      decide ((role, assignment source, assignment target) ∈ certificate.cover)
  | .exists_ role filler node =>
      decide ((role, filler, assignment node) ∈ certificate.obligations)
  | .eq left right => decide (assignment left = assignment right)

def FiniteRegularCertificate.coverClosedB
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  (List.finRange nodeCount).all (fun source =>
    certificate.edges.all (fun edge =>
      !(decide (edge.2.1 = certificate.redirect source)) ||
        decide ((edge.1, source, edge.2.2) ∈ certificate.cover))) &&
  certificate.subRoles.all (fun rule =>
    certificate.cover.all (fun edge =>
      !(decide (edge.1 = rule.1)) ||
        decide ((rule.2, edge.2.1, edge.2.2) ∈ certificate.cover))) &&
  certificate.inverseRoles.all (fun rule =>
    certificate.cover.all (fun edge =>
      !(decide (edge.1 = rule.1)) ||
        decide ((rule.2, edge.2.2, edge.2.1) ∈ certificate.cover))) &&
  certificate.chains.all (fun rule =>
    certificate.cover.all (fun left =>
      certificate.cover.all (fun right =>
        !(decide (left.1 = rule.1 ∧ right.1 = rule.2.1 ∧
          left.2.2 = right.2.1)) ||
          decide ((rule.2.2, left.2.1, right.2.2) ∈ certificate.cover)))) &&
  certificate.reflexiveRoles.all (fun role =>
    (List.finRange nodeCount).all (fun source =>
      decide ((role, source, source) ∈ certificate.cover)))

/-- Fully executable decision procedure. Every quantifier is represented by a
finite list traversal, including variable assignments. -/
def FiniteRegularCertificate.check
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.roleClauses.all certificate.authorizedB &&
  certificate.residual.all (fun clause => clause.body.all atomGuardedB) &&
  certificate.residual.all (fun clause => clause.head.all pathLiftableHeadB) &&
  certificate.labels.all (fun entry =>
    decide ((entry.1, entry.2.complement) ∉ certificate.labels)) &&
  certificate.obligations.all (fun obligation =>
    (List.finRange nodeCount).any fun witness =>
      decide ((obligation.1, obligation.2.2, witness) ∈ certificate.edges) &&
      decide ((witness, obligation.2.1) ∈ certificate.labels)) &&
  certificate.obligations.all (fun obligation =>
    decide ((obligation.1, obligation.2.1,
      certificate.redirect obligation.2.2) ∈ certificate.obligations)) &&
  certificate.coverClosedB &&
  certificate.residual.all (fun clause =>
    (allAssignments nodeCount variableCount).all fun assignment =>
      !(clause.body.all (certificate.coverHoldsAtomB assignment)) ||
        clause.head.any (certificate.coverHoldsAtomB assignment))

theorem FiniteRegularCertificate.authorizedB_eq_true
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (rule : NormalizedRoleClause (Fin variableCount) (Fin roleCount)) :
    certificate.authorizedB rule = true ↔ rule.Authorized certificate.rules := by
  cases rule <;> simp [FiniteRegularCertificate.authorizedB,
    NormalizedRoleClause.Authorized, FiniteRegularCertificate.rules]

theorem pathLiftableHeadB_eq_true (atom : Atom V C R) :
    pathLiftableHeadB atom = true ↔ PathLiftableHead atom := by
  cases atom <;> simp [pathLiftableHeadB, PathLiftableHead]

theorem FiniteRegularCertificate.coverHoldsAtomB_eq_true
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    certificate.coverHoldsAtomB assignment atom = true ↔
      certificate.state.CoverHoldsAtom certificate.coverRelation
        assignment atom := by
  cases atom <;> simp [FiniteRegularCertificate.coverHoldsAtomB,
    FiniteRegularCertificate.state, FiniteRegularCertificate.coverRelation,
    State.CoverHoldsAtom]

theorem FiniteRegularCertificate.coverClosedB_sound
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.coverClosedB = true) : certificate.CoverClosed := by
  simp only [FiniteRegularCertificate.coverClosedB, Bool.and_eq_true,
    List.all_eq_true] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hdirect, hsub⟩, hinverse⟩, hchain⟩, hrefl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro role source target hedge
    have h := hdirect source (by simp) (role, certificate.redirect source, target)
      hedge
    simpa [FiniteRegularCertificate.coverRelation] using h
  · intro premise conclusion hrule source target hedge
    have h := hsub (premise, conclusion) hrule (premise, source, target) hedge
    simpa [FiniteRegularCertificate.coverRelation] using h
  · intro premise conclusion hrule source target hedge
    have h := hinverse (premise, conclusion) hrule (premise, source, target) hedge
    simpa [FiniteRegularCertificate.coverRelation] using h
  · intro first second conclusion hrule source middle target hleft hright
    have h := hchain (first, second, conclusion) hrule
      (first, source, middle) hleft (second, middle, target) hright
    simpa [FiniteRegularCertificate.coverRelation] using h
  · intro role hrule source
    simpa [FiniteRegularCertificate.coverRelation] using
      hrefl role hrule source (by simp)

theorem FiniteRegularCertificate.check_sound
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) : certificate.Valid := by
  simp only [FiniteRegularCertificate.check, Bool.and_eq_true,
    List.all_eq_true] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨⟨hauthorized, hguarded⟩, hheads⟩, hclash⟩,
      hwitness⟩, hredirect⟩, hcover⟩, hdischarges⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rule hrule
    exact (certificate.authorizedB_eq_true rule).mp
      (hauthorized rule hrule)
  · intro clause hclause atom hatom
    have h := hguarded clause hclause atom hatom
    cases atom with
    | concept lit node =>
        rcases lit with ⟨concept, neg⟩
        cases neg <;> simp [atomGuardedB, BodyAtom] at h ⊢
    | role => trivial
    | exists_ => simp [atomGuardedB] at h
    | eq => trivial
  · intro clause hclause atom hatom
    exact (pathLiftableHeadB_eq_true atom).mp
      (hheads clause hclause atom hatom)
  · intro node concept hboth
    have hnot := hclash (node, Lit.pos concept) hboth.1
    simp only [Lit.complement, Lit.pos, Bool.not_false,
      decide_eq_true_eq] at hnot
    exact hnot hboth.2
  · intro node role filler hobligation
    have h := hwitness (role, filler, node) hobligation
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨witness, _, hedge, hlabel⟩
    exact ⟨witness, hedge, hlabel⟩
  · intro node role filler hobligation
    have h := hredirect (role, filler, node) hobligation
    simpa [FiniteRegularCertificate.state] using h
  · exact certificate.coverClosedB_sound hcover
  · intro clause hclause assignment hbody
    have h := hdischarges clause hclause assignment
      (mem_allAssignments nodeCount variableCount assignment)
    have hbodyB :
        clause.body.all (certificate.coverHoldsAtomB assignment) = true := by
      simp only [List.all_eq_true]
      intro atom hatom
      exact (certificate.coverHoldsAtomB_eq_true assignment atom).mpr
        (hbody atom hatom)
    have hheadB :
        clause.head.any (certificate.coverHoldsAtomB assignment) = true := by
      simpa [hbodyB] using h
    rw [List.any_eq_true] at hheadB
    rcases hheadB with ⟨atom, hatom, hholds⟩
    exact ⟨atom, hatom,
      (certificate.coverHoldsAtomB_eq_true assignment atom).mp hholds⟩

/-- The regular certificate's exact decoded ontology. -/
def FiniteRegularCertificate.ontology
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :=
  certificate.roleClauses.map
      (NormalizedRoleClause.toClause (Concept := Fin conceptCount)) ++
    certificate.residual

theorem FiniteRegularCertificate.models
    [NeZero nodeCount]
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.Valid) :
    (certificate.state.regularUnravelling certificate.redirect
      (fun _ _ _ _ => True) 0 certificate.rules).models
      certificate.ontology := by
  apply regularUnravelling_models_partition_of_cover certificate.state
    certificate.redirect (fun _ _ _ _ => True) 0 certificate.rules
    certificate.coverRelation certificate.roleClauses certificate.residual
  · exact hvalid.1
  · exact hvalid.2.1
  · exact hvalid.2.2.1
  · exact hvalid.2.2.2.1
  · exact hvalid.2.2.2.2.1
  · exact hvalid.2.2.2.2.2.1
  · intro source role target edge
    trivial
  · exact certificate.coverClosed_covers hvalid.2.2.2.2.2.2.1
  · exact hvalid.2.2.2.2.2.2.2

theorem FiniteRegularCertificate.check_models
    [NeZero nodeCount]
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    (certificate.state.regularUnravelling certificate.redirect
      (fun _ _ _ _ => True) 0 certificate.rules).models
      certificate.ontology :=
  certificate.models (certificate.check_sound hcheck)

private def emptyRegularCertificate : FiniteRegularCertificate 1 1 1 1 where
  labels := []
  edges := []
  obligations := []
  redirect := id
  cover := []
  subRoles := []
  inverseRoles := []
  chains := []
  reflexiveRoles := []
  roleClauses := []
  residual := []

private def missingDirectCover : FiniteRegularCertificate 1 1 1 1 where
  labels := []
  edges := [(0, 0, 0)]
  obligations := []
  redirect := id
  cover := []
  subRoles := []
  inverseRoles := []
  chains := []
  reflexiveRoles := []
  roleClauses := []
  residual := []

example : emptyRegularCertificate.check = true := by native_decide
example : missingDirectCover.check = false := by native_decide

#print axioms FiniteRegularCertificate.coverClosed_covers
#print axioms FiniteRegularCertificate.coverClosedB_sound
#print axioms FiniteRegularCertificate.check_sound
#print axioms FiniteRegularCertificate.models
#print axioms FiniteRegularCertificate.check_models

end ContextCalculus.Hypertableau
