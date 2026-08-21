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

/-- The production serializer computes role closure separately from the raw
completion graph.  When every serialized cover edge is also present in that
graph, a cover-body match is an ordinary saturated-state body match. -/
theorem FiniteRegularCertificate.coverHoldsAtom_to_holdsAtom
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcoverEdge : ∀ role source target,
      certificate.coverRelation role source target →
        certificate.state.edge role source target)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hholds : certificate.state.CoverHoldsAtom certificate.coverRelation
      assignment atom) : certificate.state.holdsAtom assignment atom := by
  cases atom with
  | concept => exact hholds
  | role role source target => exact hcoverEdge role _ _ hholds
  | exists_ => exact hholds
  | eq => exact hholds

/-- Concept and existential heads use identical truth tests in the finite
state and its role cover. -/
theorem FiniteRegularCertificate.holdsAtom_to_coverHoldsAtom_of_pathLiftable
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hliftable : PathLiftableHead atom)
    (hholds : certificate.state.holdsAtom assignment atom) :
    certificate.state.CoverHoldsAtom certificate.coverRelation assignment atom := by
  cases atom with
  | concept => exact hholds
  | role => contradiction
  | exists_ => exact hholds
  | eq => contradiction

/-- Ordinary finite saturation implies regular-cover saturation when the
producer's role cover contains no edge absent from the saturated graph. -/
theorem FiniteRegularCertificate.coverDischarges_of_discharges
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcoverEdge : ∀ role source target,
      certificate.coverRelation role source target →
        certificate.state.edge role source target)
    (clause : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hheads : ∀ atom ∈ clause.head, PathLiftableHead atom)
    (hdischarges : certificate.state.Discharges clause) :
    certificate.state.CoverDischarges certificate.coverRelation clause := by
  intro assignment hbody
  have hordinaryBody : ∀ atom ∈ clause.body,
      certificate.state.holdsAtom assignment atom := by
    intro atom hatom
    exact certificate.coverHoldsAtom_to_holdsAtom hcoverEdge assignment atom
      (hbody atom hatom)
  rcases hdischarges assignment hordinaryBody with ⟨atom, hatom, hholds⟩
  exact ⟨atom, hatom,
    certificate.holdsAtom_to_coverHoldsAtom_of_pathLiftable assignment atom
      (hheads atom hatom) hholds⟩

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
  certificate.state.RedirectWitnessComplete certificate.redirect ∧
  certificate.CoverClosed ∧
  (∀ clause ∈ certificate.residual,
    certificate.state.CoverDischarges certificate.coverRelation clause)

/-- Producer-facing refinement theorem.  Rust's exhaustive search already
establishes ordinary residual saturation.  Its serializer needs only preserve
that finite state, compute a closed role cover contained in the serialized
edge set, and preserve blocker witnesses. These operational premises construct
the exact `Valid` invariant accepted by the independent checker. -/
theorem FiniteRegularCertificate.valid_of_producer_invariants
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hauthorized : ∀ rule ∈ certificate.roleClauses,
      rule.Authorized certificate.rules)
    (hguarded : ∀ clause ∈ certificate.residual, clause.GuardedBody)
    (hheads : ∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hclash : certificate.state.ClashFree)
    (hwitness : certificate.state.RedirectWitnessComplete certificate.redirect)
    (hcoverClosed : certificate.CoverClosed)
    (hcoverEdge : ∀ role source target,
      certificate.coverRelation role source target →
        certificate.state.edge role source target)
    (hsaturated : certificate.state.SaturatedFor certificate.residual) :
    certificate.Valid := by
  refine ⟨hauthorized, hguarded, hheads, hclash, hwitness, hcoverClosed, ?_⟩
  intro clause hclause
  exact certificate.coverDischarges_of_discharges hcoverEdge clause
    (hheads clause hclause) (hsaturated clause hclause)

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

def FiniteRegularCertificate.syntacticallySimpleB
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (role : Fin roleCount) : Bool :=
  certificate.subRoles.all (fun rule => decide (rule.2 ≠ role)) &&
  certificate.inverseRoles.all (fun rule => decide (rule.2 ≠ role)) &&
  certificate.chains.all (fun rule => decide (rule.2.2 ≠ role)) &&
  decide (role ∉ certificate.reflexiveRoles)

theorem FiniteRegularCertificate.syntacticallySimpleB_sound
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (role : Fin roleCount)
    (hcheck : certificate.syntacticallySimpleB role = true) :
    certificate.rules.SyntacticallySimple role := by
  simp only [FiniteRegularCertificate.syntacticallySimpleB, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hsub, hinverse⟩, hchain⟩, hrefl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro premise hrule
    exact hsub (premise, role) hrule rfl
  · intro premise hrule
    exact hinverse (premise, role) hrule rfl
  · intro first second hrule
    exact hchain (first, second, role) hrule rfl
  · exact hrefl

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
      decide ((obligation.1, certificate.redirect obligation.2.2, witness) ∈
        certificate.edges) &&
      decide ((witness, obligation.2.1) ∈ certificate.labels)) &&
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

/-- The executable endpoint-cover check is complete as well as sound.  This
direction matters for total decision search: a producer that supplies the
mathematical `CoverClosed` invariant cannot be rejected merely because the
Boolean checker omitted one of its cases. -/
theorem FiniteRegularCertificate.coverClosedB_complete
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hclosed : certificate.CoverClosed) : certificate.coverClosedB = true := by
  simp only [FiniteRegularCertificate.coverClosedB, Bool.and_eq_true,
    List.all_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro source hsource edge hedge
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hredirect : edge.2.1 = certificate.redirect source
    · right
      rcases edge with ⟨role, edgeSource, target⟩
      simp only at hredirect ⊢
      subst edgeSource
      exact hclosed.1 role source target hedge
    · left
      simp [hredirect]
  · intro rule hrule edge hedge
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hpremise : edge.1 = rule.1
    · right
      rcases rule with ⟨premise, conclusion⟩
      rcases edge with ⟨role, source, target⟩
      simp only at hpremise ⊢
      subst role
      exact hclosed.2.1 premise conclusion hrule source target hedge
    · left
      simp [hpremise]
  · intro rule hrule edge hedge
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hpremise : edge.1 = rule.1
    · right
      rcases rule with ⟨premise, conclusion⟩
      rcases edge with ⟨role, source, target⟩
      simp only at hpremise ⊢
      subst role
      exact hclosed.2.2.1 premise conclusion hrule source target hedge
    · left
      simp [hpremise]
  · intro rule hrule left hleft right hright
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hpremises : left.1 = rule.1 ∧ right.1 = rule.2.1 ∧
        left.2.2 = right.2.1
    · right
      have hleftCover : certificate.coverRelation rule.1
          left.2.1 left.2.2 := by
        change (rule.1, left.2.1, left.2.2) ∈ certificate.cover
        rw [← hpremises.1]
        simpa only [Prod.eta] using hleft
      have hrightCover : certificate.coverRelation rule.2.1
          left.2.2 right.2.2 := by
        change (rule.2.1, left.2.2, right.2.2) ∈ certificate.cover
        rw [← hpremises.2.1, hpremises.2.2]
        simpa only [Prod.eta] using hright
      exact hclosed.2.2.2.1 rule.1 rule.2.1 rule.2.2 hrule
        left.2.1 left.2.2 right.2.2 hleftCover hrightCover
    · left
      simp [hpremises]
  · intro role hrole source hsource
    simpa [FiniteRegularCertificate.coverRelation] using
      hclosed.2.2.2.2 role hrole source

theorem FiniteRegularCertificate.check_sound
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) : certificate.Valid := by
  simp only [FiniteRegularCertificate.check, Bool.and_eq_true,
    List.all_eq_true] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨hauthorized, hguarded⟩, hheads⟩, hclash⟩,
      hwitness⟩, hcover⟩, hdischarges⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- The regular-model checker accepts every certificate satisfying its stated
finite semantic invariant. Together with `check_sound`, this makes rejection
equivalent to a genuine violation of that invariant rather than an artifact of
an incomplete executable scan. -/
theorem FiniteRegularCertificate.check_complete
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.Valid) : certificate.check = true := by
  simp only [FiniteRegularCertificate.check, Bool.and_eq_true,
    List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro rule hrule
    exact (certificate.authorizedB_eq_true rule).mpr (hvalid.1 rule hrule)
  · intro clause hclause atom hatom
    have hbody := hvalid.2.1 clause hclause atom hatom
    cases atom with
    | concept lit node =>
        rcases lit with ⟨concept, neg⟩
        cases neg <;> simp_all [atomGuardedB, BodyAtom]
    | role => simp [atomGuardedB]
    | exists_ => contradiction
    | eq => simp [atomGuardedB]
  · intro clause hclause atom hatom
    exact (pathLiftableHeadB_eq_true atom).mpr
      (hvalid.2.2.1 clause hclause atom hatom)
  · rintro ⟨node, literal⟩ hlabel
    simp only [decide_eq_true_eq]
    rcases literal with ⟨concept, neg⟩
    cases neg with
    | false =>
        intro hnegative
        exact hvalid.2.2.2.1 node concept ⟨hlabel, hnegative⟩
    | true =>
        intro hpositive
        exact hvalid.2.2.2.1 node concept ⟨hpositive, hlabel⟩
  · intro obligation hobligation
    rcases hvalid.2.2.2.2.1 obligation.2.2 obligation.1 obligation.2.1
        hobligation with ⟨witness, hedge, hlabel⟩
    rw [List.any_eq_true]
    refine ⟨witness, List.mem_finRange witness, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    simpa [FiniteRegularCertificate.state] using And.intro hedge hlabel
  · exact certificate.coverClosedB_complete hvalid.2.2.2.2.2.1
  · intro clause hclause assignment _
    by_cases hbody : ∀ atom ∈ clause.body,
        certificate.state.CoverHoldsAtom certificate.coverRelation assignment atom
    · rcases hvalid.2.2.2.2.2.2 clause hclause assignment hbody with
        ⟨atom, hatom, hholds⟩
      have hbodyB : clause.body.all
          (certificate.coverHoldsAtomB assignment) = true := by
        rw [List.all_eq_true]
        intro bodyAtom hbodyAtom
        exact (certificate.coverHoldsAtomB_eq_true assignment bodyAtom).mpr
          (hbody bodyAtom hbodyAtom)
      have hheadB : clause.head.any
          (certificate.coverHoldsAtomB assignment) = true := by
        rw [List.any_eq_true]
        exact ⟨atom, hatom,
          (certificate.coverHoldsAtomB_eq_true assignment atom).mpr hholds⟩
      simp [hbodyB, hheadB]
    · have hbodyB : clause.body.all
          (certificate.coverHoldsAtomB assignment) = false := by
        generalize hall : clause.body.all
          (certificate.coverHoldsAtomB assignment) = value
        cases value with
        | false => rfl
        | true =>
            exfalso
            apply hbody
            intro atom hatom
            exact (certificate.coverHoldsAtomB_eq_true assignment atom).mp
              ((List.all_eq_true.mp hall) atom hatom)
      simp [hbodyB]

/-- End-to-end producer boundary: the finite invariants naturally available
from exhaustive search and serialization are sufficient for executable checker
acceptance. -/
theorem FiniteRegularCertificate.check_of_producer_invariants
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (hauthorized : ∀ rule ∈ certificate.roleClauses,
      rule.Authorized certificate.rules)
    (hguarded : ∀ clause ∈ certificate.residual, clause.GuardedBody)
    (hheads : ∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hclash : certificate.state.ClashFree)
    (hwitness : certificate.state.RedirectWitnessComplete certificate.redirect)
    (hcoverClosed : certificate.CoverClosed)
    (hcoverEdge : ∀ role source target,
      certificate.coverRelation role source target →
        certificate.state.edge role source target)
    (hsaturated : certificate.state.SaturatedFor certificate.residual) :
    certificate.check = true :=
  certificate.check_complete (certificate.valid_of_producer_invariants
    hauthorized hguarded hheads hclash hwitness hcoverClosed
    hcoverEdge hsaturated)

theorem FiniteRegularCertificate.check_eq_true_iff_valid
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.check = true ↔ certificate.Valid :=
  ⟨certificate.check_sound, certificate.check_complete⟩

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
  apply regularUnravelling_models_partition_of_cover_redirect certificate.state
    certificate.redirect (fun _ _ _ _ => True) 0 certificate.rules
    certificate.coverRelation certificate.roleClauses certificate.residual
  · exact hvalid.1
  · exact hvalid.2.1
  · exact hvalid.2.2.1
  · exact hvalid.2.2.2.1
  · exact hvalid.2.2.2.2.1
  · intro source role target edge
    trivial
  · exact certificate.coverClosed_covers hvalid.2.2.2.2.2.1
  · exact hvalid.2.2.2.2.2.2

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
#print axioms FiniteRegularCertificate.coverHoldsAtom_to_holdsAtom
#print axioms FiniteRegularCertificate.coverDischarges_of_discharges
#print axioms FiniteRegularCertificate.valid_of_producer_invariants
#print axioms FiniteRegularCertificate.coverClosedB_sound
#print axioms FiniteRegularCertificate.coverClosedB_complete
#print axioms FiniteRegularCertificate.syntacticallySimpleB_sound
#print axioms FiniteRegularCertificate.check_sound
#print axioms FiniteRegularCertificate.check_complete
#print axioms FiniteRegularCertificate.check_of_producer_invariants
#print axioms FiniteRegularCertificate.check_eq_true_iff_valid
#print axioms FiniteRegularCertificate.models
#print axioms FiniteRegularCertificate.check_models

end ContextCalculus.Hypertableau
