import ContextCalculus.HypertableauRegularCertificate

/-!
# Finite derivations of regular endpoint-role edges

Cover saturation may expose a role edge absent from the raw completion graph.
This datatype records why that edge belongs to the regular endpoint closure:
it is either redirected raw data, or follows through one normalized RBox rule.
The executable checker is exact for the represented derivation and produces
an `EndpointRole` proof used by subsequent fold-refinement certificates.
-/

namespace ContextCalculus.Hypertableau

/-- Closure properties of the raw completion graph for the normalized RBox.
When these hold, an endpoint edge can differ from a raw edge only because its
direct leaves use a non-identity blocker redirect. -/
def State.RoleClosed
    (state : State Node Concept Role) (rules : UnravellingRoleRules Role) : Prop :=
  (∀ premise conclusion, rules.subRole premise conclusion →
    ∀ source target, state.edge premise source target →
      state.edge conclusion source target) ∧
  (∀ premise conclusion, rules.inverseRole premise conclusion →
    ∀ source target, state.edge premise source target →
      state.edge conclusion target source) ∧
  (∀ first second conclusion, rules.chain first second conclusion →
    ∀ source middle target,
      state.edge first source middle → state.edge second middle target →
      state.edge conclusion source target) ∧
  (∀ role, rules.reflexive role → ∀ source, state.edge role source source)

/-- Every abstract RBox relation stored in `rules` has a normalized clause
whose variables can be assigned independently. Aliased role atoms do not
represent global role inclusions and are deliberately excluded. -/
def NormalizedRoleClauses.Represent
    (rules : UnravellingRoleRules Role)
    (clauses : List (NormalizedRoleClause Variable Role)) : Prop :=
  (∀ premise conclusion, rules.subRole premise conclusion →
    ∃ source target, source ≠ target ∧
      .subRole premise conclusion source target ∈ clauses) ∧
  (∀ premise conclusion, rules.inverseRole premise conclusion →
    ∃ source target, source ≠ target ∧
      .inverseRole premise conclusion source target ∈ clauses) ∧
  (∀ first second conclusion, rules.chain first second conclusion →
    ∃ source middle target,
      source ≠ middle ∧ source ≠ target ∧ middle ≠ target ∧
      .chain first second conclusion source middle target ∈ clauses) ∧
  (∀ role, rules.reflexive role →
    ∃ source, .reflexive role source ∈ clauses)

/-- Saturation of independently quantified normalized RBox clauses establishes
the raw role-closure invariant required by checked cover rejection. -/
theorem State.roleClosed_of_saturated_normalized
    [DecidableEq Variable]
    (state : State Node Concept Role)
    (rules : UnravellingRoleRules Role)
    (clauses : List (NormalizedRoleClause Variable Role))
    (hrepresents : NormalizedRoleClauses.Represent rules clauses)
    (hsaturated : state.SaturatedFor
      (clauses.map (NormalizedRoleClause.toClause (Concept := Concept)))) :
    state.RoleClosed rules := by
  classical
  constructor
  · intro premise conclusion hrule sourceNode targetNode hedge
    obtain ⟨source, target, hne, hclause⟩ :=
      hrepresents.1 premise conclusion hrule
    let assignment := Function.update (fun _ => sourceNode) target targetNode
    have hsource : assignment source = sourceNode := by
      simp [assignment, hne]
    have htarget : assignment target = targetNode := by simp [assignment]
    have hdischarges := hsaturated
      ((NormalizedRoleClause.subRole premise conclusion source target).toClause
        (Concept := Concept))
      (List.mem_map.mpr ⟨_, hclause, rfl⟩)
    rcases hdischarges assignment (by
      intro atom hatom
      simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
      subst atom
      simpa [State.holdsAtom, hsource, htarget] using hedge) with
      ⟨atom, hatom, hhead⟩
    simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
    subst atom
    simpa [State.holdsAtom, hsource, htarget] using hhead
  constructor
  · intro premise conclusion hrule sourceNode targetNode hedge
    obtain ⟨source, target, hne, hclause⟩ :=
      hrepresents.2.1 premise conclusion hrule
    let assignment := Function.update (fun _ => sourceNode) target targetNode
    have hsource : assignment source = sourceNode := by
      simp [assignment, hne]
    have htarget : assignment target = targetNode := by simp [assignment]
    have hdischarges := hsaturated
      ((NormalizedRoleClause.inverseRole premise conclusion source target).toClause
        (Concept := Concept))
      (List.mem_map.mpr ⟨_, hclause, rfl⟩)
    rcases hdischarges assignment (by
      intro atom hatom
      simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
      subst atom
      simpa [State.holdsAtom, hsource, htarget] using hedge) with
      ⟨atom, hatom, hhead⟩
    simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
    subst atom
    simpa [State.holdsAtom, hsource, htarget] using hhead
  constructor
  · intro first second conclusion hrule sourceNode middleNode targetNode
      hleft hright
    obtain ⟨source, middle, target, hsourceMiddle, hsourceTarget,
      hmiddleTarget, hclause⟩ :=
      hrepresents.2.2.1 first second conclusion hrule
    let assignment := Function.update
      (Function.update (fun _ => sourceNode) middle middleNode)
      target targetNode
    have hsource : assignment source = sourceNode := by
      simp [assignment, hsourceMiddle, hsourceTarget]
    have hmiddle : assignment middle = middleNode := by
      simp [assignment, hmiddleTarget]
    have htarget : assignment target = targetNode := by simp [assignment]
    have hdischarges := hsaturated
      ((NormalizedRoleClause.chain first second conclusion source middle target).toClause
        (Concept := Concept))
      (List.mem_map.mpr ⟨_, hclause, rfl⟩)
    rcases hdischarges assignment (by
      intro atom hatom
      simp only [NormalizedRoleClause.toClause, List.mem_cons,
        List.not_mem_nil, or_false] at hatom
      rcases hatom with rfl | rfl
      · simpa [State.holdsAtom, hsource, hmiddle] using hleft
      · simpa [State.holdsAtom, hmiddle, htarget] using hright) with
      ⟨atom, hatom, hhead⟩
    simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
    subst atom
    simpa [State.holdsAtom, hsource, htarget] using hhead
  · intro role hrule sourceNode
    obtain ⟨source, hclause⟩ := hrepresents.2.2.2 role hrule
    let assignment := fun _ : Variable => sourceNode
    have hdischarges := hsaturated
      ((NormalizedRoleClause.reflexive role source).toClause (Concept := Concept))
      (List.mem_map.mpr ⟨_, hclause, rfl⟩)
    rcases hdischarges assignment (by
      intro atom hatom
      simp [NormalizedRoleClause.toClause] at hatom) with
      ⟨atom, hatom, hhead⟩
    simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
    subst atom
    simpa [State.holdsAtom, assignment] using hhead

inductive FiniteEndpointRoleEvidence (Node Role : Type) where
  | direct (role : Role) (source target : Node)
  | sub (premise conclusion : Role) (source target : Node)
      (child : FiniteEndpointRoleEvidence Node Role)
  | inverse (premise conclusion : Role) (source target : Node)
      (child : FiniteEndpointRoleEvidence Node Role)
  | chain (first second conclusion : Role) (source middle target : Node)
      (left right : FiniteEndpointRoleEvidence Node Role)
  | refl (role : Role) (source : Node)
deriving Repr

def FiniteEndpointRoleEvidence.role :
    FiniteEndpointRoleEvidence Node Role → Role
  | .direct role .. => role
  | .sub _ conclusion .. => conclusion
  | .inverse _ conclusion .. => conclusion
  | .chain _ _ conclusion .. => conclusion
  | .refl role .. => role

def FiniteEndpointRoleEvidence.source :
    FiniteEndpointRoleEvidence Node Role → Node
  | .direct _ source .. => source
  | .sub _ _ source .. => source
  | .inverse _ _ source .. => source
  | .chain _ _ _ source .. => source
  | .refl _ source => source

def FiniteEndpointRoleEvidence.target :
    FiniteEndpointRoleEvidence Node Role → Node
  | .direct _ _ target => target
  | .sub _ _ _ target .. => target
  | .inverse _ _ _ target .. => target
  | .chain _ _ _ _ _ target .. => target
  | .refl _ source => source

def FiniteEndpointRoleEvidence.Valid
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    FiniteEndpointRoleEvidence (Fin nodeCount) (Fin roleCount) → Prop
  | .direct role source target =>
      certificate.state.edge role (certificate.redirect source) target
  | .sub premise conclusion source target child =>
      certificate.rules.subRole premise conclusion ∧
      child.role = premise ∧ child.source = source ∧ child.target = target ∧
      child.Valid certificate
  | .inverse premise conclusion source target child =>
      certificate.rules.inverseRole premise conclusion ∧
      child.role = premise ∧ child.source = target ∧ child.target = source ∧
      child.Valid certificate
  | .chain first second conclusion source middle target left right =>
      certificate.rules.chain first second conclusion ∧
      left.role = first ∧ left.source = source ∧ left.target = middle ∧
      right.role = second ∧ right.source = middle ∧ right.target = target ∧
      left.Valid certificate ∧ right.Valid certificate
  | .refl role _ => certificate.rules.reflexive role

def FiniteEndpointRoleEvidence.check
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount) :
    FiniteEndpointRoleEvidence (Fin nodeCount) (Fin roleCount) → Bool
  | .direct role source target =>
      decide ((role, certificate.redirect source, target) ∈ certificate.edges)
  | .sub premise conclusion source target child =>
      decide ((premise, conclusion) ∈ certificate.subRoles) &&
      decide (child.role = premise) && decide (child.source = source) &&
      decide (child.target = target) && child.check certificate
  | .inverse premise conclusion source target child =>
      decide ((premise, conclusion) ∈ certificate.inverseRoles) &&
      decide (child.role = premise) && decide (child.source = target) &&
      decide (child.target = source) && child.check certificate
  | .chain first second conclusion source middle target left right =>
      decide ((first, second, conclusion) ∈ certificate.chains) &&
      decide (left.role = first) && decide (left.source = source) &&
      decide (left.target = middle) && decide (right.role = second) &&
      decide (right.source = middle) && decide (right.target = target) &&
      left.check certificate && right.check certificate
  | .refl role _ => decide (role ∈ certificate.reflexiveRoles)

theorem FiniteEndpointRoleEvidence.check_eq_true_iff
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (evidence : FiniteEndpointRoleEvidence (Fin nodeCount) (Fin roleCount)) :
    evidence.check certificate = true ↔ evidence.Valid certificate := by
  induction evidence with
  | direct => simp [FiniteEndpointRoleEvidence.check,
      FiniteEndpointRoleEvidence.Valid, FiniteRegularCertificate.state]
  | sub premise conclusion source target child ih =>
      simp [FiniteEndpointRoleEvidence.check,
        FiniteEndpointRoleEvidence.Valid, FiniteRegularCertificate.rules, ih,
        and_assoc]
  | inverse premise conclusion source target child ih =>
      simp [FiniteEndpointRoleEvidence.check,
        FiniteEndpointRoleEvidence.Valid, FiniteRegularCertificate.rules, ih,
        and_assoc]
  | chain first second conclusion source middle target left right ihLeft ihRight =>
      simp [FiniteEndpointRoleEvidence.check,
        FiniteEndpointRoleEvidence.Valid, FiniteRegularCertificate.rules,
        ihLeft, ihRight, and_assoc]
  | refl => simp [FiniteEndpointRoleEvidence.check,
      FiniteEndpointRoleEvidence.Valid, FiniteRegularCertificate.rules]

theorem FiniteEndpointRoleEvidence.endpointRole_of_valid
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (evidence : FiniteEndpointRoleEvidence (Fin nodeCount) (Fin roleCount))
    (hvalid : evidence.Valid certificate) :
    EndpointRole certificate.state certificate.redirect certificate.rules
      evidence.role evidence.source evidence.target := by
  induction evidence with
  | direct role source target =>
      exact .direct hvalid
  | sub premise conclusion source target child ih =>
      rcases hvalid with ⟨hrule, hrole, hsource, htarget, hchild⟩
      exact .sub hrule (hrole ▸ hsource ▸ htarget ▸ ih hchild)
  | inverse premise conclusion source target child ih =>
      rcases hvalid with ⟨hrule, hrole, hsource, htarget, hchild⟩
      exact .inverse hrule (hrole ▸ hsource ▸ htarget ▸ ih hchild)
  | chain first second conclusion source middle target left right ihLeft ihRight =>
      rcases hvalid with
        ⟨hrule, hlrole, hlsource, hltarget, hrrole, hrsource, hrtarget,
          hleft, hright⟩
      exact .chain hrule
        (hlrole ▸ hlsource ▸ hltarget ▸ ihLeft hleft)
        (hrrole ▸ hrsource ▸ hrtarget ▸ ihRight hright)
  | refl role source => exact .refl hvalid

theorem FiniteEndpointRoleEvidence.check_sound
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (evidence : FiniteEndpointRoleEvidence (Fin nodeCount) (Fin roleCount))
    (hcheck : evidence.check certificate = true) :
    EndpointRole certificate.state certificate.redirect certificate.rules
      evidence.role evidence.source evidence.target :=
  evidence.endpointRole_of_valid certificate
    ((evidence.check_eq_true_iff certificate).mp hcheck)

theorem EndpointRole.raw_of_identity_roleClosed
    (edge : EndpointRole state redirect rules role source target)
    (hidentity : ∀ node, redirect node = node)
    (hclosed : state.RoleClosed rules) : state.edge role source target := by
  induction edge with
  | direct edge => simpa [hidentity] using edge
  | sub rule edge ih => exact hclosed.1 _ _ rule _ _ ih
  | inverse rule edge ih => exact hclosed.2.1 _ _ rule _ _ ih
  | chain rule left right ihLeft ihRight =>
      exact hclosed.2.2.1 _ _ _ rule _ _ _ ihLeft ihRight
  | refl rule => exact hclosed.2.2.2 _ rule _

/-- A checked derivation of an edge absent from a role-closed raw graph proves
that the serialized redirect is genuinely non-identity. -/
theorem FiniteEndpointRoleEvidence.exists_nonidentity_redirect_of_check
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (evidence : FiniteEndpointRoleEvidence (Fin nodeCount) (Fin roleCount))
    (hcheck : evidence.check certificate = true)
    (hclosed : certificate.state.RoleClosed certificate.rules)
    (hraw : ¬certificate.state.edge evidence.role evidence.source
      evidence.target) :
    ∃ node, certificate.redirect node ≠ node := by
  by_contra hnone
  push Not at hnone
  apply hraw
  exact (evidence.check_sound certificate hcheck).raw_of_identity_roleClosed
    hnone hclosed

#print axioms FiniteEndpointRoleEvidence.check_eq_true_iff
#print axioms FiniteEndpointRoleEvidence.check_sound
#print axioms State.roleClosed_of_saturated_normalized
#print axioms EndpointRole.raw_of_identity_roleClosed
#print axioms FiniteEndpointRoleEvidence.exists_nonidentity_redirect_of_check

end ContextCalculus.Hypertableau
