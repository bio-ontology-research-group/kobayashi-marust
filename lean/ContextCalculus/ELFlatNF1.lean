import ContextCalculus.ELTaxonomyEdgeElision

/-!
# Exact closure of a flat NF1 taxonomy

The direct large-taxonomy route accepts named `SubClassOf(A B)` axioms and
discards only the universally valid built-in forms `A ⊑ top` and
`bottom ⊑ A`.
This module identifies the ELC completion relation on that fragment with the
reflexive/transitive graph closure computed by the route. `owl:Thing` is not a
graph vertex or endpoint, so the calculus's implicit top fact cannot feed an
explicit NF1 edge.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type}

/-- The built-in subclass forms discarded by the source scanner. -/
def UniversalBuiltinClause (top bottom : Concept) : Clause Concept Role → Prop
  | .nf1 sub sup => sup = top ∨ sub = bottom
  | _ => False

theorem universalBuiltinClause_valid {top bottom : Concept}
    {Domain : Type} (I : Interp Domain Concept Role top bottom)
    {clause : Clause Concept Role}
    (universal : UniversalBuiltinClause (Role := Role) top bottom clause) :
    satClause I clause := by
  cases clause with
  | nf1 sub sup =>
      simp only [UniversalBuiltinClause] at universal
      rcases universal with rfl | rfl
      · intro x _
        exact I.top_true x
      · intro x is_bottom
        exact False.elim (I.bottom_false x is_bottom)
  | nf2 | nf3 | nf4 | nf5 | nf6 | nf7 | reflexive =>
      simp [UniversalBuiltinClause] at universal

/-- Adding or removing any collection of the scanner's built-in tautologies
preserves exactly the same interpretations. -/
theorem models_append_universalBuiltin_iff {top bottom : Concept}
    {Domain : Type} (I : Interp Domain Concept Role top bottom)
    {O builtins : Ontology Concept Role}
    (only_universal : ∀ clause ∈ builtins,
      UniversalBuiltinClause top bottom clause) :
    models I (O ++ builtins) ↔ models I O := by
  constructor
  · intro combined clause member
    exact combined clause (List.mem_append_left _ member)
  · intro base clause member
    rcases List.mem_append.mp member with member | member
    · exact base clause member
    · exact universalBuiltinClause_valid I (only_universal clause member)

def flatNF1Ontology (edges : List (Concept × Concept)) : Ontology Concept Role :=
  edges.map fun edge => .nf1 edge.1 edge.2

inductive FlatReach (edges : List (Concept × Concept)) : Concept → Concept → Prop where
  | refl (concept : Concept) : FlatReach edges concept concept
  | step {source middle target : Concept} :
      FlatReach edges source middle →
      (middle, target) ∈ edges →
      FlatReach edges source target

theorem flatReach_to_sub {top bottom : Concept}
    {edges : List (Concept × Concept)} {source target : Concept}
    (reach : FlatReach edges source target) :
    Sub top bottom (flatNF1Ontology (Role := Role) edges) source target := by
  induction reach with
  | refl => exact Sub.refl _
  | step prior edge ih =>
      exact Sub.nf1 ih (by simpa [flatNF1Ontology] using edge)

theorem flatNF1_no_edge {top bottom : Concept}
    {edges : List (Concept × Concept)} {source target : Concept} {role : Role}
    (edge : Edge top bottom (flatNF1Ontology edges) source role target) : False := by
  cases edge <;> simp [flatNF1Ontology] at *

theorem sub_to_top_or_flatReach {top bottom : Concept}
    {edges : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    {source target : Concept}
    (sub : Sub top bottom (flatNF1Ontology (Role := Role) edges) source target) :
    target = top ∨ FlatReach edges source target := by
  exact Sub.rec
    (motive_1 := fun source target _ =>
      target = top ∨ FlatReach edges source target)
    (motive_2 := fun _ _ _ _ => False)
    (fun concept => Or.inr (.refl concept))
    (fun _ => Or.inl rfl)
    (fun {_ sub sup} _ member ih => by
      have edge : (sub, sup) ∈ edges := by
        simpa [flatNF1Ontology] using member
      rcases ih with rfl | reach
      · exact False.elim (top_not_source edge)
      · exact Or.inr (.step reach edge))
    (fun _ _ member _ _ => by simp [flatNF1Ontology] at member)
    (fun _ member _ => by simp [flatNF1Ontology] at member)
    (fun _ _ _ edge_ih _ => False.elim edge_ih)
    (fun _ _ edge_ih _ => False.elim edge_ih)
    (fun _ member _ => by simp [flatNF1Ontology] at member)
    (fun _ member _ => by simp [flatNF1Ontology] at member)
    (fun _ _ member _ _ => by simp [flatNF1Ontology] at member)
    (fun (_ : Concept) {role : Role} member => by
      simp [flatNF1Ontology] at member)
    sub

theorem sub_iff_flatReach {top bottom : Concept}
    {edges : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    {source target : Concept} (target_not_top : target ≠ top) :
    Sub top bottom (flatNF1Ontology (Role := Role) edges) source target ↔
      FlatReach edges source target := by
  constructor
  · intro sub
    rcases sub_to_top_or_flatReach top_not_source sub with is_top | reach
    · exact False.elim (target_not_top is_top)
    · exact reach
  · exact flatReach_to_sub

/-- The direct route's positive consistency verdict is exact: with no NF1 edge
leaving top and with distinct top/bottom, interpreting only top as nonempty is
a model of every accepted edge. -/
theorem flatNF1_has_model {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges) :
    ∃ I : Interp Unit Concept Role top bottom,
      models I (flatNF1Ontology edges) := by
  let I : Interp Unit Concept Role top bottom := {
    concept := fun concept _ => concept = top
    role := fun _ _ _ => False
    top_true := fun _ => rfl
    bottom_false := fun _ bottom_is_top => top_ne_bottom bottom_is_top.symm
  }
  refine ⟨I, ?_⟩
  intro clause member
  rcases List.mem_map.mp member with ⟨edge, edge_member, rfl⟩
  rcases edge with ⟨source, target⟩
  intro _ source_is_top
  change source = top at source_is_top
  subst source
  exact False.elim (top_not_source edge_member)

theorem flatNF1_not_unsatisfiable {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges) :
    ¬ Unsatisfiable (top := top) (bottom := bottom)
        (flatNF1Ontology (Role := Role) edges) := by
  rcases flatNF1_has_model (Role := Role) top_ne_bottom top_not_source with ⟨I, models_I⟩
  intro unsatisfiable
  exact unsatisfiable I models_I

/-! The ORE868 source adds only pairwise disjointness axioms, normalized as
`A ⊓ B ⊑ bottom`.  The direct route admits them after checking that no named
context reaches both operands.  The following definition and theorems state
that exact fail-closed condition. -/

def flatNF1DisjointOntology (bottom : Concept)
    (edges disjoint : List (Concept × Concept)) : Ontology Concept Role :=
  flatNF1Ontology edges ++
    disjoint.map fun pair => .nf2 pair.1 pair.2 bottom

theorem flatNF1Disjoint_no_edge {top bottom : Concept}
    {edges disjoint : List (Concept × Concept)}
    {source target : Concept} {role : Role}
    (edge : Edge top bottom (flatNF1DisjointOntology bottom edges disjoint)
      source role target) : False := by
  cases edge <;> simp [flatNF1DisjointOntology, flatNF1Ontology] at *

theorem flatNF1Disjoint_sub_to_top_or_reach_or_bottom {top bottom : Concept}
    {edges disjoint : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    (operands_not_top : ∀ {left right}, (left, right) ∈ disjoint →
      left ≠ top ∧ right ≠ top)
    (inert : ∀ {source left right}, (left, right) ∈ disjoint →
      FlatReach edges source left → FlatReach edges source right → False)
    {source target : Concept}
    (sub : Sub top bottom
      (flatNF1DisjointOntology (Role := Role) bottom edges disjoint) source target) :
    target = top ∨ FlatReach edges source target ∨ source = bottom := by
  exact Sub.rec
    (motive_1 := fun source target _ =>
      target = top ∨ FlatReach edges source target ∨ source = bottom)
    (motive_2 := fun _ _ _ _ => False)
    (fun concept => Or.inr (Or.inl (.refl concept)))
    (fun _ => Or.inl rfl)
    (fun {_ sub sup} _ member ih => by
      have edge : (sub, sup) ∈ edges := by
        simpa [flatNF1DisjointOntology, flatNF1Ontology] using member
      rcases ih with rfl | reach | rfl
      · exact False.elim (top_not_source edge)
      · exact Or.inr (Or.inl (.step reach edge))
      · exact Or.inr (Or.inr rfl))
    (fun {_ left right sup} _ _ member ihl ihr => by
      rcases List.mem_append.mp member with member | member
      · simp [flatNF1Ontology] at member
      · rcases List.mem_map.mp member with ⟨pair, pair_member, pair_clause⟩
        rcases pair with ⟨disjoint_left, disjoint_right⟩
        simp only [Clause.nf2.injEq] at pair_clause
        rcases pair_clause with ⟨rfl, rfl, rfl⟩
        rcases operands_not_top pair_member with ⟨left_not_top, right_not_top⟩
        rcases ihl with left_is_top | left_reach | source_is_bottom
        · exact False.elim (left_not_top left_is_top)
        · rcases ihr with right_is_top | right_reach | source_is_bottom
          · exact False.elim (right_not_top right_is_top)
          · exact False.elim (inert pair_member left_reach right_reach)
          · exact Or.inr (Or.inr source_is_bottom)
        · exact Or.inr (Or.inr source_is_bottom))
    (fun _ member _ => by
      simp [flatNF1DisjointOntology, flatNF1Ontology] at member)
    (fun _ _ member _ _ => by
      simp [flatNF1DisjointOntology, flatNF1Ontology] at member)
    (fun _ _ edge_ih _ => False.elim edge_ih)
    (fun _ member _ => by
      simp [flatNF1DisjointOntology, flatNF1Ontology] at member)
    (fun _ member _ => by
      simp [flatNF1DisjointOntology, flatNF1Ontology] at member)
    (fun _ _ member _ _ => by
      simp [flatNF1DisjointOntology, flatNF1Ontology] at member)
    (fun _ _ member => by
      rcases List.mem_append.mp member with member | member
      · simp [flatNF1Ontology] at member
      · rcases List.mem_map.mp member with ⟨pair, _, equality⟩
        cases pair
        cases equality)
    sub

theorem flatNF1Disjoint_sub_iff_flatReach {top bottom : Concept}
    {edges disjoint : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    (operands_not_top : ∀ {left right}, (left, right) ∈ disjoint →
      left ≠ top ∧ right ≠ top)
    (inert : ∀ {source left right}, (left, right) ∈ disjoint →
      FlatReach edges source left → FlatReach edges source right → False)
    {source target : Concept} (source_not_bottom : source ≠ bottom)
    (target_not_top : target ≠ top) :
    Sub top bottom (flatNF1DisjointOntology (Role := Role) bottom edges disjoint) source target ↔
      FlatReach edges source target := by
  constructor
  · intro sub
    rcases flatNF1Disjoint_sub_to_top_or_reach_or_bottom
      top_not_source operands_not_top inert sub with is_top | reach | is_bottom
    · exact False.elim (target_not_top is_top)
    · exact reach
    · exact False.elim (source_not_bottom is_bottom)
  · intro reach
    clear source_not_bottom target_not_top
    induction reach with
    | refl => exact Sub.refl _
    | step prior edge ih =>
        exact Sub.nf1 ih (List.mem_append_left _ (by
          simpa [flatNF1Ontology] using edge))

theorem flatNF1Disjoint_has_model {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges disjoint : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    (operands_not_top : ∀ {left right}, (left, right) ∈ disjoint →
      left ≠ top ∧ right ≠ top) :
    ∃ I : Interp Unit Concept Role top bottom,
      models I (flatNF1DisjointOntology bottom edges disjoint) := by
  let I : Interp Unit Concept Role top bottom := {
    concept := fun concept _ => concept = top
    role := fun _ _ _ => False
    top_true := fun _ => rfl
    bottom_false := fun _ bottom_is_top => top_ne_bottom bottom_is_top.symm
  }
  refine ⟨I, ?_⟩
  intro clause member
  rcases List.mem_append.mp member with edge_member | disjoint_member
  · rcases List.mem_map.mp edge_member with ⟨⟨edge_source, edge_target⟩, source_member, rfl⟩
    intro _ source_is_top
    change edge_source = top at source_is_top
    subst edge_source
    exact False.elim (top_not_source source_member)
  · rcases List.mem_map.mp disjoint_member with ⟨pair, pair_member, rfl⟩
    rcases operands_not_top pair_member with ⟨left_not_top, _⟩
    intro _ left_is_top
    exact False.elim (left_not_top left_is_top)

theorem edgeSafe_sub_iff_flatReach {top bottom : Concept}
    {O : Ontology Concept Role} {edges : List (Concept × Concept)}
    (safe : TaxonomyEdgeSafe top bottom O)
    (projection : classProjection O = flatNF1Ontology edges)
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    {source target : Concept} (target_not_top : target ≠ top) :
    Sub top bottom O source target ↔ FlatReach edges source target := by
  rw [sub_iff_classProjection safe, projection]
  exact sub_iff_flatReach top_not_source target_not_top

def RoleOnlyClause : Clause Concept Role → Prop
  | .nf6 _ _ | .nf7 _ _ _ => True
  | _ => False

def flatNF1RBoxOntology (edges : List (Concept × Concept))
    (rbox : Ontology Concept Role) : Ontology Concept Role :=
  flatNF1Ontology edges ++ rbox

theorem classProjection_roleOnly_eq_nil {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause) :
    classProjection rbox = [] := by
  apply List.filter_eq_nil_iff.2
  intro clause member
  have only := rbox_only clause member
  cases clause <;> simp [RoleOnlyClause] at only ⊢

theorem flatNF1RBox_classProjection
    {edges : List (Concept × Concept)} {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause) :
    classProjection (flatNF1RBoxOntology edges rbox) = flatNF1Ontology edges := by
  rw [flatNF1RBoxOntology, classProjection, List.filter_append]
  have role_projection := classProjection_roleOnly_eq_nil rbox_only
  change List.filter _ rbox = [] at role_projection
  rw [role_projection, List.append_nil]
  apply List.filter_eq_self.2
  intro clause member
  rcases List.mem_map.mp member with ⟨edge, _, rfl⟩
  rfl

theorem flatNF1RBox_safe {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges : List (Concept × Concept)}
    (target_not_bottom : ∀ {source target}, (source, target) ∈ edges → target ≠ bottom)
    {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause) :
    TaxonomyEdgeSafe top bottom (flatNF1RBoxOntology edges rbox) := by
  refine {
    top_ne_bottom := top_ne_bottom
    no_nf4 := ?_
    no_nf5 := ?_
    nf1_not_bottom := ?_
    nf2_not_bottom := ?_
    nf3_filler_not_bottom := ?_
  }
  · intro role filler sup member
    rcases List.mem_append.mp member with member | member
    · simp [flatNF1Ontology] at member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only
  · intro sub member
    rcases List.mem_append.mp member with member | member
    · simp [flatNF1Ontology] at member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only
  · intro sub sup member
    rcases List.mem_append.mp member with member | member
    · have edge : (sub, sup) ∈ edges := by
        simpa [flatNF1Ontology] using member
      exact target_not_bottom edge
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only
  · intro left right sup member
    rcases List.mem_append.mp member with member | member
    · simp [flatNF1Ontology] at member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only
  · intro sub role filler member
    rcases List.mem_append.mp member with member | member
    · simp [flatNF1Ontology] at member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only

theorem flatNF1RBox_sub_iff_flatReach {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    (target_not_bottom : ∀ {source target}, (source, target) ∈ edges → target ≠ bottom)
    {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause)
    {source target : Concept} (target_not_top : target ≠ top) :
    Sub top bottom (flatNF1RBoxOntology edges rbox) source target ↔
      FlatReach edges source target := by
  apply edgeSafe_sub_iff_flatReach
    (flatNF1RBox_safe top_ne_bottom target_not_bottom rbox_only)
    (flatNF1RBox_classProjection rbox_only)
    top_not_source target_not_top

theorem flatNF1RBox_has_model {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause) :
    ∃ I : Interp Unit Concept Role top bottom,
      models I (flatNF1RBoxOntology edges rbox) := by
  let I : Interp Unit Concept Role top bottom := {
    concept := fun concept _ => concept = top
    role := fun _ _ _ => False
    top_true := fun _ => rfl
    bottom_false := fun _ bottom_is_top => top_ne_bottom bottom_is_top.symm
  }
  refine ⟨I, ?_⟩
  intro clause member
  rcases List.mem_append.mp member with nf1_member | role_member
  · rcases List.mem_map.mp nf1_member with ⟨edge, edge_member, rfl⟩
    rcases edge with ⟨source, target⟩
    intro _ source_is_top
    change source = top at source_is_top
    subst source
    exact False.elim (top_not_source edge_member)
  · have only := rbox_only clause role_member
    cases clause <;> simp [RoleOnlyClause, satClause, I] at only ⊢

/-! The source-level fast path also accepts existential leaves `A ⊑ ∃r.B`.
They create role edges but cannot feed a class conclusion because the fragment
contains no NF4/NF5 consumer. The generic edge-safety theorem therefore
projects them away together with the positive RBox. -/

def flatNF1LeafOntology (edges : List (Concept × Concept))
    (leaves : List (Concept × Role × Concept))
    (rbox : Ontology Concept Role) : Ontology Concept Role :=
  flatNF1Ontology edges ++
    (leaves.map fun leaf => .nf3 leaf.1 leaf.2.1 leaf.2.2) ++ rbox

theorem flatNF1Leaf_classProjection
    {edges : List (Concept × Concept)}
    {leaves : List (Concept × Role × Concept)}
    {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause) :
    classProjection (flatNF1LeafOntology edges leaves rbox) =
      flatNF1Ontology edges := by
  rw [flatNF1LeafOntology, classProjection, List.filter_append,
    List.filter_append]
  have role_projection := classProjection_roleOnly_eq_nil rbox_only
  change List.filter _ rbox = [] at role_projection
  rw [role_projection, List.append_nil]
  have edge_projection :
      List.filter
        (fun clause : Clause Concept Role => match clause with
          | Clause.nf1 _ _ | Clause.nf2 _ _ _ => true
          | _ => false)
        (flatNF1Ontology edges) = flatNF1Ontology edges := by
    apply List.filter_eq_self.2
    intro clause member
    rcases List.mem_map.mp member with ⟨edge, _, rfl⟩
    rfl
  have leaf_projection :
      List.filter
        (fun clause : Clause Concept Role => match clause with
          | Clause.nf1 _ _ | Clause.nf2 _ _ _ => true
          | _ => false)
        (leaves.map fun leaf => Clause.nf3 leaf.1 leaf.2.1 leaf.2.2) = [] := by
    apply List.filter_eq_nil_iff.2
    intro clause member
    rcases List.mem_map.mp member with ⟨leaf, _, rfl⟩
    simp
  change
    List.filter
        (fun clause : Clause Concept Role => match clause with
          | Clause.nf1 _ _ | Clause.nf2 _ _ _ => true
          | _ => false)
        (flatNF1Ontology edges) ++
      List.filter
        (fun clause : Clause Concept Role => match clause with
          | Clause.nf1 _ _ | Clause.nf2 _ _ _ => true
          | _ => false)
        (leaves.map fun leaf => Clause.nf3 leaf.1 leaf.2.1 leaf.2.2) =
      flatNF1Ontology edges
  rw [edge_projection, leaf_projection, List.append_nil]

theorem flatNF1Leaf_safe {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges : List (Concept × Concept)}
    (edge_target_not_bottom : ∀ {source target},
      (source, target) ∈ edges → target ≠ bottom)
    {leaves : List (Concept × Role × Concept)}
    (leaf_filler_not_bottom : ∀ {source role filler},
      (source, role, filler) ∈ leaves → filler ≠ bottom)
    {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause) :
    TaxonomyEdgeSafe top bottom (flatNF1LeafOntology edges leaves rbox) := by
  refine {
    top_ne_bottom := top_ne_bottom
    no_nf4 := ?_
    no_nf5 := ?_
    nf1_not_bottom := ?_
    nf2_not_bottom := ?_
    nf3_filler_not_bottom := ?_
  }
  · intro role filler sup member
    rcases List.mem_append.mp member with left | member
    · rcases List.mem_append.mp left with member | member
      · simp [flatNF1Ontology] at member
      · simp at member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only
  · intro sub member
    rcases List.mem_append.mp member with left | member
    · rcases List.mem_append.mp left with member | member
      · simp [flatNF1Ontology] at member
      · simp at member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only
  · intro sub sup member
    rcases List.mem_append.mp member with left | member
    · rcases List.mem_append.mp left with member | member
      · have edge : (sub, sup) ∈ edges := by
          simpa [flatNF1Ontology] using member
        exact edge_target_not_bottom edge
      · simp at member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only
  · intro left right sup member
    rcases List.mem_append.mp member with left_part | member
    · rcases List.mem_append.mp left_part with member | member
      · simp [flatNF1Ontology] at member
      · simp at member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only
  · intro sub role filler member
    rcases List.mem_append.mp member with left_part | member
    · rcases List.mem_append.mp left_part with member | member
      · simp [flatNF1Ontology] at member
      · rcases List.mem_map.mp member with ⟨leaf, leaf_member, equality⟩
        rcases leaf with ⟨leaf_source, leaf_role, leaf_filler⟩
        simp only [Clause.nf3.injEq] at equality
        rcases equality with ⟨rfl, rfl, rfl⟩
        exact leaf_filler_not_bottom leaf_member
    · have only := rbox_only _ member
      simp [RoleOnlyClause] at only

theorem flatNF1Leaf_sub_iff_flatReach {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges : List (Concept × Concept)}
    (top_not_source : ∀ {target}, (top, target) ∉ edges)
    (edge_target_not_bottom : ∀ {source target},
      (source, target) ∈ edges → target ≠ bottom)
    {leaves : List (Concept × Role × Concept)}
    (leaf_filler_not_bottom : ∀ {source role filler},
      (source, role, filler) ∈ leaves → filler ≠ bottom)
    {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause)
    {source target : Concept} (target_not_top : target ≠ top) :
    Sub top bottom (flatNF1LeafOntology edges leaves rbox) source target ↔
      FlatReach edges source target := by
  apply edgeSafe_sub_iff_flatReach
    (flatNF1Leaf_safe top_ne_bottom edge_target_not_bottom
      leaf_filler_not_bottom rbox_only)
    (flatNF1Leaf_classProjection rbox_only)
    top_not_source target_not_top

theorem flatNF1Leaf_has_model {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {edges : List (Concept × Concept)}
    (edge_target_not_bottom : ∀ {source target},
      (source, target) ∈ edges → target ≠ bottom)
    {leaves : List (Concept × Role × Concept)}
    (leaf_filler_not_bottom : ∀ {source role filler},
      (source, role, filler) ∈ leaves → filler ≠ bottom)
    {rbox : Ontology Concept Role}
    (rbox_only : ∀ clause ∈ rbox, RoleOnlyClause clause) :
    ∃ I : Interp Unit Concept Role top bottom,
      models I (flatNF1LeafOntology edges leaves rbox) := by
  let I : Interp Unit Concept Role top bottom := {
    concept := fun concept _ => concept ≠ bottom
    role := fun _ _ _ => True
    top_true := fun _ => top_ne_bottom
    bottom_false := fun _ => by simp
  }
  refine ⟨I, ?_⟩
  intro clause member
  rcases List.mem_append.mp member with left_part | role_member
  · rcases List.mem_append.mp left_part with edge_member | leaf_member
    · rcases List.mem_map.mp edge_member with ⟨edge, source_member, rfl⟩
      rcases edge with ⟨source, target⟩
      intro _ _
      exact edge_target_not_bottom source_member
    · rcases List.mem_map.mp leaf_member with ⟨leaf, source_member, rfl⟩
      rcases leaf with ⟨source, role, filler⟩
      intro _ _
      exact ⟨(), trivial, leaf_filler_not_bottom source_member⟩
  · have only := rbox_only clause role_member
    cases clause <;> simp [RoleOnlyClause, satClause, I] at only ⊢

/-- With no named-to-named NF1 edge, graph reachability is only reflexivity. -/
theorem flatReach_nil_iff {source target : Concept} :
    FlatReach ([] : List (Concept × Concept)) source target ↔ source = target := by
  constructor
  · intro reach
    cases reach with
    | refl => rfl
    | step _ edge => simp at edge
  · intro equality
    subst target
    exact .refl source

/-- Positive existential leaves alone publish no proper named subsumption.
This is the normalized TBox half of the source-level positive-ABox empty
taxonomy route. The independent native-ABox projection theorem transfers the
same public taxonomy to a consistent positive ABox. -/
theorem emptyLeaf_sub_iff_eq {top bottom : Concept}
    (top_ne_bottom : top ≠ bottom)
    {leaves : List (Concept × Role × Concept)}
    (leaf_filler_not_bottom : ∀ {source role filler},
      (source, role, filler) ∈ leaves → filler ≠ bottom)
    {source target : Concept} (target_not_top : target ≠ top) :
    Sub top bottom (flatNF1LeafOntology [] leaves []) source target ↔
      source = target := by
  rw [flatNF1Leaf_sub_iff_flatReach top_ne_bottom (by simp)
    (by simp) leaf_filler_not_bottom (by simp) target_not_top]
  exact flatReach_nil_iff

#print axioms sub_iff_flatReach
#print axioms models_append_universalBuiltin_iff
#print axioms flatNF1_not_unsatisfiable
#print axioms flatNF1Disjoint_sub_iff_flatReach
#print axioms flatNF1Disjoint_has_model
#print axioms edgeSafe_sub_iff_flatReach
#print axioms flatNF1RBox_has_model
#print axioms flatNF1RBox_sub_iff_flatReach
#print axioms flatNF1Leaf_sub_iff_flatReach
#print axioms flatNF1Leaf_has_model
#print axioms emptyLeaf_sub_iff_eq

end ContextCalculus.ELCompletion
