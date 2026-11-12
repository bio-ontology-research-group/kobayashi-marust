import Std.Data.HashSet
import ContextCalculus.OWL.Semantics

/-!
# Class and object-property names of an ontology (v1.6.2)

`O.classNames` and `O.objectPropertyNames` list the names an ontology
declares or mentions, deduplicated, in first-occurrence order (axioms in
order, and inside an axiom from left to right). `owl:Thing` and
`owl:Nothing` are not class IRIs here: the parser maps them to
`ClassExpr.thing` / `.nothing` and skips their declarations.

The per-axiom lists (`Axiom.classNames`, `Axiom.objectPropertyNames`) are
the specification; the ontology-level functions only deduplicate them, in
one pass with a hash set, so they run in time linear in the ontology.
-/

namespace ContextCalculus.OWL

def ObjProp.name : ObjProp → IRI
  | .named r => r
  | .inv r => r

/-- The object-property IRIs a class expression mentions. -/
def ClassExpr.roleNames : ClassExpr → List IRI
  | .cls _ | .thing | .nothing => []
  | .and cs | .or cs => cs.attach.flatMap fun ⟨c, _⟩ => c.roleNames
  | .not c => c.roleNames
  | .some r c | .all r c => r.name :: c.roleNames
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

/-- The class IRIs an axiom declares or mentions. -/
def Axiom.classNames : Axiom → List IRI
  | .subClassOf c d => c.names ++ d.names
  | .equivalentClasses cs | .disjointClasses cs => cs.flatMap ClassExpr.names
  | .domain _ c | .range _ c => c.names
  | .declareClass a => [a]
  | .subObjectPropertyOf .. | .equivalentObjectProperties _ | .inverseObjectProperties .. => []
  | .transitive _ | .symmetric _ | .declareObjectProperty _ => []

/-- The object-property IRIs an axiom declares or mentions. -/
def Axiom.objectPropertyNames : Axiom → List IRI
  | .subClassOf c d => c.roleNames ++ d.roleNames
  | .equivalentClasses cs | .disjointClasses cs => cs.flatMap ClassExpr.roleNames
  | .domain r c | .range r c => r.name :: c.roleNames
  | .subObjectPropertyOf rs r => rs.map ObjProp.name ++ [r.name]
  | .equivalentObjectProperties rs => rs.map ObjProp.name
  | .inverseObjectProperties r s => [r.name, s.name]
  | .transitive r | .symmetric r => [r.name]
  | .declareObjectProperty r => [r]
  | .declareClass _ => []

/-- Add `x` unless it was seen; `seen` holds the names already in the
array. -/
def addNew (acc : Array IRI × Std.HashSet IRI) (x : IRI) : Array IRI × Std.HashSet IRI :=
  if acc.2.contains x then acc else (acc.1.push x, acc.2.insert x)

/-- Append the names of `xs` not seen yet. -/
def appendNew (acc : Array IRI × Std.HashSet IRI) (xs : List IRI) :
    Array IRI × Std.HashSet IRI :=
  xs.foldl addNew acc

/-- The names `f` gives for the axioms of `O`, deduplicated, in
first-occurrence order. -/
def Ontology.namesBy (O : Ontology) (f : Axiom → List IRI) : List IRI :=
  (O.axioms.foldl (init := (#[], {})) fun acc ax => appendNew acc (f ax)).1.toList

/-- The class IRIs `O` declares or mentions (deduplicated, first occurrence
first). -/
def Ontology.classNames (O : Ontology) : List IRI :=
  O.namesBy Axiom.classNames

/-- The object-property IRIs `O` declares or mentions (deduplicated, first
occurrence first). -/
def Ontology.objectPropertyNames (O : Ontology) : List IRI :=
  O.namesBy Axiom.objectPropertyNames

/-! ## The name lists are the deduplicated per-axiom lists -/

/-- The accumulator invariant: `seen` holds exactly the names of the array,
and the array has no duplicates. -/
def Synced (acc : Array IRI × Std.HashSet IRI) : Prop :=
  (∀ y, y ∈ acc.1 ↔ acc.2.contains y = true) ∧ acc.1.toList.Nodup

theorem synced_empty : Synced (#[], {}) := by
  refine ⟨fun y => ?_, List.nodup_nil⟩
  simp

theorem addNew_spec {acc : Array IRI × Std.HashSet IRI} (h : Synced acc) (x : IRI) :
    Synced (addNew acc x) ∧ ∀ y, y ∈ (addNew acc x).1 ↔ y ∈ acc.1 ∨ y = x := by
  unfold addNew
  by_cases hx : acc.2.contains x = true
  · simp only [hx, if_true]
    refine ⟨h, fun y => ⟨Or.inl, ?_⟩⟩
    rintro (hy | rfl)
    · exact hy
    · exact (h.1 _).2 hx
  · simp only [hx, if_false, Bool.false_eq_true]
    have hxa : x ∉ acc.1 := fun hm => hx ((h.1 x).1 hm)
    refine ⟨⟨fun y => ?_, ?_⟩, fun y => by simp [Array.mem_push]⟩
    · rw [Array.mem_push, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq,
        ← h.1 y]
      constructor
      · rintro (hy | rfl)
        · exact Or.inr hy
        · exact Or.inl rfl
      · rintro (rfl | hy)
        · exact Or.inr rfl
        · exact Or.inl hy
    · rw [Array.toList_push, List.nodup_append]
      refine ⟨h.2, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      subst hab
      exact hxa (Array.mem_def.2 ha)

theorem appendNew_spec {acc : Array IRI × Std.HashSet IRI} (h : Synced acc) (xs : List IRI) :
    Synced (appendNew acc xs) ∧ ∀ y, y ∈ (appendNew acc xs).1 ↔ y ∈ acc.1 ∨ y ∈ xs := by
  induction xs generalizing acc with
  | nil => exact ⟨h, fun y => by simp [appendNew]⟩
  | cons x xs ih =>
    have hs := addNew_spec h x
    have hr := ih hs.1
    refine ⟨hr.1, fun y => ?_⟩
    show y ∈ (appendNew (addNew acc x) xs).1 ↔ _
    rw [hr.2 y, hs.2 y, List.mem_cons]
    constructor
    · rintro ((h1 | h2) | h3)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h3)
    · rintro (h1 | h2 | h3)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h2)
      · exact Or.inr h3

theorem namesBy_spec (axs : List Axiom) (f : Axiom → List IRI)
    {acc : Array IRI × Std.HashSet IRI} (h : Synced acc) :
    let r := axs.foldl (init := acc) fun acc ax => appendNew acc (f ax)
    Synced r ∧ ∀ y, y ∈ r.1 ↔ y ∈ acc.1 ∨ ∃ ax ∈ axs, y ∈ f ax := by
  induction axs generalizing acc with
  | nil => exact ⟨h, fun y => by simp⟩
  | cons ax axs ih =>
    have hs := appendNew_spec h (f ax)
    have hr := ih hs.1
    refine ⟨hr.1, fun y => ?_⟩
    simp only [List.foldl_cons]
    rw [hr.2 y, hs.2 y]
    simp only [List.mem_cons]
    constructor
    · rintro ((h1 | h2) | ⟨b, hb, hy⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨ax, Or.inl rfl, h2⟩
      · exact Or.inr ⟨b, Or.inr hb, hy⟩
    · rintro (h1 | ⟨b, rfl | hb, hy⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr hy)
      · exact Or.inr ⟨b, hb, hy⟩

theorem Ontology.mem_namesBy (O : Ontology) (f : Axiom → List IRI) (y : IRI) :
    y ∈ O.namesBy f ↔ ∃ ax ∈ O.axioms, y ∈ f ax := by
  have := (namesBy_spec O.axioms f synced_empty).2 y
  unfold Ontology.namesBy
  rw [Array.mem_toList_iff, this]
  simp

theorem Ontology.namesBy_nodup (O : Ontology) (f : Axiom → List IRI) :
    (O.namesBy f).Nodup :=
  (namesBy_spec O.axioms f synced_empty).1.2

/-- A class IRI is in `O.classNames` exactly when an axiom declares or
mentions it. -/
theorem Ontology.mem_classNames (O : Ontology) (a : IRI) :
    a ∈ O.classNames ↔ ∃ ax ∈ O.axioms, a ∈ ax.classNames :=
  O.mem_namesBy _ a

theorem Ontology.classNames_nodup (O : Ontology) : O.classNames.Nodup :=
  O.namesBy_nodup _

/-- An object-property IRI is in `O.objectPropertyNames` exactly when an
axiom declares or mentions it. -/
theorem Ontology.mem_objectPropertyNames (O : Ontology) (r : IRI) :
    r ∈ O.objectPropertyNames ↔ ∃ ax ∈ O.axioms, r ∈ ax.objectPropertyNames :=
  O.mem_namesBy _ r

theorem Ontology.objectPropertyNames_nodup (O : Ontology) : O.objectPropertyNames.Nodup :=
  O.namesBy_nodup _

#print axioms Ontology.mem_classNames
#print axioms Ontology.classNames_nodup
#print axioms Ontology.mem_objectPropertyNames
#print axioms Ontology.objectPropertyNames_nodup

end ContextCalculus.OWL
