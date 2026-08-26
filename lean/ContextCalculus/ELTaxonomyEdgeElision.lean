import ContextCalculus.ELCompletion

/-!
# Taxonomy-preserving elimination of an edge-only EL component

The production ELC worker may omit NF3, NF6, NF7, and reflexive edge
materialization when no edge can contribute a class fact. This file proves the
exact dependency criterion used by Rust: NF4 and NF5 are absent, NF1/NF2 cannot
conclude bottom, and NF3 cannot name bottom as its filler. Under those premises
every full-ontology class fact is derivable from the NF1/NF2 projection, while
the projection is trivially contained in the source.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type}

def classProjection : Ontology Concept Role → Ontology Concept Role :=
  List.filter fun
    | .nf1 _ _ | .nf2 _ _ _ => true
    | _ => false

structure TaxonomyEdgeSafe (top bottom : Concept)
    (O : Ontology Concept Role) : Prop where
  top_ne_bottom : top ≠ bottom
  no_nf4 : ∀ {role filler sup}, Clause.nf4 role filler sup ∉ O
  no_nf5 : ∀ {sub}, Clause.nf5 sub ∉ O
  nf1_not_bottom : ∀ {sub sup}, Clause.nf1 sub sup ∈ O → sup ≠ bottom
  nf2_not_bottom : ∀ {left right sup}, Clause.nf2 left right sup ∈ O → sup ≠ bottom
  nf3_filler_not_bottom :
    ∀ {sub role filler}, Clause.nf3 sub role filler ∈ O → filler ≠ bottom

theorem source_sub_to_classProjection_and_bottom_source
    {top bottom : Concept} {O : Ontology Concept Role}
    (safe : TaxonomyEdgeSafe top bottom O)
    {a b : Concept} (h : Sub top bottom O a b) :
    Sub top bottom (classProjection O) a b ∧ (b = bottom → a = bottom) :=
  Sub.rec
    (motive_1 := fun a b _ =>
      Sub top bottom (classProjection O) a b ∧ (b = bottom → a = bottom))
    (motive_2 := fun a _ target _ => target = bottom → a = bottom)
    (fun a => ⟨Sub.refl a, fun hbottom => hbottom⟩)
    (fun a => ⟨Sub.top a, fun hbottom => False.elim (safe.top_ne_bottom hbottom)⟩)
    (fun _ hcl ih =>
      ⟨Sub.nf1 ih.1 (by simpa [classProjection] using hcl),
        fun hbottom => False.elim (safe.nf1_not_bottom hcl hbottom)⟩)
    (fun _ _ hcl ihl ihr =>
      ⟨Sub.nf2 ihl.1 ihr.1 (by simpa [classProjection] using hcl),
        fun hbottom => False.elim (safe.nf2_not_bottom hcl hbottom)⟩)
    (fun _ hcl _ => False.elim (safe.no_nf5 hcl))
    (fun _ _ hcl _ _ => False.elim (safe.no_nf4 hcl))
    (fun _ _ hedge hsub => by
      have htarget : _ = bottom := hsub.2 rfl
      have ha : _ = bottom := hedge htarget
      exact ⟨by simpa [ha] using
          (Sub.refl (top := top) (bottom := bottom)
            (O := classProjection O) bottom),
        fun _ => ha⟩)
    (fun _ hcl _ hbottom => False.elim (safe.nf3_filler_not_bottom hcl hbottom))
    (fun _ _ hedge => hedge)
    (fun _ _ _ hedge₁ hedge₂ hbottom => hedge₁ (hedge₂ hbottom))
    (fun a _ _ hbottom => hbottom)
    h

theorem source_sub_to_classProjection
    {top bottom : Concept} {O : Ontology Concept Role}
    (safe : TaxonomyEdgeSafe top bottom O)
    {a b : Concept} (h : Sub top bottom O a b) :
    Sub top bottom (classProjection O) a b :=
  (source_sub_to_classProjection_and_bottom_source safe h).1

theorem classProjection_sub_to_source
    {top bottom : Concept} {O : Ontology Concept Role}
    {a b : Concept} (h : Sub top bottom (classProjection O) a b) :
    Sub top bottom O a b :=
  Sub.rec
    (motive_1 := fun a b _ => Sub top bottom O a b)
    (motive_2 := fun _ _ _ _ => False)
    (fun a => Sub.refl a)
    (fun a => Sub.top a)
    (fun _ hcl ih => Sub.nf1 ih (by simpa [classProjection] using hcl))
    (fun _ _ hcl ihl ihr =>
      Sub.nf2 ihl ihr (by simpa [classProjection] using hcl))
    (fun _ hcl _ => by simp [classProjection] at hcl)
    (fun _ _ hcl _ _ => by simp [classProjection] at hcl)
    (fun _ _ hedge _ => False.elim hedge)
    (fun _ hcl _ => by simp [classProjection] at hcl)
    (fun _ hcl _ => by simp [classProjection] at hcl)
    (fun _ _ hcl _ _ => by simp [classProjection] at hcl)
    (fun _ _ hcl => by simp [classProjection] at hcl)
    h

/-- Role hierarchy, chain, reflexivity, and existential-edge clauses are
taxonomy-inert when no NF4 rule can turn an edge into a named fact and the
source closure has established that no named concept reaches bottom.  This is
the source theorem for the sparse-Horn route's deferred RBox check. -/
theorem source_sub_to_classProjection_of_no_bottom
    {top bottom : Concept} {O : Ontology Concept Role}
    (no_nf4 : ∀ {role filler sup}, Clause.nf4 role filler sup ∉ O)
    (no_bottom : ∀ {a}, Sub top bottom O a bottom → a = bottom)
    {a b : Concept} (h : Sub top bottom O a b) :
    Sub top bottom (classProjection O) a b := by
  exact (Sub.rec
    (motive_1 := fun a b _ =>
      Sub top bottom (classProjection O) a b ∧ Sub top bottom O a b)
    (motive_2 := fun a role target _ =>
      Edge top bottom O a role target ∧ (target = bottom → a = bottom))
    (fun a => ⟨Sub.refl a, Sub.refl a⟩)
    (fun a => ⟨Sub.top a, Sub.top a⟩)
    (fun _ hcl ih =>
      ⟨Sub.nf1 ih.1 (by simpa [classProjection] using hcl),
        Sub.nf1 ih.2 hcl⟩)
    (fun _ _ hcl ihl ihr =>
      ⟨Sub.nf2 ihl.1 ihr.1 (by simpa [classProjection] using hcl),
        Sub.nf2 ihl.2 ihr.2 hcl⟩)
    (fun _ hcl ih => by
      let source := Sub.nf5 ih.2 hcl
      have ha : _ = bottom := no_bottom source
      exact ⟨by simpa [ha] using
          (Sub.refl (top := top) (bottom := bottom)
            (O := classProjection O) bottom), source⟩)
    (fun _ _ hcl _ _ => False.elim (no_nf4 hcl))
    (fun _ _ hedge hsub => by
      let source := Sub.bottomEdge hedge.1 hsub.2
      have ha : _ = bottom := no_bottom source
      exact ⟨by simpa [ha] using
          (Sub.refl (top := top) (bottom := bottom)
            (O := classProjection O) bottom), source⟩)
    (fun _ hcl ih => by
      let edge := Edge.nf3 ih.2 hcl
      exact ⟨edge, fun htarget =>
        no_bottom (Sub.bottomEdge edge (by simpa [htarget] using
          (Sub.refl (top := top) (bottom := bottom) (O := O) bottom)))⟩)
    (fun _ hcl ih => by
      let edge := Edge.nf6 ih.1 hcl
      exact ⟨edge, fun htarget =>
        no_bottom (Sub.bottomEdge edge (by simpa [htarget] using
          (Sub.refl (top := top) (bottom := bottom) (O := O) bottom)))⟩)
    (fun _ _ hcl ih₁ ih₂ => by
      let edge := Edge.nf7 ih₁.1 ih₂.1 hcl
      exact ⟨edge, fun htarget =>
        no_bottom (Sub.bottomEdge edge (by simpa [htarget] using
          (Sub.refl (top := top) (bottom := bottom) (O := O) bottom)))⟩)
    (fun a _ hcl => ⟨Edge.reflexive a hcl, fun htarget => htarget⟩)
    h).1

theorem sub_iff_classProjection_of_no_bottom
    {top bottom : Concept} {O : Ontology Concept Role}
    (no_nf4 : ∀ {role filler sup}, Clause.nf4 role filler sup ∉ O)
    (no_bottom : ∀ {a}, Sub top bottom O a bottom → a = bottom)
    (a b : Concept) :
    Sub top bottom O a b ↔ Sub top bottom (classProjection O) a b :=
  ⟨source_sub_to_classProjection_of_no_bottom no_nf4 no_bottom,
    classProjection_sub_to_source⟩

#print axioms sub_iff_classProjection_of_no_bottom

theorem sub_iff_classProjection
    {top bottom : Concept} {O : Ontology Concept Role}
    (safe : TaxonomyEdgeSafe top bottom O) (a b : Concept) :
    Sub top bottom O a b ↔ Sub top bottom (classProjection O) a b :=
  ⟨source_sub_to_classProjection safe, classProjection_sub_to_source⟩

#print axioms sub_iff_classProjection

end ContextCalculus.ELCompletion
