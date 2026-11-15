import ContextCalculus.OWLFrontend.KeyRules
import ContextCalculus.OWLFrontend.HintBatch

/-!
# Asymmetric and disjoint properties on the hint route (stage C5, item 5)

The hint route needs only soundness: a model of a *stronger* ontology is a
model of the input. `edgeOff` replaces

* `AsymmetricObjectProperty(r)` by `∃r.⊤ ⊓ ∃r⁻.⊤ ⊑ ⊥` (no element has both
  an `r`-successor and an `r`-predecessor),
* `DisjointObjectProperties(r1 ... rn)` by `∃ri.⊤ ⊓ ∃rj.⊤ ⊑ ⊥` for `i < j`,
* `DisjointDataProperties(p1 ... pn)` by `∃pi ⊓ ∃pj ⊑ ⊥` for `i < j`,

each of which implies the axiom it replaces (`model_of_edgeOff`). So a hint
for `edgeOff O` certifies consistency of `O`, and every negative row of
`edgeOff O` is a negative row of `O` (`holds_of_models`,
`hintRowAnsE_sound`).

This is the cheapest sound check, and it is incomplete in a strong sense:
`edgeOff O` can be inconsistent while `O` is consistent (an asymmetric
`r`-chain `a → b → c` violates the strengthening at `b`), so a hint exists
only for inputs with a model of that shape. The exact check (edge labels of
the realisation, with the forest built from the certificate's supports)
and the complete route for these axioms stay open, as does the
`xsd:dateTime` facet range.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes

variable {DM : DatatypeMap} {Dom : Type}

/-- The inverse of an object-property expression. -/
def opInv : ObjProp → ObjProp
  | .named a => .inv a
  | .inv a => .named a
  | .top => .top
  | .bot => .bot

theorem prop_opInv (I : Interp DM Dom) (r : ObjProp) (x y : Dom) :
    I.prop (opInv r) x y ↔ I.prop r y x := by
  cases r <;> simp [opInv, Interp.prop]

/-- The pairs `(l[i], l[j])` with `i < j`. -/
def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | a :: t => t.map (a, ·) ++ pairsOf t

theorem pairwise_of_pairsOf {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, (∀ p ∈ pairsOf l, R p.1 p.2) → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | a :: t, h => by
    refine List.Pairwise.cons (fun b hb => ?_) (pairwise_of_pairsOf fun p hp => h p ?_)
    · exact h (a, b) (List.mem_append_left _ (List.mem_map_of_mem hb))
    · exact List.mem_append_right _ hp

/-- `⊓ [∃r.⊤, ∃s.⊤] ⊑ ⊥`. -/
def noBoth (r s : ObjProp) : Axiom := .subClassOf (.and [.some r .thing, .some s .thing]) .nothing

/-- `⊓ [∃p, ∃q] ⊑ ⊥`. -/
def noBothD (p q : DataProp) : Axiom :=
  .subClassOf (.and [.dataSome p (.datatype rdfsLiteral), .dataSome q (.datatype rdfsLiteral)]) .nothing

/-- The replacement of one axiom. -/
def edgeAx : Axiom → List Axiom
  | .asymmetric r => [noBoth r (opInv r)]
  | .disjointObjectProperties rs => (pairsOf rs).map fun p => noBoth p.1 p.2
  | .disjointDataProperties ps => (pairsOf ps).map fun p => noBothD p.1 p.2
  | ax => [ax]

/-- **The strengthened ontology.** -/
def edgeOff (O : Ontology) : Ontology := ⟨O.axioms.flatMap edgeAx⟩

/-- The input uses an axiom `edgeOff` replaces. -/
def hasEdgeAx (O : Ontology) : Bool :=
  O.axioms.any fun
    | .asymmetric _ | .disjointObjectProperties _ | .disjointDataProperties _ => true
    | _ => false

theorem sat_noBoth (I : Interp DM Dom) (N : List IRI) (r s : ObjProp) :
    I.sat N (noBoth r s) ↔ ∀ x, ¬ ((∃ y, I.prop r x y) ∧ ∃ y, I.prop s x y) := by
  simp only [noBoth, Interp.sat, ext_and2]
  rw [show I.ext .nothing = fun _ => False by funext x; rw [Interp.ext]]
  simp only [Interp.ext]
  simp

theorem sat_noBothD (I : Interp DM Dom) (N : List IRI) (p q : DataProp) :
    I.sat N (noBothD p q) → ∀ x v, ¬ (I.dp p x v ∧ I.dp q x v) := by
  simp only [noBothD, Interp.sat, ext_and2]
  rw [show I.ext .nothing = fun _ => False by funext x; rw [Interp.ext]]
  intro h x v ⟨hp, hq⟩
  refine h x ⟨?_, ?_⟩
  · rw [Interp.ext]; exact ⟨v, hp, by simp [Interp.drExt, DataRange.ext, DatatypeMap.dtExt]⟩
  · rw [Interp.ext]; exact ⟨v, hq, by simp [Interp.drExt, DataRange.ext, DatatypeMap.dtExt]⟩

theorem named_edgeAx (ax : Axiom) :
    (edgeAx ax).flatMap Axiom.namedIndividuals = ax.namedIndividuals := by
  cases ax <;> simp [edgeAx, noBoth, noBothD, Axiom.namedIndividuals, ClassExpr.namedIndividuals,
    List.flatMap_map]

theorem named_edgeOff (O : Ontology) : (edgeOff O).namedIndividuals = O.namedIndividuals := by
  simp only [Ontology.namedIndividuals, edgeOff, List.flatMap_assoc, named_edgeAx]

/-- **The strengthening implies the input.** -/
theorem model_of_edgeOff {O : Ontology} {I : Interp DM Dom} (h : OWL.Model (edgeOff O) I) :
    OWL.Model O I := by
  intro ax hax
  have hin : ∀ b ∈ edgeAx ax, I.sat O.namedIndividuals b := fun b hb => by
    have := h b (List.mem_flatMap.2 ⟨ax, hax, hb⟩)
    rwa [named_edgeOff] at this
  cases ax with
  | asymmetric r =>
    have := (sat_noBoth I _ r (opInv r)).1 (hin _ (List.mem_singleton_self _))
    intro x y hxy hyx
    exact this x ⟨⟨y, hxy⟩, ⟨y, (prop_opInv I r x y).2 hyx⟩⟩
  | disjointObjectProperties rs =>
    simp only [Interp.sat]
    refine pairwise_of_pairsOf fun p hp x y ⟨h1, h2⟩ => ?_
    have := (sat_noBoth I _ p.1 p.2).1 (hin _ (List.mem_map_of_mem hp))
    exact this x ⟨⟨y, h1⟩, ⟨y, h2⟩⟩
  | disjointDataProperties ps =>
    simp only [Interp.sat]
    exact pairwise_of_pairsOf fun p hp x v hv =>
      sat_noBothD I _ p.1 p.2 (hin _ (List.mem_map_of_mem hp)) x v hv
  | _ => exact hin _ (List.mem_singleton_self _)

/-- Rows hold for an ontology whose models include those of a stronger
one. -/
theorem holds_of_models (pat : String → String → Prop) {O O' : Ontology}
    (hm : ∀ (Dom : Type) (I : Interp (owl2MapP pat) Dom), OWL.Model O' I → OWL.Model O I)
    {r : HintRowSpec} (h : r.Holds pat O') : r.Holds pat O := by
  cases r with
  | consistent =>
    obtain ⟨Dom, hD, I, hI⟩ := h
    exact ⟨Dom, hD, I, hm Dom I hI⟩
  | nonsub A B => exact fun he => h fun Dom _ I hI => he Dom I (hm Dom I hI)
  | nonsubs A Bs => exact fun B hB he => h B hB fun Dom _ I hI => he Dom I (hm Dom I hI)
  | nontypes a Cs => exact fun C hC he => h C hC fun Dom _ I hI => he Dom I (hm Dom I hI)
  | _ => exact fun he => h fun Dom _ I hI => he Dom I (hm Dom I hI)

/-- **The hint route with the strengthening**: the rows of `edgeOff O` when
`O` has asymmetric or disjoint properties. -/
def hintRowAnsE (O : Ontology) (r : HintRowSpec) (hint : RawHint) : Option Bool :=
  if hasEdgeAx O then hintRowAns (edgeOff O) r hint else hintRowAns O r hint

theorem hintRowAnsE_sound (pat : String → String → Prop) {O : Ontology} {r : HintRowSpec}
    {hint : RawHint} (h : hintRowAnsE O r hint = some true) : r.Holds pat O := by
  unfold hintRowAnsE at h
  split_ifs at h
  · exact holds_of_models pat (fun _ _ hI => model_of_edgeOff hI) (hintRowAns_sound pat h)
  · exact hintRowAns_sound pat h

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.model_of_edgeOff
#print axioms ContextCalculus.OWLFrontend.hintRowAnsE_sound
