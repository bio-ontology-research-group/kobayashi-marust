import ContextCalculus.Hypertableau
import ContextCalculus.CheckerTerm

/-!
# Embedding signed hypertableau clauses into the common first-order source

The HT clause language stores concept polarity inside an atom.  The CB/ELC
certificate source stores polarity by implication position.  This module gives
the exact semantic bridge between those representations for the direct,
existential-free residual consumed by ordinary HT projection:

* a negative body concept moves to the first-order head;
* a negative head concept moves to the first-order body;
* positive concepts, roles, and equalities retain their side.

Existential obligations are not silently erased.  They are handled by the
separate checked Skolem-pair and bundle projections, so this direct embedding
has an explicit `Direct` premise excluding them.
-/

namespace ContextCalculus.HTCheckerTermEmbedding

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.CheckerTerm

def encodeVariable (index : Nat) : FTerm := .var (Int.ofNat index)

def encodePositive : Atom Nat Nat Nat → Option FLit
  | .concept literal node =>
      if literal.neg then none else some (.P (.concept literal.concept (encodeVariable node)))
  | .role role source target =>
      some (.P (.role role (encodeVariable source) (encodeVariable target)))
  | .exists_ .. => none
  | .eq left right => some (.eq (encodeVariable left) (encodeVariable right))

def encodeNegative : Atom Nat Nat Nat → Option FLit
  | .concept literal node =>
      if literal.neg then some (.P (.concept literal.concept (encodeVariable node))) else none
  | _ => none

def directAtom : Atom Nat Nat Nat → Bool
  | .exists_ .. => false
  | _ => true

def Direct (clause : Hypertableau.Clause Nat Nat Nat) : Prop :=
  ∀ atom ∈ clause.body ++ clause.head, directAtom atom = true

def encodeClause (clause : Hypertableau.Clause Nat Nat Nat) : FCL :=
  { body := clause.body.filterMap encodePositive ++ clause.head.filterMap encodeNegative
    head := clause.head.filterMap encodePositive ++ clause.body.filterMap encodeNegative }

noncomputable def checkerModel [Nonempty Domain]
    (interpretation : Interp Domain Nat Nat) : TModel Domain where
  conc := interpretation.concept
  rol := interpretation.role
  const := fun _ => Classical.choice inferInstance
  fn := fun _ value => value

def htInterp (model : TModel Domain) : Interp Domain Nat Nat where
  concept := model.conc
  role := model.rol

@[simp] theorem eval_encodeVariable (interpretation : Interp Domain Nat Nat)
    [Nonempty Domain] (assignment : Int → Domain) (index : Nat) :
    (checkerModel interpretation).evalT assignment (encodeVariable index) =
      assignment (Int.ofNat index) := rfl

theorem directAtom_no_exists (atom : Atom Nat Nat Nat)
    (hdirect : directAtom atom = true) :
    ∃ literal, encodePositive atom = some literal ∨ encodeNegative atom = some literal := by
  cases atom with
  | concept literal node =>
      cases hneg : literal.neg <;>
        simp [encodePositive, encodeNegative, hneg]
  | role role source target =>
      exact ⟨.P (.role role (encodeVariable source) (encodeVariable target)),
        Or.inl rfl⟩
  | exists_ role filler node => simp [directAtom] at hdirect
  | eq left right =>
      exact ⟨.eq (encodeVariable left) (encodeVariable right), Or.inl rfl⟩

theorem eval_positive_iff (model : TModel Domain)
    (assignment : Int → Domain) (atom : Atom Nat Nat Nat)
    (literal : FLit) (hencode : encodePositive atom = some literal) :
    model.evalL assignment literal ↔
      (htInterp model).satAtom (fun index => assignment (Int.ofNat index)) atom := by
  cases atom with
  | concept signed node =>
      simp only [encodePositive] at hencode
      split at hencode
      · contradiction
      · injection hencode with hencode
        subst literal
        simp_all [TModel.evalL, TModel.evalT, encodeVariable, Interp.satAtom, Interp.satLit,
          htInterp]
  | role role source target =>
      injection hencode with hencode
      subst literal
      rfl
  | exists_ role filler node => simp [encodePositive] at hencode
  | eq left right =>
      injection hencode with hencode
      subst literal
      rfl

theorem eval_negative_iff (model : TModel Domain)
    (assignment : Int → Domain) (atom : Atom Nat Nat Nat)
    (literal : FLit) (hencode : encodeNegative atom = some literal) :
    model.evalL assignment literal ↔
      ¬(htInterp model).satAtom (fun index => assignment (Int.ofNat index)) atom := by
  cases atom with
  | concept signed node =>
      simp only [encodeNegative] at hencode
      split at hencode
      · injection hencode with hencode
        subst literal
        simp_all [TModel.evalL, TModel.evalT, encodeVariable, Interp.satAtom, Interp.satLit,
          htInterp]
      · contradiction
  | role role source target => simp [encodeNegative] at hencode
  | exists_ role filler node => simp [encodeNegative] at hencode
  | eq left right => simp [encodeNegative] at hencode

private theorem filterMap_mem {α β : Type} {f : α → Option β}
    {items : List α} {value : β} :
    value ∈ items.filterMap f ↔ ∃ item ∈ items, f item = some value := by
  induction items with
  | nil => simp
  | cons item items ih =>
      cases h : f item <;> simp [List.filterMap, h, ih, eq_comm]

/-- Signed direct HT clauses and their proper-term encodings have exactly the
same truth condition in corresponding interpretations. -/
theorem modelsClause_encode_iff (model : TModel Domain)
    (clause : Hypertableau.Clause Nat Nat Nat)
    (hdirect : Direct clause) :
    valid model (encodeClause clause) ↔
      (htInterp model).modelsClause clause := by
  constructor
  · intro hvalid environment hbody
    classical
    let assignment : Int → Domain := fun index =>
      match index with
      | .ofNat index => environment index
      | .negSucc _ => environment 0
    by_contra hsourceHead
    push Not at hsourceHead
    have hencodedBody : ∀ literal ∈ (encodeClause clause).body,
        model.evalL assignment literal := by
      intro literal hliteral
      simp only [encodeClause, List.mem_append] at hliteral
      rcases hliteral with hliteral | hliteral
      · rcases filterMap_mem.mp hliteral with ⟨atom, hatom, hencode⟩
        exact (eval_positive_iff model assignment atom literal hencode).2
          (by simpa [assignment] using hbody atom hatom)
      · rcases filterMap_mem.mp hliteral with ⟨atom, hatom, hencode⟩
        exact (eval_negative_iff model assignment atom literal hencode).2
          (by simpa [assignment] using hsourceHead atom hatom)
    rcases hvalid assignment hencodedBody with ⟨literal, hliteral, hlit⟩
    simp only [encodeClause, List.mem_append] at hliteral
    rcases hliteral with hliteral | hliteral
    · rcases filterMap_mem.mp hliteral with ⟨atom, hatom, hencode⟩
      exact hsourceHead atom hatom (by simpa [assignment] using
        (eval_positive_iff model assignment atom literal hencode).1 hlit)
    · rcases filterMap_mem.mp hliteral with ⟨atom, hatom, hencode⟩
      exact ((eval_negative_iff model assignment atom literal hencode).1 hlit)
        (by simpa [assignment] using hbody atom hatom)
  · intro hmodels assignment hencodedBody
    classical
    let environment : Nat → Domain := fun index => assignment (Int.ofNat index)
    by_contra hencodedHead
    push Not at hencodedHead
    have hsourceBody : ∀ atom ∈ clause.body,
        (htInterp model).satAtom environment atom := by
      intro atom hatom
      have hdirectAtom : directAtom atom = true :=
        hdirect atom (List.mem_append.mpr (Or.inl hatom))
      rcases directAtom_no_exists atom hdirectAtom with
        ⟨literal, hpositive | hnegative⟩
      · exact (eval_positive_iff model assignment atom literal hpositive).1
          (hencodedBody literal (by
            simp only [encodeClause, List.mem_append]
            exact Or.inl (filterMap_mem.mpr ⟨atom, hatom, hpositive⟩)))
      · by_contra hsat
        exact hencodedHead literal (by
          simp only [encodeClause, List.mem_append]
          exact Or.inr (filterMap_mem.mpr ⟨atom, hatom, hnegative⟩))
          ((eval_negative_iff model assignment atom literal hnegative).2 hsat)
    rcases hmodels environment hsourceBody with ⟨atom, hatom, hsat⟩
    have hdirectAtom : directAtom atom = true :=
      hdirect atom (List.mem_append.mpr (Or.inr hatom))
    rcases directAtom_no_exists atom hdirectAtom with
      ⟨literal, hpositive | hnegative⟩
    · exact hencodedHead literal (by
        simp only [encodeClause, List.mem_append]
        exact Or.inl (filterMap_mem.mpr ⟨atom, hatom, hpositive⟩))
        ((eval_positive_iff model assignment atom literal hpositive).2 hsat)
    · exact ((eval_negative_iff model assignment atom literal hnegative).1
        (hencodedBody literal (by
          simp only [encodeClause, List.mem_append]
          exact Or.inr (filterMap_mem.mpr ⟨atom, hatom, hnegative⟩)))) hsat

def DirectOntology (ontology : List (Hypertableau.Clause Nat Nat Nat)) : Prop :=
  ∀ clause ∈ ontology, Direct clause

theorem models_encode_iff (model : TModel Domain)
    (ontology : List (Hypertableau.Clause Nat Nat Nat))
    (hdirect : DirectOntology ontology) :
    (∀ clause ∈ ontology, valid model (encodeClause clause)) ↔
      (htInterp model).models ontology := by
  constructor <;> intro hmodels clause hclause
  · exact (modelsClause_encode_iff model clause (hdirect clause hclause)).1
      (hmodels clause hclause)
  · exact (modelsClause_encode_iff model clause (hdirect clause hclause)).2
      (hmodels clause hclause)

def CommonEntailsSub (ontology : List (Hypertableau.Clause Nat Nat Nat))
    (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ ontology, valid model (encodeClause clause)) →
      ∀ value, model.conc sub value → model.conc sup value

def CommonUnsatisfiableConcept
    (ontology : List (Hypertableau.Clause Nat Nat Nat))
    (concept : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ ontology, valid model (encodeClause clause)) →
      ∀ value, ¬model.conc concept value

/-- Whole-taxonomy entailment is unchanged by signed direct normalization into
the common proper-term source. -/
theorem entailsSub_encode_iff
    (ontology : List (Hypertableau.Clause Nat Nat Nat))
    (hdirect : DirectOntology ontology) (sub sup : Nat) :
    CommonEntailsSub ontology sub sup ↔
      Hypertableau.EntailsSub ontology sub sup := by
  constructor
  · intro hcommon Domain interpretation hmodels value hsub
    letI : Nonempty Domain := ⟨value⟩
    let model := checkerModel interpretation
    apply hcommon Domain model
    · exact (models_encode_iff model ontology hdirect).2 (by
        simpa [model, htInterp, checkerModel] using hmodels)
    · exact hsub
  · intro hht Domain model hmodels value hsub
    exact hht Domain (htInterp model)
      ((models_encode_iff model ontology hdirect).1 hmodels) value hsub

theorem unsatisfiableConcept_encode_iff
    (ontology : List (Hypertableau.Clause Nat Nat Nat))
    (hdirect : DirectOntology ontology) (concept : Nat) :
    CommonUnsatisfiableConcept ontology concept ↔
      Hypertableau.UnsatisfiableConcept ontology concept := by
  constructor
  · intro hcommon Domain interpretation hmodels value hconcept
    letI : Nonempty Domain := ⟨value⟩
    let model := checkerModel interpretation
    apply hcommon Domain model
    · exact (models_encode_iff model ontology hdirect).2 (by
        simpa [model, htInterp, checkerModel] using hmodels)
    · exact hconcept
  · intro hht Domain model hmodels value hconcept
    exact hht Domain (htInterp model)
      ((models_encode_iff model ontology hdirect).1 hmodels) value hconcept

#print axioms modelsClause_encode_iff
#print axioms models_encode_iff
#print axioms entailsSub_encode_iff
#print axioms unsatisfiableConcept_encode_iff

end ContextCalculus.HTCheckerTermEmbedding
