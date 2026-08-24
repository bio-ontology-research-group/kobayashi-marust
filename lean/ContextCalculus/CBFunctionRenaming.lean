import ContextCalculus.CheckerTerm

/-!
# Injective Skolem-function allocation for CB preprocessing

The semantic source encoding numbers existential witnesses canonically, while
the Rust frontend interns generated functions in its own namespace.  This file
proves that replacing every canonical function id by an injective production
id preserves the complete model class and therefore every named-concept
subsumption.  A later wire checker can validate the finite allocation table
instead of requiring production ids to equal source-clause positions.
-/

namespace ContextCalculus.CBFunctionRenaming

open ContextCalculus CheckerTerm

def renameTerm (allocation : Nat → Nat) : FTerm → FTerm
  | .var id => .var id
  | .const individual => .const individual
  | .app function argument => .app (allocation function) (renameTerm allocation argument)

def renamePred (allocation : Nat → Nat) : FPred → FPred
  | .concept concept term => .concept concept (renameTerm allocation term)
  | .role role source target =>
      .role role (renameTerm allocation source) (renameTerm allocation target)

def renameLiteral (allocation : Nat → Nat) : FLit → FLit
  | .P predicate => .P (renamePred allocation predicate)
  | .eq left right => .eq (renameTerm allocation left) (renameTerm allocation right)
  | .ineq left right => .ineq (renameTerm allocation left) (renameTerm allocation right)

def renameClause (allocation : Nat → Nat) (clause : FCL) : FCL where
  body := clause.body.map (renameLiteral allocation)
  head := clause.head.map (renameLiteral allocation)

def renameOntology (allocation : Nat → Nat) (ontology : List FCL) : List FCL :=
  ontology.map (renameClause allocation)

@[simp] theorem renameTerm_id (term : FTerm) : renameTerm id term = term := by
  induction term with
  | var => rfl
  | const => rfl
  | app function argument ih => simp [renameTerm, ih]

@[simp] theorem renamePred_id (predicate : FPred) : renamePred id predicate = predicate := by
  cases predicate <;> simp [renamePred]

@[simp] theorem renameLiteral_id (literal : FLit) : renameLiteral id literal = literal := by
  cases literal <;> simp [renameLiteral]

private theorem map_renameLiteral_id (literals : List FLit) :
    literals.map (renameLiteral id) = literals := by
  induction literals with
  | nil => rfl
  | cons literal rest ih => rw [List.map_cons, renameLiteral_id, ih]

@[simp] theorem renameClause_id (clause : FCL) : renameClause id clause = clause := by
  cases clause with
  | mk body head =>
      simp only [renameClause]
      rw [map_renameLiteral_id, map_renameLiteral_id]

@[simp] theorem renameOntology_id (ontology : List FCL) :
    renameOntology id ontology = ontology := by
  induction ontology with
  | nil => rfl
  | cons clause rest ih =>
      simp only [renameOntology] at ih ⊢
      rw [List.map_cons, renameClause_id, ih]

/-- Restrict a model over production function ids to canonical source ids. -/
def pullbackModel (allocation : Nat → Nat) (model : TModel D) : TModel D where
  conc := model.conc
  rol := model.rol
  const := model.const
  fn function := model.fn (allocation function)

@[simp] theorem evalTerm_pullback (allocation : Nat → Nat) (model : TModel D)
    (assignment : Int → D) (term : FTerm) :
    (pullbackModel allocation model).evalT assignment term =
      model.evalT assignment (renameTerm allocation term) := by
  induction term with
  | var id => rfl
  | const individual => rfl
  | app function argument ih =>
      change model.fn (allocation function)
          ((pullbackModel allocation model).evalT assignment argument) =
        model.fn (allocation function)
          (model.evalT assignment (renameTerm allocation argument))
      rw [ih]

@[simp] theorem evalLiteral_pullback (allocation : Nat → Nat) (model : TModel D)
    (assignment : Int → D) (literal : FLit) :
    (pullbackModel allocation model).evalL assignment literal ↔
      model.evalL assignment (renameLiteral allocation literal) := by
  cases literal with
  | P predicate =>
      cases predicate with
      | concept concept term =>
          change model.conc concept
              ((pullbackModel allocation model).evalT assignment term) ↔
            model.conc concept
              (model.evalT assignment (renameTerm allocation term))
          rw [evalTerm_pullback]
      | role role source target =>
          change model.rol role
              ((pullbackModel allocation model).evalT assignment source)
              ((pullbackModel allocation model).evalT assignment target) ↔
            model.rol role
              (model.evalT assignment (renameTerm allocation source))
              (model.evalT assignment (renameTerm allocation target))
          rw [evalTerm_pullback, evalTerm_pullback]
  | eq left right =>
      change (pullbackModel allocation model).evalT assignment left =
          (pullbackModel allocation model).evalT assignment right ↔
        model.evalT assignment (renameTerm allocation left) =
          model.evalT assignment (renameTerm allocation right)
      rw [evalTerm_pullback, evalTerm_pullback]
  | ineq left right =>
      change (pullbackModel allocation model).evalT assignment left ≠
          (pullbackModel allocation model).evalT assignment right ↔
        model.evalT assignment (renameTerm allocation left) ≠
          model.evalT assignment (renameTerm allocation right)
      rw [evalTerm_pullback, evalTerm_pullback]

theorem valid_pullback_iff (allocation : Nat → Nat) (model : TModel D)
    (clause : FCL) :
    valid (pullbackModel allocation model) clause ↔
      valid model (renameClause allocation clause) := by
  constructor
  · intro hvalid assignment hbody
    have hsourceBody : ∀ literal ∈ clause.body,
        (pullbackModel allocation model).evalL assignment literal := by
      intro literal hliteral
      exact (evalLiteral_pullback allocation model assignment literal).2
        (hbody (renameLiteral allocation literal)
          (List.mem_map.mpr ⟨literal, hliteral, rfl⟩))
    rcases hvalid assignment hsourceBody with ⟨literal, hliteral, htrue⟩
    exact ⟨renameLiteral allocation literal,
      List.mem_map.mpr ⟨literal, hliteral, rfl⟩,
      (evalLiteral_pullback allocation model assignment literal).1 htrue⟩
  · intro hvalid assignment hbody
    have htargetBody : ∀ literal ∈ (renameClause allocation clause).body,
        model.evalL assignment literal := by
      intro literal hliteral
      rcases List.mem_map.mp hliteral with ⟨source, hsource, rfl⟩
      exact (evalLiteral_pullback allocation model assignment source).1
        (hbody source hsource)
    rcases hvalid assignment htargetBody with ⟨literal, hliteral, htrue⟩
    rcases List.mem_map.mp hliteral with ⟨source, hsource, rfl⟩
    exact ⟨source, hsource,
      (evalLiteral_pullback allocation model assignment source).2 htrue⟩

/-- Extend a canonical model to all production function ids.  On an allocated
id it uses the unique canonical preimage; unallocated ids are irrelevant and
receive function zero's interpretation. -/
noncomputable def pushforwardModel (allocation : Nat → Nat) (model : TModel D) :
    TModel D := by
  classical
  exact {
    conc := model.conc
    rol := model.rol
    const := model.const
    fn := fun production =>
      if h : ∃ source, allocation source = production then
        model.fn (Classical.choose h)
      else model.fn 0 }

@[simp] theorem pushforward_fn (allocation : Nat → Nat)
    (hinjective : Function.Injective allocation) (model : TModel D) (function : Nat) :
    (pushforwardModel allocation model).fn (allocation function) = model.fn function := by
  simp only [pushforwardModel]
  have hexists : ∃ source, allocation source = allocation function := ⟨function, rfl⟩
  rw [dif_pos hexists]
  congr 1
  exact hinjective (Classical.choose_spec hexists)

@[simp] theorem evalTerm_pushforward (allocation : Nat → Nat)
    (hinjective : Function.Injective allocation) (model : TModel D)
    (assignment : Int → D) (term : FTerm) :
    (pushforwardModel allocation model).evalT assignment
        (renameTerm allocation term) = model.evalT assignment term := by
  induction term with
  | var id => rfl
  | const individual => rfl
  | app function argument ih =>
      simp [renameTerm, TModel.evalT, pushforward_fn allocation hinjective, ih]

@[simp] theorem evalLiteral_pushforward (allocation : Nat → Nat)
    (hinjective : Function.Injective allocation) (model : TModel D)
    (assignment : Int → D) (literal : FLit) :
    (pushforwardModel allocation model).evalL assignment
        (renameLiteral allocation literal) ↔ model.evalL assignment literal := by
  cases literal with
  | P predicate =>
      cases predicate with
      | concept concept term =>
          change (pushforwardModel allocation model).conc concept
              ((pushforwardModel allocation model).evalT assignment
                (renameTerm allocation term)) ↔ model.conc concept
              (model.evalT assignment term)
          rw [evalTerm_pushforward allocation hinjective]
          rfl
      | role role source target =>
          change (pushforwardModel allocation model).rol role
              ((pushforwardModel allocation model).evalT assignment
                (renameTerm allocation source))
              ((pushforwardModel allocation model).evalT assignment
                (renameTerm allocation target)) ↔
            model.rol role (model.evalT assignment source)
              (model.evalT assignment target)
          rw [evalTerm_pushforward allocation hinjective,
            evalTerm_pushforward allocation hinjective]
          rfl
  | eq left right =>
      change (pushforwardModel allocation model).evalT assignment
          (renameTerm allocation left) =
          (pushforwardModel allocation model).evalT assignment
            (renameTerm allocation right) ↔
        model.evalT assignment left = model.evalT assignment right
      rw [evalTerm_pushforward allocation hinjective,
        evalTerm_pushforward allocation hinjective]
  | ineq left right =>
      change (pushforwardModel allocation model).evalT assignment
          (renameTerm allocation left) ≠
          (pushforwardModel allocation model).evalT assignment
            (renameTerm allocation right) ↔
        model.evalT assignment left ≠ model.evalT assignment right
      rw [evalTerm_pushforward allocation hinjective,
        evalTerm_pushforward allocation hinjective]

theorem valid_pushforward_iff (allocation : Nat → Nat)
    (hinjective : Function.Injective allocation) (model : TModel D)
    (clause : FCL) :
    valid (pushforwardModel allocation model) (renameClause allocation clause) ↔
      valid model clause := by
  constructor
  · intro hvalid assignment hbody
    have htargetBody : ∀ literal ∈ (renameClause allocation clause).body,
        (pushforwardModel allocation model).evalL assignment literal := by
      intro literal hliteral
      rcases List.mem_map.mp hliteral with ⟨source, hsource, rfl⟩
      exact (evalLiteral_pushforward allocation hinjective model assignment source).2
        (hbody source hsource)
    rcases hvalid assignment htargetBody with ⟨literal, hliteral, htrue⟩
    rcases List.mem_map.mp hliteral with ⟨source, hsource, rfl⟩
    exact ⟨source, hsource,
      (evalLiteral_pushforward allocation hinjective model assignment source).1 htrue⟩
  · intro hvalid assignment hbody
    have hsourceBody : ∀ literal ∈ clause.body, model.evalL assignment literal := by
      intro literal hliteral
      exact (evalLiteral_pushforward allocation hinjective model assignment literal).1
        (hbody (renameLiteral allocation literal)
          (List.mem_map.mpr ⟨literal, hliteral, rfl⟩))
    rcases hvalid assignment hsourceBody with ⟨literal, hliteral, htrue⟩
    exact ⟨renameLiteral allocation literal,
      List.mem_map.mpr ⟨literal, hliteral, rfl⟩,
      (evalLiteral_pushforward allocation hinjective model assignment literal).2 htrue⟩

def Entails (ontology : List FCL) (sub sup : Nat) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ ontology, valid model clause) →
      ∀ element, model.conc sub element → model.conc sup element

theorem entails_rename_iff (allocation : Nat → Nat)
    (hinjective : Function.Injective allocation) (ontology : List FCL)
    (sub sup : Nat) :
    Entails (renameOntology allocation ontology) sub sup ↔
      Entails ontology sub sup := by
  constructor
  · intro hrenamed D model hmodels element hsub
    let production := pushforwardModel allocation model
    exact hrenamed D production (by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
      exact (valid_pushforward_iff allocation hinjective model source).2
        (hmodels source hsource)) element hsub
  · intro hsource D model hmodels element hsub
    let source := pullbackModel allocation model
    exact hsource D source (by
      intro clause hclause
      exact (valid_pullback_iff allocation model clause).2
        (hmodels (renameClause allocation clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))) element hsub

#print axioms valid_pullback_iff
#print axioms valid_pushforward_iff
#print axioms entails_rename_iff

end ContextCalculus.CBFunctionRenaming
