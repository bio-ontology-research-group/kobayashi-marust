import ContextCalculus.CBEqEncoding

/-!
# Exact role-chain encoding for CB nested terms

This module extends the equational source semantics with arbitrary finite role
chains. Transitivity is the special chain `R ∘ R ⊑ R`. The encoding uses one
universally quantified variable per path position and one role atom per chain
edge, exactly matching the first-order semantics of an OWL property chain.
-/

namespace ContextCalculus.CBRoleChainEncoding

open ContextCalculus CheckerTerm Eqv

/-- A normalized role-chain inclusion `body₀ ∘ ... ∘ bodyₙ₋₁ ⊑ sup`. -/
structure RoleChain (Role : Type) where
  body : List Role
  sup : Role
deriving DecidableEq, Repr

/-- Values along a chain path. The premise contains one edge for every role in
    the chain and the conclusion contains the corresponding super-role edge. -/
def satChain {D Role : Type} (interpretation : Role → D → D → Prop)
    (chain : RoleChain Role) : Prop :=
  ∀ values : Fin (chain.body.length + 1) → D,
    (∀ i : Fin chain.body.length,
      interpretation (chain.body.get i)
        (values ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (values ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)) →
    interpretation chain.sup (values ⟨0, Nat.zero_lt_succ _⟩)
      (values ⟨chain.body.length, Nat.lt_succ_self _⟩)

structure SourceOntology (Concept Role Individual : Type) where
  clauses : Eqv.Ontology Concept Role Individual
  chains : List (RoleChain Role)

def models {D Concept Role Individual : Type}
    (interpretation : Eqv.Interp D Concept Role Individual)
    (source : SourceOntology Concept Role Individual) : Prop :=
  Eqv.models interpretation source.clauses ∧
    ∀ chain ∈ source.chains, satChain interpretation.r chain

private def node (index : Nat) : FTerm :=
  .var (-(Int.ofNat index))

private abbrev rol (role : Fin roleCount) (source target : FTerm) : FLit :=
  CBALCEncoding.rol role source target

private def chainBody (chain : RoleChain (Fin roleCount)) : List FLit :=
  List.ofFn fun i : Fin chain.body.length =>
    rol (chain.body.get i) (node i.val) (node (i.val + 1))

def encodeChain (chain : RoleChain (Fin roleCount)) : FCL :=
  ⟨chainBody chain,
    [rol chain.sup (node 0) (node chain.body.length)]⟩

def encode
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    List FCL :=
  CBEqEncoding.encode source.clauses ++ source.chains.map encodeChain

private def chainAssignment {length : Nat}
    (values : Fin (length + 1) → D) (id : Int) : D :=
  if h : id.natAbs < length + 1 then values ⟨id.natAbs, h⟩
  else values ⟨0, Nat.zero_lt_succ _⟩

@[simp] private theorem chainAssignment_node {length : Nat}
    (values : Fin (length + 1) → D) (index : Nat) (hindex : index < length + 1) :
    chainAssignment values (-(Int.ofNat index)) = values ⟨index, hindex⟩ := by
  rw [chainAssignment, dif_pos (by simpa using hindex)]
  apply congrArg values
  apply Fin.ext
  simp

private theorem mem_chainBody {chain : RoleChain (Fin roleCount)} {literal : FLit} :
    literal ∈ chainBody chain ↔
      ∃ i : Fin chain.body.length,
        literal = rol (chain.body.get i) (node i.val) (node (i.val + 1)) := by
  simpa only [chainBody, List.mem_ofFn, eq_comm]

theorem valid_encodeChain_iff (model : TModel D)
    (chain : RoleChain (Fin roleCount)) :
    valid model (encodeChain chain) ↔
      satChain (fun role => model.rol role.val) chain := by
  constructor
  · intro hvalid values hedges
    let assignment : Int → D := chainAssignment values
    rcases hvalid assignment (by
      intro literal hliteral
      change literal ∈ chainBody chain at hliteral
      rw [mem_chainBody] at hliteral
      rcases hliteral with ⟨i, rfl⟩
      change model.rol (chain.body.get i).val
        (chainAssignment values (-(Int.ofNat i.val)))
        (chainAssignment values (-(Int.ofNat (i.val + 1))))
      rw [chainAssignment_node values i.val (Nat.lt_succ_of_lt i.isLt),
        chainAssignment_node values (i.val + 1) (Nat.add_lt_add_right i.isLt 1)]
      exact hedges i) with
      ⟨literal, hliteral, htrue⟩
    simp only [encodeChain, List.mem_singleton] at hliteral
    subst literal
    change model.rol chain.sup.val
      (chainAssignment values (-(Int.ofNat 0)))
      (chainAssignment values (-(Int.ofNat chain.body.length))) at htrue
    rw [chainAssignment_node values 0 (Nat.zero_lt_succ _),
      chainAssignment_node values chain.body.length (Nat.lt_succ_self _)] at htrue
    exact htrue
  · intro hsemantic assignment hbody
    let values : Fin (chain.body.length + 1) → D :=
      fun i => assignment (-(Int.ofNat i.val))
    refine ⟨rol chain.sup (node 0) (node chain.body.length), by simp [encodeChain], ?_⟩
    exact hsemantic values (by
      intro i
      exact hbody
        (rol (chain.body.get i) (node i.val) (node (i.val + 1)))
        (mem_chainBody.mpr ⟨i, rfl⟩))

def restrictModel (model : TModel D) :
    Eqv.Interp D (Fin conceptCount) (Fin roleCount) (Fin individualCount) :=
  CBEqEncoding.restrictModel model

theorem models_restrict
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (model : TModel D) (hmodels : ∀ clause ∈ encode source, valid model clause) :
    models (restrictModel model) source := by
  constructor
  · apply CBEqEncoding.models_restrict source.clauses model
    intro clause hclause
    exact hmodels clause (by simp [encode, hclause])
  · intro chain hchain
    apply (valid_encodeChain_iff model chain).1
    exact hmodels (encodeChain chain) (by
      simp only [encode, List.mem_append, List.mem_map]
      exact Or.inr ⟨chain, hchain, rfl⟩)

noncomputable def extendModel
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : models interpretation source) (default : D) : TModel D :=
  CBEqEncoding.extendModel source.clauses interpretation hmodels.1 default

theorem models_extend
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : models interpretation source) (default : D) :
    ∀ clause ∈ encode source,
      valid (extendModel source interpretation hmodels default) clause := by
  intro clause hclause
  simp only [encode, List.mem_append, List.mem_map] at hclause
  rcases hclause with hbase | ⟨chain, hchain, rfl⟩
  · exact CBEqEncoding.models_extend source.clauses interpretation hmodels.1 default
      clause hbase
  · apply (valid_encodeChain_iff
      (extendModel source interpretation hmodels default) chain).2
    intro values hedges
    have hchainSemantic := hmodels.2 chain hchain
    have hresult := hchainSemantic values (by
      intro i
      simpa [extendModel, CBEqEncoding.extendModel, (chain.body.get i).isLt] using
        hedges i)
    simpa [extendModel, CBEqEncoding.extendModel, chain.sup.isLt] using hresult

def EntailsSub
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (sub sup : Fin conceptCount) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ encode source, valid model clause) →
      ∀ element, model.conc sub.val element → model.conc sup.val element

theorem entailsSub_iff_source
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (sub sup : Fin conceptCount) :
    EntailsSub source sub sup ↔
      ∀ (D : Type)
        (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
          (Fin individualCount)),
        models interpretation source → ∀ element,
          interpretation.c sub element → interpretation.c sup element := by
  constructor
  · intro hentails D interpretation hmodels element hsub
    let model := extendModel source interpretation hmodels element
    have hsup := hentails D model
      (models_extend source interpretation hmodels element) element
      (by simpa [model, extendModel, CBEqEncoding.extendModel, sub.isLt] using hsub)
    simpa [model, extendModel, CBEqEncoding.extendModel, sup.isLt] using hsup
  · intro hentails D model hmodels element hsub
    exact hentails D (restrictModel model) (models_restrict source model hmodels)
      element hsub

def SourceSatisfiable
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    Prop :=
  ∃ (D : Type) (_ : Nonempty D)
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount)),
    models interpretation source

def EncodedSatisfiable
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    Prop :=
  ∃ (D : Type) (model : TModel D),
    ∀ clause ∈ encode source, valid model clause

theorem satisfiable_iff_source
    (source : SourceOntology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    EncodedSatisfiable source ↔ SourceSatisfiable source := by
  constructor
  · rintro ⟨D, model, hmodel⟩
    exact ⟨D, ⟨model.const 0⟩, restrictModel model,
      models_restrict source model hmodel⟩
  · rintro ⟨D, hnonempty, interpretation, hmodel⟩
    let default : D := Classical.choice hnonempty
    exact ⟨D, extendModel source interpretation hmodel default,
      models_extend source interpretation hmodel default⟩

/-- The ordinary semantic form of role transitivity. -/
def TransitiveRole {D Role : Type} (interpretation : Role → D → D → Prop)
    (role : Role) : Prop :=
  ∀ first middle last, interpretation role first middle →
    interpretation role middle last → interpretation role first last

def transitiveChain (role : Role) : RoleChain Role :=
  ⟨[role, role], role⟩

/-- The `R ∘ R ⊑ R` chain is exactly transitivity, not an approximation. -/
theorem satChain_transitiveChain_iff {D Role : Type}
    (interpretation : Role → D → D → Prop) (role : Role) :
    satChain interpretation (transitiveChain role) ↔
      TransitiveRole interpretation role := by
  constructor
  · intro h first middle last hfirst hlast
    let values : Fin 3 → D := ![first, middle, last]
    apply h values
    intro i
    fin_cases i <;> simp [transitiveChain, values, hfirst, hlast]
  · intro h values hedges
    apply h (values 0) (values 1) (values 2)
    · simpa [transitiveChain] using
        hedges ⟨0, by simp [transitiveChain]⟩
    · simpa [transitiveChain] using
        hedges ⟨1, by simp [transitiveChain]⟩

#print axioms valid_encodeChain_iff
#print axioms models_restrict
#print axioms models_extend
#print axioms entailsSub_iff_source
#print axioms satisfiable_iff_source
#print axioms satChain_transitiveChain_iff

end ContextCalculus.CBRoleChainEncoding
