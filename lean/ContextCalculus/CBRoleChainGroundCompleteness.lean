import ContextCalculus.CBGroundEqualityBridge
import ContextCalculus.CBRoleChainEncoding

/-!
# Finite ground completeness with arbitrary role chains

`CompletenessEq` supplies the congruence-quotient model for every normalized CB
source constructor except arbitrary role chains. This module extends its
concrete finite grounder with every path instance of every chain and proves that
the same quotient model satisfies those chains. The resulting completeness
theorem covers the complete typed source language accepted by `CBSourceWire`.
-/

namespace ContextCalculus.CBRoleChainGroundCompleteness

open ContextCalculus PropRes Eqv CBRoleChainEncoding

variable {CN RN T : Type} [DecidableEq CN] [DecidableEq RN] [DecidableEq T]

def chainGroundBody (chain : RoleChain RN)
    (values : Fin (chain.body.length + 1) → T) : List (GAtom CN RN T) :=
  List.ofFn fun index : Fin chain.body.length =>
    .rol (chain.body.get index)
      (values ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩)
      (values ⟨index.val + 1, Nat.add_lt_add_right index.isLt 1⟩)

def chainGroundClause (chain : RoleChain RN)
    (values : Fin (chain.body.length + 1) → T) :
    PClause (GAtom CN RN T) :=
  clImp (chainGroundBody chain values)
    [.rol chain.sup
      (values ⟨0, Nat.zero_lt_succ _⟩)
      (values ⟨chain.body.length, Nat.lt_succ_self _⟩)]

theorem mem_chainGroundBody_iff {chain : RoleChain RN}
    {values : Fin (chain.body.length + 1) → T} {atom : GAtom CN RN T} :
    atom ∈ chainGroundBody chain values ↔
      ∃ index : Fin chain.body.length,
        atom = .rol (chain.body.get index)
          (values ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩)
          (values ⟨index.val + 1, Nat.add_lt_add_right index.isLt 1⟩) := by
  simp [chainGroundBody, eq_comm]

section Finite

variable [Fintype T] [Fintype CN] [Fintype RN]

def chainInsts (chain : RoleChain RN) : Finset (PClause (GAtom CN RN T)) :=
  Finset.univ.image (chainGroundClause chain)

def chainsGround (chains : List (RoleChain RN)) :
    Finset (PClause (GAtom CN RN T)) :=
  (chains.map chainInsts).foldr (· ∪ ·) ∅

def roleAxiomGroundClause (roleAxiom : RoleAxiom RN) (values : Fin 3 → T) :
    PClause (GAtom CN RN T) :=
  match roleAxiom with
  | .symmetric role => clImp [.rol role (values 0) (values 1)]
      [.rol role (values 1) (values 0)]
  | .asymmetric role => clImp
      [.rol role (values 0) (values 1), .rol role (values 1) (values 0)] []
  | .reflexive role => clImp [] [.rol role (values 0) (values 0)]
  | .irreflexive role => clImp [.rol role (values 0) (values 0)] []
  | .inverseFunctional role => clImp
      [.rol role (values 1) (values 0), .rol role (values 2) (values 0)]
      [.eqa (values 1) (values 2)]
  | .disjoint left right => clImp
      [.rol left (values 0) (values 1), .rol right (values 0) (values 1)] []

def roleAxiomInsts (roleAxiom : RoleAxiom RN) :
    Finset (PClause (GAtom CN RN T)) :=
  Finset.univ.image (roleAxiomGroundClause roleAxiom)

def roleAxiomsGround (roleAxioms : List (RoleAxiom RN)) :
    Finset (PClause (GAtom CN RN T)) :=
  (roleAxioms.map roleAxiomInsts).foldr (· ∪ ·) ∅

def groundSource (wit : CN → RN → CN → T → T)
    (source : SourceOntology CN RN T) :
    Finset (PClause (GAtom CN RN T)) :=
  (Eqv.ground wit source.clauses ∪ chainsGround source.chains) ∪
    roleAxiomsGround source.roleAxioms

theorem mem_chainsGround {chain : RoleChain RN} {chains : List (RoleChain RN)}
    (hchain : chain ∈ chains) :
    chainInsts (CN := CN) (T := T) chain ⊆
      chainsGround (CN := CN) (T := T) chains := by
  induction chains with
  | nil => simp at hchain
  | cons first rest ih =>
      rw [List.mem_cons] at hchain
      simp only [chainsGround, List.map_cons, List.foldr_cons]
      rcases hchain with rfl | hrest
      · exact Finset.subset_union_left
      · exact (ih hrest).trans Finset.subset_union_right

theorem mem_groundSource_base {wit : CN → RN → CN → T → T}
    {source : SourceOntology CN RN T} {clause : PClause (GAtom CN RN T)}
    (hclause : clause ∈ Eqv.ground wit source.clauses) :
    clause ∈ groundSource wit source :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hclause)))

theorem mem_groundSource_chain {wit : CN → RN → CN → T → T}
    {source : SourceOntology CN RN T} {chain : RoleChain RN}
    (hchain : chain ∈ source.chains)
    (values : Fin (chain.body.length + 1) → T) :
    chainGroundClause chain values ∈ groundSource wit source := by
  apply Finset.mem_union.mpr
  apply Or.inl
  apply Finset.mem_union.mpr
  apply Or.inr
  apply mem_chainsGround hchain
  exact Finset.mem_image_of_mem _ (Finset.mem_univ values)

theorem mem_roleAxiomsGround {roleAxiom : RoleAxiom RN}
    {roleAxioms : List (RoleAxiom RN)} (hroleAxiom : roleAxiom ∈ roleAxioms) :
    roleAxiomInsts (CN := CN) (T := T) roleAxiom ⊆
      roleAxiomsGround (CN := CN) (T := T) roleAxioms := by
  induction roleAxioms with
  | nil => simp at hroleAxiom
  | cons first rest ih =>
      rw [List.mem_cons] at hroleAxiom
      simp only [roleAxiomsGround, List.map_cons, List.foldr_cons]
      rcases hroleAxiom with rfl | hrest
      · exact Finset.subset_union_left
      · exact (ih hrest).trans Finset.subset_union_right

theorem mem_groundSource_roleAxiom {wit : CN → RN → CN → T → T}
    {source : SourceOntology CN RN T} {roleAxiom : RoleAxiom RN}
    (hroleAxiom : roleAxiom ∈ source.roleAxioms) (values : Fin 3 → T) :
    roleAxiomGroundClause roleAxiom values ∈ groundSource wit source := by
  apply Finset.mem_union.mpr
  apply Or.inr
  apply mem_roleAxiomsGround hroleAxiom
  exact Finset.mem_image_of_mem _ (Finset.mem_univ values)

theorem quotient_satisfies_chain
    {valuation : GAtom CN RN T → Prop} (respects : RespectsEq valuation)
    {G : Finset (PClause (GAtom CN RN T))}
    (hmodels : ∀ clause ∈ G, clause.sat valuation)
    (chain : RoleChain RN)
    (hinstances : ∀ values : Fin (chain.body.length + 1) → T,
      chainGroundClause chain values ∈ G) :
    satChain (congruenceModel valuation respects).r chain := by
  intro quotientValues hedges
  have hrepresentative : ∀ index, ∃ term : T,
      Quotient.mk _ term = quotientValues index := fun index =>
    Quotient.exists_rep (quotientValues index)
  choose values hvalues using hrepresentative
  have hbody : ∀ atom ∈ chainGroundBody chain values, valuation atom := by
    intro atom hatom
    rw [mem_chainGroundBody_iff] at hatom
    obtain ⟨index, rfl⟩ := hatom
    have hedge := hedges index
    rw [← hvalues ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩,
      ← hvalues ⟨index.val + 1, Nat.add_lt_add_right index.isLt 1⟩] at hedge
    exact hedge
  obtain ⟨atom, hatom, htrue⟩ :=
    Eqv.useClause hmodels (hinstances values) hbody
  simp only [List.mem_singleton] at hatom
  subst atom
  rw [← hvalues ⟨0, Nat.zero_lt_succ _⟩,
    ← hvalues ⟨chain.body.length, Nat.lt_succ_self _⟩]
  exact htrue

theorem quotient_satisfies_roleAxiom
    {valuation : GAtom CN RN T → Prop} (respects : RespectsEq valuation)
    {G : Finset (PClause (GAtom CN RN T))}
    (hmodels : ∀ clause ∈ G, clause.sat valuation)
    (roleAxiom : RoleAxiom RN)
    (hinstances : ∀ values : Fin 3 → T,
      roleAxiomGroundClause roleAxiom values ∈ G) :
    satRoleAxiom (congruenceModel valuation respects).r roleAxiom := by
  cases roleAxiom with
  | symmetric role =>
      intro first second hedge
      obtain ⟨x, rfl⟩ := Quotient.exists_rep first
      obtain ⟨y, rfl⟩ := Quotient.exists_rep second
      let values : Fin 3 → T := ![x, y, x]
      obtain ⟨atom, hatom, htrue⟩ := Eqv.useClause hmodels
        (hinstances values) (by
          intro atom hatom
          simp only [roleAxiomGroundClause, List.mem_singleton] at hatom
          subst atom
          exact hedge)
      simp only [roleAxiomGroundClause, List.mem_singleton] at hatom
      subst atom
      exact htrue
  | asymmetric role =>
      intro first second hforward hbackward
      obtain ⟨x, rfl⟩ := Quotient.exists_rep first
      obtain ⟨y, rfl⟩ := Quotient.exists_rep second
      let values : Fin 3 → T := ![x, y, x]
      obtain ⟨atom, hatom, _⟩ := Eqv.useClause hmodels
        (hinstances values) (by
          intro atom hatom
          simp only [roleAxiomGroundClause, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false] at hatom
          rcases hatom with rfl | rfl
          · exact hforward
          · exact hbackward)
      simp only [roleAxiomGroundClause, List.not_mem_nil] at hatom
  | reflexive role =>
      intro first
      obtain ⟨x, rfl⟩ := Quotient.exists_rep first
      let values : Fin 3 → T := ![x, x, x]
      obtain ⟨atom, hatom, htrue⟩ := Eqv.useClause hmodels
        (hinstances values) (by
          intro atom hatom
          simp only [roleAxiomGroundClause, List.not_mem_nil] at hatom)
      simp only [roleAxiomGroundClause, List.mem_singleton] at hatom
      subst atom
      exact htrue
  | irreflexive role =>
      intro first hreflexive
      obtain ⟨x, rfl⟩ := Quotient.exists_rep first
      let values : Fin 3 → T := ![x, x, x]
      obtain ⟨atom, hatom, _⟩ := Eqv.useClause hmodels
        (hinstances values) (by
          intro atom hatom
          simp only [roleAxiomGroundClause, List.mem_singleton] at hatom
          subst atom
          exact hreflexive)
      simp only [roleAxiomGroundClause, List.not_mem_nil] at hatom
  | inverseFunctional role =>
      intro target first second hfirst hsecond
      obtain ⟨x, rfl⟩ := Quotient.exists_rep target
      obtain ⟨y, rfl⟩ := Quotient.exists_rep first
      obtain ⟨z, rfl⟩ := Quotient.exists_rep second
      let values : Fin 3 → T := ![x, y, z]
      obtain ⟨atom, hatom, htrue⟩ := Eqv.useClause hmodels
        (hinstances values) (by
          intro atom hatom
          simp only [roleAxiomGroundClause, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false] at hatom
          rcases hatom with rfl | rfl
          · exact hfirst
          · exact hsecond)
      simp only [roleAxiomGroundClause, List.mem_singleton] at hatom
      subst atom
      exact Quotient.sound htrue
  | disjoint left right =>
      intro source target hleft hright
      obtain ⟨x, rfl⟩ := Quotient.exists_rep source
      obtain ⟨y, rfl⟩ := Quotient.exists_rep target
      let values : Fin 3 → T := ![x, y, x]
      obtain ⟨atom, hatom, _⟩ := Eqv.useClause hmodels
        (hinstances values) (by
          intro atom hatom
          simp only [roleAxiomGroundClause, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false] at hatom
          rcases hatom with rfl | rfl
          · exact hleft
          · exact hright)
      simp only [roleAxiomGroundClause, List.not_mem_nil] at hatom

theorem quotient_models_source
    {valuation : GAtom CN RN T → Prop}
    {wit : CN → RN → CN → T → T}
    {source : SourceOntology CN RN T}
    (hmodels : ∀ clause ∈ groundSource wit source, clause.sat valuation) :
    let respects := Eqv.respectsEq_of_grounds
      (fun clause hclause => hmodels clause (mem_groundSource_base hclause))
      (Eqv.grounds_ground wit source.clauses)
    CBRoleChainEncoding.models (Eqv.congruenceModel valuation respects) source := by
  let hbase : ∀ clause ∈ Eqv.ground wit source.clauses, clause.sat valuation :=
    fun clause hclause => hmodels clause (mem_groundSource_base hclause)
  let respects := Eqv.respectsEq_of_grounds hbase
    (Eqv.grounds_ground wit source.clauses)
  constructor
  · exact Eqv.congruenceModel_models respects hbase
      (Eqv.grounds_ground wit source.clauses)
  · constructor
    · intro chain hchain
      exact quotient_satisfies_chain respects hmodels chain
        (fun values => mem_groundSource_chain hchain values)
    · intro roleAxiom hroleAxiom
      exact quotient_satisfies_roleAxiom respects hmodels roleAxiom
        (fun values => mem_groundSource_roleAxiom hroleAxiom values)

theorem source_complete_ground
    (wit : CN → RN → CN → T → T)
    (source : SourceOntology CN RN T)
    (hclash : ¬ PropRes.Derivable (groundSource wit source) PClause.bot) :
    ∃ (D : Type) (interpretation : Interp D CN RN T),
      CBRoleChainEncoding.models interpretation source := by
  have hsatisfiable : ∃ valuation : GAtom CN RN T → Prop,
      ∀ clause ∈ groundSource wit source, clause.sat valuation := by
    by_contra hunsat
    exact hclash (PropRes.completeness (groundSource wit source) hunsat)
  obtain ⟨valuation, hmodels⟩ := hsatisfiable
  let hbase : ∀ clause ∈ Eqv.ground wit source.clauses, clause.sat valuation :=
    fun clause hclause => hmodels clause (mem_groundSource_base hclause)
  let respects := Eqv.respectsEq_of_grounds hbase
    (Eqv.grounds_ground wit source.clauses)
  exact ⟨Eqv.QDom valuation respects, Eqv.congruenceModel valuation respects,
    quotient_models_source hmodels⟩

#print axioms quotient_satisfies_chain
#print axioms quotient_models_source
#print axioms source_complete_ground

end Finite

end ContextCalculus.CBRoleChainGroundCompleteness
