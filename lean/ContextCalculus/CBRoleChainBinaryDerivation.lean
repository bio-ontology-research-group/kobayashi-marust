import ContextCalculus.CBRegularRoleCountermodel

/-!
# Checked binary derivations for arbitrary source role chains

A derivation tree associates each source role atom with its renamed target role
and combines adjacent subpaths only through an explicitly listed binary target
chain. This lets the existing binary regular-unravelling certificate justify
an arbitrary finite source chain without trusting a preprocessing algorithm.
-/

namespace ContextCalculus.CBRoleChainBinaryDerivation

open ContextCalculus
open ContextCalculus.CBRoleChainEncoding

def Path (relation : Role → D → D → Prop) :
    List Role → D → D → Prop
  | [], source, target => source = target
  | role :: roles, source, target =>
      ∃ middle, relation role source middle ∧ Path relation roles middle target

theorem path_append_iff
    (relation : Role → D → D → Prop)
    (left right : List Role) (source target : D) :
    Path relation (left ++ right) source target ↔
      ∃ middle, Path relation left source middle ∧
        Path relation right middle target := by
  induction left generalizing source with
  | nil =>
      simp only [List.nil_append, Path]
      constructor
      · intro h
        exact ⟨source, rfl, h⟩
      · rintro ⟨middle, rfl, h⟩
        exact h
  | cons role roles ih =>
      simp only [List.cons_append, Path]
      constructor
      · rintro ⟨first, hedge, htail⟩
        rcases (ih first).1 htail with ⟨middle, hleft, hright⟩
        exact ⟨middle, ⟨first, hedge, hleft⟩, hright⟩
      · rintro ⟨middle, ⟨first, hedge, hleft⟩, hright⟩
        exact ⟨first, hedge, (ih first).2 ⟨middle, hleft, hright⟩⟩

theorem path_of_indexed_edges
    (roles : List Role) (values : Fin (roles.length + 1) → D)
    (edges : ∀ index : Fin roles.length,
      relation (roles.get index)
        (values ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩)
        (values ⟨index.val + 1, Nat.add_lt_add_right index.isLt 1⟩)) :
    Path relation roles (values ⟨0, Nat.zero_lt_succ _⟩)
      (values ⟨roles.length, Nat.lt_succ_self _⟩) := by
  induction roles with
  | nil =>
      simp only [Path]
      apply congrArg values
      apply Fin.ext
      rfl
  | cons role roles ih =>
      let tailValues : Fin (roles.length + 1) → D := fun index =>
        values ⟨index.val + 1, by simpa using Nat.add_lt_add_right index.isLt 1⟩
      refine ⟨values ⟨1, by simp⟩, ?_, ?_⟩
      · simpa using edges ⟨0, by simp⟩
      · have htail := ih tailValues (by
          intro index
          simpa [tailValues] using edges
            ⟨index.val + 1, by simpa using Nat.add_lt_add_right index.isLt 1⟩)
        simpa [tailValues] using htail

/-- A recursive path has an exact finite sequence of vertices. This is the
    converse representation needed to apply the OWL indexed-chain semantics. -/
theorem indexed_edges_of_path
    (roles : List Role) (source target : D)
    (path : Path relation roles source target) :
    ∃ values : Fin (roles.length + 1) → D,
      values ⟨0, Nat.zero_lt_succ _⟩ = source ∧
      values ⟨roles.length, Nat.lt_succ_self _⟩ = target ∧
      ∀ index : Fin roles.length,
        relation (roles.get index)
          (values ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩)
          (values ⟨index.val + 1, Nat.add_lt_add_right index.isLt 1⟩) := by
  induction roles generalizing source with
  | nil =>
      refine ⟨fun _ => source, rfl, ?_, ?_⟩
      · simpa [Path] using path
      · intro index
        exact Fin.elim0 index
  | cons role roles ih =>
      rcases path with ⟨middle, hedge, tail⟩
      rcases ih middle tail with ⟨tailValues, hstart, hend, hedges⟩
      let values : Fin ((role :: roles).length + 1) → D :=
        Fin.cases source tailValues
      refine ⟨values, ?_, ?_, ?_⟩
      · simp [values]
      · simpa [values, hend] using hend
      · intro index
        refine Fin.cases ?_ (fun tailIndex => ?_) index
        · change relation role source (tailValues ⟨0, Nat.zero_lt_succ _⟩)
          rw [hstart]
          exact hedge
        · simpa [values] using hedges tailIndex

theorem satChain_apply_path
    (chain : RoleChain Role) (hchain : satChain relation chain)
    (path : Path relation chain.body source target) :
    relation chain.sup source target := by
  rcases indexed_edges_of_path chain.body source target path with
    ⟨values, hsource, htarget, hedges⟩
  rw [← hsource, ← htarget]
  exact hchain values hedges

inductive Derivation (roleMap : SourceRole → TargetRole)
    (rules : List (CBRegularRoleCountermodel.BinaryChain TargetRole)) :
    List SourceRole → TargetRole → Prop where
  | atom (role : SourceRole) : Derivation roleMap rules [role] (roleMap role)
  | compose
      (left : Derivation roleMap rules leftBody leftRole)
      (right : Derivation roleMap rules rightBody rightRole)
      (rule : CBRegularRoleCountermodel.BinaryChain TargetRole)
      (hrule : rule ∈ rules)
      (hfirst : rule.first = leftRole)
      (hsecond : rule.second = rightRole)
      (hconclusion : rule.conclusion = resultRole) :
      Derivation roleMap rules (leftBody ++ rightBody) resultRole

theorem Derivation.weaken
    (derivation : Derivation roleMap rules body resultRole)
    (hsubset : ∀ rule, rule ∈ rules → rule ∈ largerRules) :
    Derivation roleMap largerRules body resultRole := by
  induction derivation with
  | atom role => exact .atom role
  | compose left right rule hrule hfirst hsecond hconclusion ihLeft ihRight =>
      exact .compose ihLeft ihRight rule
        (hsubset rule hrule) hfirst hsecond hconclusion

theorem Derivation.sound
    (roleMap : SourceRole → TargetRole)
    (rules : List (CBRegularRoleCountermodel.BinaryChain TargetRole))
    {body : List SourceRole} {resultRole : TargetRole}
    (derivation : Derivation roleMap rules body resultRole)
    (target : TargetRole → D → D → Prop)
    (hrules : ∀ rule ∈ rules,
      satChain target rule.toRoleChain) :
    ∀ source targetValue,
      Path (fun role => target (roleMap role)) body source targetValue →
      target resultRole source targetValue := by
  induction derivation with
  | atom role =>
      intro source targetValue hpath
      rcases hpath with ⟨middle, hedge, hequal⟩
      simpa [Path] using hequal ▸ hedge
  | compose left right rule hrule hfirst hsecond hconclusion ihLeft ihRight =>
      intro source targetValue hpath
      rcases (path_append_iff _ _ _ _ _).1 hpath with
        ⟨middle, hleft, hright⟩
      have hleftRole := ihLeft source middle hleft
      have hrightRole := ihRight middle targetValue hright
      have hbinary := hrules rule hrule
      let values : Fin 3 → D := fun index =>
        if index = 0 then source else if index = 1 then middle else targetValue
      have hresult := hbinary values (by
        intro index
        fin_cases index
        · simpa [CBRegularRoleCountermodel.BinaryChain.toRoleChain, values,
            hfirst] using hleftRole
        · simpa [CBRegularRoleCountermodel.BinaryChain.toRoleChain, values,
            hsecond] using hrightRole)
      simpa [CBRegularRoleCountermodel.BinaryChain.toRoleChain, values,
        hconclusion] using hresult

theorem satChain_of_derivation
    (roleMap : SourceRole → TargetRole)
    (rules : List (CBRegularRoleCountermodel.BinaryChain TargetRole))
    (chain : RoleChain SourceRole)
    (derivation : Derivation roleMap rules chain.body (roleMap chain.sup))
    (target : TargetRole → D → D → Prop)
    (hrules : ∀ rule ∈ rules, satChain target rule.toRoleChain) :
    satChain (fun role => target (roleMap role)) chain := by
  intro values edges
  exact Derivation.sound roleMap rules derivation target hrules _ _
    (path_of_indexed_edges chain.body values edges)

#print axioms path_of_indexed_edges
#print axioms indexed_edges_of_path
#print axioms satChain_apply_path
#print axioms Derivation.weaken
#print axioms Derivation.sound
#print axioms satChain_of_derivation

end ContextCalculus.CBRoleChainBinaryDerivation
