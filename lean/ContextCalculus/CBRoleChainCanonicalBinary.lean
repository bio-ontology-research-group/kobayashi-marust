import ContextCalculus.CBRoleChainBinaryDerivation

/-!
# Canonical binary decomposition of finite role chains

Target roles are represented symbolically by nonempty source-role paths. A
source role maps to its singleton path. Every longer path gets a finite binary
prefix rule, and the final rule concludes in the singleton source super-role.
-/

namespace ContextCalculus.CBRoleChainCanonicalBinary

open ContextCalculus

def singletonRole (role : Role) : List Role := [role]

@[simp] theorem path_singleton_iff
    (relation : Role → D → D → Prop) (role : Role) (source target : D) :
    CBRoleChainBinaryDerivation.Path relation [role] source target ↔
      relation role source target := by
  simp [CBRoleChainBinaryDerivation.Path]

/-- Path concatenation interprets every internal rule introduced by the
    canonical decomposition. -/
theorem sat_append_rule
    (relation : Role → D → D → Prop) (left right : List Role) :
    CBRoleChainEncoding.satChain
      (CBRoleChainBinaryDerivation.Path relation)
      (CBRegularRoleCountermodel.BinaryChain.toRoleChain {
        first := left, second := right, conclusion := left ++ right }) := by
  change ∀ values : Fin 3 → D,
    (∀ i : Fin 2,
      CBRoleChainBinaryDerivation.Path relation ([left, right].get i)
        (values ⟨i.val, by omega⟩) (values ⟨i.val + 1, by omega⟩)) →
    CBRoleChainBinaryDerivation.Path relation (left ++ right)
      (values ⟨0, by omega⟩) (values ⟨2, by omega⟩)
  intro values edges
  apply (CBRoleChainBinaryDerivation.path_append_iff
    relation left right _ _).2
  refine ⟨values ⟨1, by decide⟩, ?_, ?_⟩
  · simpa [CBRegularRoleCountermodel.BinaryChain.toRoleChain] using
      edges ⟨0, by decide⟩
  · simpa [CBRegularRoleCountermodel.BinaryChain.toRoleChain] using
      edges ⟨1, by decide⟩

structure IdentityDerivation (body : List Role) where
  rules : List (CBRegularRoleCountermodel.BinaryChain (List Role))
  derivation : CBRoleChainBinaryDerivation.Derivation singletonRole rules body body

def identityDerivation : (first : Role) → (rest : List Role) →
    IdentityDerivation (first :: rest)
  | first, [] => {
      rules := []
      derivation := .atom first }
  | first, second :: rest =>
      let tail := identityDerivation second rest
      let rule : CBRegularRoleCountermodel.BinaryChain (List Role) := {
        first := [first]
        second := second :: rest
        conclusion := first :: second :: rest }
      {
        rules := tail.rules ++ [rule]
        derivation := .compose (.atom first)
          (tail.derivation.weaken (by
            intro candidate hcandidate
            exact List.mem_append_left _ hcandidate))
          rule (by simp) rfl rfl rfl }

theorem identityDerivation_rules_sound
    (relation : Role → D → D → Prop) (first : Role) (rest : List Role) :
    ∀ rule ∈ (identityDerivation first rest).rules,
      CBRoleChainEncoding.satChain
        (CBRoleChainBinaryDerivation.Path relation) rule.toRoleChain := by
  induction rest generalizing first with
  | nil => simp [identityDerivation]
  | cons second rest ih =>
      intro rule hrule
      simp only [identityDerivation] at hrule
      rcases List.mem_append.mp hrule with htail | hfinal
      · exact ih second rule htail
      · simp only [List.mem_singleton] at hfinal
        subst rule
        exact sat_append_rule relation [first] (second :: rest)

structure ChainDerivation (first second : Role) (rest : List Role) (sup : Role) where
  rules : List (CBRegularRoleCountermodel.BinaryChain (List Role))
  derivation : CBRoleChainBinaryDerivation.Derivation singletonRole rules
    (first :: second :: rest) [sup]

def chainDerivation (first second : Role) (rest : List Role) (sup : Role) :
    ChainDerivation first second rest sup :=
  let tail := identityDerivation second rest
  let finalRule : CBRegularRoleCountermodel.BinaryChain (List Role) := {
    first := [first]
    second := second :: rest
    conclusion := [sup] }
  {
    rules := tail.rules ++ [finalRule]
    derivation := .compose (.atom first)
      (tail.derivation.weaken (by
        intro candidate hcandidate
        exact List.mem_append_left _ hcandidate))
      finalRule (by simp) rfl rfl rfl }

theorem chainDerivation_rules_sound
    (relation : Role → D → D → Prop)
    (first second : Role) (rest : List Role) (sup : Role)
    (hsource : CBRoleChainEncoding.satChain relation {
      body := first :: second :: rest, sup := sup }) :
    ∀ rule ∈ (chainDerivation first second rest sup).rules,
      CBRoleChainEncoding.satChain
        (CBRoleChainBinaryDerivation.Path relation) rule.toRoleChain := by
  intro rule hrule
  simp only [chainDerivation] at hrule
  rcases List.mem_append.mp hrule with htail | hfinal
  · exact identityDerivation_rules_sound relation second rest rule htail
  · simp only [List.mem_singleton] at hfinal
    subst rule
    change ∀ values : Fin 3 → D,
      (∀ i : Fin 2,
        CBRoleChainBinaryDerivation.Path relation
          ([[first], second :: rest].get i)
          (values ⟨i.val, by omega⟩) (values ⟨i.val + 1, by omega⟩)) →
      CBRoleChainBinaryDerivation.Path relation [sup]
        (values ⟨0, by omega⟩) (values ⟨2, by omega⟩)
    intro values edges
    have hleft := edges ⟨0, by decide⟩
    have hright := edges ⟨1, by decide⟩
    have hpath : CBRoleChainBinaryDerivation.Path relation
        (first :: second :: rest) (values ⟨0, by decide⟩)
          (values ⟨2, by decide⟩) :=
      (CBRoleChainBinaryDerivation.path_append_iff relation [first]
        (second :: rest) _ _).2 ⟨values ⟨1, by decide⟩, hleft, hright⟩
    have hresult := CBRoleChainBinaryDerivation.satChain_apply_path
      { body := first :: second :: rest, sup := sup } hsource hpath
    simpa [CBRegularRoleCountermodel.BinaryChain.toRoleChain] using hresult

theorem every_chain_of_length_at_least_two
    (chain : CBRoleChainEncoding.RoleChain Role)
    (hlength : 2 ≤ chain.body.length) :
    ∃ rules : List (CBRegularRoleCountermodel.BinaryChain (List Role)),
      CBRoleChainBinaryDerivation.Derivation singletonRole rules
        chain.body (singletonRole chain.sup) := by
  cases hbody : chain.body with
  | nil => simp [hbody] at hlength
  | cons first tail =>
      cases htail : tail with
      | nil => simp [hbody, htail] at hlength
      | cons second rest =>
          let canonical := chainDerivation first second rest chain.sup
          refine ⟨canonical.rules, ?_⟩
          simpa [hbody, htail, canonical, singletonRole] using canonical.derivation

theorem every_finite_chain_family
    (chains : List (CBRoleChainEncoding.RoleChain Role))
    (hlength : ∀ chain ∈ chains, 2 ≤ chain.body.length) :
    ∃ rules : List (CBRegularRoleCountermodel.BinaryChain (List Role)),
      ∀ chain, chain ∈ chains →
        CBRoleChainBinaryDerivation.Derivation singletonRole rules
          chain.body (singletonRole chain.sup) := by
  induction chains with
  | nil =>
      exact ⟨[], by simp⟩
  | cons chain chains ih =>
      obtain ⟨chainRules, chainDerivation⟩ :=
        every_chain_of_length_at_least_two chain
          (hlength chain (by simp))
      obtain ⟨tailRules, tailDerivations⟩ := ih (by
        intro tail htail
        exact hlength tail (List.mem_cons_of_mem chain htail))
      refine ⟨chainRules ++ tailRules, ?_⟩
      intro actual hactual
      rcases List.mem_cons.mp hactual with hequal | htail
      · subst actual
        exact chainDerivation.weaken (by
          intro rule hrule
          exact List.mem_append_left _ hrule)
      · exact (tailDerivations actual htail).weaken (by
          intro rule hrule
          exact List.mem_append_right _ hrule)

/-- The canonical binary compilation is conservative. Every source
    interpretation satisfying the original chain family extends to the target
    role signature by interpreting a symbolic path as relational composition. -/
theorem every_finite_chain_family_conservative
    (chains : List (CBRoleChainEncoding.RoleChain Role))
    (hlength : ∀ chain ∈ chains, 2 ≤ chain.body.length) :
    ∃ rules : List (CBRegularRoleCountermodel.BinaryChain (List Role)),
      (∀ chain, chain ∈ chains →
        CBRoleChainBinaryDerivation.Derivation singletonRole rules
          chain.body (singletonRole chain.sup)) ∧
      ∀ (D : Type) (relation : Role → D → D → Prop),
        (∀ chain ∈ chains, CBRoleChainEncoding.satChain relation chain) →
        ∀ rule ∈ rules,
          CBRoleChainEncoding.satChain
            (CBRoleChainBinaryDerivation.Path relation) rule.toRoleChain := by
  induction chains with
  | nil =>
      refine ⟨[], by simp, ?_⟩
      simp
  | cons chain chains ih =>
      cases hbody : chain.body with
      | nil => simp [hbody] at hlength
      | cons first tail =>
          cases htail : tail with
          | nil => simp [hbody, htail] at hlength
          | cons second rest =>
              let compiled := chainDerivation first second rest chain.sup
              obtain ⟨tailRules, tailDerivations, tailSound⟩ := ih (by
                intro actual hactual
                exact hlength actual (List.mem_cons_of_mem chain hactual))
              refine ⟨compiled.rules ++ tailRules, ?_, ?_⟩
              · intro actual hactual
                rcases List.mem_cons.mp hactual with hequal | hmember
                · subst actual
                  rw [hbody, htail]
                  apply compiled.derivation.weaken
                  intro rule hrule
                  exact List.mem_append_left _ hrule
                · apply (tailDerivations actual hmember).weaken
                  intro rule hrule
                  exact List.mem_append_right _ hrule
              · intro D relation hsource rule hrule
                rcases List.mem_append.mp hrule with hcompiled | htailRule
                · apply chainDerivation_rules_sound relation first second rest chain.sup
                    (by
                      have := hsource chain (by simp)
                      have hchain : chain = {
                          body := first :: second :: rest,
                          sup := chain.sup } := by
                        cases chain
                        simp_all
                      rw [hchain] at this
                      exact this)
                    rule hcompiled
                · exact tailSound D relation (by
                    intro actual hactual
                    exact hsource actual (List.mem_cons_of_mem chain hactual))
                    rule htailRule

#print axioms IdentityDerivation.derivation
#print axioms every_chain_of_length_at_least_two
#print axioms every_finite_chain_family
#print axioms every_finite_chain_family_conservative

end ContextCalculus.CBRoleChainCanonicalBinary
