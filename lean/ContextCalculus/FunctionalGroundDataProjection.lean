import Init.Data.Nat.Bitwise.Lemmas
import ContextCalculus.GroundDataProjection
namespace ContextCalculus.FunctionalGroundDataProjection
open ContextCalculus.GroundDataProjection
variable {P I O D B : Type}

def Compatible (facts : P → I → D → Prop) (denote : I → O) (functional : P → Prop) : Prop :=
  ∀ p i j v w, functional p → facts p i v → facts p j w → denote i = denote j → v = w

theorem extension_functional_iff_compatible
    (facts : P → I → D → Prop) (denote : I → O) (functional : P → Prop) :
    (∀ p o v w, functional p → extension facts denote p o v →
      extension facts denote p o w → v = w) ↔ Compatible facts denote functional := by
  constructor
  · intro h p i j v w hp hi hj hij
    apply h p (denote i) v w hp (source_fact facts denote p i v hi)
    exact ⟨j, hj, hij.symm⟩
  · intro h p o v w hp hv hw
    obtain ⟨i, hi, hio⟩ := hv
    obtain ⟨j, hj, hjo⟩ := hw
    exact h p i j v w hp hi hj (hio.trans hjo.symm)

/-- Private bit predicates on owners have exactly the consequences of
functional data values. The construction does not assume unique owner names. -/
theorem compatible_iff_bit_model
    (facts : P → I → D → Prop) (denote : I → O) (functional : P → Prop)
    (code : P → D → B → Prop)
    (injective : ∀ p i j v w, functional p → facts p i v → facts p j w →
      (∀ b, code p v b ↔ code p w b) → v = w) :
    Compatible facts denote functional ↔
    ∃ bits : P → B → O → Prop,
      ∀ p i v, functional p → facts p i v → ∀ b, bits p b (denote i) ↔ code p v b := by
  constructor
  · intro hc
    refine ⟨fun p b o => ∃ i v, facts p i v ∧ denote i = o ∧ code p v b, ?_⟩
    intro p i v hp hf b
    constructor
    · rintro ⟨j, w, hj, heq, hb⟩
      have hwv := hc p j i w v hp hj hf heq
      simpa only [hwv] using hb
    · intro hb
      exact ⟨i, v, hf, rfl, hb⟩
  · rintro ⟨bits, hb⟩ p i j v w hp hi hj heq
    apply injective p i j v w hp hi hj
    intro b
    have hbi := hb p i v hp hi b
    have hbj := hb p j w hp hj b
    rw [heq] at hbi
    exact hbi.symm.trans hbj

theorem exact_functional_model_extension
    (facts : P → I → D → Prop) (denote : I → O)
    (domain : P → O → Prop) (range : P → D → Prop)
    (sub : P → P → Prop) (functional : P → Prop) (objectTheory : Prop)
    (closed : ∀ p q i v, sub p q → facts p i v → facts q i v)
    (valid : ∀ p i v, facts p i v → range p v) :
    (objectTheory ∧ (∀ p i v, facts p i v → domain p (denote i)) ∧
      Compatible facts denote functional) ↔
    (∃ edge : P → O → D → Prop,
      objectTheory ∧
      (∀ p i v, facts p i v → edge p (denote i) v) ∧
      (∀ p o v, edge p o v → domain p o) ∧
      (∀ p o v, edge p o v → range p v) ∧
      (∀ p q o v, sub p q → edge p o v → edge q o v) ∧
      (∀ p o v w, functional p → edge p o v → edge p o w → v = w)) := by
  constructor
  · rintro ⟨ht, hd, hc⟩
    refine ⟨extension facts denote, ht, ?_, ?_, ?_, ?_, ?_⟩
    · exact source_fact facts denote
    · exact (projected_domains_iff_extension_domains facts denote domain).mp hd
    · intro p o v he
      obtain ⟨i, hf, _⟩ := he
      exact valid p i v hf
    · intro p q o v hpq he
      obtain ⟨i, hf, hi⟩ := he
      exact ⟨i, closed p q i v hpq hf, hi⟩
    · exact (extension_functional_iff_compatible facts denote functional).mpr hc
  · rintro ⟨edge, ht, hf, hd, _, _, hfunc⟩
    refine ⟨ht, (fun p i v h => hd p (denote i) v (hf p i v h)), ?_⟩
    intro p i j v w hp hi hj hij
    apply hfunc p (denote i) v w hp (hf p i v hi)
    rw [hij]
    exact hf p j w hj

#print axioms exact_functional_model_extension
theorem bounded_bit_codes_injective {x y width : Nat}
    (hx : x < 2 ^ width) (hy : y < 2 ^ width)
    (same : ∀ i, i < width → x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < width
  · exact same i hi
  · have hp : 2 ^ width ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy hp)]

#print axioms bounded_bit_codes_injective
#print axioms extension_functional_iff_compatible
#print axioms compatible_iff_bit_model

/-- Disjoint positive colours encode value bits without forcing unrelated
objects to choose a bit. -/
theorem compatible_iff_disjoint_bit_model
    (facts : P → I → D → Prop) (denote : I → O) (functional : P → Prop)
    (code : P → D → B → Bool)
    (injective : ∀ p i j v w, functional p → facts p i v → facts p j w →
      (∀ b, code p v b = code p w b) → v = w) :
    Compatible facts denote functional ↔
    ∃ marks : P → B → Bool → O → Prop,
      (∀ p b o, marks p b false o → marks p b true o → False) ∧
      (∀ p i v, functional p → facts p i v →
        ∀ b, marks p b (code p v b) (denote i)) := by
  constructor
  · intro hc
    refine ⟨fun p b colour o => functional p ∧
      ∃ i v, facts p i v ∧ denote i = o ∧ code p v b = colour, ?_, ?_⟩
    · rintro p b o ⟨hp, i, v, hi, hio, hv⟩ ⟨_, j, w, hj, hjo, hw⟩
      have h := hc p i j v w hp hi hj (hio.trans hjo.symm)
      subst w
      rw [hv] at hw
      cases hw
    · intro p i v hp hi b
      exact ⟨hp, i, v, hi, rfl, rfl⟩
  · rintro ⟨marks, hd, hm⟩ p i j v w hp hi hj hij
    apply injective p i j v w hp hi hj
    intro b
    have hv := hm p i v hp hi b
    have hw := hm p j w hp hj b
    rw [hij] at hv
    cases hcv : code p v b <;> cases hcw : code p w b
    · rfl
    · rw [hcv] at hv
      rw [hcw] at hw
      exact False.elim (hd p b (denote j) hv hw)
    · rw [hcv] at hv
      rw [hcw] at hw
      exact False.elim (hd p b (denote j) hw hv)
    · rfl

#print axioms compatible_iff_disjoint_bit_model
end ContextCalculus.FunctionalGroundDataProjection
