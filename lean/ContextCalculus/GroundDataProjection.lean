/-! Exact elimination of non-functional ground data properties. Object and data
carriers remain separate. Facts are closed under the retained subproperty
relation, and literal membership in all inherited ranges is checked first.
The only remaining object constraints are the entailed domain assertions. -/
namespace ContextCalculus.GroundDataProjection
variable {Property Individual Object Data : Type}

def extension (facts : Property → Individual → Data → Prop)
    (denote : Individual → Object) (p : Property) (o : Object) (v : Data) : Prop :=
  ∃ i, facts p i v ∧ denote i = o

theorem source_fact (facts : Property → Individual → Data → Prop)
    (denote : Individual → Object) (p : Property) (i : Individual) (v : Data)
    (h : facts p i v) : extension facts denote p (denote i) v :=
  ⟨i, h, rfl⟩

theorem projected_domains_iff_extension_domains
    (facts : Property → Individual → Data → Prop) (denote : Individual → Object)
    (domain : Property → Object → Prop) :
    (∀ p i v, facts p i v → domain p (denote i)) ↔
    (∀ p o v, extension facts denote p o v → domain p o) := by
  constructor
  · intro h p o v he
    obtain ⟨i, hf, hi⟩ := he
    simpa only [← hi] using h p i v hf
  · intro h p i v hf
    exact h p (denote i) v (source_fact facts denote p i v hf)

/-- Retained relational domain/range/hierarchy schema never constrains the
object reduct further: its internal object-role encodings can all be empty. -/
theorem empty_schema_model
    (domain range : Property → Object → Prop) (sub : Property → Property → Prop) :
    ∃ edge : Property → Object → Object → Prop,
      (∀ p x y, edge p x y → domain p x) ∧
      (∀ p x y, edge p x y → range p y) ∧
      (∀ p q x y, sub p q → edge p x y → edge q x y) := by
  exact ⟨fun _ _ _ => False, (fun _ _ _ h => h.elim),
    (fun _ _ _ h => h.elim), (fun _ _ _ _ _ h => h.elim)⟩

theorem exact_model_extension
    (facts : Property → Individual → Data → Prop) (denote : Individual → Object)
    (domain : Property → Object → Prop) (range : Property → Data → Prop)
    (sub : Property → Property → Prop) (objectTheory : Prop)
    (closed : ∀ p q i v, sub p q → facts p i v → facts q i v)
    (valid : ∀ p i v, facts p i v → range p v) :
    (objectTheory ∧ ∀ p i v, facts p i v → domain p (denote i)) ↔
    (∃ edge : Property → Object → Data → Prop,
      objectTheory ∧
      (∀ p i v, facts p i v → edge p (denote i) v) ∧
      (∀ p o v, edge p o v → domain p o) ∧
      (∀ p o v, edge p o v → range p v) ∧
      (∀ p q o v, sub p q → edge p o v → edge q o v)) := by
  constructor
  · rintro ⟨ht, hd⟩
    refine ⟨extension facts denote, ht, ?_, ?_, ?_, ?_⟩
    · exact source_fact facts denote
    · exact (projected_domains_iff_extension_domains facts denote domain).mp hd
    · intro p o v he
      obtain ⟨i, hf, _⟩ := he
      exact valid p i v hf
    · intro p q o v hpq he
      obtain ⟨i, hf, hi⟩ := he
      exact ⟨i, closed p q i v hpq hf, hi⟩
  · rintro ⟨edge, ht, hf, hd, _, _⟩
    exact ⟨ht, fun p i v h => hd p (denote i) v (hf p i v h)⟩

#print axioms source_fact
#print axioms projected_domains_iff_extension_domains
#print axioms empty_schema_model
#print axioms exact_model_extension
end ContextCalculus.GroundDataProjection
