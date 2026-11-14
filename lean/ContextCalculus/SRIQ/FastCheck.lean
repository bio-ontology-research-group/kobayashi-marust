import ContextCalculus.SRIQ.FastComplete

/-!
# Certificate check for the fast SHIQ procedure: the checked route (stage C1c)

`fastClassify O req U` returns the rows read from the live nodes of `U`
when `closedB` accepts `U`, and `none` (decline) otherwise. For an
ALCHIQ ontology every returned row is exact (`fastClassify_spec`): the
row of `a` is `none` exactly when `a` is unsatisfiable, and otherwise it
lists exactly the subsumers of `a`. No statement mentions the generator
of `U`; `fastClassifyGen_spec` holds for every generator.
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat} {O : Ontology (Fin n) (Fin m)} {U : Cand n m} {req : List (Fin n)}

/-- **Completeness of the rows** under the closure conditions. -/
theorem fastRows_complete (hC : ClosedP (mkIx O) U req) {p : Fin n × Option (List (Fin n))}
    (hp : p ∈ fastRows (mkIx O) U req) :
    (p.2 = none →
      ∀ (D : Type) [Nonempty D] (I : Interp D (Fin n) (Fin m)), models I O → ∀ x, ¬ I.c p.1 x) ∧
    ∀ L, p.2 = some L → ∀ b ∈ L, EntailsSub O p.1 b := by
  simp only [fastRows, List.mem_map] at hp
  obtain ⟨⟨a, k⟩, hak, rfl⟩ := hp
  refine ⟨fun hn D _ I hI x hx => ?_, fun L hL b hb D _ I hI x hx => ?_⟩
  · obtain ⟨i, hi, -⟩ := complete hI hC hak hx
    exact (rowOf_none.1 hn) i hi
  · obtain ⟨i, hi, hix⟩ := complete hI hC hak hx
    exact (mem_typeOf I).1 (hix (((rowOf_some hL).2 b).1 hb i hi))

/-- **The checked route is exact.** -/
theorem fastClassify_spec (hA : IsALCHIQ O) {rows : List (Fin n × Option (List (Fin n)))}
    (h : fastClassify O req U = some rows) :
    (∀ a ∈ req, ∃ p ∈ rows, p.1 = a) ∧
    ∀ p ∈ rows, p.1 ∈ req ∧
      (p.2 = none ↔
        ∀ (D : Type) [Nonempty D] (I : Interp D (Fin n) (Fin m)), models I O → ∀ x, ¬ I.c p.1 x) ∧
      ∀ L, p.2 = some L → ∀ b, b ∈ L ↔ EntailsSub O p.1 b := by
  unfold fastClassify at h
  dsimp only at h
  split at h
  · next hc =>
    simp only [Option.some.injEq] at h
    subst h
    have hC : ClosedP (mkIx O) U req := of_decide_eq_true hc
    refine ⟨fun a ha => ?_, fun p hp => ?_⟩
    · have hmap : (req.zip U.roots).map Prod.fst = req := List.map_fst_zip (by rw [hC.1])
      rw [← hmap] at ha
      obtain ⟨⟨a', k⟩, hak, rfl⟩ := List.mem_map.1 ha
      exact ⟨_, List.mem_map.2 ⟨(a', k), hak, rfl⟩, rfl⟩
    · obtain ⟨hreq, hsnd⟩ := fastRows_sound hA hp
      obtain ⟨hnone, hsome⟩ := fastRows_complete hC hp
      refine ⟨hreq, ⟨hnone, fun hun => ?_⟩, fun L hL b => ⟨hsome L hL b, (hsnd L hL).1 b⟩⟩
      cases hp2 : p.2 with
      | none => rfl
      | some L => exact absurd hun ((hsnd L hp2).2)
  · simp at h

/-- The route with any generator of candidate sets. -/
def fastClassifyGen (gen : Ontology (Fin n) (Fin m) → List (Fin n) → Cand n m)
    (O : Ontology (Fin n) (Fin m)) (req : List (Fin n)) :
    Option (List (Fin n × Option (List (Fin n)))) :=
  fastClassify O req (gen O req)

/-- **Exact for every generator.** -/
theorem fastClassifyGen_spec (gen : Ontology (Fin n) (Fin m) → List (Fin n) → Cand n m)
    (hA : IsALCHIQ O) {rows : List (Fin n × Option (List (Fin n)))}
    (h : fastClassifyGen gen O req = some rows) :
    (∀ a ∈ req, ∃ p ∈ rows, p.1 = a) ∧
    ∀ p ∈ rows, p.1 ∈ req ∧
      (p.2 = none ↔
        ∀ (D : Type) [Nonempty D] (I : Interp D (Fin n) (Fin m)), models I O → ∀ x, ¬ I.c p.1 x) ∧
      ∀ L, p.2 = some L → ∀ b, b ∈ L ↔ EntailsSub O p.1 b :=
  fastClassify_spec hA h

/-- The rows of the checked route, in request order. -/
theorem fastClassify_get {rows : List (Fin n × Option (List (Fin n)))}
    (h : fastClassify O req U = some rows) {i : Nat} (hi : i < req.length) :
    ∃ p, rows[i]? = some p ∧ p.1 = req[i] := by
  unfold fastClassify at h
  dsimp only at h
  split at h
  · next hc =>
    simp only [Option.some.injEq] at h
    subst h
    have hC : ClosedP (mkIx O) U req := of_decide_eq_true hc
    have hik : i < U.roots.length := by rw [hC.1]; exact hi
    refine ⟨(req[i], rowOf U (aliveArr (mkIx O) U) U.roots[i] req[i]), ?_, rfl⟩
    have hz : (req.zip U.roots)[i]? = some (req[i], U.roots[i]) := by
      rw [List.getElem?_eq_getElem (by simp [hi, hik])]
      simp
    simp only [fastRows, List.getElem?_map, hz, Option.map_some]
  · simp at h

end ContextCalculus.SRIQ.Fast

#print axioms ContextCalculus.SRIQ.Fast.fastRows_complete
#print axioms ContextCalculus.SRIQ.Fast.fastClassify_spec
#print axioms ContextCalculus.SRIQ.Fast.fastClassifyGen_spec
