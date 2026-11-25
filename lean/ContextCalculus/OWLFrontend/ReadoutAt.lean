import ContextCalculus.OWLFrontend.ReferenceReadout
import ContextCalculus.OWL.EntailsAt

/-!
# The probe readout at one datatype map (v1.7.0 stage C4, part D)

`owlReadout_exactAt` is `owlReadout_exact` with entailment, inconsistency
and unsatisfiability taken at one datatype map `DM` (`OWLExactAt`). The
SHIQ(D) route is exact at the OWL 2 datatype map (`owlSHIQDReference_sound`),
so its readout means what this theorem says with `DM = owl2MapP pat`.
-/

namespace ContextCalculus.OWL

/-- The class IRI `A` is unsatisfiable in `O` at the map `DM`. -/
def UnsatisfiableAt (DM : DatatypeMap) (O : Ontology) (A : IRI) : Prop :=
  ∀ (Domain : Type) [Nonempty Domain] (I : Interp DM Domain), Model O I → ∀ x, ¬ I.cls A x

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy
open ContextCalculus.OWL (EntailsSubAt InconsistentAt UnsatisfiableAt DatatypeMap)

variable {DM : DatatypeMap}

/-- The conclusion of a route's soundness theorem at the map `DM`. -/
def OWLExactAt (DM : DatatypeMap) (O : OWL.Ontology) (requested : List OWL.IRI) (a : OWLAnswer) :
    Prop :=
  a.named = requested.eraseDups ∧
    ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
      (a.bit i j = true ↔ EntailsSubAt DM O a.named[i] a.named[j])

theorem inconsistentAt_iff_entailsSubAt_fresh {O : OWL.Ontology} {P Q : OWL.IRI}
    (hP : ¬ O.mentionsClass P) (hQ : ¬ O.mentionsClass Q) (hPQ : P ≠ Q) :
    InconsistentAt DM O ↔ EntailsSubAt DM O P Q := by
  constructor
  · intro h D _ I hI
    exact absurd hI (h D I)
  · intro hsub D _ I hI
    obtain ⟨x⟩ := ‹Nonempty D›
    have hI' := OWL.model_update_unmentioned hQ (fun _ => False)
      (OWL.model_update_unmentioned hP (fun _ => True) hI)
    have := hsub D _ hI' x
    simp [hPQ] at this

theorem unsatisfiableAt_iff_entailsSubAt_fresh {O : OWL.Ontology} {A Q : OWL.IRI}
    (hQ : ¬ O.mentionsClass Q) (hAQ : A ≠ Q) :
    UnsatisfiableAt DM O A ↔ EntailsSubAt DM O A Q := by
  constructor
  · intro h D _ I hI x hx
    exact absurd hx (h D I hI x)
  · intro hsub D _ I hI x hx
    have hI' := OWL.model_update_unmentioned hQ (fun _ => False) hI
    have := hsub D _ hI' x
    simp [hAQ] at this
    exact this hx

/-- An `OWLExact` answer to `probeRequest O` read through its bits. -/
theorem exact_bitsAt {O : OWL.Ontology} {a : OWLAnswer}
    (hexact : OWLExactAt DM O (probeRequest O) a)
    (hA : probeA ∉ O.classNames) (hB : probeB ∉ O.classNames) :
    a.named = probeRequest O ∧ a.named.length = O.classNames.length + 2 := by
  have hn : a.named = probeRequest O := by
    rw [hexact.1, eraseDups_of_nodup (probeRequest_nodup hA hB)]
  refine ⟨hn, ?_⟩
  rw [hn, probeRequest, List.length_append]
  rfl

/-- What the printed readout means under the OWL 2 direct semantics at the datatype map `DM`. With
`names = O.classNames` and `n = names.length`:

1. the verdict is `true` exactly when `O` is inconsistent, and then nothing
   else is printed;
2. on a consistent ontology, the printed unsatisfiable indices are exactly
   the unsatisfiable classes;
3. every satisfiable class has a printed row;
4. every printed row is about a satisfiable class `i < n`, and lists exactly
   the classes `j < n` with `O ⊨ names[i] ⊑ names[j]`. -/
theorem owlReadout_exactAt {O : OWL.Ontology} {a : OWLAnswer}
    (hexact : OWLExactAt DM O (probeRequest O) a)
    (hA : probeA ∉ O.classNames) (hB : probeB ∉ O.classNames) :
    let names := O.classNames
    let r := owlReadout names.length a
    (r.inconsistent = true ↔ OWL.InconsistentAt DM O) ∧
    (r.inconsistent = true → r.unsat = [] ∧ r.rows = []) ∧
    (r.inconsistent = false →
      (∀ i ∈ r.unsat, i < names.length) ∧
      (∀ i (hi : i < names.length), (i ∈ r.unsat ↔ OWL.UnsatisfiableAt DM O names[i])) ∧
      (∀ i (hi : i < names.length), ¬ OWL.UnsatisfiableAt DM O names[i] →
        ∃ s, (i, s) ∈ r.rows) ∧
      (∀ p ∈ r.rows, ∃ hi : p.1 < names.length, ¬ OWL.UnsatisfiableAt DM O names[p.1] ∧
        ∀ j (hj : j < names.length), (j ∈ p.2 ↔ OWL.EntailsSubAt DM O names[p.1] names[j]))) := by
  intro names r
  obtain ⟨hnamed, hlen⟩ := exact_bitsAt hexact hA hB
  have hbit := hexact.2
  -- The requested IRIs by index.
  have hget_lt : ∀ i (hi : i < O.classNames.length), ∃ h : i < a.named.length, a.named[i] = O.classNames[i] := by
    intro i hi
    refine ⟨by omega, ?_⟩
    simp only [hnamed, probeRequest]
    rw [List.getElem_append_left hi]
  have hget_a : ∃ h : O.classNames.length < a.named.length, a.named[O.classNames.length] = probeA := by
    refine ⟨by omega, ?_⟩
    simp only [hnamed, probeRequest]
    rw [List.getElem_append_right (by simp)]
    simp
  have hget_b : ∃ h : O.classNames.length + 1 < a.named.length, a.named[O.classNames.length + 1] = probeB := by
    refine ⟨by omega, ?_⟩
    simp only [hnamed, probeRequest]
    rw [List.getElem_append_right (by simp)]
    simp
  have hfreshA : ¬ O.mentionsClass probeA := by
    rw [mentionsClass_iff_mem_classNames]; exact hA
  have hfreshB : ¬ O.mentionsClass probeB := by
    rw [mentionsClass_iff_mem_classNames]; exact hB
  -- Inconsistency is the bit `O.classNames.length ⊑ O.classNames.length + 1`.
  have hinc : bitAt a.rows.toArray O.classNames.length (O.classNames.length + 1) = true ↔ OWL.InconsistentAt DM O := by
    obtain ⟨ha, hea⟩ := hget_a
    obtain ⟨hb, heb⟩ := hget_b
    rw [bitAt_toArray, hbit O.classNames.length (O.classNames.length + 1) ha hb, hea, heb]
    exact (inconsistentAt_iff_entailsSubAt_fresh hfreshA hfreshB probeA_ne_probeB).symm
  -- Unsatisfiability of class `i` is the bit `i ⊑ O.classNames.length + 1`.
  have hunsat : ∀ i (hi : i < O.classNames.length),
      bitAt a.rows.toArray i (O.classNames.length + 1) = true ↔ OWL.UnsatisfiableAt DM O O.classNames[i] := by
    intro i hi
    obtain ⟨hi', hei⟩ := hget_lt i hi
    obtain ⟨hb, heb⟩ := hget_b
    rw [bitAt_toArray, hbit i (O.classNames.length + 1) hi' hb, hei, heb]
    have hne : O.classNames[i] ≠ probeB := by
      intro h
      exact hB (h ▸ List.getElem_mem hi)
    exact (unsatisfiableAt_iff_entailsSubAt_fresh hfreshB hne).symm
  -- Subsumption between classes is the bit `i ⊑ j`.
  have hsub : ∀ i j (hi : i < O.classNames.length) (hj : j < O.classNames.length),
      bitAt a.rows.toArray i j = true ↔ OWL.EntailsSubAt DM O O.classNames[i] O.classNames[j] := by
    intro i j hi hj
    obtain ⟨hi', hei⟩ := hget_lt i hi
    obtain ⟨hj', hej⟩ := hget_lt j hj
    rw [bitAt_toArray, hbit i j hi' hj', hei, hej]
  -- Every class has a row (its reflexive bit is set).
  have hrow : ∀ i (hi : i < O.classNames.length), ∃ row : SparseRow, a.rows.toArray[i]? = some row := by
    intro i hi
    have hrefl : bitAt a.rows.toArray i i = true :=
      (hsub i i hi hi).2 (fun _ _ _ _ _ hx => hx)
    unfold bitAt at hrefl
    split at hrefl
    · next row hrow => exact ⟨row, hrow⟩
    · exact absurd hrefl (by simp)
  -- In a row whose `probeB` bit is clear, the bits are the `sups`.
  have hrowbit : ∀ (i : Nat) (row : SparseRow), a.rows.toArray[i]? = some row →
      row.bit (O.classNames.length + 1) = false →
      ∀ j, row.bit j = row.sups.contains j := by
    intro i row _ hb j
    simp only [SparseRow.bit, Bool.or_eq_false_iff] at hb
    simp [SparseRow.bit, hb.1]
  have hr_def : r = owlReadout O.classNames.length a := rfl
  by_cases hI : bitAt a.rows.toArray O.classNames.length (O.classNames.length + 1) = true
  · have hr : r = { inconsistent := true, unsat := [], rows := [] } := by
      rw [hr_def]; unfold owlReadout; simp only [hI, if_true]
    rw [hr]
    exact ⟨⟨fun _ => hinc.1 hI, fun _ => rfl⟩, fun _ => ⟨rfl, rfl⟩,
      fun h => absurd h (by simp)⟩
  · have hI' : bitAt a.rows.toArray O.classNames.length (O.classNames.length + 1) = false := by simpa using hI
    have hr : r = { inconsistent := false
                    unsat := (List.range O.classNames.length).filter fun i => bitAt a.rows.toArray i (O.classNames.length + 1)
                    rows := (List.range O.classNames.length).filterMap (readRow O.classNames.length a.rows.toArray) } := by
      rw [hr_def]; unfold owlReadout; simp only [hI', Bool.false_eq_true, if_false]
    rw [hr]
    refine ⟨⟨fun h => absurd h (by simp), fun h => absurd (hinc.2 h) hI⟩,
      fun h => absurd h (by simp), fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · intro i hi
      simp only [List.mem_filter, List.mem_range] at hi
      exact hi.1
    · intro i hi
      simp only [List.mem_filter, List.mem_range]
      exact ⟨fun h => (hunsat i hi).1 h.2, fun h => ⟨hi, (hunsat i hi).2 h⟩⟩
    · intro i hi hsat
      obtain ⟨row, hrw⟩ := hrow i hi
      have hb : row.bit (O.classNames.length + 1) = false := by
        have : bitAt a.rows.toArray i (O.classNames.length + 1) = false := by
          cases h : bitAt a.rows.toArray i (O.classNames.length + 1)
          · rfl
          · exact absurd ((hunsat i hi).1 h) hsat
        simpa [bitAt, hrw] using this
      refine ⟨row.sups.filter (· < O.classNames.length), ?_⟩
      simp only [List.mem_filterMap, List.mem_range]
      exact ⟨i, hi, by simp [readRow, hrw, hb]⟩
    · intro p hp
      simp only [List.mem_filterMap, List.mem_range] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      unfold readRow at hpi
      split at hpi
      · next row hrw =>
          by_cases hb : row.bit (O.classNames.length + 1) = true
          · simp [hb] at hpi
          · have hb' : row.bit (O.classNames.length + 1) = false := by simpa using hb
            simp only [hb', Bool.false_eq_true, if_false, Option.some.injEq] at hpi
            subst hpi
            refine ⟨hi, ?_, ?_⟩
            · intro hu
              have := (hunsat i hi).2 hu
              simp [bitAt, hrw, hb'] at this
            · intro j hj
              rw [← hsub i j hi hj]
              have hbj := hrowbit i row hrw hb' j
              simp only [bitAt, hrw, hbj, List.mem_filter, decide_eq_true_eq,
                List.contains_iff_mem]
              exact ⟨fun h => h.1, fun h => ⟨h, hj⟩⟩
      · simp at hpi

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.owlReadout_exactAt
