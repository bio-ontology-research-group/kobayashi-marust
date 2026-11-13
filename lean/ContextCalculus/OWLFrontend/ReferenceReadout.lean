import ContextCalculus.OWLFrontend.ReferenceSHI
import ContextCalculus.OWL.Names

/-!
# The probe readout of an OWL reference answer (`km-owl-reference`)

`docs/V1.6.2-FRONTEND-PLAN.md`, section 7. The executable `km-owl-reference`
requests the class IRIs of the ontology (`OWL.Ontology.classNames`) followed
by two probe IRIs, `probeA` and `probeB`, runs `owlReference` or
`owlReferenceSHI` (or one of their routes) and prints three things read from the answer's bits:

- the inconsistency verdict: the bit `probeA ⊑ probeB`
  (`OWL.inconsistent_iff_entailsSub_fresh`);
- the unsatisfiable classes: the classes `A` with bit `A ⊑ probeB`
  (`OWL.unsatisfiable_iff_entailsSub_fresh`);
- one row per satisfiable class with its class superclasses (the probes are
  dropped).

An inconsistent ontology prints no unsatisfiable class and no row: every
class is unsatisfiable and every subsumption holds.

`owlReadout_exact` states what the printed readout means under the OWL 2
direct semantics, from the conclusion of `owlReference_sound` (`OWLExact`) and
the freshness of the probes. The executable calls the publishing function only
with a proof of the route's equation, so every printed readout satisfies it.

The readout reads the rows from an `Array` (constant-time access) and loops
over `List.range n` with `filter` and `filterMap`, which compile to tail
recursive code (`List.filterTR`, `List.filterMapTR`).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy

/-- The probe IRI whose subsumption by `probeB` reads inconsistency. -/
def probeA : OWL.IRI := "urn:km:owl-reference:probe-a"

/-- The probe IRI that reads unsatisfiability (`A ⊑ probeB`). -/
def probeB : OWL.IRI := "urn:km:owl-reference:probe-b"

theorem probeA_ne_probeB : probeA ≠ probeB := by
  simp [probeA, probeB]

/-- The request of `km-owl-reference`: the class IRIs, then the probes. -/
def probeRequest (O : OWL.Ontology) : List OWL.IRI :=
  O.classNames ++ [probeA, probeB]

/-- The conclusion of `owlReference_sound` for one answer. -/
def OWLExact (O : OWL.Ontology) (requested : List OWL.IRI) (a : OWLAnswer) : Prop :=
  a.named = requested.eraseDups ∧
    ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
      (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j])

/-! ### Routes -/

/-- The procedures of `km-owl-reference`. -/
inductive OWLProcedure where
  | el
  | alc
  | elThenAlc
  /-- The SHI route alone (`owlSRIReference`). -/
  | sri
  /-- EL first, then SHI (`owlReferenceSHI`). -/
  | elThenSri
  deriving DecidableEq, Repr

/-- The equation a published answer of a procedure comes with. -/
def RouteAnswer : OWLProcedure → OWL.Ontology → List OWL.IRI → OWLAnswer → Prop
  | .el, O, requested, a => owlELReference O requested = some a
  | .alc, O, requested, a => owlALCReference O requested = some a
  | .elThenAlc, O, requested, a => owlReference O requested = some a
  | .sri, O, requested, a => owlSRIReference O requested = some a
  | .elThenSri, O, requested, a => owlReferenceSHI O requested = some a

theorem routeAnswer_exact {p : OWLProcedure} {O : OWL.Ontology}
    {requested : List OWL.IRI} {a : OWLAnswer} (h : RouteAnswer p O requested a) :
    OWLExact O requested a := by
  cases p with
  | el => exact owlELReference_sound h
  | alc => exact owlALCReference_sound h
  | elThenAlc => exact owlReference_sound h
  | sri => exact owlSRIReference_sound h
  | elThenSri => exact owlReferenceSHI_sound h

/-! ### The readout -/

/-- What `km-owl-reference` prints, by class index (`O.classNames[i]`). -/
structure OWLReadout where
  inconsistent : Bool
  unsat : List Nat
  /-- `(i, sups)`: the class superclasses of the satisfiable class `i`. -/
  rows : List (Nat × List Nat)
deriving Repr

/-- `OWLAnswer.bit` on the rows as an array. -/
def bitAt (rows : Array SparseRow) (i j : Nat) : Bool :=
  match rows[i]? with
  | some r => r.bit j
  | none => false

/-- The printed row of class `i` among `n` classes: none when `i` is
unsatisfiable (bit `i ⊑ probeB`, index `n + 1`), else its superclasses below
`n`. -/
def readRow (n : Nat) (rows : Array SparseRow) (i : Nat) : Option (Nat × List Nat) :=
  match rows[i]? with
  | some r => if r.bit (n + 1) then none else some (i, r.sups.filter (· < n))
  | none => none

/-- The readout of an answer to `probeRequest O` with `n = O.classNames.length`. -/
def owlReadout (n : Nat) (a : OWLAnswer) : OWLReadout :=
  let arr := a.rows.toArray
  if bitAt arr n (n + 1) then { inconsistent := true, unsat := [], rows := [] }
  else
    { inconsistent := false
      unsat := (List.range n).filter fun i => bitAt arr i (n + 1)
      rows := (List.range n).filterMap (readRow n arr) }

/-! ### Lemmas -/

theorem bitAt_toArray (a : OWLAnswer) (i j : Nat) :
    bitAt a.rows.toArray i j = a.bit i j := by
  cases h : a.rows[i]? <;> simp [bitAt, OWLAnswer.bit, h]

theorem eraseDups_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
      rw [List.nodup_cons] at h
      rw [List.eraseDups_cons]
      have hf : as.filter (fun b => !b == a) = as := by
        rw [List.filter_eq_self]
        intro b hb
        have : b ≠ a := fun hba => h.1 (hba ▸ hb)
        simp [this]
      rw [hf, eraseDups_of_nodup h.2]

theorem classIRIs_eq_classNames (ax : OWL.Axiom) : ax.classIRIs = ax.classNames := by
  cases ax <;> rfl

theorem mentionsClass_iff_mem_classNames (O : OWL.Ontology) (A : OWL.IRI) :
    O.mentionsClass A ↔ A ∈ O.classNames := by
  rw [OWL.Ontology.mem_classNames]
  simp only [OWL.Ontology.mentionsClass, classIRIs_eq_classNames]

theorem probeRequest_nodup {O : OWL.Ontology} (hA : probeA ∉ O.classNames)
    (hB : probeB ∉ O.classNames) : (probeRequest O).Nodup := by
  unfold probeRequest
  rw [List.nodup_append]
  refine ⟨O.classNames_nodup, ?_, ?_⟩
  · simp [probeA_ne_probeB]
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hA hx
    · exact hB hx

/-- An `OWLExact` answer to `probeRequest O` read through its bits. -/
private theorem exact_bits {O : OWL.Ontology} {a : OWLAnswer}
    (hexact : OWLExact O (probeRequest O) a)
    (hA : probeA ∉ O.classNames) (hB : probeB ∉ O.classNames) :
    a.named = probeRequest O ∧ a.named.length = O.classNames.length + 2 := by
  have hn : a.named = probeRequest O := by
    rw [hexact.1, eraseDups_of_nodup (probeRequest_nodup hA hB)]
  refine ⟨hn, ?_⟩
  rw [hn, probeRequest, List.length_append]
  rfl

/-- What the printed readout means under the OWL 2 direct semantics. With
`names = O.classNames` and `n = names.length`:

1. the verdict is `true` exactly when `O` is inconsistent, and then nothing
   else is printed;
2. on a consistent ontology, the printed unsatisfiable indices are exactly
   the unsatisfiable classes;
3. every satisfiable class has a printed row;
4. every printed row is about a satisfiable class `i < n`, and lists exactly
   the classes `j < n` with `O ⊨ names[i] ⊑ names[j]`. -/
theorem owlReadout_exact {O : OWL.Ontology} {a : OWLAnswer}
    (hexact : OWLExact O (probeRequest O) a)
    (hA : probeA ∉ O.classNames) (hB : probeB ∉ O.classNames) :
    let names := O.classNames
    let r := owlReadout names.length a
    (r.inconsistent = true ↔ OWL.Inconsistent O) ∧
    (r.inconsistent = true → r.unsat = [] ∧ r.rows = []) ∧
    (r.inconsistent = false →
      (∀ i ∈ r.unsat, i < names.length) ∧
      (∀ i (hi : i < names.length), (i ∈ r.unsat ↔ OWL.Unsatisfiable O names[i])) ∧
      (∀ i (hi : i < names.length), ¬ OWL.Unsatisfiable O names[i] →
        ∃ s, (i, s) ∈ r.rows) ∧
      (∀ p ∈ r.rows, ∃ hi : p.1 < names.length, ¬ OWL.Unsatisfiable O names[p.1] ∧
        ∀ j (hj : j < names.length), (j ∈ p.2 ↔ OWL.EntailsSub O names[p.1] names[j]))) := by
  intro names r
  obtain ⟨hnamed, hlen⟩ := exact_bits hexact hA hB
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
  have hinc : bitAt a.rows.toArray O.classNames.length (O.classNames.length + 1) = true ↔ OWL.Inconsistent O := by
    obtain ⟨ha, hea⟩ := hget_a
    obtain ⟨hb, heb⟩ := hget_b
    rw [bitAt_toArray, hbit O.classNames.length (O.classNames.length + 1) ha hb, hea, heb]
    exact (OWL.inconsistent_iff_entailsSub_fresh hfreshA hfreshB probeA_ne_probeB).symm
  -- Unsatisfiability of class `i` is the bit `i ⊑ O.classNames.length + 1`.
  have hunsat : ∀ i (hi : i < O.classNames.length),
      bitAt a.rows.toArray i (O.classNames.length + 1) = true ↔ OWL.Unsatisfiable O O.classNames[i] := by
    intro i hi
    obtain ⟨hi', hei⟩ := hget_lt i hi
    obtain ⟨hb, heb⟩ := hget_b
    rw [bitAt_toArray, hbit i (O.classNames.length + 1) hi' hb, hei, heb]
    have hne : O.classNames[i] ≠ probeB := by
      intro h
      exact hB (h ▸ List.getElem_mem hi)
    exact (OWL.unsatisfiable_iff_entailsSub_fresh hfreshB hne).symm
  -- Subsumption between classes is the bit `i ⊑ j`.
  have hsub : ∀ i j (hi : i < O.classNames.length) (hj : j < O.classNames.length),
      bitAt a.rows.toArray i j = true ↔ OWL.EntailsSub O O.classNames[i] O.classNames[j] := by
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

#print axioms probeA_ne_probeB
#print axioms routeAnswer_exact
#print axioms mentionsClass_iff_mem_classNames
#print axioms owlReadout_exact

end ContextCalculus.OWLFrontend
