import ContextCalculus.OWLFrontend.SRIQTranslateCorrect
import ContextCalculus.OWLFrontend.SRIReference
import ContextCalculus.SRIQ.Procedure
import ContextCalculus.SRIQ.Transitivity

/-!
# The v1.7.0 OWL route: SHIQ through the SRIQ normal form (stage C1)

`docs/V1.7.0-C1-SHIQ-DESIGN.md`, section 6. `owlSHIQReference` translates
the ontology to the SRIQ normal form (`translateSRIQ`), checks `isSHIQB`
(every role chain is an inclusion or a transitivity axiom, and every role of
a counting clause is simple), removes transitivity (`encTransQ`), classifies
the requested names with the star elimination (`classifyQO`, built on
`SRIQ.Proc.alive`) and reads out one sparse row per requested IRI, in the
format of the SHI route. An unsatisfiable name gets a row with
`unsat := true` and no listed subsumers.

The star elimination enumerates every record over the concept and role
indices of the encoding, so its run time grows exponentially with their
number; a demand-driven procedure is a later step.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy
open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

/-! ## The Boolean SHIQ check -/

/-- A chain is an inclusion or a transitivity axiom. -/
def chainOKQ {n m : Nat} : SRIQ.Clause (Fin n) (Fin m) → Bool
  | .chain body S => body.length == 1 || body == [S, S]
  | _ => true

/-- The roles of the counting clauses. -/
def countRoles {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : List (RoleT (Fin m)) :=
  O.filterMap fun
    | .atLeast _ _ R _ => some R
    | .atMost _ _ R _ => some R
    | _ => none

/-- The transitive roles: `T` with `chain [T, T] T`. -/
def transRoles {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : List (RoleT (Fin m)) :=
  O.filterMap fun
    | .chain [T, T'] S => if T = S ∧ T' = S then some S else none
    | _ => none

/-- No transitive role lies below a role of a counting clause or below its
inverse. `SRI.Proc.roleUp P T` lists the roles above `T`. -/
def simpleB {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : Bool :=
  (transRoles O).all fun T =>
    let up := SRI.Proc.roleUp (sriPart O) T
    (countRoles O).all fun R => !(up.contains R) && !(up.contains R.flip)

/-- `IsSHIQ` as a Boolean: chains are inclusions or transitivity, and the
roles of counting clauses are simple. -/
def isSHIQB {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : Bool :=
  O.all chainOKQ && simpleB O

theorem mem_countRoles {n m : Nat} {O : SRIQ.Ontology (Fin n) (Fin m)} {a b : Fin n} {k : Nat}
    {R : RoleT (Fin m)} (h : Clause.atLeast a k R b ∈ O ∨ Clause.atMost a k R b ∈ O) :
    R ∈ countRoles O := by
  rcases h with h | h <;> exact List.mem_filterMap.2 ⟨_, h, rfl⟩

theorem mem_transRoles {n m : Nat} {O : SRIQ.Ontology (Fin n) (Fin m)} {T : RoleT (Fin m)}
    (h : Clause.chain [T, T] T ∈ O) : T ∈ transRoles O :=
  List.mem_filterMap.2 ⟨_, h, by simp⟩

theorem isSHIQ_of_isSHIQB {n m : Nat} {O : SRIQ.Ontology (Fin n) (Fin m)}
    (h : isSHIQB O = true) : Proc.IsSHIQ O := by
  simp only [isSHIQB, Bool.and_eq_true] at h
  obtain ⟨hc, hs⟩ := h
  refine ⟨fun body S hcl => ?_, fun a k R b hcl T hT => ?_⟩
  · have := List.all_eq_true.1 hc _ hcl
    simp only [chainOKQ, Bool.or_eq_true, beq_iff_eq] at this
    exact this
  · have h1 := List.all_eq_true.1 hs T (mem_transRoles hT)
    have h2 := List.all_eq_true.1 h1 R (mem_countRoles hcl)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
    refine ⟨fun hle => ?_, fun hle => ?_⟩
    · have h' : (SRI.Proc.roleUp (sriPart O) T).contains R = true :=
        List.contains_iff_mem.2 (SRI.Proc.mem_roleUp.2 hle)
      rw [h2.1] at h'; exact absurd h' (by simp)
    · have h' : (SRI.Proc.roleUp (sriPart O) T).contains R.flip = true :=
        List.contains_iff_mem.2 (SRI.Proc.mem_roleUp.2 hle)
      rw [h2.2] at h'; exact absurd h' (by simp)

/-! ## Classification with the star elimination -/

namespace QProc

open ContextCalculus.SRIQ.Proc

variable {n m : Nat}

/-- Subsumption read from a set of records (`entailsQ` on `alive`). -/
def entailsA (A : Finset (QRec n m)) (a b : Fin n) : Bool :=
  decide (∀ ρ ∈ A, ρ.2 = none → a ∈ ρ.1 → b ∈ ρ.1)

/-- Satisfiability read from a set of records (`satQ` on `alive`). -/
def satA (A : Finset (QRec n m)) (a : Fin n) : Bool :=
  decide (∃ ρ ∈ A, ρ.2 = none ∧ a ∈ ρ.1)

/-- Every requested name with `none` (unsatisfiable) or its subsumers. The
record set `alive O` is computed once. -/
def classifyQO (O : SRIQ.Ontology (Fin n) (Fin m)) (req : List (Fin n)) :
    List (Fin n × Option (List (Fin n))) :=
  let A := alive O
  req.map fun a =>
    (a, if satA A a then some ((List.finRange n).filter fun b => entailsA A a b) else none)

theorem entailsA_alive (O : SRIQ.Ontology (Fin n) (Fin m)) (a b : Fin n) :
    entailsA (alive O) a b = entailsQ O a b := rfl

theorem satA_alive (O : SRIQ.Ontology (Fin n) (Fin m)) (a : Fin n) :
    satA (alive O) a = satQ O a := rfl

/-- **Classification.** Each requested name comes with `none` exactly when
it is unsatisfiable, and otherwise with exactly its subsumers. -/
theorem classifyQO_spec {O : SRIQ.Ontology (Fin n) (Fin m)} (hA : IsALCHIQ O)
    {req : List (Fin n)} :
    ∀ p ∈ classifyQO O req, p.1 ∈ req ∧
      (p.2 = none ↔
        ∀ (D : Type) [Nonempty D] (I : Interp D (Fin n) (Fin m)), models I O → ∀ x, ¬ I.c p.1 x) ∧
      ∀ L, p.2 = some L → ∀ b, b ∈ L ↔ EntailsSub O p.1 b := by
  intro p hp
  simp only [classifyQO, List.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  refine ⟨ha, ?_, ?_⟩
  · rw [← satQ_iff hA a, ← satA_alive]
    cases satA (alive O) a <;> simp
  · intro L hL b
    cases hs : satA (alive O) a
    · simp [hs] at hL
    · simp only [hs, if_true, Option.some.injEq] at hL
      subst hL
      simp only [List.mem_filter, List.mem_finRange, true_and, entailsA_alive]
      exact entailsQ_iff hA a b

end QProc

/-! ## The route -/

/-- The requested indices `0 .. named.length - 1`, as names of the
encoding. -/
def sriqRequest (T : SRIQTranslation) (k : Nat) : List (Fin (T.conceptCount + k)) :=
  List.ofFn fun i : Fin T.named.length =>
    Fin.castAdd k ⟨i.val, Nat.lt_of_lt_of_le i.isLt T.hnamed⟩

/-- One row per requested index. -/
def sriqRows (T : SRIQTranslation) {k : Nat}
    (cls : List (Fin (T.conceptCount + k) × Option (List (Fin (T.conceptCount + k))))) :
    List SparseRow :=
  sriRowsN T.named.length cls

/-- The SHIQ route. -/
def owlSHIQReference (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match translateSRIQ O requested with
  | none => none
  | some T =>
      if isSHIQB T.ontology then
        let E := SRIQ.Proc.encTransQ T.ontology
        some { named := T.named,
               rows := sriqRows T (QProc.classifyQO E.2 (sriqRequest T E.1)) }
      else none

/-! ### Exactness -/

/-- The bits of the answer over any ALCHIQ ontology on the encoded names. -/
theorem sriq_bit (T : SRIQTranslation) {k : Nat}
    {O' : SRIQ.Ontology (Fin (T.conceptCount + k)) (Fin T.roleCount)} (hA : IsALCHIQ O')
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWLAnswer.bit
        { named := T.named, rows := sriqRows T (QProc.classifyQO O' (sriqRequest T k)) } i j
        = true ↔
      SRIQ.EntailsSub O' (Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩)
        (Fin.castAdd k ⟨j, Nat.lt_of_lt_of_le hj T.hnamed⟩) := by
  obtain ⟨g, hg⟩ : ∃ g : Fin (T.conceptCount + k) → Option (List (Fin (T.conceptCount + k))),
      QProc.classifyQO O' (sriqRequest T k) = (sriqRequest T k).map fun a => (a, g a) :=
    ⟨_, rfl⟩
  have hiC : i < T.conceptCount := Nat.lt_of_lt_of_le hi T.hnamed
  have hjC : j < T.conceptCount := Nat.lt_of_lt_of_le hj T.hnamed
  have hmem : (Fin.castAdd k ⟨i, hiC⟩, g (Fin.castAdd k ⟨i, hiC⟩)) ∈
      QProc.classifyQO O' (sriqRequest T k) := by
    rw [hg]
    refine List.mem_map_of_mem ?_
    simp only [sriqRequest, List.mem_ofFn]
    exact ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨-, hnone, hsome⟩ := QProc.classifyQO_spec hA _ hmem
  have hrow : OWLAnswer.bit
      { named := T.named, rows := sriqRows T (QProc.classifyQO O' (sriqRequest T k)) } i j
      = (sriRowN T.named.length (Fin.castAdd k ⟨i, hiC⟩, g (Fin.castAdd k ⟨i, hiC⟩))).bit j := by
    simp only [OWLAnswer.bit, sriqRows, sriRowsN]
    rw [hg, List.map_map, List.getElem?_map]
    simp only [sriqRequest, List.getElem?_ofFn, hi, dite_true, Option.map_some, Function.comp]
  rw [hrow]
  cases hga : g (Fin.castAdd k ⟨i, hiC⟩) with
  | none =>
    simp only [sriRowN, SparseRow.bit, Bool.true_or, true_iff]
    intro D _ I hI x hx
    exact absurd hx (hnone.1 hga D I hI x)
  | some L =>
    simp only [sriRowN, SparseRow.bit, Bool.false_or, List.contains_iff_mem, List.mem_filter,
      List.mem_map, decide_eq_true_eq]
    rw [← hsome L hga]
    constructor
    · rintro ⟨⟨b, hb, hbj⟩, -⟩
      have : Fin.castAdd k ⟨j, hjC⟩ = b := Fin.ext (by simp [hbj])
      rw [this]; exact hb
    · intro h
      exact ⟨⟨_, h, rfl⟩, by simpa using hj⟩

/-- Every answer of the SHIQ route is exact under the OWL 2 direct
semantics, for every requested pair. -/
theorem owlSHIQReference_sound {O : OWL.Ontology} {requested : List OWL.IRI}
    {a : OWLAnswer} (h : owlSHIQReference O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlSHIQReference at h
  split at h
  · exact absurd h (by simp)
  next T hT =>
    split at h
    · next hS =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨translateSRIQ_named hT, ?_⟩
      intro i j hi hj
      rw [translateSRIQ_correct hT i j hi hj,
        SRIQ.Proc.encTransQ_correct (isSHIQ_of_isSHIQB hS)]
      exact sriq_bit T (SRIQ.Proc.encTransQ_isALCHIQ T.ontology) i j hi hj
    · exact absurd h (by simp)

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.isSHIQ_of_isSHIQB
#print axioms ContextCalculus.OWLFrontend.QProc.classifyQO_spec
#print axioms ContextCalculus.OWLFrontend.owlSHIQReference_sound
