import ContextCalculus.SRIQN.Procedure

/-!
# A lazy hint check (stage C3c, check speed)

Compiled, `checkRealisationN` computed the alive records (`aliveN`, an
elimination over every record, exponential in the names) even when the
hint has no children or a certificate, so a hint over a few dozen names ran
out of memory. `checkRealisationNF` is the same Boolean with the three
cases as nested `if`s and the elimination behind a `Unit` argument; it is
registered with `@[csimp]` (`checkRealisationN_eq_F`), so no theorem
changes.
-/

namespace ContextCalculus.SRIQ.Proc

variable {n m : Nat}

/-- The star check as a Boolean over the clause lists. -/
def starOKB (O : SRIQ.Ontology (Fin n) (Fin m)) (t : Finset (Fin n)) (N : List (QNbr n m)) : Bool :=
  decide (SRIQ.Closed O t) &&
  N.all (fun e => decide (SRIQ.UpClosed O e.1) && decide (SRIQ.EdgeOK O t e)) &&
  (SRIQ.lowerL O).all (fun q => !decide (q.1 ∈ t) || decide (q.2.1 ≤ SRIQ.cnt N q.2.2.1 q.2.2.2)) &&
  (SRIQ.upperL O).all (fun q => !decide (q.1 ∈ t) || decide (SRIQ.cnt N q.2.2.1 q.2.2.2 ≤ q.2.1))

theorem starOKB_iff (O : SRIQ.Ontology (Fin n) (Fin m)) (t : Finset (Fin n)) (N : List (QNbr n m)) :
    starOKB O t N = true ↔ SRIQ.StarOK O t N := by
  rw [starOK_iff]
  simp only [starOKB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, fun q hq ht => (h3 q hq).resolve_left (not_not.2 ht),
      fun q hq ht => (h4 q hq).resolve_left (not_not.2 ht)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun q hq => ?_⟩, fun q hq => ?_⟩
    · by_cases ht : q.1 ∈ t
      · exact Or.inr (h3 q hq ht)
      · exact Or.inl ht
    · by_cases ht : q.1 ∈ t
      · exact Or.inr (h4 q hq ht)
      · exact Or.inl ht

/-- The star decision through `starOKB`. -/
def decStarOKF (O : SRIQ.Ontology (Fin n) (Fin m)) (t : Finset (Fin n)) (N : List (QNbr n m)) :
    Decidable (SRIQ.StarOK O t N) :=
  decidable_of_iff _ (starOKB_iff O t N)

/-- The compiled star decision built `Finset.powerset` (exponential in the
names); this equal instance does not. -/
@[csimp] theorem instDecidableStarOKFin_eq_F : @instDecidableStarOKFin = @decStarOKF := by
  funext n m O t N
  exact Subsingleton.elim _ _

end ContextCalculus.SRIQ.Proc

namespace ContextCalculus.SRIQN.Proc

variable {n m : Nat}

/-- The elimination case of the hint check, delayed. -/
@[noinline] def aliveChk (B : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n)) (h : HintN n m)
    (_ : Unit) : Bool :=
  let G := aliveN B N h.ty
  decide (∀ b, ∀ e ∈ h.kids b, anchorRec b e ∈ G)

def checkRealisationNF (B : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n)) (h : HintN n m) : Bool :=
  if decide (0 < h.k ∧ coreOKN N h.ty h.lab ∧
      ∀ b, SRIQ.StarOK B (h.ty b) (SRIQ.Proc.nbrsL h.ty h.lab b ++ h.kids b)) then
    if (List.finRange h.k).all (fun b => (h.kids b).isEmpty) then true
    else if decide (CertOK B N h) then true
    else aliveChk B N h ()
  else false

@[csimp] theorem checkRealisationN_eq_F : @checkRealisationN = @checkRealisationNF := by
  funext n m B N h
  unfold checkRealisationN checkRealisationNF aliveChk
  split_ifs with h1 h2 h3 <;> simp_all

/-- `consistentN` through the lazy check (callers compiled after this file
use it). -/
def consistentNF (B : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n)) (hint : Option (HintN n m)) :
    Bool :=
  hint.any (checkRealisationNF B N) || searchN B N

@[csimp] theorem consistentN_eq_F : @consistentN = @consistentNF := by
  funext n m B N hint
  rw [consistentN, consistentNF, checkRealisationN_eq_F]

end ContextCalculus.SRIQN.Proc

#print axioms ContextCalculus.SRIQ.Proc.instDecidableStarOKFin_eq_F
#print axioms ContextCalculus.SRIQN.Proc.checkRealisationN_eq_F
#print axioms ContextCalculus.SRIQN.Proc.consistentN_eq_F
