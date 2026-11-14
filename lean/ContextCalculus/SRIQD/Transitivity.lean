import ContextCalculus.SRIQD.Procedure
import ContextCalculus.SRIQ.ABox

/-!
# Transitivity for SHIQ with data (stage C4, step 3)

`encTransQD` applies `SRIQ.Proc.encTransQ` to the object part and passes
the data clauses through on the old names. Data clauses mention concept
names and data properties only, and the model maps of
`SRIQ/Transitivity.lean` keep the old names and leave the data relation
alone, so the encoding keeps subsumption between old names under the
SHIQ conditions on the object part (`encTransQD_correct`). Its object
part is ALCHIQ (`encTransQD_isALCHIQ`), so `classifyQD` applies; the
composition is `entailsQDS` (`entailsQDS_iff`).
-/

namespace ContextCalculus.SRIQD.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ.Proc (encTransQ models_upI models_downI)

variable {n m p q : Nat} {V : Type}

/-- The object part is SHIQ: chains are inclusions or transitivity, and
counting clauses use simple roles. -/
def IsSHIQD (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) : Prop :=
  SRIQ.Proc.IsSHIQ (objPart O)

/-- A data clause on the old names of an encoding with `k` new names. -/
def liftData (k : Nat) :
    Clause (Fin n) (Fin m) (Fin p) (Fin q) → Option (Clause (Fin (n + k)) (Fin m) (Fin p) (Fin q))
  | .obj _ => none
  | .dEx a u pos neg => some (.dEx (Fin.castAdd k a) u pos neg)
  | .dAll a u head => some (.dAll (Fin.castAdd k a) u head)
  | .dAtLeast a j u pos neg => some (.dAtLeast (Fin.castAdd k a) j u pos neg)
  | .dAtMost a j u pos neg => some (.dAtMost (Fin.castAdd k a) j u pos neg)
  | .dSub u w => some (.dSub u w)

/-- The encoding: `encTransQ` on the object part, the data clauses
unchanged on the old names. -/
def encTransQD (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) :
    Σ k, Ontology (Fin (n + k)) (Fin m) (Fin p) (Fin q) :=
  ⟨(encTransQ (objPart O)).1,
    (encTransQ (objPart O)).2.map Clause.obj ++ O.filterMap (liftData (encTransQ (objPart O)).1)⟩

theorem objPart_lift {k : Nat} (L : SRIQ.Ontology (Fin (n + k)) (Fin m))
    (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) :
    objPart (L.map (Clause.obj (DProp := Fin p) (DAtom := Fin q)) ++ O.filterMap (liftData k)) =
      L := by
  have h2 : List.filterMap (toObj (CName := Fin (n + k)) (Role := Fin m))
      (O.filterMap (liftData k)) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro cl hcl
    obtain ⟨cl0, -, he⟩ := List.mem_filterMap.1 hcl
    cases cl0 <;> simp only [liftData, Option.some.injEq, reduceCtorEq] at he <;> subst he <;> rfl
  unfold objPart
  rw [List.filterMap_append, List.filterMap_map, h2, List.append_nil]
  simp [toObj]

theorem objPart_encTransQD (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) :
    objPart (encTransQD O).2 = (encTransQ (objPart O)).2 :=
  objPart_lift _ O

theorem encTransQD_isALCHIQ (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) :
    IsALCHIQ (encTransQD O).2 := by
  unfold IsALCHIQ
  rw [objPart_encTransQD]
  exact SRIQ.Proc.encTransQ_isALCHIQ _

/-- A lifted data clause holds where the original holds on the old names. -/
theorem dLocal_liftData (atom : Fin q → V → Prop) {k : Nat} {cl : Clause (Fin n) (Fin m) (Fin p) (Fin q)}
    {cl' : Clause (Fin (n + k)) (Fin m) (Fin p) (Fin q)} (h : liftData k cl = some cl')
    (c : Fin (n + k) → Prop) (d : Fin p → V → Prop) :
    dLocal atom c d cl' ↔ dLocal atom (fun a => c (Fin.castAdd k a)) d cl := by
  cases cl <;> simp only [liftData, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- **Transitivity removal with data.** For a SHIQ object part, the
encoding keeps subsumption between the old names, for every data theory. -/
theorem encTransQD_correct {Θ : DataTheory (Fin q)} {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    (h : IsSHIQD O) (a b : Fin n) :
    EntailsSub Θ O a b ↔
      EntailsSub Θ (encTransQD O).2 (Fin.castAdd _ a) (Fin.castAdd _ b) := by
  constructor
  · intro hO D V _ atom hΘ J hJ x hx
    obtain ⟨hJo, hJd⟩ := models_iff.1 hJ
    rw [objPart_encTransQD] at hJo
    let I : DInterp D V (Fin n) (Fin m) (Fin p) :=
      { toInterp := SRI.Proc.downI (SRIQ.sriPart (objPart O)) J.toInterp, d := J.d }
    refine hO D V atom hΘ I (models_iff.2 ⟨models_downI h hJo, fun cl hcl y => ?_⟩) x hx
    cases hl : liftData (encTransQ (objPart O)).1 cl with
    | none =>
      cases cl <;> simp only [liftData, reduceCtorEq] at hl
      trivial
    | some cl' =>
      have := hJd cl' (List.mem_append_right _ (List.mem_filterMap.2 ⟨cl, hcl, hl⟩)) y
      exact (dLocal_liftData atom hl _ _).1 this
  · intro hE D V _ atom hΘ I hI x hx
    obtain ⟨hIo, hId⟩ := models_iff.1 hI
    let J : DInterp D V (Fin (n + (encTransQD O).1)) (Fin m) (Fin p) :=
      { toInterp := SRI.Proc.upI (SRIQ.sriPart (objPart O)) I.toInterp, d := I.d }
    have hc : ∀ y, (fun a => J.c (Fin.castAdd _ a) y) = fun a => I.c a y := fun y =>
      funext fun a => propext (SRI.Proc.upI_old I.toInterp a y)
    have hJ : models atom J (encTransQD O).2 := by
      refine models_iff.2 ⟨?_, fun cl hcl y => ?_⟩
      · rw [objPart_encTransQD]
        exact models_upI hIo
      · rcases List.mem_append.1 hcl with h1 | h1
        · obtain ⟨cl0, -, rfl⟩ := List.mem_map.1 h1
          trivial
        · obtain ⟨cl0, h0, hl⟩ := List.mem_filterMap.1 h1
          refine (dLocal_liftData atom hl (fun a => J.c a y) (fun u => J.d u y)).2 ?_
          show dLocal atom (fun a => J.c (Fin.castAdd _ a) y) (fun u => I.d u y) cl0
          rw [hc]
          exact hId cl0 h0 y
    have := hE D V atom hΘ J hJ x ((SRI.Proc.upI_old I.toInterp a x).2 hx)
    exact (SRI.Proc.upI_old I.toInterp b x).1 this

/-- Subsumption for SHIQ with data: `entailsQD` on the encoding. -/
def entailsQDS (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat)
    (a b : Fin n) : Bool :=
  entailsQD (encTransQD O).2 card (Fin.castAdd _ a) (Fin.castAdd _ b)

theorem entailsQDS_iff {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat}
    (hspec : OracleSpec Θ card) {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)} (h : IsSHIQD O)
    (a b : Fin n) : entailsQDS O card a b = true ↔ EntailsSub Θ O a b := by
  rw [entailsQDS, entailsQD_iff hspec (encTransQD_isALCHIQ O), encTransQD_correct h]

end ContextCalculus.SRIQD.Proc

#print axioms ContextCalculus.SRIQD.Proc.encTransQD_isALCHIQ
#print axioms ContextCalculus.SRIQD.Proc.encTransQD_correct
#print axioms ContextCalculus.SRIQD.Proc.entailsQDS_iff
