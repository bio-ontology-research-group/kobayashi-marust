import ContextCalculus.OWLFrontend.SROIQAnon
import ContextCalculus.SROIQ.ChainSelf
import ContextCalculus.SROIQ.ChainFast

/-!
# The OWL route with irreflexive and reflexive properties (stage C3c)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, sections 5 and 6, deviation D12. The
SROIQ(D) knowledge-base part with `IrreflexiveObjectProperty` over basic
properties (`Ontology.isSROIQDSKB`). The route moves the irreflexive and
reflexive axioms out (`selfOff`, each replaced by `SubObjectPropertyOf(p p)`),
reads them back as self clauses on the role table (`selfCls`: irreflexivity
`selfL R []`, reflexivity `selfR [] R`), eliminates the chains, and applies
the Self encoding (`SRIQN.encSelfD`) before the C2a parts.

Reflexive properties become self clauses here, not reflexivity chains, so
a reflexive property is a simple role and may occur in number restrictions
(the chain route declines that).

* `sroiqS_consistent`: `O` is consistent iff the data ontology with the
  self clauses is.
* `sroiqSParts_iff`: the decision on the encoding, exact under the checks.
* `owlSROIQDSConsistent`: the route of `owlSROIQDAConsistent` first; when it
  declines, this route on the ontology with anonymous individuals renamed.
  `_sound` and `_isSome_iff` as before.
-/

namespace ContextCalculus.OWL

/-- The property axioms read as self clauses. -/
def Axiom.isSelfAx : Axiom → Bool
  | .irreflexive r => r.isBasic
  | .reflexive r => r.isBasic
  | _ => false

/-- An axiom of the SROIQ(D) knowledge-base part with irreflexive
properties. -/
def Axiom.isSROIQDSKB (ax : Axiom) : Bool := ax.isSelfAx || ax.isSROIQDKB

def Ontology.isSROIQDSKB (O : Ontology) : Bool := O.axioms.all Axiom.isSROIQDSKB

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

variable {DM : DatatypeMap} {D : Type}

/-! ## Moving the self axioms out -/

/-- The property of a self axiom. -/
def selfProp : Axiom → Option ObjProp
  | .irreflexive r | .reflexive r => some r
  | _ => none

def selfOffAx (ax : Axiom) : List Axiom :=
  if ax.isSelfAx then (selfProp ax).toList.map fun p => .subObjectPropertyOf [p] p else [ax]

/-- The ontology without its self axioms (their properties kept). -/
def selfOff (O : Ontology) : Ontology := ⟨O.axioms.flatMap selfOffAx⟩

/-- The self axioms. -/
def selfAxs (O : Ontology) : List Axiom := O.axioms.filter Axiom.isSelfAx

theorem selfOff_isSROIQDKB {O : Ontology} (h : O.isSROIQDSKB = true) :
    (selfOff O).isSROIQDKB = true := by
  simp only [Ontology.isSROIQDSKB, List.all_eq_true] at h
  simp only [Ontology.isSROIQDKB, selfOff, List.all_eq_true, List.mem_flatMap]
  rintro ax' ⟨ax, hax, hm⟩
  unfold selfOffAx at hm
  split_ifs at hm with hr
  · cases ax with
    | irreflexive r =>
      simp only [selfProp, Option.toList_some, List.map_cons, List.map_nil,
        List.mem_singleton] at hm
      subst hm
      simp only [Axiom.isSelfAx] at hr
      simp [Axiom.isSROIQDKB, Axiom.isRoleC3, Axiom.isSHOIQDKB, Axiom.isSHIQD, Axiom.isSHI, hr]
    | reflexive r =>
      simp only [selfProp, Option.toList_some, List.map_cons, List.map_nil,
        List.mem_singleton] at hm
      subst hm
      simp only [Axiom.isSelfAx] at hr
      simp [Axiom.isSROIQDKB, Axiom.isRoleC3, Axiom.isSHOIQDKB, Axiom.isSHIQD, Axiom.isSHI, hr]
    | _ => simp [Axiom.isSelfAx] at hr
  · rw [List.mem_singleton] at hm; subst hm
    have := h ax' hax
    simpa [Axiom.isSROIQDSKB, hr] using this

theorem isSROIQDSKB_of_isSROIQDKB {O : Ontology} (h : O.isSROIQDKB = true) :
    O.isSROIQDSKB = true := by
  simp only [Ontology.isSROIQDKB, Ontology.isSROIQDSKB, List.all_eq_true] at h ⊢
  exact fun ax hax => by simp [Axiom.isSROIQDSKB, h ax hax]

theorem sat_N_self {I : Interp DM D} {ax : Axiom} (h : ax.isSelfAx = true) (N N' : List IRI) :
    I.sat N ax ↔ I.sat N' ax := by
  cases ax <;> first | exact Iff.rfl | simp [Axiom.isSelfAx] at h

theorem sat_N_sroiqS {I : Interp DM D} {ax : Axiom} (h : ax.isSROIQDSKB = true) (N N' : List IRI) :
    I.sat N ax ↔ I.sat N' ax := by
  by_cases hr : ax.isSelfAx = true
  · exact sat_N_self hr N N'
  · exact sat_N_sroiq (by simpa [Axiom.isSROIQDSKB, hr] using h) N N'

/-- **The self axioms moved out.** -/
theorem model_selfOff {O : Ontology} (h : O.isSROIQDSKB = true) (I : Interp DM D) :
    OWL.Model O I ↔ OWL.Model (selfOff O) I ∧ ∀ ax ∈ selfAxs O, I.sat [] ax := by
  have h' : ∀ ax ∈ O.axioms, ax.isSROIQDSKB = true := by
    simpa [Ontology.isSROIQDSKB, List.all_eq_true] using h
  constructor
  · intro hI
    refine ⟨fun ax' hax' => ?_, fun ax hax => ?_⟩
    · obtain ⟨ax, hax, hm⟩ := List.mem_flatMap.1 hax'
      unfold selfOffAx at hm
      split_ifs at hm with hr
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hm
        exact sat_incl I _ p
      · rw [List.mem_singleton] at hm; subst hm
        exact (sat_N_sroiqS (h' ax' hax) _ _).1 (hI ax' hax)
    · obtain ⟨hax, -⟩ := List.mem_filter.1 hax
      exact (sat_N_sroiqS (h' ax hax) _ _).1 (hI ax hax)
  · rintro ⟨hI, hR⟩ ax hax
    by_cases hr : ax.isSelfAx = true
    · exact (sat_N_sroiqS (h' ax hax) _ _).1 (hR ax (List.mem_filter.2 ⟨hax, hr⟩))
    · have hm : ax ∈ (selfOff O).axioms :=
        List.mem_flatMap.2 ⟨ax, hax, by simp [selfOffAx, hr]⟩
      exact (sat_N_sroiqS (h' ax hax) _ _).1 (hI ax hm)

/-! ## Self clauses from the role table -/

/-- The self clause of a self axiom. -/
def selfClause (T : SRIQDKBTranslation) :
    Axiom → Option (List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
  | .irreflexive r => (roleOfT T r).map fun R => [.selfL R []]
  | .reflexive r => (roleOfT T r).map fun R => [.selfR [] R]
  | _ => some []

/-- The self clauses of the self axioms. -/
def selfCls (T : SRIQDKBTranslation) (O : Ontology) :
    Option (List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  SRIQKB.collect (selfClause T) (selfAxs O)

section Corr

variable {T : SRIQDKBTranslation} {Dom : Type}

theorem sat_selfClause {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)}
    {I : Interp DM Dom} (hC : RoleCorr T K I) {ax : Axiom} (hax : ax.isSelfAx = true)
    {l : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (h : selfClause T ax = some l) : (∀ sc ∈ l, SRIQN.satS K sc) ↔ I.sat [] ax := by
  cases ax with
  | irreflexive r =>
    simp only [Axiom.isSelfAx] at hax
    simp only [selfClause] at h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [List.mem_singleton, forall_eq, SRIQN.satS, Interp.sat]
    refine forall_congr' fun x => ?_
    rw [roleCorr_of hC hax hR x x]
    simp
  | reflexive r =>
    simp only [Axiom.isSelfAx] at hax
    simp only [selfClause] at h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [List.mem_singleton, forall_eq, SRIQN.satS, Interp.sat, List.not_mem_nil,
      false_implies, implies_true, true_implies]
    exact forall_congr' fun x => roleCorr_of hC hax hR x x
  | _ => simp [Axiom.isSelfAx] at hax

theorem sat_selfCls {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)}
    {I : Interp DM Dom} (hC : RoleCorr T K I) {O : Ontology} {SC}
    (hS : selfCls T O = some SC) : (∀ sc ∈ SC, SRIQN.satS K sc) ↔ ∀ ax ∈ selfAxs O, I.sat [] ax := by
  constructor
  · intro h ax hax
    obtain ⟨l, hl, hsub⟩ := SRIQKB.collect_some hS ax hax
    exact (sat_selfClause hC (List.mem_filter.1 hax).2 hl).1 fun sc hsc => h sc (hsub sc hsc)
  · intro h sc hsc
    obtain ⟨ax, hax, l, hl, hsc'⟩ := SRIQKB.collect_mem hS sc hsc
    exact (sat_selfClause hC (List.mem_filter.1 hax).2 hl).2 (h ax hax) sc hsc'

end Corr

/-- **Consistency with self clauses.** -/
theorem sroiqS_consistent (pat : String → String → Prop) {O : Ontology} (hO : O.isSROIQDSKB = true)
    {T : SRIQDKBTranslation} (hT : translateSHOIQD (roleOff (selfOff O)) [] = some T) {E}
    (hE : roleCls T (selfOff O) = some E) {SC} (hS : selfCls T O = some SC) :
    ConsistentAt (owl2MapP pat) O ↔
      SRIQN.ConsistentDS (owlTheory pat (spec T.tab))
        (dosnC T (nomNames (roleOff (selfOff O)) []) E) SC := by
  have hO' := selfOff_isSROIQDKB hO
  constructor
  · rintro ⟨Dom, hD, I, hI⟩
    obtain ⟨hI0, hIS⟩ := (model_selfOff hO I).1 hI
    obtain ⟨hI1, hI2⟩ := (model_roleOff hO' I).1 hI0
    obtain ⟨V, atom, hΘ, K, hK, hn, hC⟩ := shoiqd_upR pat hT I hI1
    refine ⟨Dom, V, hD, atom, hΘ, K, ?_, by rw [dnoms_dosnC]; exact hn, (sat_selfCls hC hS).2 hIS⟩
    rw [dbase_dosnC, models_append_obj]
    exact ⟨by rw [← dbase_dosn T (nomNames (roleOff (selfOff O)) [])]; exact hK,
      (sat_roleCls hC hE).2 hI2⟩
  · rintro ⟨Dom, V, hD, atom, hΘ, K, hK, hn, hSK⟩
    rw [dbase_dosnC, models_append_obj] at hK
    rw [dnoms_dosnC] at hn
    obtain ⟨I, hI, hC⟩ := shoiqd_downR pat hT hΘ K (by rw [dbase_dosn]; exact hK.1) hn
    exact ⟨Dom, hD, I, (model_selfOff hO I).2
      ⟨(model_roleOff hO' I).2 ⟨hI, (sat_roleCls hC hE).1 hK.2⟩, (sat_selfCls hC hS).1 hSK⟩⟩

end ContextCalculus.OWLFrontend

/-! ## The loop roles and the checks -/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRIQN (SClause LamOK)

variable {n m : Nat}

/-- One closure step of the loop roles: below a role of a self clause, or
below an at-most role above a loop role, up to inverses. -/
def lamStep (le : RT m → RT m → Bool) (B : SRIQ.Ontology (Fin n) (Fin m))
    (SC : List (SClause (Fin n) (Fin m))) (L : List (RT m)) : List (RT m) :=
  let gens := (SC.map SClause.role ++ B.filterMap fun
    | .atMost _ _ T _ => if L.any (fun R => le R T) then some T else none
    | _ => none).dedup
  (allRT m).filter fun R => gens.any fun T => le R T || le R.flip T

/-- Iterate until nothing changes (at most `k` rounds). -/
def lamIter (f : List (RT m) → List (RT m)) : Nat → List (RT m) → List (RT m)
  | 0, L => L
  | k + 1, L => let L' := f L; if L'.length = L.length then L' else lamIter f k L'

/-- The loop roles for a given hierarchy test. -/
def lamOfL (le : RT m → RT m → Bool) (B : SRIQ.Ontology (Fin n) (Fin m))
    (SC : List (SClause (Fin n) (Fin m))) : List (RT m) :=
  lamIter (lamStep le B SC) (2 * m + 2) []

/-- The loop roles (`lam` of `SRIQN.encSelfD`), iterated to a fixpoint;
`lamOKB` checks the result. -/
def lamOf (B : SRIQ.Ontology (Fin n) (Fin m)) (SC : List (SClause (Fin n) (Fin m))) : List (RT m) :=
  let hm := Std.HashMap.ofList (mkTab B)
  let le := leH hm
  lamOfL le B SC

/-- A self clause `selfL R []` (irreflexivity). -/
def isIrrOf (le : RT m → RT m → Bool) (T : RT m) : SClause (Fin n) (Fin m) → Bool
  | .selfL R [] => le T R || le T.flip R
  | _ => false

/-- The roles below an irreflexive role. -/
def irrOfL (le : RT m → RT m → Bool) (SC : List (SClause (Fin n) (Fin m))) : List (RT m) :=
  (allRT m).filter fun T => SC.any (isIrrOf le T)

def irrOf (B : SRIQ.Ontology (Fin n) (Fin m)) (SC : List (SClause (Fin n) (Fin m))) : List (RT m) :=
  let hm := Std.HashMap.ofList (mkTab B)
  let le := leH hm
  irrOfL le SC

/-- The at-most condition of one clause. -/
def atMostOK (le : RT m → RT m → Bool) (lam : List (RT m)) : SRIQ.Clause (Fin n) (Fin m) → Bool
  | .atMost _ _ T _ => decide (T ∈ lam) || lam.all fun R => !le R T
  | _ => true

/-- **The check of `LamOK`.** -/
def lamOKBL (le : RT m → RT m → Bool) (B : SRIQ.Ontology (Fin n) (Fin m))
    (SC : List (SClause (Fin n) (Fin m))) (lam irr : List (RT m)) : Bool :=
  lam.all (fun R => decide (R.flip ∈ lam)) &&
  (allRT m).all (fun R => decide (R ∈ lam) || lam.all fun T => !le R T) &&
  SC.all (fun sc => decide (sc.role ∈ lam)) &&
  B.all (atMostOK le lam) &&
  irr.all (fun T => decide (T ∈ lam)) &&
  irr.all (fun T => SC.any (isIrrOf le T))

def lamOKB (B : SRIQ.Ontology (Fin n) (Fin m)) (SC : List (SClause (Fin n) (Fin m)))
    (lam irr : List (RT m)) : Bool :=
  let hm := Std.HashMap.ofList (mkTab B)
  let le := leH hm
  lam.all (fun R => decide (R.flip ∈ lam)) &&
  (allRT m).all (fun R => decide (R ∈ lam) || lam.all fun T => !le R T) &&
  SC.all (fun sc => decide (sc.role ∈ lam)) &&
  B.all (atMostOK le lam) &&
  irr.all (fun T => decide (T ∈ lam)) &&
  irr.all (fun T => SC.any (isIrrOf le T))

theorem lamOK_of_lamOKB {B : SRIQ.Ontology (Fin n) (Fin m)} {SC : List (SClause (Fin n) (Fin m))}
    {lam irr : List (RT m)} (h : lamOKB B SC lam irr = true) : LamOK B SC lam irr := by
  simp only [lamOKB, leH_mkTab, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, fun R T hle hT => ?_, h3, fun a k T b hcl hT R hR hle => ?_, h5, fun T hT => ?_⟩
  · rcases h2 R (mem_allRT R) with h | h
    · exact h
    · have := h T hT
      rw [leB_iff.2 hle] at this
      cases this
  · have := h4 _ hcl
    simp only [atMostOK, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at this
    rcases this with h | h
    · exact hT h
    · have := h R hR
      rw [leB_iff.2 hle] at this
      cases this
  · obtain ⟨sc, hsc, hi⟩ := List.any_eq_true.1 (h6 T hT)
    match sc, hsc, hi with
    | .selfL R [], hsc, hi =>
      simp only [isIrrOf, Bool.or_eq_true] at hi
      exact ⟨R, hi.imp leB_iff.1 leB_iff.1, hsc⟩

/-- The negative self clauses are on simple roles, from a precomputed
hierarchy test and rule list. -/
def selfSimpleBL (le : RT m → RT m → Bool) (rs : List (RT m × List (RT m)))
    (SC : List (SClause (Fin n) (Fin m))) : Bool :=
  SC.all fun
    | .selfL R _ => !rs.any fun p => le p.1 R
    | _ => true

/-- The negative self clauses are on simple roles, computed. -/
def selfSimpleB (B : SRIQ.Ontology (Fin n) (Fin m)) (SC : List (SClause (Fin n) (Fin m))) : Bool :=
  let hm := Std.HashMap.ofList (mkTab B)
  let le := leH hm
  let rs := rules B
  selfSimpleBL le rs SC

end ContextCalculus.SROIQ.Proc

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ
open ContextCalculus.SROIQ.Proc (encChainDN liftSC lamOf irrOf lamOKB selfSimpleB lamOfL irrOfL
  lamOKBL)

theorem selfSimple_of {T : SRIQDKBTranslation} {L : List IRI}
    {E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    {SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (h : selfSimpleB (objC T L E) SC = true) : SROIQ.Proc.SelfSimple (dosnC T L E) SC := by
  intro R head hsc
  simp only [selfSimpleB, SROIQ.Proc.selfSimpleBL, List.all_eq_true] at h
  have := h _ hsc
  simp only [SROIQ.Proc.leH_mkTab, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact SROIQ.Proc.simpleC_of_not_any (by rw [this]; simp)

/-- The data ontology after chain elimination. -/
abbrev chC (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  encChainDN (dosnC T L E)

/-- The self clauses after chain elimination. -/
abbrev scC (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  liftSC (dosnC T L E) SC

/-- The loop roles of the encoding. -/
abbrev lamC (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  lamOf (SRIQD.objPart (SRIQN.dbase (chC T L E))) (scC T L E SC)

abbrev irrC (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  irrOf (SRIQD.objPart (SRIQN.dbase (chC T L E))) (scC T L E SC)

/-- **The encoded data ontology**: chains eliminated, then the Self encoding. -/
abbrev encS (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  SRIQN.encSelfD (chC T L E) (scC T L E SC) (lamC T L E SC) (irrC T L E SC)

/-- **The checks**: regularity, chain elimination, simple roles of the
negative self clauses, the loop roles, C2a of the encoding (with and
without the transitivity pass), supported data atoms. -/
def sroiqSOK (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Bool :=
  SROIQ.Proc.regularB (objC T L E) && SROIQ.Proc.condB (objC T L E) &&
    selfSimpleB (objC T L E) SC &&
    lamOKB (SRIQD.objPart (SRIQN.dbase (chC T L E))) (scC T L E SC) (lamC T L E SC) (irrC T L E SC) &&
    decide (SRIQN.IsC2aD (encS T L E SC)) &&
    decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN (encS T L E SC))) &&
    (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

/-- `sroiqSOK` with the loop roles and the encoding computed once. -/
def sroiqSOKF (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Bool :=
  let B0 := objC T L E
  let D1 := chC T L E
  let B1 := SRIQD.objPart (SRIQN.dbase D1)
  let sc1 := scC T L E SC
  let hm1 := Std.HashMap.ofList (SROIQ.Proc.mkTab B1)
  let le1 := SROIQ.Proc.leH hm1
  let lam := SROIQ.Proc.lamOfL le1 B1 sc1
  let irr := SROIQ.Proc.irrOfL le1 sc1
  let D := SRIQN.encSelfD D1 sc1 lam irr
  SROIQ.Proc.regularB B0 && SROIQ.Proc.condB B0 && selfSimpleB B0 SC &&
    SROIQ.Proc.lamOKBL le1 B1 sc1 lam irr && decide (SRIQN.IsC2aD D) &&
    decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN D)) &&
    (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

@[csimp] theorem sroiqSOK_eq_F : @sroiqSOK = @sroiqSOKF := by
  funext T L E SC
  rfl

/-- The small-cell threshold. -/
def sroiqSBound (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Nat :=
  ContextCalculus.SRIQD.dbnd (SRIQN.dbase (SRIQN.Proc.encTransDN (encS T L E SC))) *
    (ContextCalculus.SRIQD.allG (allFrees (spec T.tab)).length).length

/-- Some part of the data theory accepts the encoded ontology. -/
def sroiqSParts (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hint : Option RawHint) : Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  SRIQN.consistentPartsN (encS T L E SC) cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqSBound T L E SC) (owlE sp)) (owlE sp)
    (hint.bind fun h => h.toHintN _ _)

theorem isSHIQD_of_isALCHIQ {n m p q : Nat} {O : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (h : ContextCalculus.SRIQD.IsALCHIQ (SRIQN.dbase O)) :
    ContextCalculus.SRIQD.Proc.IsSHIQD (SRIQN.dbase O) :=
  ⟨fun body S hcl => Or.inl (h body S hcl), fun a k R b _ T hT => absurd (h _ _ hT) (by simp)⟩

theorem sroiqSParts_iff (pat : String → String → Prop) {T : SRIQDKBTranslation} {L : List IRI}
    {E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    {SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (hok : sroiqSOK T L E SC = true) (hint : Option RawHint) :
    sroiqSParts T L E SC hint = true ↔
      SRIQN.ConsistentDS (owlTheory pat (spec T.tab)) (dosnC T L E) SC := by
  simp only [sroiqSOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
  have hsup : ∀ p, drSupported (spec T.tab p) = true := fun p =>
    List.all_eq_true.1 h6 p (List.mem_finRange p)
  have heq : owlTheory pat (spec T.tab) = ContextCalculus.SRIQD.cellTheory
      (cellOf (allBases (spec T.tab))) (owlE (spec T.tab)) := by
    funext V atom
    exact propext (owlTheory_iff pat hsup V atom)
  have hA1 : SRIQ.IsALCHIQ (SRIQD.objPart (SRIQN.dbase (chC T L E))) := by
    rw [SROIQ.Proc.dbase_encChainDN, SROIQ.Proc.objPart_encChainQD]
    exact SROIQ.Proc.encChain_isALCHIQ _
  rw [heq, SROIQ.Proc.consistentDS_encChainDN (SROIQ.Proc.condC_of_condB h1) (selfSimple_of h2),
    SRIQN.consistentDS_iff_encSelf (cellSpec _) (SROIQ.Proc.lamOK_of_lamOKB h3) hA1 h4]
  exact SRIQN.consistentPartsN_iff (cellSpec _) (le_refl (sroiqSBound T L E SC))
    ContextCalculus.SRIQD.splitCell_ok.1 ContextCalculus.SRIQD.splitCell_ok.2
    (isSHIQD_of_isALCHIQ (SRIQN.isALCHIQ_encSelfD hA1)) (le_refl _) h5 _

/-! ## The route -/

/-- The route on an ontology without anonymous individuals. -/
def owlSelfCore (O : OWL.Ontology) (hint : Option RawHint) : Option Bool :=
  if O.isSROIQDSKB && !(selfAxs O).isEmpty then
    match translateSHOIQD (roleOff (selfOff O)) [] with
    | none => none
    | some T =>
      match roleCls T (selfOff O) with
      | none => none
      | some E =>
        match selfCls T O with
        | none => none
        | some SC =>
          if sroiqSOK T (nomNames (roleOff (selfOff O)) []) E SC then
            some (sroiqSParts T (nomNames (roleOff (selfOff O)) []) E SC hint)
          else none
  else none

theorem owlSelfCore_sound (pat : String → String → Prop) {O : OWL.Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlSelfCore O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlSelfCore at h
  split_ifs at h with hO'
  have hO : O.isSROIQDSKB = true := (Bool.and_eq_true _ _ ▸ hO').1
  split at h
  · cases h
  next T hT =>
    split at h
    · cases h
    next E hE =>
      split at h
      · cases h
      next SC hS =>
        split_ifs at h with hok
        simp only [Option.some.injEq] at h
        subst h
        rw [sroiqSParts_iff pat hok, ← sroiqS_consistent pat hO hT hE hS]

/-- The checks of the route on the translation. -/
def SelfChecks (O : OWL.Ontology) : Prop :=
  ∀ T, translateSHOIQD (roleOff (selfOff O)) [] = some T →
    ∃ E, roleCls T (selfOff O) = some E ∧ ∃ SC, selfCls T O = some SC ∧
      sroiqSOK T (nomNames (roleOff (selfOff O)) []) E SC = true

theorem owlSelfCore_isSome_iff (O : OWL.Ontology) (hint : Option RawHint) :
    (owlSelfCore O hint).isSome = true ↔
      (O.isSROIQDSKB && !(selfAxs O).isEmpty) = true ∧ SelfChecks O := by
  constructor
  · intro h
    unfold owlSelfCore at h
    split_ifs at h with hO
    · refine ⟨hO, fun T' hT' => ?_⟩
      split at h
      · simp at h
      next T hT =>
        rw [hT] at hT'; cases hT'
        split at h
        · simp at h
        next E hE =>
          split at h
          · simp at h
          next SC hS =>
            split_ifs at h with hok
            · exact ⟨E, hE, SC, hS, hok⟩
            · simp at h
    · simp at h
  · rintro ⟨hO, hc⟩
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1
      (translateSHOIQD_isSome (roleOff_isSHOIQDKB (selfOff_isSROIQDKB
        (Bool.and_eq_true _ _ ▸ hO).1)) [])
    obtain ⟨E, hE, SC, hS, hok⟩ := hc T hT
    unfold owlSelfCore
    rw [if_pos hO, hT]
    dsimp only
    rw [hE]
    dsimp only
    rw [hS]
    dsimp only
    rw [if_pos hok]
    rfl

theorem noKey_of_isSROIQDSKB {ax : Axiom} (h : ax.isSROIQDSKB = true) : ax.noKey = true := by
  by_cases hs : ax.isSelfAx = true
  · cases ax <;> simp_all [Axiom.isSelfAx, Axiom.noKey]
  · exact noKey_of_isSROIQDKB (by simpa [Axiom.isSROIQDSKB, hs] using h)

theorem noKey_of_anonOffS {W : List IRI} {O : Ontology} (h : (anonOff W O).isSROIQDSKB = true) :
    O.noKey = true := by
  simp only [Ontology.isSROIQDSKB, anonOff, List.all_map, List.all_eq_true, Function.comp_apply] at h
  simp only [Ontology.noKey, List.all_eq_true]
  intro ax hax
  rw [← noKey_mapI (anonG W O)]
  exact noKey_of_isSROIQDSKB (h ax hax)

/-- **Consistency with irreflexive and reflexive properties**: the route of
`owlSROIQDAConsistent`, and when it declines, the Self route on the
ontology with its anonymous individuals renamed. -/
def owlSROIQDSConsistent (O : Ontology) (hint : Option RawHint) : Option Bool :=
  match owlSROIQDAConsistent O hint with
  | some v => some v
  | none => owlSelfCore (anonOff [] O) hint

/-- **Soundness.** Every answer is consistency at `owl2MapP pat`. -/
theorem owlSROIQDSConsistent_sound (pat : String → String → Prop) {O : Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDSConsistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlSROIQDSConsistent at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h
    subst h
    exact owlSROIQDAConsistent_sound pat hv
  next hv =>
    have hk : O.noKey = true := noKey_of_anonOffS
      (Bool.and_eq_true _ _ ▸ ((owlSelfCore_isSome_iff _ hint).1 (by rw [h]; rfl)).1).1
    rw [owlSelfCore_sound pat h, consistentAt_anonOff hk]

/-- **Completeness.** The route answers exactly when one of the two routes
does. -/
theorem owlSROIQDSConsistent_isSome_iff (O : Ontology) (hint : Option RawHint) :
    (owlSROIQDSConsistent O hint).isSome = true ↔
      ((anonOff [] O).isSROIQDKB = true ∧ SROIQDC2aChecks (anonOff [] O)) ∨
        (((anonOff [] O).isSROIQDSKB && !(selfAxs (anonOff [] O)).isEmpty) = true ∧
          SelfChecks (anonOff [] O)) := by
  rw [← owlSROIQDAConsistent_isSome_iff O hint, ← owlSelfCore_isSome_iff _ hint]
  unfold owlSROIQDSConsistent
  cases h : owlSROIQDAConsistent O hint <;> simp

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.model_selfOff
#print axioms ContextCalculus.OWLFrontend.sroiqS_consistent
#print axioms ContextCalculus.SROIQ.Proc.lamOK_of_lamOKB
#print axioms ContextCalculus.OWLFrontend.sroiqSParts_iff
#print axioms ContextCalculus.OWLFrontend.owlSelfCore_sound
#print axioms ContextCalculus.OWLFrontend.owlSelfCore_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSConsistent_isSome_iff
