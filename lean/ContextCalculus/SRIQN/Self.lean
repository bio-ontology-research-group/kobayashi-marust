import ContextCalculus.SRIQN.SelfLoop
import ContextCalculus.SROIQ.RegularCheck

/-!
# Self and irreflexive roles by loop names (stage C3c, design section 5, D12)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, section 5 and deviation D12. Self
clauses (`selfR body R`: `⊓body ⊑ ∃R.Self`; `selfL R head`:
`∃R.Self ⊑ ⊔head`; irreflexivity is `selfL R []`, reflexivity
`selfR [] R`) sit beside a data ontology with nominals whose object part
is ALCHIQ. The encoding `encSelfD` replaces the loops of the roles of a
set `lam` by loop names `S_R` ("an `R`-loop here"):

* `S_R` up-closed along the inclusions inside `lam` and closed under
  inverses; the self clauses become gcis on `S_R`;
* a universal clause `a ⊑ ∀T.c` gains `a ⊓ S_R ⊑ c` for `R ∈ lam`,
  `R ⊑* T`;
* an at-most clause on `T ∈ lam` gains `a ⊓ S_T ⊓ b ⊑ ≤(k-1) T.b`;
* an existential or at-least clause on `T ∈ lam` outside `irr` (roles
  below an irreflexive role) splits: `a ⊑ Z ⊔ W`, `Z ⊑ ≥k T.b`,
  `W ⊑ S_T ⊓ b ⊓ ≥(k-1) T.b`;
* each nominal name `o` (and a fresh nominal `⋆`) gets `o ⊑ ∀T.Q_o`
  (`T ∈ lam`) and `o ⊓ Q_o ⊑ ⊥`: no `lam`-loop at a nominal element.

`lam` must be closed under inverses and sub-roles, contain the roles of
the self clauses, and no at-most role outside `lam` may lie above a role
of `lam` (`LamOK`). The route computes `lam` and checks these.

* `encSelf_up`: a model of the ontology and the self clauses gives a
  model of the encoding (the `lam`-loops removed).
* `encSelf_down`: a model of the encoding whose loops sit at nominal
  elements (`ConsistentDL`) gives a model of the ontology and the self
  clauses (the loops added back from `S_R`).
* `consistentDS_iff_encSelf`: in a cell theory, for a C2a encoding, the
  ontology with the self clauses is consistent iff the encoding is
  (`loopNom_cells` supplies the loop-free model).
-/

set_option linter.unusedSimpArgs false

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory)

variable {D CName Role DProp DAtom : Type}

/-- Self clauses. -/
inductive SClause (CName Role : Type) where
  /-- `⊓body ⊑ ∃R.Self`. -/
  | selfR (body : List CName) (R : RoleT Role)
  /-- `∃R.Self ⊑ ⊔head`. -/
  | selfL (R : RoleT Role) (head : List CName)
deriving DecidableEq, Repr

/-- The role of a self clause. -/
def SClause.role : SClause CName Role → RoleT Role
  | .selfR _ R => R
  | .selfL R _ => R

/-- Satisfaction of a self clause. -/
def satS (I : Interp D CName Role) : SClause CName Role → Prop
  | .selfR body R => ∀ x, (∀ a ∈ body, I.c a x) → I.rt R x x
  | .selfL R head => ∀ x, I.rt R x x → ∃ b ∈ head, I.c b x

/-- A data model with nominals of the ontology and of the self clauses. -/
def ConsistentDS (Θ : DataTheory DAtom) (O : DOntology CName Role DProp DAtom)
    (SC : List (SClause CName Role)) : Prop :=
  ∃ (D V : Type) (_ : Nonempty D) (atom : DAtom → V → Prop), Θ V atom ∧
    ∃ I : DInterp D V CName Role DProp, SRIQD.models atom I (dbase O) ∧
      (∀ a ∈ dnoms O, NomAt I.toInterp a) ∧ ∀ sc ∈ SC, satS I.toInterp sc

/-- Without self clauses, `ConsistentDS` is `ConsistentDN`. -/
theorem consistentDS_nil (Θ : DataTheory DAtom) (O : DOntology CName Role DProp DAtom) :
    ConsistentDS Θ O [] ↔ ConsistentDN Θ O := by
  unfold ConsistentDS ConsistentDN
  simp

namespace SelfE

variable {n m p q : Nat}

/-! ## Names -/

/-- The number of fresh names over `nc` object clauses. -/
abbrev kF (n m nc : Nat) : Nat := (m + m) + ((nc + (nc + nc)) + ((n + 1) + 1))

/-- The index of a role term. -/
def rIx : RoleT (Fin m) → Fin (m + m)
  | .pos r => Fin.castAdd m r
  | .inv r => Fin.natAdd m r

/-- The role term of an index. -/
def rDec (j : Fin (m + m)) : RoleT (Fin m) := Fin.addCases (motive := fun _ => RoleT (Fin m)) .pos .inv j

@[simp] theorem rDec_rIx (R : RoleT (Fin m)) : rDec (rIx R) = R := by
  cases R <;> simp only [rDec, rIx, Fin.addCases_left, Fin.addCases_right]

variable (nc : Nat)

/-- An old name. -/
def oldN (a : Fin n) : Fin (n + kF n m nc) := Fin.castAdd _ a

/-- The loop name of a role term. -/
def sN (R : RoleT (Fin m)) : Fin (n + kF n m nc) := Fin.natAdd n (Fin.castAdd _ (rIx R))

/-- The split names of an object clause. -/
def zN (i : Fin nc) : Fin (n + kF n m nc) :=
  Fin.natAdd n (Fin.natAdd (m + m) (Fin.castAdd _ (Fin.castAdd (nc + nc) i)))

def wN (i : Fin nc) : Fin (n + kF n m nc) :=
  Fin.natAdd n (Fin.natAdd (m + m) (Fin.castAdd _ (Fin.natAdd nc (Fin.castAdd nc i))))

def yN (i : Fin nc) : Fin (n + kF n m nc) :=
  Fin.natAdd n (Fin.natAdd (m + m) (Fin.castAdd _ (Fin.natAdd nc (Fin.natAdd nc i))))

/-- The guard names of the nominals (`Fin.last n` for the fresh one). -/
def qN (o : Fin (n + 1)) : Fin (n + kF n m nc) :=
  Fin.natAdd n (Fin.natAdd (m + m) (Fin.natAdd (nc + (nc + nc)) (Fin.castAdd 1 o)))

/-- The fresh nominal. -/
def starN : Fin (n + kF n m nc) :=
  Fin.natAdd n (Fin.natAdd (m + m) (Fin.natAdd (nc + (nc + nc)) (Fin.natAdd (n + 1) (0 : Fin 1))))

/-- A function on the names, by blocks. -/
def mkC {α : Type} (fo : Fin n → α) (fs : RoleT (Fin m) → α) (fz fw fy : Fin nc → α)
    (fq : Fin (n + 1) → α) (fst : α) : Fin (n + kF n m nc) → α :=
  Fin.addCases (motive := fun _ => α) fo (Fin.addCases (motive := fun _ => α) (fun j => fs (rDec j))
    (Fin.addCases (motive := fun _ => α)
      (Fin.addCases (motive := fun _ => α) fz
        (Fin.addCases (motive := fun _ => α) fw fy))
      (Fin.addCases (motive := fun _ => α) fq (fun _ => fst))))

section MkC

variable {nc} {α : Type} (fo : Fin n → α) (fs : RoleT (Fin m) → α) (fz fw fy : Fin nc → α)
  (fq : Fin (n + 1) → α) (fst : α)

@[simp] theorem mkC_old (a : Fin n) : mkC nc fo fs fz fw fy fq fst (oldN nc a) = fo a := by
  simp only [mkC, oldN, Fin.addCases_left, Fin.addCases_right, rDec_rIx]

@[simp] theorem mkC_s (R : RoleT (Fin m)) : mkC nc fo fs fz fw fy fq fst (sN nc R) = fs R := by
  simp only [mkC, sN, Fin.addCases_left, Fin.addCases_right, rDec_rIx]

@[simp] theorem mkC_z (i : Fin nc) : mkC nc fo fs fz fw fy fq fst (zN nc i) = fz i := by
  simp only [mkC, zN, Fin.addCases_left, Fin.addCases_right, rDec_rIx]

@[simp] theorem mkC_w (i : Fin nc) : mkC nc fo fs fz fw fy fq fst (wN nc i) = fw i := by
  simp only [mkC, wN, Fin.addCases_left, Fin.addCases_right, rDec_rIx]

@[simp] theorem mkC_y (i : Fin nc) : mkC nc fo fs fz fw fy fq fst (yN nc i) = fy i := by
  simp only [mkC, yN, Fin.addCases_left, Fin.addCases_right, rDec_rIx]

@[simp] theorem mkC_q (o : Fin (n + 1)) : mkC nc fo fs fz fw fy fq fst (qN nc o) = fq o := by
  simp only [mkC, qN, Fin.addCases_left, Fin.addCases_right, rDec_rIx]

@[simp] theorem mkC_star : mkC nc fo fs fz fw fy fq fst (starN nc) = fst := by
  simp only [mkC, starN, Fin.addCases_left, Fin.addCases_right, rDec_rIx]

end MkC

theorem oldN_inj : Function.Injective (oldN (n := n) (m := m) nc) := fun a b h => by
  simpa [oldN] using h

/-! ## The encoding -/

variable (B : SRIQ.Ontology (Fin n) (Fin m)) (lam irr : List (RoleT (Fin m)))

/-- The existential and at-least clauses on `T` split. -/
def splitB (T : RoleT (Fin m)) : Bool := decide (T ∈ lam) && !decide (T ∈ irr)

abbrev NC := Fin (n + kF n m B.length)

/-- The encoding of the object clause number `i`. -/
def encObj (i : Fin B.length) : SRIQ.Clause (Fin n) (Fin m) → List (SRIQ.Clause (NC B) (Fin m))
  | .gci body head => [.gci (body.map (oldN _)) (head.map (oldN _))]
  | .chain body S => [.chain body S]
  | .exRight a T b =>
    if splitB lam irr T then
      [.gci [oldN _ a] [zN _ i, wN _ i], .exRight (zN _ i) T (oldN _ b),
        .gci [wN _ i] [sN _ T], .gci [wN _ i] [oldN _ b]]
    else [.exRight (oldN _ a) T (oldN _ b)]
  | .atLeast a k T b =>
    if splitB lam irr T then
      [.gci [oldN _ a] [zN _ i, wN _ i], .atLeast (zN _ i) k T (oldN _ b),
        .gci [wN _ i] [sN _ T], .gci [wN _ i] [oldN _ b],
        .atLeast (wN _ i) (k - 1) T (oldN _ b)]
    else [.atLeast (oldN _ a) k T (oldN _ b)]
  | .atMost a k T b =>
    .atMost (oldN _ a) k T (oldN _ b) ::
      (if T ∈ lam then
        (if k = 0 then [.gci [oldN _ a, sN _ T, oldN _ b] []]
        else [.gci [oldN _ a, sN _ T, oldN _ b] [yN _ i], .atMost (yN _ i) (k - 1) T (oldN _ b)])
      else [])
  | .allRight a T c =>
    .allRight (oldN _ a) T (oldN _ c) ::
      lam.filterMap fun R =>
        if SROIQ.Proc.leB B R T then some (.gci [oldN _ a, sN _ R] [oldN _ c]) else none

/-- The closure of the loop names. -/
def sClose : List (SRIQ.Clause (NC B) (Fin m)) :=
  lam.map (fun R => .gci [sN _ R] [sN _ R.flip]) ++
    B.filterMap fun
      | .chain [R] T => if R ∈ lam ∧ T ∈ lam then some (.gci [sN _ R] [sN _ T]) else none
      | _ => none

/-- The self clauses on the loop names. -/
def selfCl : SClause (Fin n) (Fin m) → SRIQ.Clause (NC B) (Fin m)
  | .selfR body R => .gci (body.map (oldN _)) [sN _ R]
  | .selfL R head => .gci [sN _ R] (head.map (oldN _))

/-- The nominal names of the encoding. -/
def nomL (N : List (Fin n)) : List (NC B) := N.map (oldN _) ++ [starN _]

/-- The nominal names of the encoding with their guard names. -/
def nomQ (N : List (Fin n)) : List (NC B × NC B) :=
  N.map (fun a => (oldN _ a, qN _ a.castSucc)) ++ [(starN _, qN _ (Fin.last n))]

/-- No `lam`-loop at a nominal element. -/
def forbidCls (N : List (Fin n)) : List (SRIQ.Clause (NC B) (Fin m)) :=
  (nomQ B N).flatMap fun oq => .gci [oq.1, oq.2] [] :: lam.map fun T => .allRight oq.1 T oq.2

/-- The object clauses of the encoding. -/
def objCls (SC : List (SClause (Fin n) (Fin m))) (N : List (Fin n)) :
    List (SRIQ.Clause (NC B) (Fin m)) :=
  (List.finRange B.length).flatMap (fun i => encObj B lam irr i (B.get i)) ++ sClose B lam ++
    SC.map (selfCl B) ++ forbidCls B lam N

end SelfE

open SelfE

variable {n m p q : Nat}

/-- **The Self encoding.** -/
def encSelfD (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (SC : List (SClause (Fin n) (Fin m)))
    (lam irr : List (RoleT (Fin m))) :
    DOntology (NC (SRIQD.objPart (dbase O))) (Fin m) (Fin p) (Fin q) :=
  ((objCls (SRIQD.objPart (dbase O)) lam irr SC (dnoms O)).map SRIQD.Clause.obj ++
      (dbase O).filterMap (SRIQD.Proc.liftData _)).map DClause.base ++
    (nomL _ (dnoms O)).map fun a => .nom (id a)

/-- The conditions on `lam` and `irr`. -/
structure LamOK (B : SRIQ.Ontology (Fin n) (Fin m)) (SC : List (SClause (Fin n) (Fin m)))
    (lam irr : List (RoleT (Fin m))) : Prop where
  flip : ∀ R ∈ lam, R.flip ∈ lam
  down : ∀ R T, SRIQ.RoleLe B R T → T ∈ lam → R ∈ lam
  self : ∀ sc ∈ SC, sc.role ∈ lam
  atMost : ∀ a k T b, SRIQ.Clause.atMost a k T b ∈ B → T ∉ lam → ∀ R ∈ lam, ¬ SRIQ.RoleLe B R T
  irrIn : ∀ T ∈ irr, T ∈ lam
  irrB : ∀ T ∈ irr, ∃ R, SRIQ.RoleLe B T R ∧ SClause.selfL R [] ∈ SC

section Facts

variable (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (SC : List (SClause (Fin n) (Fin m)))
  (lam irr : List (RoleT (Fin m)))

theorem dbase_encSelfD :
    dbase (encSelfD O SC lam irr) =
      (objCls (SRIQD.objPart (dbase O)) lam irr SC (dnoms O)).map SRIQD.Clause.obj ++
        (dbase O).filterMap (SRIQD.Proc.liftData _) :=
  Proc.dbase_map_noms _ _ _

theorem dnoms_encSelfD :
    dnoms (encSelfD O SC lam irr) = nomL _ (dnoms O) := by
  simp [encSelfD, dnoms, List.filterMap_append, List.filterMap_map]

theorem objPart_encSelfD :
    SRIQD.objPart (dbase (encSelfD O SC lam irr)) = objCls (SRIQD.objPart (dbase O)) lam irr SC (dnoms O) := by
  rw [dbase_encSelfD]
  exact SRIQD.Proc.objPart_lift _ _

end Facts

section Lemmas

variable {B : SRIQ.Ontology (Fin n) (Fin m)} {lam irr : List (RoleT (Fin m))}
  {SC : List (SClause (Fin n) (Fin m))} {N : List (Fin n)}

theorem mem_objCls {cl : SRIQ.Clause (NC B) (Fin m)} :
    cl ∈ objCls B lam irr SC N ↔ (∃ i, cl ∈ encObj B lam irr i (B.get i)) ∨ cl ∈ sClose B lam ∨
      cl ∈ SC.map (selfCl B) ∨ cl ∈ forbidCls B lam N := by
  simp only [objCls, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, or_assoc]

theorem mem_sClose_flip {R : RoleT (Fin m)} (h : R ∈ lam) :
    SRIQ.Clause.gci [sN _ R] [sN _ R.flip] ∈ sClose B lam :=
  List.mem_append_left _ (List.mem_map.2 ⟨R, h, rfl⟩)

theorem mem_sClose_chain {R T : RoleT (Fin m)} (hc : SRIQ.Clause.chain [R] T ∈ B) (hR : R ∈ lam)
    (hT : T ∈ lam) : SRIQ.Clause.gci [sN _ R] [sN _ T] ∈ sClose B lam := by
  refine List.mem_append_right _ (List.mem_filterMap.2 ⟨_, hc, ?_⟩)
  simp [hR, hT]

theorem mem_nomQ {a : Fin n} (ha : a ∈ N) : (oldN B.length a, qN B.length a.castSucc) ∈ nomQ B N :=
  List.mem_append_left _ (List.mem_map.2 ⟨a, ha, rfl⟩)

theorem star_mem_nomQ : (starN B.length, qN B.length (Fin.last n)) ∈ nomQ B N :=
  List.mem_append_right _ (List.mem_singleton.2 rfl)

theorem mem_forbid_gci {oq : NC B × NC B} (h : oq ∈ nomQ B N) :
    SRIQ.Clause.gci [oq.1, oq.2] [] ∈ forbidCls B lam N :=
  List.mem_flatMap.2 ⟨oq, h, List.mem_cons_self⟩

theorem mem_forbid_all {oq : NC B × NC B} (h : oq ∈ nomQ B N) {T : RoleT (Fin m)} (hT : T ∈ lam) :
    SRIQ.Clause.allRight oq.1 T oq.2 ∈ forbidCls B lam N :=
  List.mem_flatMap.2 ⟨oq, h, List.mem_cons_of_mem _ (List.mem_map.2 ⟨T, hT, rfl⟩)⟩

theorem mem_nomL {a : NC B} : a ∈ nomL B N ↔ (∃ b ∈ N, oldN _ b = a) ∨ a = starN _ := by
  simp [nomL, eq_comm]

theorem nomL_ne_nil : nomL B N ≠ [] := by simp [nomL]

theorem lamOK_flip_iff (hok : LamOK B SC lam irr) (R : RoleT (Fin m)) : R.flip ∈ lam ↔ R ∈ lam :=
  ⟨fun h => by simpa using hok.flip _ h, hok.flip R⟩

end Lemmas

/-! ## Down: from a loop-free model of the encoding -/

section Down

variable {V : Type} {atom : Fin q → V → Prop}
variable {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} {SC : List (SClause (Fin n) (Fin m))}
  {lam irr : List (RoleT (Fin m))}
variable (F : DInterp D V (NC (SRIQD.objPart (dbase O))) (Fin m) (Fin p))

/-- A loop comes from a loop name below. -/
def Lp (lam : List (RoleT (Fin m))) (T : RoleT (Fin m)) (x : D) : Prop :=
  ∃ R ∈ lam, SRIQ.RoleLe (SRIQD.objPart (dbase O)) R T ∧ F.c (sN _ R) x

/-- The interpretation with the loops of the loop names. -/
def downS (lam : List (RoleT (Fin m))) : DInterp D V (Fin n) (Fin m) (Fin p) where
  c a x := F.c (oldN _ a) x
  r s x y := F.r s x y ∨ (x = y ∧ Lp F lam (.pos s) x)
  d := F.d

variable {F} (hok : LamOK (SRIQD.objPart (dbase O)) SC lam irr)
  (hF : SRIQ.models F.toInterp (objCls (SRIQD.objPart (dbase O)) lam irr SC (dnoms O)))

include hF in
theorem sat_of_mem {cl : SRIQ.Clause (NC (SRIQD.objPart (dbase O))) (Fin m)} (h : cl ∈ objCls (SRIQD.objPart (dbase O)) lam irr SC (dnoms O)) :
    SRIQ.satClause F.toInterp cl := hF cl h

include hF in
theorem sN_flip {R : RoleT (Fin m)} (hR : R ∈ lam) {x : D} (h : F.c (sN _ R) x) :
    F.c (sN _ R.flip) x := by
  obtain ⟨b, hb, hbx⟩ := sat_of_mem hF (mem_objCls.2 (Or.inr (Or.inl (mem_sClose_flip hR)))) x
    (by simpa using h)
  simp only [List.mem_singleton] at hb
  subst hb; exact hbx

include hok hF in
theorem Lp_flip {T : RoleT (Fin m)} {x : D} (h : Lp F lam T x) : Lp F lam T.flip x := by
  obtain ⟨R, hR, hle, hs⟩ := h
  exact ⟨R.flip, hok.flip R hR, SRIQ.roleLe_flip hle, sN_flip hF hR hs⟩

include hok hF in
theorem downS_rt (T : RoleT (Fin m)) (x y : D) :
    (downS F lam).rt T x y ↔ F.rt T x y ∨ (x = y ∧ Lp F lam T x) := by
  cases T with
  | pos s => exact Iff.rfl
  | inv s =>
    show (F.r s y x ∨ (y = x ∧ Lp F lam (.pos s) y)) ↔ (F.r s y x ∨ (x = y ∧ Lp F lam (.inv s) x))
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, Lp_flip hok hF h⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, by simpa using Lp_flip hok hF h⟩

include hok hF in
/-- The loop names are up-closed inside `lam`. -/
theorem sN_up {R T : RoleT (Fin m)} (hle : SRIQ.RoleLe (SRIQD.objPart (dbase O)) R T) (hT : T ∈ lam) {x : D}
    (h : F.c (sN _ R) x) : F.c (sN _ T) x := by
  induction hle with
  | refl => exact h
  | @tail U W hRU hUW ih =>
    have hU : U ∈ lam := hok.down U W (Relation.ReflTransGen.single hUW) hT
    have hSU := ih hU
    rcases hUW with h1 | h1
    · have hc := SRIQ.mem_sriPart.1 h1
      obtain ⟨b, hb, hbx⟩ := sat_of_mem hF (mem_objCls.2 (Or.inr (Or.inl
        (mem_sClose_chain hc hU hT)))) x (by simpa using hSU)
      simp only [List.mem_singleton] at hb
      subst hb; exact hbx
    · have hc := SRIQ.mem_sriPart.1 h1
      have hf := sN_flip hF hU hSU
      obtain ⟨b, hb, hbx⟩ := sat_of_mem hF (mem_objCls.2 (Or.inr (Or.inl
        (mem_sClose_chain hc (hok.flip U hU) (hok.flip W hT))))) x (by simpa using hf)
      simp only [List.mem_singleton] at hb
      subst hb
      simpa using sN_flip hF (hok.flip W hT) hbx

include hok hF in
theorem Lp_iff {T : RoleT (Fin m)} (hT : T ∈ lam) {x : D} : Lp F lam T x ↔ F.c (sN _ T) x :=
  ⟨fun ⟨_, _, hle, hs⟩ => sN_up hok hF hle hT hs,
    fun h => ⟨T, hT, Relation.ReflTransGen.refl, h⟩⟩

variable (hL : LoopNom F.toInterp (nomL (SRIQD.objPart (dbase O)) (dnoms O)))

include hF hL in
/-- No `lam`-loop in the encoding's model. -/
theorem noloop {T : RoleT (Fin m)} (hT : T ∈ lam) (x : D) : ¬ F.rt T x x := by
  intro hx
  obtain ⟨a, ha, hax⟩ := hL T x hx
  have hq : ∃ oq ∈ nomQ (SRIQD.objPart (dbase O)) (dnoms O), oq.1 = a := by
    rcases mem_nomL.1 ha with ⟨b, hb, rfl⟩ | rfl
    · exact ⟨_, mem_nomQ hb, rfl⟩
    · exact ⟨_, star_mem_nomQ, rfl⟩
  obtain ⟨oq, hoq, rfl⟩ := hq
  have h1 := sat_of_mem hF (mem_objCls.2 (Or.inr (Or.inr (Or.inr (mem_forbid_all hoq hT))))) x hax x hx
  obtain ⟨b, hb, -⟩ := sat_of_mem hF (mem_objCls.2 (Or.inr (Or.inr (Or.inr (mem_forbid_gci hoq))))) x
    (by simp [hax, h1])
  simp at hb

theorem mem_encObj_cl {i : Fin (SRIQD.objPart (dbase O)).length} {cl : SRIQ.Clause (NC (SRIQD.objPart (dbase O))) (Fin m)}
    (h : cl ∈ encObj (SRIQD.objPart (dbase O)) lam irr i ((SRIQD.objPart (dbase O)).get i)) : cl ∈ objCls (SRIQD.objPart (dbase O)) lam irr SC (dnoms O) :=
  mem_objCls.2 (Or.inl ⟨i, h⟩)

include hok hF hL in
theorem downS_obj (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O))) : SRIQ.models (downS F lam).toInterp (SRIQD.objPart (dbase O)) := by
  classical
  intro cl0 hcl0
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 hcl0
  have hsat : ∀ cl ∈ encObj (SRIQD.objPart (dbase O)) lam irr i cl0, SRIQ.satClause F.toInterp cl := fun cl hcl =>
    sat_of_mem hF (mem_encObj_cl (SC := SC) (by rw [hi]; exact hcl))
  have hrt := downS_rt hok hF
  cases cl0 with
  | gci body head =>
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hsat (.gci (body.map (oldN _)) (head.map (oldN _))) (by simp [encObj]) x (by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact hx)
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    exact ⟨b', hb', hbx⟩
  | chain body S =>
    have hlen := hA body S hcl0
    match body, hlen, hcl0, hsat with
    | [R], _, hcl0, hsat =>
      intro x y hp
      rw [SROIQ.path_single] at hp
      rw [hrt] at hp ⊢
      rcases hp with hp | ⟨rfl, hl⟩
      · refine Or.inl ?_
        exact hsat (.chain [R] S) (by simp [encObj]) x y ((SROIQ.path_single _ _ _ _).2 hp)
      · obtain ⟨R', hR', hle, hs⟩ := hl
        exact Or.inr ⟨rfl, R', hR', SRIQ.RoleLe.trans hle (SRIQ.roleLe_single hcl0), hs⟩
  | exRight a T b =>
    intro x hx
    by_cases hs : splitB lam irr T = true
    · have hT : T ∈ lam := by simp [splitB] at hs; exact hs.1
      simp only [encObj, if_pos hs] at hsat
      obtain ⟨c, hc, hcx⟩ := hsat (.gci [oldN _ a] [zN _ i, wN _ i]) (by simp) x (by simpa using hx)
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨y, hy, hby⟩ := hsat (.exRight (zN _ i) T (oldN _ b)) (by simp) x hcx
        exact ⟨y, (hrt T x y).2 (Or.inl hy), hby⟩
      · obtain ⟨c', hc', h1⟩ := hsat (.gci [wN _ i] [sN _ T]) (by simp) x (by simpa using hcx)
        obtain ⟨c'', hc'', h2⟩ := hsat (.gci [wN _ i] [oldN _ b]) (by simp) x (by simpa using hcx)
        simp only [List.mem_singleton] at hc' hc''
        subst hc' hc''
        exact ⟨x, (hrt T x x).2 (Or.inr ⟨rfl, (Lp_iff hok hF hT).2 h1⟩), h2⟩
    · simp only [encObj, if_neg hs] at hsat
      obtain ⟨y, hy, hby⟩ := hsat (.exRight (oldN _ a) T (oldN _ b)) (by simp) x hx
      exact ⟨y, (hrt T x y).2 (Or.inl hy), hby⟩
  | atLeast a k T b =>
    intro x hx
    by_cases hs : splitB lam irr T = true
    · have hT : T ∈ lam := by simp [splitB] at hs; exact hs.1
      simp only [encObj, if_pos hs] at hsat
      obtain ⟨c, hc, hcx⟩ := hsat (.gci [oldN _ a] [zN _ i, wN _ i]) (by simp) x (by simpa using hx)
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨l, hnd, hlen, hl⟩ := hsat (.atLeast (zN _ i) k T (oldN _ b)) (by simp) x hcx
        exact ⟨l, hnd, hlen, fun y hy => ⟨(hrt T x y).2 (Or.inl (hl y hy).1), (hl y hy).2⟩⟩
      · obtain ⟨c', hc', h1⟩ := hsat (.gci [wN _ i] [sN _ T]) (by simp) x (by simpa using hcx)
        obtain ⟨c'', hc'', h2⟩ := hsat (.gci [wN _ i] [oldN _ b]) (by simp) x (by simpa using hcx)
        simp only [List.mem_singleton] at hc' hc''
        subst hc' hc''
        obtain ⟨l, hnd, hlen, hl⟩ := hsat (.atLeast (wN _ i) (k - 1) T (oldN _ b)) (by simp) x hcx
        rcases Nat.eq_zero_or_pos k with hk | hk
        · exact ⟨[], List.nodup_nil, by simp [hk], by simp⟩
        refine ⟨x :: l, List.nodup_cons.2 ⟨fun hxl => noloop hF hL hT x (hl x hxl).1, hnd⟩,
          by simp [hlen]; omega, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨(hrt T y y).2 (Or.inr ⟨rfl, (Lp_iff hok hF hT).2 h1⟩), h2⟩
        · exact ⟨(hrt T x y).2 (Or.inl (hl y hy).1), (hl y hy).2⟩
    · simp only [encObj, if_neg hs] at hsat
      obtain ⟨l, hnd, hlen, hl⟩ := hsat (.atLeast (oldN _ a) k T (oldN _ b)) (by simp) x hx
      exact ⟨l, hnd, hlen, fun y hy => ⟨(hrt T x y).2 (Or.inl (hl y hy).1), (hl y hy).2⟩⟩
  | atMost a k T b =>
    intro x hx l hnd hl
    have hmain := hsat (.atMost (oldN _ a) k T (oldN _ b)) List.mem_cons_self x hx
    by_cases hT : T ∈ lam
    · by_cases hxl : x ∈ l
      · have hloop : F.c (sN _ T) x := by
          rcases (hrt T x x).1 (hl x hxl).1 with h | ⟨-, h⟩
          · exact absurd h (noloop hF hL hT x)
          · exact (Lp_iff hok hF hT).1 h
        have hbx : F.c (oldN _ b) x := (hl x hxl).2
        have hF' : ∀ y ∈ l.erase x, F.rt T x y ∧ F.c (oldN _ b) y := by
          intro y hy
          have hy' := (List.Nodup.mem_erase_iff hnd).1 hy
          rcases (hrt T x y).1 (hl y hy'.2).1 with h | ⟨h, -⟩
          · exact ⟨h, (hl y hy'.2).2⟩
          · exact absurd h.symm hy'.1
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          obtain ⟨c, hc, -⟩ := hsat (.gci [oldN _ a, sN _ T, oldN _ b] []) (by simp [encObj, hT]) x
            (by simp [show F.c (oldN _ a) x from hx, hloop, hbx])
          simp at hc
        · have hk0 : k ≠ 0 := by omega
          obtain ⟨c, hc, hcx⟩ := hsat (.gci [oldN _ a, sN _ T, oldN _ b] [yN _ i])
            (by simp [encObj, hT, hk0]) x (by simp [show F.c (oldN _ a) x from hx, hloop, hbx])
          simp only [List.mem_singleton] at hc
          subst hc
          have := hsat (.atMost (yN _ i) (k - 1) T (oldN _ b)) (by simp [encObj, hT, hk0]) x hcx
            (l.erase x) (hnd.erase x) hF'
          rw [List.length_erase_of_mem hxl] at this
          have hl0 : 0 < l.length := List.length_pos_of_mem hxl
          omega
      · refine hmain l hnd fun y hy => ?_
        rcases (hrt T x y).1 (hl y hy).1 with h | ⟨rfl, -⟩
        · exact ⟨h, (hl y hy).2⟩
        · exact absurd hy hxl
    · refine hmain l hnd fun y hy => ?_
      rcases (hrt T x y).1 (hl y hy).1 with h | ⟨-, R, hR, hle, -⟩
      · exact ⟨h, (hl y hy).2⟩
      · exact absurd hle (hok.atMost a k T b hcl0 hT R hR)
  | allRight a T c =>
    intro x hx y hy
    rcases (hrt T x y).1 hy with h | ⟨rfl, R, hR, hle, hs⟩
    · exact hsat (.allRight (oldN _ a) T (oldN _ c)) List.mem_cons_self x hx y h
    · have hm : SRIQ.Clause.gci [oldN _ a, sN _ R] [oldN _ c] ∈
          encObj (SRIQD.objPart (dbase O)) lam irr i (.allRight a T c) := by
        refine List.mem_cons_of_mem _ (List.mem_filterMap.2 ⟨R, hR, ?_⟩)
        rw [if_pos (SROIQ.Proc.leB_iff.2 hle)]
      obtain ⟨c', hc', h'⟩ := hsat _ hm x (by simp [show F.c (oldN _ a) x from hx, hs])
      simp only [List.mem_singleton] at hc'
      subst hc'; exact h'

include hok hF hL in
theorem downS_self : ∀ sc ∈ SC, satS (downS F lam).toInterp sc := by
  intro sc hsc
  have hsat := sat_of_mem hF (mem_objCls.2 (Or.inr (Or.inr (Or.inl (List.mem_map.2 ⟨sc, hsc, rfl⟩)))))
  have hrole := hok.self sc hsc
  cases sc with
  | selfR body R =>
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hsat x (by
      simp only [selfCl, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact hx)
    simp only [List.mem_singleton] at hb
    subst hb
    exact (downS_rt hok hF R x x).2 (Or.inr ⟨rfl, (Lp_iff hok hF hrole).2 hbx⟩)
  | selfL R head =>
    intro x hx
    rcases (downS_rt hok hF R x x).1 hx with h | ⟨-, h⟩
    · exact absurd h (noloop hF hL hrole x)
    · obtain ⟨b, hb, hbx⟩ := hsat x (by simpa [selfCl] using (Lp_iff hok hF hrole).1 h)
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      exact ⟨b', hb', hbx⟩

end Down

/-- **Down.** A model of the encoding whose loops sit at nominal elements
gives a model of the ontology and the self clauses. -/
theorem encSelf_down {Θ : DataTheory (Fin q)} {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    {SC : List (SClause (Fin n) (Fin m))} {lam irr : List (RoleT (Fin m))}
    (hok : LamOK (SRIQD.objPart (dbase O)) SC lam irr) (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O)))
    (h : ConsistentDL Θ (encSelfD O SC lam irr)) : ConsistentDS Θ O SC := by
  obtain ⟨D, V, hD, atom, hΘ, F, hFm, hn, hL⟩ := h
  rw [dnoms_encSelfD] at hn hL
  obtain ⟨hFo, hFd⟩ := SRIQD.models_iff.1 hFm
  rw [objPart_encSelfD] at hFo
  refine ⟨D, V, hD, atom, hΘ, downS F lam, SRIQD.models_iff.2 ⟨downS_obj hok hFo hL hA,
    fun cl hcl y => ?_⟩, fun a ha => ?_, downS_self hok hFo hL⟩
  · cases hl : SRIQD.Proc.liftData (kF n m (SRIQD.objPart (dbase O)).length) cl with
    | none =>
      cases cl <;> simp only [SRIQD.Proc.liftData, reduceCtorEq] at hl
      trivial
    | some cl' =>
      have hm : cl' ∈ dbase (encSelfD O SC lam irr) := by
        rw [dbase_encSelfD]
        exact List.mem_append_right _ (List.mem_filterMap.2 ⟨cl, hcl, hl⟩)
      exact (SRIQD.Proc.dLocal_liftData atom hl _ _).1 (hFd cl' hm y)
  · exact hn _ (mem_nomL.2 (Or.inl ⟨a, ha, rfl⟩))

/-! ## Up: removing the `lam`-loops -/

section Up

variable {V : Type} {atom : Fin q → V → Prop}
variable {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} {SC : List (SClause (Fin n) (Fin m))}
  {lam irr : List (RoleT (Fin m))}
variable (I : DInterp D V (Fin n) (Fin m) (Fin p))

/-- An edge outside the `lam`-loops. -/
def rl (lam : List (RoleT (Fin m))) (T : RoleT (Fin m)) (x y : D) : Prop :=
  I.rt T x y ∧ ¬ (x = y ∧ T ∈ lam)

/-- The first split name: the clause holds without the loop. -/
def zS : SRIQ.Clause (Fin n) (Fin m) → D → Prop
  | .exRight a T b, x | .atLeast a _ T b, x => I.c a x ∧ ¬ (I.rt T x x ∧ I.c b x)
  | _, _ => False

/-- The second and third split names: the loop counts. -/
def wS : SRIQ.Clause (Fin n) (Fin m) → D → Prop
  | .exRight a T b, x | .atLeast a _ T b, x | .atMost a _ T b, x => I.c a x ∧ I.rt T x x ∧ I.c b x
  | _, _ => False

/-- The nominal of a guard index. -/
def jo (x0 : D) (o : Fin (n + 1)) (z : D) : Prop :=
  Fin.lastCases (motive := fun _ => Prop) (z = x0) (fun a => I.c a z) o

/-- The interpretation of the encoding. -/
def upS (B : SRIQ.Ontology (Fin n) (Fin m)) (lam : List (RoleT (Fin m))) (x0 : D) :
    DInterp D V (NC B) (Fin m) (Fin p) where
  c := mkC B.length (fun a x => I.c a x) (fun R x => I.rt R x x) (fun i => zS I (B.get i))
    (fun i => wS I (B.get i)) (fun i => wS I (B.get i))
    (fun o y => ∃ z, jo I x0 o z ∧ ∃ T ∈ lam, rl I lam T z y) (fun x => x = x0)
  r s x y := I.r s x y ∧ ¬ (x = y ∧ RoleT.pos s ∈ lam)
  d := I.d

variable {I}

local notation "BO" => SRIQD.objPart (dbase O)

variable (hok : LamOK (SRIQD.objPart (dbase O)) SC lam irr) (x0 : D)

include hok in
theorem upS_rt (T : RoleT (Fin m)) (x y : D) :
    (upS I (SRIQD.objPart (dbase O)) lam x0).rt T x y ↔ rl I lam T x y := by
  cases T with
  | pos s => exact Iff.rfl
  | inv s =>
    show (I.r s y x ∧ ¬ (y = x ∧ RoleT.pos s ∈ lam)) ↔ (I.r s y x ∧ ¬ (x = y ∧ RoleT.inv s ∈ lam))
    have : RoleT.pos s ∈ lam ↔ RoleT.inv s ∈ lam := (lamOK_flip_iff hok (.pos s)).symm
    rw [this, eq_comm]

variable (hI : SRIQD.models atom I (dbase O)) (hn : ∀ a ∈ dnoms O, NomAt I.toInterp a)
  (hS : ∀ sc ∈ SC, satS I.toInterp sc)

include hok hI hS in
theorem rl_of_not_split {T : RoleT (Fin m)} (hs : splitB lam irr T = false) {x y : D}
    (h : I.rt T x y) : rl I lam T x y := by
  refine ⟨h, ?_⟩
  rintro ⟨rfl, hT⟩
  have hirr : T ∈ irr := by simp [splitB, hT] at hs; exact hs
  obtain ⟨R, hle, hR⟩ := hok.irrB T hirr
  have hIB : SRIQ.models I.toInterp (SRIQD.objPart (dbase O)) := (SRIQD.models_iff.1 hI).1
  obtain ⟨b, hb, -⟩ := hS _ hR x (SRIQ.roleLe_sound hIB hle x x h)
  simp at hb

@[simp] theorem upS_old (B : SRIQ.Ontology (Fin n) (Fin m)) (a : Fin n) (x : D) :
    (upS I B lam x0).c (oldN _ a) x ↔ I.c a x := by simp [upS]

@[simp] theorem upS_s (B : SRIQ.Ontology (Fin n) (Fin m)) (R : RoleT (Fin m)) (x : D) :
    (upS I B lam x0).c (sN _ R) x ↔ I.rt R x x := by simp [upS]

@[simp] theorem upS_z (B : SRIQ.Ontology (Fin n) (Fin m)) (i : Fin B.length) (x : D) :
    (upS I B lam x0).c (zN _ i) x ↔ zS I (B.get i) x := by simp [upS]

@[simp] theorem upS_w (B : SRIQ.Ontology (Fin n) (Fin m)) (i : Fin B.length) (x : D) :
    (upS I B lam x0).c (wN _ i) x ↔ wS I (B.get i) x := by simp [upS]

@[simp] theorem upS_y (B : SRIQ.Ontology (Fin n) (Fin m)) (i : Fin B.length) (x : D) :
    (upS I B lam x0).c (yN _ i) x ↔ wS I (B.get i) x := by simp [upS]

@[simp] theorem upS_q (B : SRIQ.Ontology (Fin n) (Fin m)) (o : Fin (n + 1)) (y : D) :
    (upS I B lam x0).c (qN _ o) y ↔ ∃ z, jo I x0 o z ∧ ∃ T ∈ lam, rl I lam T z y := by simp [upS]

@[simp] theorem upS_star (B : SRIQ.Ontology (Fin n) (Fin m)) (x : D) :
    (upS I B lam x0).c (starN _) x ↔ x = x0 := by simp [upS]

include hok hI hS in
theorem upS_encObj (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O))) (i : Fin (SRIQD.objPart (dbase O)).length)
    {cl : SRIQ.Clause (NC (SRIQD.objPart (dbase O))) (Fin m)}
    (hcl : cl ∈ encObj (SRIQD.objPart (dbase O)) lam irr i ((SRIQD.objPart (dbase O)).get i)) :
    SRIQ.satClause (upS I (SRIQD.objPart (dbase O)) lam x0).toInterp cl := by
  classical
  have hIB : SRIQ.models I.toInterp (SRIQD.objPart (dbase O)) := (SRIQD.models_iff.1 hI).1
  have hmem : (SRIQD.objPart (dbase O)).get i ∈ SRIQD.objPart (dbase O) := List.get_mem _ _
  have hI0 := hIB _ hmem
  have hrt := upS_rt (I := I) hok x0
  generalize hc : (SRIQD.objPart (dbase O)).get i = cl0 at hcl hmem hI0
  have hz : ∀ x, (upS I (SRIQD.objPart (dbase O)) lam x0).c (zN _ i) x ↔ zS I cl0 x := by
    intro x; rw [upS_z, hc]
  have hw : ∀ x, (upS I (SRIQD.objPart (dbase O)) lam x0).c (wN _ i) x ↔ wS I cl0 x := by
    intro x; rw [upS_w, hc]
  have hy : ∀ x, (upS I (SRIQD.objPart (dbase O)) lam x0).c (yN _ i) x ↔ wS I cl0 x := by
    intro x; rw [upS_y, hc]
  cases cl0 with
  | gci body head =>
    simp only [encObj, List.mem_singleton] at hcl
    subst hcl
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hI0 x fun a ha => (upS_old (I := I) x0 _ a x).1 (hx _ (List.mem_map_of_mem ha))
    exact ⟨_, List.mem_map_of_mem hb, (upS_old x0 _ b x).2 hbx⟩
  | chain body S =>
    simp only [encObj, List.mem_singleton] at hcl
    subst hcl
    have hlen := hA body S hmem
    match body, hlen, hmem, hI0 with
    | [R], _, hmem, hI0 =>
      intro x y hp
      rw [SROIQ.path_single, hrt] at hp
      rw [hrt]
      refine ⟨hI0 x y ((SROIQ.path_single _ _ _ _).2 hp.1), ?_⟩
      rintro ⟨rfl, hS'⟩
      exact hp.2 ⟨rfl, hok.down R S (SRIQ.roleLe_single hmem) hS'⟩
  | exRight a T b =>
    by_cases hs : splitB lam irr T = true
    · have hT : T ∈ lam := by simp [splitB] at hs; exact hs.1
      simp only [encObj, if_pos hs, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hcl
      rcases hcl with rfl | rfl | rfl | rfl
      · intro x hx
        have hax : I.c a x := by simpa using hx
        by_cases hl : I.rt T x x ∧ I.c b x
        · exact ⟨wN _ i, by simp, (hw x).2 ⟨hax, hl⟩⟩
        · exact ⟨zN _ i, by simp, (hz x).2 ⟨hax, hl⟩⟩
      · intro x hx
        obtain ⟨hax, hnl⟩ := (hz x).1 hx
        obtain ⟨y, hxy, hby⟩ := hI0 x hax
        refine ⟨y, (hrt T x y).2 ⟨hxy, ?_⟩, (upS_old x0 _ b y).2 hby⟩
        rintro ⟨rfl, -⟩
        exact hnl ⟨hxy, hby⟩
      · intro x hx
        obtain ⟨-, h1, -⟩ := (hw x).1 (hx _ (List.mem_singleton.2 rfl))
        exact ⟨_, List.mem_singleton.2 rfl, (upS_s x0 _ T x).2 h1⟩
      · intro x hx
        obtain ⟨-, -, h2⟩ := (hw x).1 (hx _ (List.mem_singleton.2 rfl))
        exact ⟨_, List.mem_singleton.2 rfl, (upS_old x0 _ b x).2 h2⟩
    · simp only [encObj, if_neg hs, List.mem_singleton] at hcl
      subst hcl
      intro x hx
      obtain ⟨y, hxy, hby⟩ := hI0 x ((upS_old x0 _ a x).1 hx)
      exact ⟨y, (hrt T x y).2 (rl_of_not_split hok hI hS (by simpa using hs) hxy),
        (upS_old x0 _ b y).2 hby⟩
  | atLeast a k T b =>
    by_cases hs : splitB lam irr T = true
    · have hT : T ∈ lam := by simp [splitB] at hs; exact hs.1
      simp only [encObj, if_pos hs, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hcl
      rcases hcl with rfl | rfl | rfl | rfl | rfl
      · intro x hx
        have hax : I.c a x := by simpa using hx
        by_cases hl : I.rt T x x ∧ I.c b x
        · exact ⟨wN _ i, by simp, (hw x).2 ⟨hax, hl⟩⟩
        · exact ⟨zN _ i, by simp, (hz x).2 ⟨hax, hl⟩⟩
      · intro x hx
        obtain ⟨hax, hnl⟩ := (hz x).1 hx
        obtain ⟨l, hnd, hlen, hl⟩ := hI0 x hax
        refine ⟨l, hnd, hlen, fun y hy => ⟨(hrt T x y).2 ⟨(hl y hy).1, ?_⟩,
          (upS_old x0 _ b y).2 (hl y hy).2⟩⟩
        rintro ⟨rfl, -⟩
        exact hnl (hl x hy)
      · intro x hx
        obtain ⟨-, h1, -⟩ := (hw x).1 (hx _ (List.mem_singleton.2 rfl))
        exact ⟨_, List.mem_singleton.2 rfl, (upS_s x0 _ T x).2 h1⟩
      · intro x hx
        obtain ⟨-, -, h2⟩ := (hw x).1 (hx _ (List.mem_singleton.2 rfl))
        exact ⟨_, List.mem_singleton.2 rfl, (upS_old x0 _ b x).2 h2⟩
      · intro x hx
        obtain ⟨hax, -, -⟩ := (hw x).1 hx
        obtain ⟨l, hnd, hlen, hl⟩ := hI0 x hax
        refine ⟨(l.erase x).take (k - 1), (hnd.erase x).sublist (List.take_sublist _ _), ?_,
          fun y hy => ?_⟩
        · rw [List.length_take]
          have : k - 1 ≤ (l.erase x).length := by
            by_cases hxl : x ∈ l
            · rw [List.length_erase_of_mem hxl]; omega
            · rw [List.erase_of_not_mem hxl]; omega
          omega
        · have hy' := (List.Nodup.mem_erase_iff hnd).1 (List.mem_of_mem_take hy)
          refine ⟨(hrt T x y).2 ⟨(hl y hy'.2).1, fun h => hy'.1 h.1.symm⟩,
            (upS_old x0 _ b y).2 (hl y hy'.2).2⟩
    · simp only [encObj, if_neg hs, List.mem_singleton] at hcl
      subst hcl
      intro x hx
      obtain ⟨l, hnd, hlen, hl⟩ := hI0 x ((upS_old x0 _ a x).1 hx)
      exact ⟨l, hnd, hlen, fun y hy => ⟨(hrt T x y).2 (rl_of_not_split hok hI hS (by simpa using hs)
        (hl y hy).1), (upS_old x0 _ b y).2 (hl y hy).2⟩⟩
  | atMost a k T b =>
    simp only [encObj, List.mem_cons] at hcl
    rcases hcl with rfl | hcl
    · intro x hx l hnd hl
      exact hI0 x ((upS_old x0 _ a x).1 hx) l hnd fun y hy =>
        ⟨((hrt T x y).1 (hl y hy).1).1, (upS_old x0 _ b y).1 (hl y hy).2⟩
    · by_cases hT : T ∈ lam
      swap
      · simp [hT] at hcl
      by_cases hk : k = 0
      · simp only [if_pos hT, if_pos hk, List.mem_singleton] at hcl
        subst hcl hk
        intro x hx
        have hax : I.c a x := (upS_old x0 _ a x).1 (hx _ (by simp))
        have hlp : I.rt T x x := (upS_s x0 _ T x).1 (hx _ (by simp))
        have hbx : I.c b x := (upS_old x0 _ b x).1 (hx _ (by simp))
        have := hI0 x hax [x] (List.nodup_singleton x) (by simp [hlp, hbx])
        simp at this
      · simp only [if_pos hT, if_neg hk, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hcl
        rcases hcl with rfl | rfl
        · intro x hx
          have hax : I.c a x := (upS_old x0 _ a x).1 (hx _ (by simp))
          have hlp : I.rt T x x := (upS_s x0 _ T x).1 (hx _ (by simp))
          have hbx : I.c b x := (upS_old x0 _ b x).1 (hx _ (by simp))
          exact ⟨_, List.mem_singleton.2 rfl, (hy x).2 ⟨hax, hlp, hbx⟩⟩
        · intro x hx l hnd hl
          obtain ⟨hax, hlp, hbx⟩ := (hy x).1 hx
          have hxl : x ∉ l := fun h => ((hrt T x x).1 (hl x h).1).2 ⟨rfl, hT⟩
          have := hI0 x hax (x :: l) (List.nodup_cons.2 ⟨hxl, hnd⟩) (by
            intro y hy'
            rcases List.mem_cons.1 hy' with rfl | hy'
            · exact ⟨hlp, hbx⟩
            · exact ⟨((hrt T x y).1 (hl y hy').1).1, (upS_old x0 _ b y).1 (hl y hy').2⟩)
          simp only [List.length_cons] at this
          omega
  | allRight a T c =>
    simp only [encObj, List.mem_cons] at hcl
    rcases hcl with rfl | hcl
    · intro x hx y hxy
      exact (upS_old x0 _ c y).2 (hI0 x ((upS_old x0 _ a x).1 hx) y ((hrt T x y).1 hxy).1)
    · obtain ⟨R, hR, hcR⟩ := List.mem_filterMap.1 hcl
      by_cases hle : SROIQ.Proc.leB (SRIQD.objPart (dbase O)) R T = true
      · rw [if_pos hle, Option.some.injEq] at hcR
        subst hcR
        intro x hx
        have hax : I.c a x := (upS_old x0 _ a x).1 (hx _ (by simp))
        have hlp : I.rt R x x := (upS_s x0 _ R x).1 (hx _ (by simp))
        have := hI0 x hax x (SRIQ.roleLe_sound hIB (SROIQ.Proc.leB_iff.1 hle) x x hlp)
        exact ⟨_, List.mem_singleton.2 rfl, (upS_old x0 _ c x).2 this⟩
      · rw [if_neg hle] at hcR
        cases hcR

include hok hI hn hS in
theorem upS_obj (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O))) :
    SRIQ.models (upS I (SRIQD.objPart (dbase O)) lam x0).toInterp
      (objCls (SRIQD.objPart (dbase O)) lam irr SC (dnoms O)) := by
  classical
  have hIB : SRIQ.models I.toInterp (SRIQD.objPart (dbase O)) := (SRIQD.models_iff.1 hI).1
  have hrt := upS_rt (I := I) hok x0
  intro cl hcl
  rcases mem_objCls.1 hcl with ⟨i, hi⟩ | hc | hc | hc
  · exact upS_encObj hok x0 hI hS hA i hi
  · rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨R, -, rfl⟩ := List.mem_map.1 hc
      intro x hx
      have h := (upS_s x0 _ R x).1 (hx _ (List.mem_singleton.2 rfl))
      exact ⟨_, List.mem_singleton.2 rfl, (upS_s x0 _ _ x).2 ((SRI.Interp.rt_flip _ _ _ _).2 h)⟩
    · obtain ⟨cl0, hcl0, he⟩ := List.mem_filterMap.1 hc
      match cl0, hcl0, he with
      | .chain [R] T, hcl0, he =>
        simp only at he
        split_ifs at he with hRT
        simp only [Option.some.injEq] at he
        subst he
        intro x hx
        have h := (upS_s x0 _ R x).1 (hx _ (List.mem_singleton.2 rfl))
        exact ⟨_, List.mem_singleton.2 rfl, (upS_s x0 _ _ x).2
          (hIB _ hcl0 x x ((SROIQ.path_single _ _ _ _).2 h))⟩
  · obtain ⟨sc, hsc, rfl⟩ := List.mem_map.1 hc
    have h := hS sc hsc
    cases sc with
    | selfR body R =>
      intro x hx
      exact ⟨_, List.mem_singleton.2 rfl, (upS_s x0 _ R x).2
        (h x fun a ha => (upS_old x0 _ a x).1 (hx _ (List.mem_map_of_mem ha)))⟩
    | selfL R head =>
      intro x hx
      obtain ⟨b, hb, hbx⟩ := h x ((upS_s x0 _ R x).1 (hx _ (List.mem_singleton.2 rfl)))
      exact ⟨_, List.mem_map_of_mem hb, (upS_old x0 _ b x).2 hbx⟩
  · obtain ⟨oq, hoq, hc⟩ := List.mem_flatMap.1 hc
    -- the nominal of the pair, as a guard index
    have hj : ∃ o : Fin (n + 1), oq.2 = qN _ o ∧
        (∀ z, (upS I (SRIQD.objPart (dbase O)) lam x0).c oq.1 z ↔ jo I x0 o z) ∧
        ∀ z z', jo I x0 o z → jo I x0 o z' → z = z' := by
      rcases List.mem_append.1 hoq with h | h
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
        refine ⟨a.castSucc, rfl, fun z => by simp [jo], fun z z' hz hz' => ?_⟩
        simp only [jo, Fin.lastCases_castSucc] at hz hz'
        obtain ⟨w, hw⟩ := hn a ha
        rw [(hw z).1 hz, (hw z').1 hz']
      · rw [List.mem_singleton] at h
        subst h
        refine ⟨Fin.last n, rfl, fun z => by simp [jo], fun z z' hz hz' => ?_⟩
        simp only [jo, Fin.lastCases_last] at hz hz'
        rw [hz, hz']
    obtain ⟨o, hq, hjo, hsing⟩ := hj
    rcases List.mem_cons.1 hc with rfl | hc
    · intro y hy
      have h1 := (hjo y).1 (hy _ (by simp))
      have h2 := hy oq.2 (by simp)
      rw [hq, upS_q] at h2
      obtain ⟨z, hz, T, hT, hzy⟩ := h2
      rw [hsing z y hz h1] at hzy
      exact absurd ⟨rfl, hT⟩ hzy.2
    · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hc
      intro x hx y hxy
      rw [hq, upS_q]
      exact ⟨x, (hjo x).1 hx, T, hT, (hrt T x y).1 hxy⟩

end Up

/-- **Up.** A model of the ontology and the self clauses gives a model of
the encoding. -/
theorem encSelf_up {Θ : DataTheory (Fin q)} {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    {SC : List (SClause (Fin n) (Fin m))} {lam irr : List (RoleT (Fin m))}
    (hok : LamOK (SRIQD.objPart (dbase O)) SC lam irr) (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O)))
    (h : ConsistentDS Θ O SC) : ConsistentDN Θ (encSelfD O SC lam irr) := by
  obtain ⟨D, V, hD, atom, hΘ, I, hI, hn, hS⟩ := h
  obtain ⟨x0⟩ := hD
  refine ⟨D, V, ⟨x0⟩, atom, hΘ, upS I (SRIQD.objPart (dbase O)) lam x0, ?_, ?_⟩
  · refine SRIQD.models_iff.2 ⟨?_, fun cl hcl y => ?_⟩
    · rw [objPart_encSelfD]
      exact upS_obj hok x0 hI hn hS hA
    · rw [dbase_encSelfD] at hcl
      rcases List.mem_append.1 hcl with h1 | h1
      · obtain ⟨cl0, -, rfl⟩ := List.mem_map.1 h1
        trivial
      · obtain ⟨cl0, h0, hl⟩ := List.mem_filterMap.1 h1
        refine (SRIQD.Proc.dLocal_liftData atom hl _ (fun u => I.d u y)).2 ?_
        have hc : (fun a => (upS I (SRIQD.objPart (dbase O)) lam x0).c (Fin.castAdd _ a) y) =
            fun a => I.c a y := funext fun a => propext (upS_old x0 _ a y)
        show SRIQD.dLocal atom
          (fun a => (upS I (SRIQD.objPart (dbase O)) lam x0).c (Fin.castAdd _ a) y)
          (fun u => I.d u y) cl0
        rw [hc]
        exact (SRIQD.models_iff.1 hI).2 cl0 h0 y
  · intro a ha
    rw [dnoms_encSelfD, mem_nomL] at ha
    rcases ha with ⟨b, hb, rfl⟩ | rfl
    · obtain ⟨x, hx⟩ := hn b hb
      exact ⟨x, fun y => (upS_old x0 _ b y).trans (hx y)⟩
    · exact ⟨x0, fun y => upS_star x0 _ y⟩

/-- The encoding is ALCHIQ when the ontology is. -/
theorem isALCHIQ_encSelfD {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    {SC : List (SClause (Fin n) (Fin m))} {lam irr : List (RoleT (Fin m))}
    (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O))) :
    SRIQD.IsALCHIQ (dbase (encSelfD O SC lam irr)) := by
  unfold SRIQD.IsALCHIQ
  rw [objPart_encSelfD]
  intro body S hcl
  rcases mem_objCls.1 hcl with ⟨i, hi⟩ | hc | hc | hc
  · have hmem : (SRIQD.objPart (dbase O)).get i ∈ SRIQD.objPart (dbase O) := List.get_mem _ _
    generalize (SRIQD.objPart (dbase O)).get i = cl0 at hi hmem
    cases cl0 with
    | chain body' S' =>
      simp only [encObj, List.mem_singleton, SRIQ.Clause.chain.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact hA _ _ hmem
    | gci => simp [encObj] at hi
    | exRight a T b => simp only [encObj] at hi; split_ifs at hi <;> simp at hi
    | atLeast a k T b => simp only [encObj] at hi; split_ifs at hi <;> simp at hi
    | atMost a k T b => simp only [encObj] at hi; split_ifs at hi <;> simp at hi
    | allRight a T c =>
      simp only [encObj, List.mem_cons] at hi
      rcases hi with h | h
      · cases h
      · obtain ⟨R, -, hR⟩ := List.mem_filterMap.1 h
        split_ifs at hR <;> cases hR
  · rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨R, -, h⟩ := List.mem_map.1 hc
      cases h
    · obtain ⟨cl0, -, he⟩ := List.mem_filterMap.1 hc
      match cl0, he with
      | .chain [R] T, he =>
        simp only at he
        split_ifs at he
        cases he
  · obtain ⟨sc, -, h⟩ := List.mem_map.1 hc
    cases sc <;> cases h
  · obtain ⟨oq, -, hc⟩ := List.mem_flatMap.1 hc
    rcases List.mem_cons.1 hc with h | hc
    · cases h
    · obtain ⟨T, -, h⟩ := List.mem_map.1 hc
      cases h

/-- **The Self encoding is exact** in a cell theory, for a C2a encoding. -/
theorem consistentDS_iff_encSelf {Val K : Type} [DecidableEq K] {s : Nat} {key : Val → K}
    {cells : List K} {size : K → Option Nat} {E : Fin q → K → (Fin s → Bool) → Bool}
    (hc : SRIQD.CellSpec key cells size) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    {SC : List (SClause (Fin n) (Fin m))} {lam irr : List (RoleT (Fin m))}
    (hok : LamOK (SRIQD.objPart (dbase O)) SC lam irr) (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O)))
    (hC : IsC2aD (encSelfD O SC lam irr)) :
    ConsistentDS (SRIQD.cellTheory key E) O SC ↔
      ConsistentDN (SRIQD.cellTheory key E) (encSelfD O SC lam irr) := by
  refine ⟨encSelf_up hok hA, fun h => encSelf_down hok hA ?_⟩
  refine loopNom_cells hc (isALCHIQ_encSelfD hA) hC ?_ h
  rw [dnoms_encSelfD]
  exact nomL_ne_nil

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.encSelf_up
#print axioms ContextCalculus.SRIQN.encSelf_down
#print axioms ContextCalculus.SRIQN.consistentDS_iff_encSelf
