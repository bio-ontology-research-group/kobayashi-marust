import ContextCalculus.SROIQ.ChainEnc

/-!
# Fast evaluation of the chain encoding (stage C3)

The definitions of `ChainEnc.lean` recompute the role hierarchy for every
hierarchy test (`leB` runs `upFix`) and the list of fresh names for every
name lookup (`nameOf` runs `pairsP`). This file gives equal definitions
that compute a table of super-roles once (`mkTab`, `leF`) and the list of
pairs once, and registers them with `@[csimp]`, so compiled code uses
them. Every replacement is a proved equality (`pairsP_eq_F`,
`encChain_eq_F`, `regularB_eq_F`); the theorems are unchanged.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (Clause Ontology RoleLe)
open ContextCalculus.SROIQ (Stack rules)

variable {n m : Nat}

/-- The chain clauses (the role hierarchy depends on them only). -/
def chainsOnly (O : Ontology (Fin n) (Fin m)) : Ontology (Fin n) (Fin m) :=
  O.filter fun
    | .chain .. => true
    | _ => false

theorem mem_chainsOnly {O : Ontology (Fin n) (Fin m)} {body : List (RT m)} {S : RT m} :
    Clause.chain body S ∈ chainsOnly O ↔ Clause.chain body S ∈ O := by
  simp [chainsOnly, List.mem_filter]

theorem roleLe_chainsOnly (O : Ontology (Fin n) (Fin m)) (R S : RT m) :
    RoleLe (chainsOnly O) R S ↔ RoleLe O R S := by
  have hs : SRI.RoleStep (SRIQ.sriPart (chainsOnly O)) = SRI.RoleStep (SRIQ.sriPart O) := by
    funext R S
    simp only [SRI.RoleStep, SRIQ.mem_sriPart, SRIQ.ofSRI, mem_chainsOnly]
  unfold SRIQ.RoleLe SRI.RoleLe
  rw [hs]

theorem leB_chainsOnly (O : Ontology (Fin n) (Fin m)) : leB (chainsOnly O) = leB O := by
  funext R S
  rw [Bool.eq_iff_iff, leB_iff, leB_iff, roleLe_chainsOnly]

/-- The super-roles of every role term, from the chain clauses. -/
def mkTab (O : Ontology (Fin n) (Fin m)) : List (RT m × List (RT m)) :=
  let C := SRIQ.sriPart (chainsOnly O)
  (allRT m).map fun R => (R, SRI.Proc.upFix C R (2 * m + 2) [R])

/-- `R ⊑₁* S` read from a table. -/
def leF (tab : List (RT m × List (RT m))) (R S : RT m) : Bool :=
  match tab.lookup R with
  | some L => decide (S ∈ L)
  | none => false

theorem lookup_map_self (f : RT m → List (RT m)) :
    ∀ (l : List (RT m)) (R : RT m), R ∈ l → (l.map fun x => (x, f x)).lookup R = some (f R)
  | [], _, h => by simp at h
  | x :: l, R, h => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases hx : R = x
    · subst hx; simp
    · have : (R == x) = false := by simp [hx]
      rw [this]
      exact lookup_map_self f l R ((List.mem_cons.1 h).resolve_left hx)

theorem leF_mkTab (O : Ontology (Fin n) (Fin m)) : leF (mkTab O) = leB O := by
  rw [← leB_chainsOnly]
  funext R S
  unfold leF mkTab leB
  rw [lookup_map_self _ _ R (mem_allRT R)]

/-- A hash for role terms. -/
instance instHashableRT : Hashable (RoleT (Fin m)) where
  hash | .pos r => mixHash 1 (hash r) | .inv r => mixHash 2 (hash r)

/-- `leF` over a hash map of the table (stage C3e: `List.lookup` made every
hierarchy test linear in the number of role terms). -/
def leH (hm : Std.HashMap (RT m) (List (RT m))) (R S : RT m) : Bool :=
  match hm[R]? with
  | some L => decide (S ∈ L)
  | none => false

theorem nodup_allRT (m : Nat) : (allRT m).Nodup := by
  unfold allRT
  rw [List.nodup_flatMap]
  refine ⟨fun r _ => by simp, ?_⟩
  refine (List.nodup_finRange m).pairwise_of_forall_ne fun a _ b _ hab => ?_
  simp only [Function.onFun, List.disjoint_cons_left, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, reduceCtorEq, false_or, RoleT.pos.injEq, RoleT.inv.injEq,
    List.disjoint_nil_left, and_true]
  exact ⟨hab, hab⟩

theorem leH_mkTab (O : Ontology (Fin n) (Fin m)) :
    leH (Std.HashMap.ofList (mkTab O)) = leB O := by
  rw [← leF_mkTab]
  funext R S
  have hp : (mkTab O).Pairwise fun a b => (a.1 == b.1) = false := by
    unfold mkTab
    rw [List.pairwise_map]
    exact (nodup_allRT m).imp fun h => by simpa using h
  have hm : (R, SRI.Proc.upFix (SRIQ.sriPart (chainsOnly O)) R (2 * m + 2) [R]) ∈ mkTab O :=
    List.mem_map.2 ⟨R, mem_allRT R, rfl⟩
  unfold leH leF
  rw [Std.HashMap.getElem?_ofList_of_mem (beq_self_eq_true R) hp hm]
  unfold mkTab
  rw [lookup_map_self _ _ R (mem_allRT R)]

/-! ## Listing -/

def expandLT (sf : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    (L : List (Stack (Fin m))) : List (Stack (Fin m)) :=
  (L ++ L.flatMap fun st => (sf st).map Prod.snd).dedup

def reachItT (sf : Stack (Fin m) → List (Option (RT m) × Stack (Fin m))) (cap : Nat) :
    Nat → List (Stack (Fin m)) → List (Stack (Fin m))
  | 0, L => L
  | k + 1, L =>
    if cap < L.length then L
    else
      let L' := expandLT sf L
      if L'.length = L.length then L else reachItT sf cap k L'

theorem reachIt_eq (O : Ontology (Fin n) (Fin m)) (cap : Nat) :
    ∀ (k : Nat) (L : List (Stack (Fin m))), reachIt O cap k L = reachItT (succs O) cap k L
  | 0, _ => rfl
  | k + 1, L => by
    simp only [reachIt, reachItT]
    have : expandL O L = expandLT (succs O) L := rfl
    rw [this, reachIt_eq O cap k]

def closedT (sf : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    (L : List (Stack (Fin m))) : Bool :=
  L.all fun st => (sf st).all fun p => decide (p.2 ∈ L)

theorem closedB_eq (O : Ontology (Fin n) (Fin m)) : closedB O = closedT (succs O) := rfl

/-- `closedT` with the listed stacks in a hash set (stage C3e: the list
membership test made the closure check quadratic in the listing). -/
def closedTH (sf : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    (L : List (Stack (Fin m))) : Bool :=
  let S := Std.HashSet.ofList L
  L.all fun st => (sf st).all fun p => S.contains p.2

@[csimp] theorem closedT_eq_H : @closedT = @closedTH := by
  funext m sf L
  simp only [closedT, closedTH, Std.HashSet.contains_ofList, List.elem_eq_mem]

/-! ## The pairs -/

def allsQT (rs : List (RT m × List (RT m))) (le : RT m → RT m → Bool)
    (O : Ontology (Fin n) (Fin m)) : List (Fin n × RT m × Fin n) :=
  O.filterMap fun
    | .allRight a S c => if rs.any (fun p => le p.1 S) then some (a, S, c) else none
    | _ => none

/-- The listing of each distinct role of `qs`, computed once per role
(stage C3e: the listing was recomputed for every universal clause). -/
def reachTab (sf : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    (qs : List (Fin n × RT m × Fin n)) : List (RT m × List (Stack (Fin m))) :=
  (qs.map (·.2.1)).dedup.map fun S => (S, reachItT sf 4096 64 [[(S, false)]])

theorem lookup_map_selfG {α β : Type} [DecidableEq α] (f : α → β) {x : α} :
    ∀ {l : List α}, x ∈ l → (l.map fun s => (s, f s)).lookup x = some (f x)
  | [], h => by simp at h
  | a :: l, h => by
    by_cases hx : x = a
    · subst hx; simp
    · have hb : (x == a) = false := by simpa using hx
      simp only [List.map_cons, List.lookup, hb]
      exact lookup_map_selfG f (by simpa [hx] using h)

theorem reachTab_lookup (sf : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    {qs : List (Fin n × RT m × Fin n)} {q : Fin n × RT m × Fin n} (hq : q ∈ qs) :
    (reachTab sf qs).lookup q.2.1 = some (reachItT sf 4096 64 [[(q.2.1, false)]]) :=
  lookup_map_selfG (fun S => reachItT sf 4096 64 [[(S, false)]])
    (List.mem_dedup.2 (List.mem_map_of_mem (f := fun q : Fin n × RT m × Fin n => q.2.1) hq))

def pairsPF (O : Ontology (Fin n) (Fin m)) : List (Pair n m) :=
  let rs := rules O
  let tab := mkTab O
  let hm := Std.HashMap.ofList tab
  let le := leH hm
  let sf := succsT rs le
  let qs := allsQT rs le O
  let tbl := reachTab sf qs
  qs.flatMap fun q => ((tbl.lookup q.2.1).getD []).map (q, ·)

@[csimp] theorem pairsP_eq_F : @pairsP = @pairsPF := by
  funext n m O
  simp only [pairsPF]
  rw [List.flatMap_congr fun q hq => by rw [reachTab_lookup _ hq, Option.getD_some]]
  simp only [leH_mkTab, succsT_eq, pairsP, reachL, reachIt_eq]
  rfl

/-- The number of fresh names, through `pairsPF`. -/
def kCF (O : Ontology (Fin n) (Fin m)) : Nat := (pairsPF O).length

@[csimp] theorem kC_eq_F : @kC = @kCF := by
  funext n m O
  simp only [kCF, kC, ← pairsP_eq_F]

/-! ## The encoding -/

section IdxG

variable {α : Type} [BEq α] [LawfulBEq α] [Hashable α]

/-- The first position of every member, as a hash map. -/
def idxMapG (l : List α) : Std.HashMap α Nat :=
  (l.zipIdx.foldr fun p m => m.insert p.1 p.2) ∅

theorem idxMapG_go (a : α) : ∀ (l : List α) (k : Nat),
    ((l.zipIdx k).foldr (fun p m => m.insert p.1 p.2) (∅ : Std.HashMap α Nat))[a]? =
      if a ∈ l then some (k + l.idxOf a) else none
  | [], k => by simp
  | x :: l, k => by
    simp only [List.zipIdx_cons, List.foldr_cons]
    rw [Std.HashMap.getElem?_insert, idxMapG_go a l (k + 1)]
    by_cases hx : x = a
    · subst hx; simp
    · have : (x == a) = false := by simp [hx]
      rw [this]
      simp only [Bool.false_eq_true, ite_false, List.mem_cons]
      have hi : List.idxOf a (x :: l) = List.idxOf a l + 1 := by
        simp [List.idxOf_cons, hx]
      rw [hi]
      by_cases ha : a ∈ l
      · simp [ha]; omega
      · simp [ha, Ne.symm hx]

theorem idxMapG_getD (l : List α) (a : α) : ((idxMapG l)[a]?).getD l.length = l.idxOf a := by
  unfold idxMapG
  rw [idxMapG_go a l 0]
  split_ifs with h
  · simp
  · simp [List.idxOf_eq_length h]

end IdxG

def encChainF (O : Ontology (Fin n) (Fin m)) : Ontology (Fin (n + kC O)) (Fin m) :=
  let P := pairsP O
  let k := P.length
  let tab := mkTab O
  let rs := rules O
  let hm := Std.HashMap.ofList tab
  let sf := succsT rs (leH hm)
  let mp := idxMapG P
  let nm : Pair n m → Option (Fin (n + kC O)) := fun p =>
    if h : (mp[p]?).getD k < k then some (Fin.natAdd n ⟨_, h⟩) else none
  O.filterMap (liftC k) ++ P.zipIdx.flatMap fun pj =>
    if h : pj.2 < k then
      let X : Fin (n + kC O) := Fin.natAdd n ⟨pj.2, h⟩
      (if pj.1.2 = [(pj.1.1.2.1, false)] then [.gci [Fin.castAdd k pj.1.1.1] [X]] else []) ++
      (if pj.1.2 = [] then [.gci [X] [Fin.castAdd k pj.1.1.2.2]] else []) ++
      (sf pj.1.2).filterMap (fun lp => (nm (pj.1.1, lp.2)).map fun Y =>
        match lp.1 with
        | some R => .allRight X R Y
        | none => .gci [X] [Y])
    else []

@[csimp] theorem encChain_eq_F : @encChain = @encChainF := by
  funext n m O
  simp only [encChainF, leH_mkTab, succsT_eq, idxMapG_getD]
  rfl

/-! ## The regularity check -/

section Close

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Fintype α]

/-- The closure, stopping at the first round that adds nothing. -/
def closeS (E : α → Finset α) : Nat → Finset α → Finset α
  | 0, A => A
  | k + 1, A =>
    let B := stepF E A
    if B = A then A else closeS E k B

theorem iter_fix {E : α → Finset α} {A : Finset α} (h : stepF E A = A) :
    ∀ k, (stepF E)^[k] A = A
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply, h, iter_fix h k]

theorem closeS_eq (E : α → Finset α) : ∀ (k : Nat) (A : Finset α), closeS E k A = (stepF E)^[k] A
  | 0, _ => rfl
  | k + 1, A => by
    simp only [closeS]
    split_ifs with h
    · exact (iter_fix h (k + 1)).symm
    · rw [closeS_eq E k, Function.iterate_succ_apply]

theorem closeS_closeF (E : α → Finset α) (A : Finset α) :
    closeS E (Fintype.card α + 1) A = closeF E A := closeS_eq E _ A

end Close

/-- `regularB` with the forced pairs computed once and each closure
stopped when it is stable. -/
def regularBF (O : Ontology (Fin n) (Fin m)) : Bool :=
  let nl := needL O
  let sc : RT m → Finset (RT m) := fun R =>
    (nl.filterMap fun p => if p.1 = R then some p.2 else none).toFinset
  let N := Fintype.card (RT m) + 1
  let C := chainsOnly O
  decide (∀ R : RT m,
    (fun A => R ∉ A ∧ ∀ S ∈ A, leB C S R = false) (closeS sc N (sc R)))

@[csimp] theorem regularB_eq_F : @regularB = @regularBF := by
  funext n m O
  simp only [regularBF, closeS_closeF, leB_chainsOnly]
  rfl

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.pairsP_eq_F
#print axioms ContextCalculus.SROIQ.Proc.encChain_eq_F
#print axioms ContextCalculus.SROIQ.Proc.regularB_eq_F
