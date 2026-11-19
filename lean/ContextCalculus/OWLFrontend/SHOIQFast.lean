import ContextCalculus.OWLFrontend.SHOIQDC2aReference

/-!
# Fast evaluation of the nominal rewriting (stage C3, check speed)

`nmOf O requested a` recomputes the individual list and the base of the
nominal classes for every individual, and finds the index by a linear
search; `nameIx` does the same for the named IRIs of a translation. On
inputs with tens of thousands of individuals the rewriting is quadratic.
This file gives equal definitions that build an index table once
(`idxFast`, a hash map from an IRI to its first position, `idxFast_eq`)
and registers them with `@[csimp]`: `nomOntD`, `nomNames`,
`translateSHOIQD`, `nomIxs`, `dosn`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL SHIQD SHOIQ

/-- The first position of every member, as a hash map. -/
def idxMap {α : Type} [DecidableEq α] [Hashable α] (l : List α) : Std.HashMap α Nat :=
  (l.zipIdx.foldr fun p m => m.insert p.1 p.2) ∅

theorem idxMap_go {α : Type} [DecidableEq α] [Hashable α] (a : α) : ∀ (l : List α) (k : Nat),
    ((l.zipIdx k).foldr (fun p m => m.insert p.1 p.2) (∅ : Std.HashMap α Nat))[a]? =
      if a ∈ l then some (k + l.idxOf a) else none
  | [], k => by simp
  | x :: l, k => by
    simp only [List.zipIdx_cons, List.foldr_cons]
    rw [Std.HashMap.getElem?_insert, idxMap_go a l (k + 1)]
    by_cases hx : x = a
    · subst hx; simp
    · have : (x == a) = false := by simp [hx]
      rw [this]
      simp only [Bool.false_eq_true, ite_false, List.mem_cons]
      have hi : List.idxOf a (x :: l) = List.idxOf a l + 1 := by
        simp [hx]
      rw [hi]
      by_cases ha : a ∈ l
      · simp [ha]; omega
      · simp [ha, Ne.symm hx]

/-- The position of `a` in `l` (`l.length` if absent), through the table. -/
def idxFast {α : Type} [DecidableEq α] [Hashable α] (l : List α) : α → Nat :=
  let m := idxMap l
  fun a => (m[a]?).getD l.length

theorem idxFast_eq {α : Type} [DecidableEq α] [Hashable α] (l : List α) :
    idxFast l = fun a => l.idxOf a := by
  funext a
  unfold idxFast idxMap
  have := idxMap_go a l 0
  rw [this]
  split_ifs with h
  · simp
  · simp [List.idxOf_eq_length h]

theorem idxMap_getD {α : Type} [DecidableEq α] [Hashable α] (l : List α) (a : α) :
    ((idxMap l)[a]?).getD l.length = l.idxOf a :=
  congrFun (idxFast_eq l) a

/-! ## The nominal rewriting -/

def nomOntDF (O : Ontology) (requested : List IRI) : Ontology :=
  let base := nomBase O requested
  let inds := O.individualNames
  let m := idxMap inds
  let len := inds.length
  ⟨O.axioms.flatMap (rwAxD fun a => nomName base ((m[a]?).getD len))⟩

@[csimp] theorem nomOntD_eq_F : @nomOntD = @nomOntDF := by
  funext O requested
  simp only [nomOntDF, idxMap_getD]
  rfl

def nomNamesF (O : Ontology) (requested : List IRI) : List IRI :=
  let base := nomBase O requested
  let inds := O.individualNames
  let m := idxMap inds
  let len := inds.length
  inds.map fun a => nomName base ((m[a]?).getD len)

@[csimp] theorem nomNames_eq_F : @nomNames = @nomNamesF := by
  funext O requested
  simp only [nomNamesF, idxMap_getD]
  rfl

/-! ## Removing duplicates with a hash set -/

def dedupGo : Std.HashSet IRI → List IRI → List IRI
  | _, [] => []
  | s, a :: as => if s.contains a then dedupGo s as else a :: dedupGo (s.insert a) as

theorem dedupGo_eq : ∀ (l : List IRI) (s : Std.HashSet IRI),
    dedupGo s l = (l.filter fun x => !s.contains x).eraseDups
  | [], s => by simp [dedupGo]
  | a :: as, s => by
    by_cases h : s.contains a = true
    · simp only [dedupGo, h, if_true, List.filter_cons, Bool.not_true, Bool.false_eq_true]
      exact dedupGo_eq as s
    · simp only [dedupGo, h, Bool.false_eq_true, if_false, List.filter_cons, Bool.not_false,
        if_true, List.eraseDups_cons]
      rw [dedupGo_eq as (s.insert a), List.filter_filter]
      congr 2
      apply List.filter_congr
      intro x _
      rw [Std.HashSet.contains_insert]
      by_cases hxa : x = a
      · subst hxa; simp [h]
      · have h1 : (a == x) = false := beq_false_of_ne fun e => hxa e.symm
        have h2 : (x == a) = false := beq_false_of_ne hxa
        rw [h1, h2]; simp

/-- Duplicates removed with a hash set; equal to `eraseDups`. -/
def eraseDupsH (l : List IRI) : List IRI := dedupGo ∅ l

theorem eraseDupsH_eq (l : List IRI) : eraseDupsH l = l.eraseDups := by
  simp [eraseDupsH, dedupGo_eq]

/-- Last-occurrence deduplication step with a hash set. -/
def dedupStepS {α : Type} [DecidableEq α] [Hashable α] (a : α) (r : Std.HashSet α × List α) :
    Std.HashSet α × List α :=
  if r.1.contains a then r else (r.1.insert a, a :: r.2)

theorem dedupRS_spec {α : Type} [DecidableEq α] [Hashable α] :
    ∀ (l : List α), (l.foldr dedupStepS (∅, [])).2 = l.dedup ∧
      ∀ x, (l.foldr dedupStepS (∅, [])).1.contains x = decide (x ∈ l.dedup)
  | [] => by simp
  | a :: as => by
    obtain ⟨h2, h1⟩ := dedupRS_spec as
    simp only [List.foldr_cons, dedupStepS, h1 a]
    by_cases hm : a ∈ as.dedup
    · simp only [decide_eq_true hm, if_true, h2, List.dedup_cons_of_mem' hm]
      exact ⟨trivial, h1⟩
    · simp only [decide_eq_false hm, Bool.false_eq_true, if_false, h2,
        List.dedup_cons_of_notMem' hm]
      refine ⟨trivial, fun x => ?_⟩
      rw [Std.HashSet.contains_insert, h1 x]
      by_cases hxa : x = a
      · subst hxa; simp
      · have hb : (a == x) = false := beq_false_of_ne fun e => hxa e.symm
        simp [hb, hxa]

/-- Tail-recursive last-occurrence deduplication with a hash set; equal to `List.dedup`. -/
def dedupHS {α : Type} [DecidableEq α] [Hashable α] (l : List α) : List α :=
  (l.reverse.foldl (fun r a => dedupStepS a r) (∅, [])).2

theorem dedupHS_eq {α : Type} [DecidableEq α] [Hashable α] (l : List α) : dedupHS l = l.dedup := by
  unfold dedupHS
  rw [← List.foldr_eq_foldl_reverse]
  exact (dedupRS_spec l).1

instance instHashableLiteral : Hashable Literal where
  hash l := mixHash (hash l.lexical) (mixHash (hash l.datatype) (hash l.lang))

def hashDR : DataRange → UInt64
  | .datatype t => mixHash 1 (hash t)
  | .and rs => rs.attach.foldl (fun h ⟨r, _⟩ => mixHash h (hashDR r)) 2
  | .or rs => rs.attach.foldl (fun h ⟨r, _⟩ => mixHash h (hashDR r)) 3
  | .not r => mixHash 4 (hashDR r)
  | .oneOf ls => mixHash 5 (hash ls)
  | .restriction t fs => mixHash 6 (mixHash (hash t) (hash fs))
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

instance instHashableDataRange : Hashable DataRange where
  hash := hashDR

instance instHashableDataProp : Hashable DataProp where
  hash
    | .named r => mixHash 1 (hash r)
    | .top => 3
    | .bot => 4

instance instHashableDExpr : Hashable DExpr where
  hash e := mixHash (hash e.kind) (mixHash (hash e.n) (mixHash (hash e.p) (hash e.R)))

/-- `SHIQD.spec` through an array computed once, wrapped in a structure so
that the compiler does not eta-expand the array construction into each lookup. -/
def useSpec (arr : Array DataRange) (q : Nat) (h : arr.size = q) (j : Fin q) : DataRange :=
  arr[j.val]'(by rw [h]; exact j.isLt)

structure SpecS (q : Nat) where
  f : Fin q → DataRange

def specS (tab : List DExpr) : SpecS tab.length :=
  let arr : Array DataRange := (tab.map DExpr.R).toArray
  ⟨useSpec arr tab.length (by simp [arr])⟩

@[simp] theorem specS_f (tab : List DExpr) : (specS tab).f = SHIQD.spec tab := by
  funext j
  simp only [SHIQD.spec, specS, useSpec, List.getElem_toArray, List.getElem_map]
  rfl

instance instHashableRat : Hashable ℚ where
  hash q := mixHash (hash q.num) (hash q.den)

instance instHashableFloatV {e m : Nat} : Hashable (Datatypes.FloatV e m) where
  hash
    | .fin neg E M => mixHash 1 (mixHash (hash neg) (mixHash (hash E.val) (hash M.val)))
    | .inf neg => mixHash 2 (hash neg)
    | .nan => 3

instance instHashableValOfQ : Hashable (Datatypes.ValOf ℚ) where
  hash
    | .num x => mixHash 1 (hash x)
    | .dbl x => mixHash 2 (hash x)
    | .flt x => mixHash 3 (hash x)
    | .str s l => mixHash 4 (mixHash (hash s) (hash l))
    | .bool b => mixHash 5 (hash b)
    | .hex bs => mixHash 6 (hash bs)
    | .b64 bs => mixHash 7 (hash bs)
    | .uri s => mixHash 8 (hash s)
    | .time t z => mixHash 9 (mixHash (hash t) (hash z))
    | .xml s => mixHash 10 (hash s)
    | .extra n => mixHash 11 (hash n)

instance instHashableCell : Hashable Datatypes.Cell where
  hash
    | .pt w => mixHash 1 (hash w)
    | .gap lo hi cls => mixHash 2 (mixHash (hash lo) (mixHash (hash hi) (hash cls.val)))
    | .fN d => mixHash 3 (hash d)
    | .fA d p => mixHash 4 (mixHash (hash d) (hash p))
    | .fI d lo hi => mixHash 5 (mixHash (hash d) (mixHash (hash lo) (hash hi)))
    | .strR => 6
    | .langR => 7
    | .tagR => 8
    | .uriR => 9
    | .hexR => 10
    | .b64R => 11
    | .xmlR => 12
    | .timeTz => 13
    | .timeLoc => 14
    | .other => 15

def numPtsF (as : List Datatypes.BAtom) : List ℚ :=
  dedupHS (as.flatMap Datatypes.BAtom.nums)

@[csimp] theorem numPts_eq_F : @Datatypes.numPts = @numPtsF := by
  funext as; exact (dedupHS_eq _).symm

def otherPtsF (as : List Datatypes.BAtom) : List (Datatypes.ValOf ℚ) :=
  dedupHS (as.flatMap Datatypes.BAtom.others ++ [Datatypes.ValOf.bool true, Datatypes.ValOf.bool false])

@[csimp] theorem otherPts_eq_F : @Datatypes.otherPts = @otherPtsF := by
  funext as; exact (dedupHS_eq _).symm

def allPtsF (as : List Datatypes.BAtom) : List (Datatypes.ValOf ℚ) :=
  (numPtsF as).map .num ++ otherPtsF as

@[csimp] theorem allPts_eq_F : @Datatypes.allPts = @allPtsF := by
  funext as
  simp only [Datatypes.allPts, allPtsF, ← numPts_eq_F, ← otherPts_eq_F]

def fOrdsF (d : Bool) (as : List Datatypes.BAtom) : List Int :=
  dedupHS ((otherPtsF as).filterMap (Datatypes.fpOrd d))

@[csimp] theorem fOrds_eq_F : @Datatypes.fOrds = @fOrdsF := by
  funext d as
  simp only [Datatypes.fOrds, fOrdsF, ← otherPts_eq_F, dedupHS_eq]

def fCellsF (d : Bool) (as : List Datatypes.BAtom) : List Datatypes.Cell :=
  let fo := fOrdsF d as
  .fN d :: (fo.map (Datatypes.Cell.fA d) ++
    (Datatypes.fPairs fo (Datatypes.fTop d)).map fun x => Datatypes.Cell.fI d x.1 x.2)

@[csimp] theorem fCells_eq_F : @Datatypes.fCells = @fCellsF := by
  funext d as
  simp only [Datatypes.fCells, fCellsF, ← fOrds_eq_F]

def cellsOfF (as : List Datatypes.BAtom) : List Datatypes.Cell :=
  let npts := numPtsF as
  let opts := otherPtsF as
  let foT := dedupHS (opts.filterMap (Datatypes.fpOrd true))
  let foF := dedupHS (opts.filterMap (Datatypes.fpOrd false))
  let fcT := Datatypes.Cell.fN true :: (foT.map (Datatypes.Cell.fA true) ++
    (Datatypes.fPairs foT (Datatypes.fTop true)).map fun x => Datatypes.Cell.fI true x.1 x.2)
  let fcF := Datatypes.Cell.fN false :: (foF.map (Datatypes.Cell.fA false) ++
    (Datatypes.fPairs foF (Datatypes.fTop false)).map fun x => Datatypes.Cell.fI false x.1 x.2)
  dedupHS ((npts.map Datatypes.ValOf.num ++ opts).map Datatypes.Cell.pt ++
    (Datatypes.gapPairs npts).flatMap
      (fun x : Option ℚ × Option ℚ => [0, 1, 2, 3].map (Datatypes.Cell.gap x.1 x.2)) ++
    (Datatypes.restCells ++ fcT ++ fcF))

@[csimp] theorem cellsOf_eq_F : @Datatypes.cellsOf = @cellsOfF := by
  funext as
  simp only [Datatypes.cellsOf, cellsOfF, Datatypes.allPts, Datatypes.fCells, Datatypes.fOrds,
    ← numPts_eq_F, ← otherPts_eq_F, dedupHS_eq]

def allFreesF {q : Nat} (spec : Fin q → DataRange) : List IRI :=
  dedupHS ((List.finRange q).flatMap fun p => Datatypes.drFrees (spec p))

@[csimp] theorem allFrees_eq_F : @Datatypes.allFrees = @allFreesF := by
  funext q spec; exact (dedupHS_eq _).symm

/-- `Datatypes.cellSize` wrapped in a structure so `otherPts as` is computed once. -/
structure CellSizeS where
  f : Datatypes.Cell → Option Nat

def cellSizeS (as : List Datatypes.BAtom) : CellSizeS :=
  let opts := Datatypes.otherPts as
  ⟨Datatypes.cellSizeWith opts⟩

@[simp] theorem cellSizeS_f (as : List Datatypes.BAtom) : (cellSizeS as).f = Datatypes.cellSize as := by
  funext c
  cases c <;> rfl

/-- `Datatypes.owlE` wrapped in a structure so `allFrees` and `compileDR` are computed once. -/
structure OwlES {q : Nat} (spec : Fin q → DataRange) where
  f : Fin q → Datatypes.Cell → (Fin (Datatypes.allFrees spec).length → Bool) → Bool

def owlES {q : Nat} (spec : Fin q → DataRange) : OwlES spec :=
  let arr : Array Datatypes.CExpr := Array.ofFn fun p => Datatypes.compileDR (spec p)
  ⟨Datatypes.owlEWith (Datatypes.allFrees spec) arr q (Array.size_ofFn ..)⟩

@[simp] theorem owlES_f {q : Nat} (spec : Fin q → DataRange) : (owlES spec).f = Datatypes.owlE spec := by
  funext p c g
  simp only [owlES, Datatypes.owlEWith, Array.getElem_ofFn, Datatypes.evalCE_compileDR, Datatypes.owlE]

/-- Single-literal `.oneOf [some w]` compiled data range. -/
def singleLit? : Datatypes.CExpr → Option (Datatypes.ValOf ℚ)
  | .oneOf [some w] => some w
  | _ => none

theorem singleLit?_eq_some {ce : Datatypes.CExpr} {w : Datatypes.ValOf ℚ} :
    singleLit? ce = some w ↔ ce = .oneOf [some w] := by
  cases ce with
  | oneOf ws =>
    rcases ws with _ | ⟨_ | w', _ | _⟩ <;> simp [singleLit?]
  | _ => simp [singleLit?]

theorem evalCell_lit (w' : Datatypes.ValOf ℚ) (c : Datatypes.Cell) :
    Datatypes.evalCell (.lit w') c = match c with
      | .pt w => w == w'
      | _ => false := by
  cases c <;> rfl

theorem evalCE_oneOf_single (c : Datatypes.Cell) (fv : IRI → Bool) (w' : Datatypes.ValOf ℚ) :
    Datatypes.evalCE (fun a => Datatypes.evalCell a c) fv (.oneOf [some w']) =
      match c with
      | .pt w => w == w'
      | _ => false := by
  simp [Datatypes.evalCE, evalCell_lit]

def ptMapStep {q : Nat} (arr : Array Datatypes.CExpr) (p : Fin q)
    (mp : Std.HashMap (Datatypes.ValOf ℚ) (List (Fin q))) :
    Std.HashMap (Datatypes.ValOf ℚ) (List (Fin q)) :=
  match arr[p.val]?.bind singleLit? with
  | some w => mp.insert w (p :: (mp[w]?).getD [])
  | none => mp

def buildPtMap {q : Nat} (arr : Array Datatypes.CExpr) :
    Std.HashMap (Datatypes.ValOf ℚ) (List (Fin q)) :=
  (List.finRange q).reverse.foldl (fun mp p => ptMapStep arr p mp) ∅

theorem mem_foldr_ptMapStep {q : Nat} (arr : Array Datatypes.CExpr) (w : Datatypes.ValOf ℚ)
    (p : Fin q) :
    ∀ (l : List (Fin q)),
      p ∈ ((l.foldr (ptMapStep arr) ∅)[w]?).getD [] ↔
        p ∈ l ∧ arr[p.val]?.bind singleLit? = some w
  | [] => by simp
  | p' :: l => by
    simp only [List.foldr_cons, ptMapStep]
    rcases h : arr[p'.val]?.bind singleLit? with _ | w'
    · simp only [mem_foldr_ptMapStep arr w p l, List.mem_cons]
      constructor
      · rintro ⟨hp, hw⟩; exact ⟨Or.inr hp, hw⟩
      · rintro ⟨rfl | hp, hw⟩
        · rw [h] at hw; cases hw
        · exact ⟨hp, hw⟩
    · rw [Std.HashMap.getElem?_insert]
      by_cases hw : w' = w
      · subst hw
        simp only [beq_self_eq_true, ↓reduceIte, Option.getD_some, List.mem_cons,
          mem_foldr_ptMapStep arr w' p l]
        constructor
        · rintro (rfl | ⟨hp, h2⟩)
          · exact ⟨Or.inl rfl, h⟩
          · exact ⟨Or.inr hp, h2⟩
        · rintro ⟨rfl | hp, h2⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hp, h2⟩
      · simp only [beq_eq_false_iff_ne.2 hw, Bool.false_eq_true, ↓reduceIte,
          mem_foldr_ptMapStep arr w p l, List.mem_cons]
        constructor
        · rintro ⟨hp, h2⟩; exact ⟨Or.inr hp, h2⟩
        · rintro ⟨rfl | hp, h2⟩
          · rw [h, Option.some.injEq] at h2; exact absurd h2 hw
          · exact ⟨hp, h2⟩

theorem mem_buildPtMap {q : Nat} (arr : Array Datatypes.CExpr) (w : Datatypes.ValOf ℚ) (p : Fin q) :
    p ∈ ((buildPtMap arr)[w]?).getD [] ↔ arr[p.val]?.bind singleLit? = some w := by
  unfold buildPtMap
  rw [← List.foldr_eq_foldl_reverse, mem_foldr_ptMapStep]
  simp [List.mem_finRange]

def buildRestAtoms {q : Nat} (arr : Array Datatypes.CExpr) : List (Fin q × Datatypes.CExpr) :=
  (List.finRange q).filterMap fun p =>
    match arr[p.val]? with
    | some ce => if (singleLit? ce).isSome then none else some (p, ce)
    | none => none

def vtcOwlWith {q : Nat} (frees : List IRI)
    (ptMap : Std.HashMap (Datatypes.ValOf ℚ) (List (Fin q)))
    (rest : List (Fin q × Datatypes.CExpr))
    (c : Datatypes.Cell) (g : Fin frees.length → Bool) : Finset (Fin q) :=
  let pts : List (Fin q) := match c with
    | .pt w => (ptMap[w]?).getD []
    | _ => []
  let rs : List (Fin q) := rest.filterMap fun e =>
    if Datatypes.evalCE (fun a => Datatypes.evalCell a c) (Datatypes.freeVal frees g) e.2 then
      some e.1
    else none
  ContextCalculus.SRI.Proc.ofL (pts ++ rs)

structure VtcOwlS {q : Nat} (spec : Fin q → DataRange) where
  f : Datatypes.Cell → (Fin (Datatypes.allFrees spec).length → Bool) → Finset (Fin q)

def vtcOwlS {q : Nat} (spec : Fin q → DataRange) : VtcOwlS spec :=
  let arr : Array Datatypes.CExpr := Array.ofFn fun p => Datatypes.compileDR (spec p)
  let ptMap := buildPtMap arr
  let rest := buildRestAtoms arr
  ⟨vtcOwlWith (Datatypes.allFrees spec) ptMap rest⟩

theorem vtcOwlS_f {q : Nat} (spec : Fin q → DataRange) (c : Datatypes.Cell)
    (g : Fin (Datatypes.allFrees spec).length → Bool) :
    (vtcOwlS spec).f c g = ContextCalculus.SRIQD.vtc (Datatypes.owlE spec) c g := by
  ext p
  unfold vtcOwlS
  set arr : Array Datatypes.CExpr := Array.ofFn fun p => Datatypes.compileDR (spec p)
  have harr : ∀ p' : Fin q, arr[p'.val]? = some (Datatypes.compileDR (spec p')) := fun p' => by
    simp [arr, p'.isLt]
  simp only [vtcOwlWith, ContextCalculus.SRI.Proc.ofL_eq, List.mem_toFinset, List.mem_append,
    List.mem_filterMap, buildRestAtoms, List.mem_finRange, true_and, ContextCalculus.SRIQD.vtc,
    Finset.mem_filter, Finset.mem_univ, Datatypes.owlE, ← Datatypes.evalCE_compileDR]
  rcases hs : singleLit? (Datatypes.compileDR (spec p)) with _ | w'
  · have hpts : p ∉ (match c with | .pt w => ((buildPtMap arr)[w]?).getD [] | _ => []) := by
      cases c <;> simp [mem_buildPtMap, harr, hs]
    rw [or_iff_right hpts]
    constructor
    · rintro ⟨⟨p', ce⟩, ⟨p'', h1⟩, h2⟩
      rw [harr p''] at h1
      dsimp only at h1
      split_ifs at h1 with h3
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      split_ifs at h2 with h4
      cases h2
      exact h4
    · intro h
      refine ⟨(p, Datatypes.compileDR (spec p)), ⟨p, ?_⟩, by simp [h]⟩
      rw [harr p]
      simp [hs]
  · have hrs : ¬ ∃ x : Fin q × Datatypes.CExpr,
        (∃ a : Fin q, (match arr[a.val]? with
          | some ce => if (singleLit? ce).isSome = true then none else some (a, ce)
          | none => none) = some x) ∧
        (if Datatypes.evalCE (fun a => Datatypes.evalCell a c)
            (Datatypes.freeVal (Datatypes.allFrees spec) g) x.2 = true then some x.1 else none) = some p := by
      rintro ⟨⟨p', ce⟩, ⟨p'', h1⟩, h2⟩
      rw [harr p''] at h1
      dsimp only at h1
      split_ifs at h1 with h3
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      split_ifs at h2 with h4
      cases h2
      rw [hs] at h3
      simp at h3
    rw [or_iff_left hrs, singleLit?_eq_some.1 hs, evalCE_oneOf_single]
    cases c with
    | pt w =>
      simp only [mem_buildPtMap, harr, Option.bind_some, hs, Option.some.injEq, beq_iff_eq]
      exact ⟨Eq.symm, Eq.symm⟩
    | _ => simp

def tableKF (O : Ontology) : List DExpr := dedupHS ((rwAxiomsK O).flatMap axDexprsK)

@[csimp] theorem tableK_eq_F : @tableK = @tableKF := by
  funext O
  exact (dedupHS_eq _).symm

def dpropsKF (O : Ontology) : List IRI :=
  dedupHS ((tableK O).map DExpr.p ++ (O.axioms.flatMap subPairs).flatMap fun pq => [pq.1, pq.2])

@[csimp] theorem dpropsK_eq_F : @dpropsK = @dpropsKF := by
  funext O
  exact (dedupHS_eq _).symm

def fNameF (base : String) (tmap : Std.HashMap DExpr Nat) (tlen : Nat) (e : DExpr) : IRI :=
  SRIQKB.defName base (2 * (tmap[e]?).getD tlen)

def wNameF (base : String) (tmap : Std.HashMap DExpr Nat) (tlen : Nat) (e : DExpr) : IRI :=
  SRIQKB.defName base (2 * (tmap[e]?).getD tlen + 1)

def freshNamesF (base : String) (tmap : Std.HashMap DExpr Nat) (tlen : Nat) (tab : List DExpr) :
    List IRI :=
  tab.flatMap fun e => [fNameF base tmap tlen e, wNameF base tmap tlen e]

def nameIxKF (T : SRIQKBTranslation) (nmap : Std.HashMap IRI Nat) (a : IRI) :
    Option (Fin T.conceptCount) :=
  if h : (nmap[a]?).getD T.named.length < T.named.length then
    some ⟨_, Nat.lt_of_lt_of_le h T.hnamed⟩
  else none

def dpIxF (dps : List IRI) (dmap : Std.HashMap IRI Nat) (p : IRI) : Option (Fin dps.length) :=
  if h : (dmap[p]?).getD dps.length < dps.length then some ⟨_, h⟩ else none

def dataClauseOfKF (T : SRIQKBTranslation) (base : String) (tab : List DExpr) (dps : List IRI)
    (tmap : Std.HashMap DExpr Nat) (nmap : Std.HashMap IRI Nat) (dmap : Std.HashMap IRI Nat)
    (jt : DExpr × Nat) : Option (List (DClause T.conceptCount T.roleCount dps.length tab.length)) :=
  match nameIxKF T nmap (fNameF base tmap tab.length jt.1),
        nameIxKF T nmap (wNameF base tmap tab.length jt.1),
        dpIxF dps dmap jt.1.p with
  | some F, some W, some u =>
    if h : jt.2 < tab.length then some (entryClauses (m := T.roleCount) jt.1 F W u ⟨jt.2, h⟩)
    else none
  | _, _, _ => none

def subClauseOfKF (T : SRIQKBTranslation) (dps : List IRI) (tab : List DExpr)
    (dmap : Std.HashMap IRI Nat) (pq : IRI × IRI) :
    Option (List (DClause T.conceptCount T.roleCount dps.length tab.length)) :=
  match dpIxF dps dmap pq.1, dpIxF dps dmap pq.2 with
  | some u, some v => some [.dSub u v]
  | _, _ => none

def translateSRIQDKBF (O : OWL.Ontology) (requested : List OWL.IRI) (extra : List OWL.IRI := []) :
    Option SRIQDKBTranslation :=
  if O.isSHIQDKB then
    let base := SRIQKB.defBase O requested
    let tab := tableK O
    let tmap := idxMap tab
    let dps := dpropsK O
    let dmap := idxMap dps
    let objO : Ontology := ⟨(rwAxiomsK O).map (absAxK (fNameF base tmap tab.length))⟩
    match translateSRIQKB objO (requested ++ freshNamesF base tmap tab.length tab) extra with
    | none => none
    | some T =>
      let nmap := idxMap T.named
      let dataCl := SRIQKB.collect (dataClauseOfKF T base tab dps tmap nmap dmap) tab.zipIdx
      let subCl := SRIQKB.collect (subClauseOfKF T dps tab dmap) (O.axioms.flatMap subPairs)
      match dataCl, subCl with
      | some dc, some sc =>
        some { obj := T, named := eraseDupsH requested, dps := dps, tab := tab,
               ontology := T.ontology.map .obj ++ dc ++ sc }
      | _, _ => none
  else none

theorem nameIxKF_eq (T : SRIQKBTranslation) (a : IRI) :
    nameIxKF T (idxMap T.named) a = nameIxK T a := by
  simp only [nameIxKF, nameIxK, idxMap_getD]

theorem dpIxF_eq (dps : List IRI) (p : IRI) :
    dpIxF dps (idxMap dps) p = dpIx dps p := by
  simp only [dpIxF, dpIx, idxMap_getD]

@[csimp] theorem translateSRIQDKB_eq_F : @translateSRIQDKB = @translateSRIQDKBF := by
  funext O requested extra
  have hf : ∀ base (tab : List DExpr), fNameF base (idxMap tab) tab.length = fName base tab := by
    intro base tab; funext e; simp only [fNameF, fName, idxMap_getD]
  have hw : ∀ base (tab : List DExpr), wNameF base (idxMap tab) tab.length = wName base tab := by
    intro base tab; funext e; simp only [wNameF, wName, idxMap_getD]
  have hfn : ∀ base (tab : List DExpr),
      freshNamesF base (idxMap tab) tab.length tab = freshNames base tab := by
    intro base tab; simp only [freshNamesF, freshNames, hf, hw]
  have hdc : ∀ T base (tab : List DExpr) dps,
      dataClauseOfKF T base tab dps (idxMap tab) (idxMap T.named) (idxMap dps) =
        dataClauseOfK T base tab dps := by
    intro T base tab dps; funext jt
    simp only [dataClauseOfKF, dataClauseOfK, nameIxKF_eq, dpIxF_eq, fNameF, fName, wNameF, wName,
      idxMap_getD]
    rfl
  have hsc : ∀ T (dps : List IRI) tab,
      subClauseOfKF T dps tab (idxMap dps) = subClauseOfK T dps tab := by
    intro T dps tab; funext pq
    simp only [subClauseOfKF, subClauseOfK, dpIxF_eq]
    rfl
  simp only [translateSRIQDKBF, translateSRIQDKB, eraseDupsH_eq, objOntK, hf, hfn, hdc, hsc]
  rfl

def translateSHOIQDF (O : Ontology) (requested : List IRI) : Option SRIQDKBTranslation :=
  if O.isSHOIQDKB then translateSRIQDKB (nomOntDF O requested) (requested ++ nomNamesF O requested)
  else none

@[csimp] theorem translateSHOIQD_eq_F : @translateSHOIQD = @translateSHOIQDF := by
  funext O requested
  simp only [translateSHOIQDF, translateSHOIQD, ← nomOntD_eq_F, ← nomNames_eq_F]

/-! ## Nominal indices of a translation -/

def nomIxsF (T : SRIQKBTranslation) (L : List IRI) : List (Fin T.conceptCount) :=
  let m := idxMap T.named
  let len := T.named.length
  L.filterMap fun a =>
    if h : (m[a]?).getD len < len then
      some ⟨(m[a]?).getD len, Nat.lt_of_lt_of_le h T.hnamed⟩ else none

@[csimp] theorem nomIxs_eq_F : @nomIxs = @nomIxsF := by
  funext T L
  simp only [nomIxsF, idxMap_getD]
  rfl

def dosnF (T : SRIQDKBTranslation) (L : List IRI) :
    SRIQN.DOntology (Fin T.obj.conceptCount) (Fin T.obj.roleCount) (Fin T.dps.length)
      (Fin T.tab.length) :=
  T.ontology.map SRIQN.DClause.base ++ (nomIxsF T.obj L).map fun a => .nom (id a)

@[csimp] theorem dosn_eq_F : @dosn = @dosnF := by
  funext T L
  simp only [dosnF, dosn, ← nomIxs_eq_F]

/-- Tail-recursive `SRIQKB.collect`. -/
def collectF {α β : Type} (f : α → Option (List β)) (xs : List α) : Option (List β) :=
  (xs.mapM f).map List.flatten

theorem collectF_eq {α β : Type} (f : α → Option (List β)) :
    ∀ (xs : List α), collectF f xs = SRIQKB.collect f xs
  | [] => rfl
  | x :: xs => by
    unfold collectF SRIQKB.collect
    rw [← collectF_eq f xs]
    unfold collectF
    cases hfx : f x <;> cases hxs : xs.mapM f <;> simp [hfx, hxs]

@[csimp] theorem collect_eq_F : @SRIQKB.collect = @collectF := by
  funext α β f xs
  exact (collectF_eq f xs).symm

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.idxFast_eq
#print axioms ContextCalculus.OWLFrontend.dedupHS_eq
#print axioms ContextCalculus.OWLFrontend.specS_f
#print axioms ContextCalculus.OWLFrontend.cellSizeS_f
#print axioms ContextCalculus.OWLFrontend.owlES_f
#print axioms ContextCalculus.OWLFrontend.cellsOf_eq_F
#print axioms ContextCalculus.OWLFrontend.translateSRIQDKB_eq_F
#print axioms ContextCalculus.OWLFrontend.translateSHOIQD_eq_F
#print axioms ContextCalculus.OWLFrontend.dosn_eq_F
#print axioms ContextCalculus.OWLFrontend.collect_eq_F
#print axioms ContextCalculus.OWLFrontend.vtcOwlS_f
