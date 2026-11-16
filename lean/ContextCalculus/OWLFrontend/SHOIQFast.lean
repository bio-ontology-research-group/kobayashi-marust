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

/-- `SHIQD.spec` through an array computed once. -/
def useSpec (arr : Array DataRange) (q : Nat) (h : arr.size = q) (j : Fin q) : DataRange :=
  arr[j.val]'(by rw [h]; exact j.isLt)

def specF (tab : List DExpr) : Fin tab.length → DataRange :=
  useSpec (tab.map DExpr.R).toArray tab.length (by simp)

@[csimp] theorem spec_eq_F : @SHIQD.spec = @specF := by
  funext tab j
  simp only [SHIQD.spec, specF, useSpec, List.getElem_toArray, List.getElem_map]
  rfl

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
    match translateSRIQKB objO (requested ++ freshNames base tab) extra with
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
  simp only [translateSRIQDKBF, translateSRIQDKB, eraseDupsH_eq, objOntK, hf, hdc, hsc]
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
#print axioms ContextCalculus.OWLFrontend.spec_eq_F
#print axioms ContextCalculus.OWLFrontend.translateSRIQDKB_eq_F
#print axioms ContextCalculus.OWLFrontend.translateSHOIQD_eq_F
#print axioms ContextCalculus.OWLFrontend.dosn_eq_F
#print axioms ContextCalculus.OWLFrontend.collect_eq_F
