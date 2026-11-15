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
def idxMap (l : List IRI) : Std.HashMap IRI Nat :=
  (l.zipIdx.foldr fun p m => m.insert p.1 p.2) ∅

theorem idxMap_go (a : IRI) : ∀ (l : List IRI) (k : Nat),
    ((l.zipIdx k).foldr (fun p m => m.insert p.1 p.2) (∅ : Std.HashMap IRI Nat))[a]? =
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
        simp [List.idxOf_cons, hx]
      rw [hi]
      by_cases ha : a ∈ l
      · simp [ha]; omega
      · simp [ha, Ne.symm hx]

/-- The position of `a` in `l` (`l.length` if absent), through the table. -/
def idxFast (l : List IRI) : IRI → Nat :=
  let m := idxMap l
  fun a => (m[a]?).getD l.length

theorem idxFast_eq (l : List IRI) : idxFast l = fun a => l.idxOf a := by
  funext a
  unfold idxFast idxMap
  have := idxMap_go a l 0
  rw [this]
  split_ifs with h
  · simp
  · simp [List.idxOf_eq_length h]

theorem idxMap_getD (l : List IRI) (a : IRI) : ((idxMap l)[a]?).getD l.length = l.idxOf a :=
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

def translateSRIQDKBF (O : OWL.Ontology) (requested : List OWL.IRI) (extra : List OWL.IRI := []) :
    Option SRIQDKBTranslation :=
  if O.isSHIQDKB then
    let base := SRIQKB.defBase O requested
    let tab := tableK O
    let dps := dpropsK O
    match translateSRIQKB (objOntK O base) (requested ++ freshNames base tab) extra with
    | none => none
    | some T =>
      let dataCl := SRIQKB.collect (dataClauseOfK T base tab dps) tab.zipIdx
      let subCl := SRIQKB.collect (subClauseOfK T dps tab) (O.axioms.flatMap subPairs)
      match dataCl, subCl with
      | some dc, some sc =>
        some { obj := T, named := eraseDupsH requested, dps := dps, tab := tab,
               ontology := T.ontology.map .obj ++ dc ++ sc }
      | _, _ => none
  else none

@[csimp] theorem translateSRIQDKB_eq_F : @translateSRIQDKB = @translateSRIQDKBF := by
  funext O requested extra
  simp only [translateSRIQDKBF, translateSRIQDKB, eraseDupsH_eq]
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

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.idxFast_eq
#print axioms ContextCalculus.OWLFrontend.translateSHOIQD_eq_F
#print axioms ContextCalculus.OWLFrontend.dosn_eq_F
