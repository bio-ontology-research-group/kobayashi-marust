import ContextCalculus.SROIQ.ChainFast
import ContextCalculus.SRIQN.DataParts

/-!
# Chain elimination with nominals and data (stage C3, design section 4)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, section 4. `encChain` on the base part,
the nominal clauses and the data clauses on the old names. Both model maps
of `ChainEnc.lean` keep the extensions of the old names and leave the data
relation alone, so nominal and data clauses hold on one side iff on the
other.

* `consistentN_encChainN`, `entailsSubN_encChainN`: nominals.
* `consistentDN_encChainDN`: nominals and data.
* `isSHIQD_encChainDN`: the result has chains of length one only, so it is
  SHIQ with no transitive role and the C2a route with data
  (`SRIQN.consistentPartsN_iff`) applies to it.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQN (ConsistentN EntailsSubN basePart noms ofSRIQ models_iff NomAt
  DOntology DClause dbase dnoms ConsistentDN)
open ContextCalculus.SRIQD (DInterp DataTheory)

variable {n m p q : Nat} {D : Type}

/-! ## Nominals -/

/-- The conditions on the base part. -/
def CondCN (O : SRIQN.Ontology (Fin n) (Fin m)) : Prop := CondC (basePart O)

abbrev kCN (O : SRIQN.Ontology (Fin n) (Fin m)) : Nat := kC (basePart O)

/-- **Chain elimination with nominals.** -/
def encChainN (O : SRIQN.Ontology (Fin n) (Fin m)) : SRIQN.Ontology (Fin (n + kCN O)) (Fin m) :=
  ofSRIQ (encChain (basePart O)) ++ (noms O).map fun a => .nom (Fin.castAdd (kCN O) a)

theorem basePart_encChainN (O : SRIQN.Ontology (Fin n) (Fin m)) :
    basePart (encChainN O) = encChain (basePart O) :=
  SRIQN.basePart_ofSRIQ_noms _ _ _

theorem noms_encChainN (O : SRIQN.Ontology (Fin n) (Fin m)) :
    noms (encChainN O) = (noms O).map (Fin.castAdd _) := by
  simp only [encChainN, noms, ofSRIQ, List.filterMap_append, List.filterMap_map]
  simp [List.map_filterMap]

theorem isALCHOIQ_encChainN (O : SRIQN.Ontology (Fin n) (Fin m)) :
    SRIQN.IsALCHOIQ (encChainN O) := by
  unfold SRIQN.IsALCHOIQ
  rw [basePart_encChainN]
  exact encChain_isALCHIQ _

theorem models_encChainN_up {O : SRIQN.Ontology (Fin n) (Fin m)} {I : Interp D (Fin n) (Fin m)}
    (hI : SRIQN.models I O) : SRIQN.models (upC (basePart O) I) (encChainN O) := by
  obtain ⟨hb, hn⟩ := models_iff.1 hI
  refine models_iff.2 ⟨by rw [basePart_encChainN]; exact models_upC hb, fun a' ha' => ?_⟩
  rw [noms_encChainN] at ha'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
  obtain ⟨x, hx⟩ := hn a ha
  exact ⟨x, fun y => (upC_old I a y).trans (hx y)⟩

theorem models_encChainN_down {O : SRIQN.Ontology (Fin n) (Fin m)} (h : CondCN O)
    {J : Interp D (Fin (n + kCN O)) (Fin m)} (hJ : SRIQN.models J (encChainN O)) :
    SRIQN.models (downC (basePart O) J) O := by
  obtain ⟨hb, hn⟩ := models_iff.1 hJ
  rw [basePart_encChainN] at hb
  refine models_iff.2 ⟨models_downC h hb, fun a ha => ?_⟩
  exact hn (Fin.castAdd _ a) (by rw [noms_encChainN]; exact List.mem_map_of_mem ha)

/-- **Chain elimination keeps consistency** (nominals). -/
theorem consistentN_encChainN {O : SRIQN.Ontology (Fin n) (Fin m)} (h : CondCN O) :
    ConsistentN O ↔ ConsistentN (encChainN O) := by
  constructor
  · rintro ⟨D, hD, I, hI⟩
    exact ⟨D, hD, _, models_encChainN_up hI⟩
  · rintro ⟨D, hD, J, hJ⟩
    exact ⟨D, hD, _, models_encChainN_down h hJ⟩

/-- **Chain elimination keeps subsumption** between old names (nominals). -/
theorem entailsSubN_encChainN {O : SRIQN.Ontology (Fin n) (Fin m)} (h : CondCN O) (a b : Fin n) :
    EntailsSubN O a b ↔ EntailsSubN (encChainN O) (Fin.castAdd _ a) (Fin.castAdd _ b) := by
  constructor
  · intro hO D _ J hJ x hx
    exact hO D _ (models_encChainN_down h hJ) x hx
  · intro hE D _ I hI x hx
    have := hE D _ (models_encChainN_up hI) x ((upC_old I a x).2 hx)
    exact (upC_old I b x).1 this

/-! ## Nominals and data -/

/-- The conditions on the object part. -/
def CondCD (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) : Prop :=
  CondC (SRIQD.objPart (dbase O))

abbrev kCD (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) : Nat := kC (SRIQD.objPart (dbase O))

/-- The `SRIQD` clauses of the encoding. -/
def encChainQD (O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)) :
    SRIQD.Ontology (Fin (n + kC (SRIQD.objPart O))) (Fin m) (Fin p) (Fin q) :=
  (encChain (SRIQD.objPart O)).map SRIQD.Clause.obj ++
    O.filterMap (SRIQD.Proc.liftData (kC (SRIQD.objPart O)))

/-- **Chain elimination with nominals and data.** -/
def encChainDN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    DOntology (Fin (n + kCD O)) (Fin m) (Fin p) (Fin q) :=
  let k := kCD O
  (encChainQD (dbase O)).map DClause.base ++ (dnoms O).map fun a => .nom (Fin.castAdd k a)

theorem dbase_encChainDN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    dbase (encChainDN O) = encChainQD (dbase O) :=
  SRIQN.Proc.dbase_map_noms _ _ _

theorem dnoms_encChainDN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    dnoms (encChainDN O) = (dnoms O).map (Fin.castAdd _) := by
  simp only [encChainDN, dnoms, List.filterMap_append, List.filterMap_map]
  simp [List.map_filterMap]

theorem objPart_encChainQD (O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)) :
    SRIQD.objPart (encChainQD O) = encChain (SRIQD.objPart O) :=
  SRIQD.Proc.objPart_lift _ O

/-- The encoding is SHIQ (chains of length one, no transitive role). -/
theorem isSHIQD_encChainDN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    SRIQD.Proc.IsSHIQD (dbase (encChainDN O)) := by
  unfold SRIQD.Proc.IsSHIQD
  rw [dbase_encChainDN, objPart_encChainQD]
  have h := encChain_isALCHIQ (SRIQD.objPart (dbase O))
  refine ⟨fun body S hcl => Or.inl (h body S hcl), fun a k R b _ T hT => ?_⟩
  exact absurd (h _ _ hT) (by simp)

variable {V : Type}

theorem models_encChainQD_up {atom : Fin q → V → Prop}
    {O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)} {I : DInterp D V (Fin n) (Fin m) (Fin p)}
    (hI : SRIQD.models atom I O) :
    SRIQD.models atom ({ toInterp := upC (SRIQD.objPart O) I.toInterp, d := I.d } :
      DInterp D V (Fin (n + kC (SRIQD.objPart O))) (Fin m) (Fin p)) (encChainQD O) := by
  obtain ⟨hIo, hId⟩ := SRIQD.models_iff.1 hI
  refine SRIQD.models_iff.2 ⟨?_, fun cl hcl y => ?_⟩
  · rw [objPart_encChainQD]
    exact models_upC hIo
  · rcases List.mem_append.1 hcl with h1 | h1
    · obtain ⟨cl0, -, rfl⟩ := List.mem_map.1 h1
      trivial
    · obtain ⟨cl0, h0, hl⟩ := List.mem_filterMap.1 h1
      refine (SRIQD.Proc.dLocal_liftData atom hl _ (fun u => I.d u y)).2 ?_
      have hc : (fun a => (upC (SRIQD.objPart O) I.toInterp).c (Fin.castAdd _ a) y) =
          fun a => I.c a y := funext fun a => propext (upC_old I.toInterp a y)
      show SRIQD.dLocal atom (fun a => (upC (SRIQD.objPart O) I.toInterp).c (Fin.castAdd _ a) y)
        (fun u => I.d u y) cl0
      rw [hc]
      exact hId cl0 h0 y

theorem models_encChainQD_down {atom : Fin q → V → Prop}
    {O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)} (h : CondC (SRIQD.objPart O))
    {J : DInterp D V (Fin (n + kC (SRIQD.objPart O))) (Fin m) (Fin p)}
    (hJ : SRIQD.models atom J (encChainQD O)) :
    SRIQD.models atom ({ toInterp := downC (SRIQD.objPart O) J.toInterp, d := J.d } :
      DInterp D V (Fin n) (Fin m) (Fin p)) O := by
  obtain ⟨hJo, hJd⟩ := SRIQD.models_iff.1 hJ
  rw [objPart_encChainQD] at hJo
  refine SRIQD.models_iff.2 ⟨models_downC h hJo, fun cl hcl y => ?_⟩
  cases hl : SRIQD.Proc.liftData (kC (SRIQD.objPart O)) cl with
  | none =>
    cases cl <;> simp only [SRIQD.Proc.liftData, reduceCtorEq] at hl
    trivial
  | some cl' =>
    have := hJd cl' (List.mem_append_right _ (List.mem_filterMap.2 ⟨cl, hcl, hl⟩)) y
    exact (SRIQD.Proc.dLocal_liftData atom hl _ _).1 this

/-- **Chain elimination keeps consistency** (nominals and data), for every
data theory. -/
theorem consistentDN_encChainDN {Θ : DataTheory (Fin q)}
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (h : CondCD O) :
    ConsistentDN Θ O ↔ ConsistentDN Θ (encChainDN O) := by
  constructor
  · rintro ⟨D, V, hD, atom, hΘ, I, hI, hn⟩
    refine ⟨D, V, hD, atom, hΘ, _, by rw [dbase_encChainDN]; exact models_encChainQD_up hI,
      fun a' ha' => ?_⟩
    rw [dnoms_encChainDN] at ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
    obtain ⟨x, hx⟩ := hn a ha
    exact ⟨x, fun y => (upC_old I.toInterp a y).trans (hx y)⟩
  · rintro ⟨D, V, hD, atom, hΘ, J, hJ, hn⟩
    rw [dbase_encChainDN] at hJ
    refine ⟨D, V, hD, atom, hΘ, _, models_encChainQD_down h hJ, fun a ha => ?_⟩
    exact hn (Fin.castAdd _ a) (by rw [dnoms_encChainDN]; exact List.mem_map_of_mem ha)

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.consistentN_encChainN
#print axioms ContextCalculus.SROIQ.Proc.entailsSubN_encChainN
#print axioms ContextCalculus.SROIQ.Proc.isALCHOIQ_encChainN
#print axioms ContextCalculus.SROIQ.Proc.consistentDN_encChainDN
#print axioms ContextCalculus.SROIQ.Proc.isSHIQD_encChainDN
