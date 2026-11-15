import ContextCalculus.SRIQN.Transitivity
import ContextCalculus.SRIQD.ABoxProcedure
import ContextCalculus.SRIQD.BadFast

/-!
# Data with nominals (stage C2, design section 6)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. `SRIQD` clauses (object clauses and
data clauses over data properties `DProp` and data atoms `DAtom`) plus
nominal clauses. Data stars depend on the centre type only, so the C4
reduction carries over: forbid every type without a data star by one gci
(`SRIQD.reduceWith`), keep the nominal clauses, and run the object
procedure. Data assertions on an individual become data clauses on its
nominal name (`N_i ⊑ ∃u.L`, `N_i ⊑ ∀u.¬L`), so the ontology carries no
ABox.

* `consistentN_reduceN`: under `OracleSpec Θ card`, the data ontology is
  consistent iff the reduced `SRIQN` ontology is.
* `consistentDN_iff`: the C2a procedure on the reduced ontology over
  `Fin` names (`reduceNQ`, the forbidden types decided by `dataSatB`) is
  exact for every hint when the reduced ontology is ALCHOIQ and C2a.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory OracleSpec DataSat)

variable {CName Role DProp DAtom : Type}

/-- Clauses with data and nominals. -/
inductive DClause (CName Role DProp DAtom : Type) where
  | base (cl : SRIQD.Clause CName Role DProp DAtom)
  | nom (a : CName)

abbrev DOntology (CName Role DProp DAtom : Type) := List (DClause CName Role DProp DAtom)

/-- The `SRIQD` clauses. -/
def dbase (O : DOntology CName Role DProp DAtom) : SRIQD.Ontology CName Role DProp DAtom :=
  O.filterMap fun
    | .base cl => some cl
    | .nom _ => none

/-- The nominal names. -/
def dnoms (O : DOntology CName Role DProp DAtom) : List CName :=
  O.filterMap fun
    | .nom a => some a
    | .base _ => none

/-- The data ontology has a model over a nonempty domain and an admissible
pair of the data theory. -/
def ConsistentDN (Θ : DataTheory DAtom) (O : DOntology CName Role DProp DAtom) : Prop :=
  ∃ (D V : Type) (_ : Nonempty D) (atom : DAtom → V → Prop), Θ V atom ∧
    ∃ I : DInterp D V CName Role DProp, SRIQD.models atom I (dbase O) ∧
      ∀ a ∈ dnoms O, NomAt I.toInterp a

section Reduce

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]

/-- The reduced `SRIQN` ontology: the object part, the forbidding gcis and
the nominal clauses. -/
def reduceN (O : DOntology CName Role DProp DAtom) (toL : Finset CName → List CName)
    (bad : List (Finset CName)) : Ontology CName Role :=
  ofSRIQ (SRIQD.reduceWith (dbase O) toL bad) ++ (dnoms O).map fun a => .nom (id a)

theorem basePart_reduceN (O : DOntology CName Role DProp DAtom) (toL : Finset CName → List CName)
    (bad : List (Finset CName)) :
    basePart (reduceN O toL bad) = SRIQD.reduceWith (dbase O) toL bad :=
  basePart_ofSRIQ_noms _ _ _

theorem noms_reduceN (O : DOntology CName Role DProp DAtom) (toL : Finset CName → List CName)
    (bad : List (Finset CName)) : noms (reduceN O toL bad) = dnoms O := by
  rw [reduceN, noms_append, noms_ofSRIQ]
  simp [noms, List.filterMap_map]

variable {Θ : DataTheory DAtom} {card : Finset DAtom → Option Nat}

/-- **Reduction.** Under the oracle specification, the data ontology with
nominals is consistent iff the reduced ontology is. -/
theorem consistentN_reduceN (hspec : OracleSpec Θ card) {O : DOntology CName Role DProp DAtom}
    {toL : Finset CName → List CName} (htoL : ∀ t a, a ∈ toL t ↔ a ∈ t)
    {bad : List (Finset CName)} (hbad : ∀ t, t ∈ bad ↔ ¬ DataSat (dbase O) card t) :
    ConsistentN (reduceN O toL bad) ↔ ConsistentDN Θ O := by
  constructor
  · rintro ⟨D, hD, I, hI⟩
    obtain ⟨hb, hn⟩ := models_iff.1 hI
    rw [basePart_reduceN] at hb
    rw [noms_reduceN] at hn
    obtain ⟨hIo, hds⟩ := (SRIQD.models_reduceWith_iff htoL hbad).1 hb
    obtain ⟨V, atom, hΘ, d, hm⟩ := SRIQD.exists_dmodel_types hspec.lower I hIo (SRIQ.typeOf I)
      (fun a x => (SRIQ.mem_typeOf I).symm) hds
    exact ⟨D, V, hD, atom, hΘ, _, hm, hn⟩
  · rintro ⟨D, V, hD, atom, hΘ, I, hI, hn⟩
    refine ⟨D, hD, I.toInterp, models_iff.2 ⟨?_, ?_⟩⟩
    · rw [basePart_reduceN]
      exact (SRIQD.models_reduceWith_iff htoL hbad).2
        ⟨(SRIQD.models_iff.1 hI).1, SRIQD.dataSat_of_model hspec.upper hΘ hI⟩
    · rw [noms_reduceN]
      exact hn

end Reduce

/-! ## The procedure -/

namespace Proc

variable {n m p q : Nat}

/-- The reduced ontology over `Fin` names, the forbidden types computed. -/
def reduceNQ (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat) :
    Ontology (Fin n) (Fin m) :=
  reduceN O SRIQD.Proc.toLFin (SRIQD.Proc.badQ (dbase O) card)

/-- **Consistency with data and nominals.** -/
def consistentDN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (hint : Option (HintN n m)) : Bool :=
  consistentN (basePart (reduceNQ O card)) (noms (reduceNQ O card)) hint

/-- **Exactness with data**, for every hint, when the reduced ontology is
ALCHOIQ and C2a. -/
theorem consistentDN_iff {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat}
    (hspec : OracleSpec Θ card) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hA : IsALCHOIQ (reduceNQ O card)) (hC : IsC2a (reduceNQ O card))
    (hint : Option (HintN n m)) : consistentDN O card hint = true ↔ ConsistentDN Θ O := by
  rw [consistentDN, consistentN_iff hA hC, reduceNQ,
    consistentN_reduceN hspec SRIQD.Proc.mem_toLFin SRIQD.Proc.mem_badQ]

end Proc

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.consistentN_reduceN
#print axioms ContextCalculus.SRIQN.Proc.consistentDN_iff
