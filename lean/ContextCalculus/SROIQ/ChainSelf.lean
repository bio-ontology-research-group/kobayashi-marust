import ContextCalculus.SROIQ.ChainEncN
import ContextCalculus.SRIQN.Self

/-!
# Chain elimination with self clauses (stage C3c)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, sections 4 and 5. The model maps of
chain elimination keep the old names and the roles of the up direction,
and the down direction keeps every edge and adds none on a simple role
(`downC_rt_simple`). So a positive self clause (`selfR`) holds after
either map, and a negative one (`selfL`) after the down map when its role
is simple. `consistentDS_encChainDN`: chain elimination keeps consistency
with self clauses.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQN (DOntology dbase dnoms ConsistentDS SClause satS NomAt)

variable {n m p q : Nat}

/-- Rename the concept names of a self clause. -/
def SClause.mapC {C C' Role : Type} (f : C → C') : SClause C Role → SClause C' Role
  | .selfR body R => .selfR (body.map f) R
  | .selfL R head => .selfL R (head.map f)

/-- The self clauses on the old names of the chain encoding. -/
def liftSC (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (SC : List (SClause (Fin n) (Fin m))) :
    List (SClause (Fin (n + kCD O)) (Fin m)) :=
  SC.map (SClause.mapC (Fin.castAdd _))

/-- `liftSC` without evaluating the number of fresh names (stage C3e: as an
argument of `Fin.castAdd` it was computed again wherever the lifted
clauses were used). -/
def liftSCF (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (SC : List (SClause (Fin n) (Fin m))) :
    List (SClause (Fin (n + kCD O)) (Fin m)) :=
  SC.map (SClause.mapC fun a => ⟨a.val, Nat.lt_of_lt_of_le a.2 (Nat.le_add_right _ _)⟩)

@[csimp] theorem liftSC_eq_F : @liftSC = @liftSCF := by
  funext n m p q O SC
  rfl

/-- The negative self clauses are on simple roles. -/
def SelfSimple (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (SC : List (SClause (Fin n) (Fin m))) :
    Prop :=
  ∀ R head, SClause.selfL R head ∈ SC → SimpleC (SRIQD.objPart (dbase O)) R

/-- **Chain elimination keeps consistency with self clauses.** -/
theorem consistentDS_encChainDN {Θ : SRIQD.DataTheory (Fin q)}
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} {SC : List (SClause (Fin n) (Fin m))}
    (h : CondCD O) (hs : SelfSimple O SC) :
    ConsistentDS Θ O SC ↔ ConsistentDS Θ (encChainDN O) (liftSC O SC) := by
  constructor
  · rintro ⟨D, V, hD, atom, hΘ, I, hI, hn, hS⟩
    refine ⟨D, V, hD, atom, hΘ, _, by rw [dbase_encChainDN]; exact models_encChainQD_up hI,
      fun a' ha' => ?_, fun sc' hsc' => ?_⟩
    · rw [dnoms_encChainDN] at ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
      obtain ⟨x, hx⟩ := hn a ha
      exact ⟨x, fun y => (upC_old I.toInterp a y).trans (hx y)⟩
    · obtain ⟨sc, hsc, rfl⟩ := List.mem_map.1 hsc'
      have := hS sc hsc
      cases sc with
      | selfR body R =>
        intro x hx
        rw [upC_rt]
        exact this x fun a ha => (upC_old I.toInterp a x).1 (hx _ (List.mem_map_of_mem ha))
      | selfL R head =>
        intro x hx
        rw [upC_rt] at hx
        obtain ⟨b, hb, hbx⟩ := this x hx
        exact ⟨_, List.mem_map_of_mem hb, (upC_old I.toInterp b x).2 hbx⟩
  · rintro ⟨D, V, hD, atom, hΘ, J, hJ, hn, hS⟩
    rw [dbase_encChainDN] at hJ
    have hJo : SRIQ.models J.toInterp (encChain (SRIQD.objPart (dbase O))) := by
      have := (SRIQD.models_iff.1 hJ).1
      rwa [objPart_encChainQD] at this
    refine ⟨D, V, hD, atom, hΘ, _, models_encChainQD_down h hJ, fun a ha => ?_, fun sc hsc => ?_⟩
    · exact hn (Fin.castAdd _ a) (by rw [dnoms_encChainDN]; exact List.mem_map_of_mem ha)
    · have := hS _ (List.mem_map_of_mem (f := SClause.mapC (Fin.castAdd _)) hsc)
      cases sc with
      | selfR body R =>
        intro x hx
        have h1 := this x fun a' ha' => by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
          exact (downC_old J.toInterp a x).1 (hx a ha)
        exact (downC_rt R x x).2 ⟨[R], gen_self R, (path_single _ R x x).2 h1⟩
      | selfL R head =>
        intro x hx
        have h1 := (downC_rt_simple hJo (hs R head hsc) x x).1 hx
        obtain ⟨b', hb', hbx⟩ := this x h1
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
        exact ⟨b, hb, hbx⟩

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.consistentDS_encChainDN
