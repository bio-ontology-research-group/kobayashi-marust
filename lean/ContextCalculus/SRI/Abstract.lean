import ContextCalculus.SRI.Procedure

/-!
# The abstract interface of the v1.6.3 procedure

Soundness and completeness of `entails` use only two facts about the
record sets: the candidate set is closed under the root, child and
augment rules and holds closed types (`RulesClosed`), and the alive set
is its greatest part whose records are witnessed inside it (`IsElim`).
This file states both properties for any record sets, proves soundness
from them, and shows that `Gstar` and `alive` have them.
`Completeness.lean` proves `entails_iff_of` for any such pair, so any
faster computation of the two sets (`Fast.lean`) inherits exactness.
-/

namespace ContextCalculus.SRI.Proc

open ContextCalculus.SRI

variable {n m : Nat}

/-- `G` is closed under the root, child and augment rules, and every type
in it is closed. -/
structure RulesClosed (O : Ontology (Fin n) (Fin m)) (req : List (Fin n))
    (G : Finset (Rec n)) : Prop where
  root : ∀ a ∈ req, ∀ t ∈ branches O {a}, (⟨{a}, ∅, t⟩ : Rec n) ∈ G
  child : ∀ r ∈ G, ∀ a R b, (a, R, b) ∈ demands O r.t →
    ∀ s ∈ branches O (insert b (fwd O r.t R)),
      (⟨insert b (fwd O r.t R), ∅, s⟩ : Rec n) ∈ G
  augment : ∀ r ∈ G, ∀ r' ∈ G, ∀ a R b, (a, R, b) ∈ demands O r.t →
    b ∈ r'.K → r'.K ⊆ insert b (fwd O r.t R) →
    ∀ t' ∈ branches O (r.K ∪ (r.A ∪ back O r'.t R)),
      (⟨r.K, r.A ∪ back O r'.t R, t'⟩ : Rec n) ∈ G
  closed : ∀ r ∈ G, Closed O r.t

/-- `E` is the greatest subset of `G` whose records are witnessed in it. -/
structure IsElim (O : Ontology (Fin n) (Fin m)) (G E : Finset (Rec n)) : Prop where
  subset : E ⊆ G
  witnessed : ∀ r ∈ E, Proc.witnessed O E r
  greatest : ∀ S ⊆ G, (∀ r ∈ S, Proc.witnessed O S r) → S ⊆ E

/-- `witnessed` with the witness found by its exact context: a record
whose context is the child context `insert b (fwd O r.t R)` of the
demand. The completeness proof always finds its witnesses there. -/
def witnessedK (O : Ontology (Fin n) (Fin m)) (G : Finset (Rec n)) (r : Rec n) : Prop :=
  ∀ d ∈ demands O r.t, ∃ r' ∈ G, r'.K = insert d.2.2 (fwd O r.t d.2.1) ∧
    back O r'.t d.2.1 ⊆ r.t

/-- `E` is the greatest subset of `G` whose records are witnessed in it
by exact context. -/
structure IsElimK (O : Ontology (Fin n) (Fin m)) (G E : Finset (Rec n)) : Prop where
  subset : E ⊆ G
  witnessed : ∀ r ∈ E, witnessedK O E r
  greatest : ∀ S ⊆ G, (∀ r ∈ S, witnessedK O S r) → S ⊆ E

variable {O : Ontology (Fin n) (Fin m)} {req : List (Fin n)} {G E : Finset (Rec n)}

/-! ## The rules in the form the completeness proof uses -/

theorem RulesClosed.mem_root (hG : RulesClosed O req G) {a : Fin n} (ha : a ∈ req)
    {t : Ty n} (ht : t ∈ branches O {a}) : (⟨{a}, ∅, t⟩ : Rec n) ∈ G :=
  hG.root a ha t ht

theorem RulesClosed.mem_child (hG : RulesClosed O req G) {r : Rec n} (hr : r ∈ G)
    {a b : Fin n} {R : RT m} (hd : (a, R, b) ∈ demands O r.t) {s : Ty n}
    (hs : s ∈ branches O (insert b (fwd O r.t R))) :
    (⟨insert b (fwd O r.t R), ∅, s⟩ : Rec n) ∈ G :=
  hG.child r hr a R b hd s hs

theorem RulesClosed.mem_augment (hG : RulesClosed O req G) {r r' : Rec n} (hr : r ∈ G)
    (hr' : r' ∈ G) {a b : Fin n} {R : RT m} (hd : (a, R, b) ∈ demands O r.t)
    (hb : b ∈ r'.K) (hK : r'.K ⊆ insert b (fwd O r.t R)) {t' : Ty n}
    (ht' : t' ∈ branches O (r.K ∪ (r.A ∪ back O r'.t R))) :
    (⟨r.K, r.A ∪ back O r'.t R, t'⟩ : Rec n) ∈ G :=
  hG.augment r hr r' hr' a R b hd hb hK t' ht'

/-! ## Soundness -/

/-- **Soundness.** The types of an elimination result are good. -/
theorem good_of_isElim (hG : RulesClosed O req G) (hE : IsElim O G E) {r : Rec n}
    (hr : r ∈ E) : Good O r.t := by
  refine ⟨E.image Rec.t, Finset.mem_image_of_mem _ hr, ?_⟩
  intro t ht
  obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.1 ht
  refine ⟨hG.closed r0 (hE.subset hr0), ?_⟩
  intro a R b hcl ha
  obtain ⟨r', hr', hb, hf, hbk⟩ := hE.witnessed r0 hr0 (a, R, b) (mem_demands.2 ⟨hcl, ha⟩)
  exact ⟨r'.t, Finset.mem_image_of_mem _ hr', hb, (compat_iff R r0.t r'.t).2 ⟨hf, hbk⟩⟩

/-- When every record of `G` holds its context in its type, a witness by
exact context is a witness. -/
theorem witnessed_of_witnessedK (hKt : ∀ r ∈ G, r.K ⊆ r.t) {S : Finset (Rec n)} (hSG : S ⊆ G)
    {r : Rec n} (h : witnessedK O S r) : witnessed O S r := by
  intro d hd
  obtain ⟨r', hr', hK, hb⟩ := h d hd
  have hsub : insert d.2.2 (fwd O r.t d.2.1) ⊆ r'.t := by
    rw [← hK]; exact hKt r' (hSG hr')
  exact ⟨r', hr', hsub (Finset.mem_insert_self _ _), (Finset.subset_insert _ _).trans hsub, hb⟩

/-- **Soundness** for elimination by exact context. -/
theorem good_of_isElimK (hG : RulesClosed O req G) (hKt : ∀ r ∈ G, r.K ⊆ r.t)
    (hE : IsElimK O G E) {r : Rec n} (hr : r ∈ E) : Good O r.t := by
  refine ⟨E.image Rec.t, Finset.mem_image_of_mem _ hr, ?_⟩
  intro t ht
  obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.1 ht
  refine ⟨hG.closed r0 (hE.subset hr0), ?_⟩
  intro a R b hcl ha
  obtain ⟨r', hr', hb, hf, hbk⟩ := witnessed_of_witnessedK hKt hE.subset (hE.witnessed r0 hr0)
    (a, R, b) (mem_demands.2 ⟨hcl, ha⟩)
  exact ⟨r'.t, Finset.mem_image_of_mem _ hr', hb, (compat_iff R r0.t r'.t).2 ⟨hf, hbk⟩⟩

/-! ## The reference sets meet the interface -/

theorem Gstar_rulesClosed : RulesClosed O req (Gstar O req) where
  root _ ha _ ht := Gstar_root ha ht
  child _ hr _ _ _ hd _ hs := Gstar_child hr hd hs
  augment _ hr _ hr' _ _ _ hd hb hK _ ht' := Gstar_augment hr hr' hd hb hK ht'
  closed _ hr := Gstar_closed hr

theorem alive_isElim : IsElim O (Gstar O req) (alive O req) where
  subset := alive_subset
  witnessed _ hr := alive_witnessed hr
  greatest _ hS hw := subset_alive hS hw

end ContextCalculus.SRI.Proc

#print axioms ContextCalculus.SRI.Proc.good_of_isElim
#print axioms ContextCalculus.SRI.Proc.good_of_isElimK
#print axioms ContextCalculus.SRI.Proc.Gstar_rulesClosed
#print axioms ContextCalculus.SRI.Proc.alive_isElim
