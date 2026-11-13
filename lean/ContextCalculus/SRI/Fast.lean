import ContextCalculus.SRI.Completeness
import ContextCalculus.SRI.FastTy
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

/-!
# A fast executable procedure for ALCHI (v1.6.3, P2b)

`Procedure.lean` computes `Gstar` in rounds that apply every rule to
every record and pair of records, and `alive` in rounds over the whole
set. This file computes a rule-closed candidate set and its elimination
result with indexes and a worklist, and proves the properties of
`Abstract.lean` (`RulesClosed`, `IsElimK`). `entails_iff_ofK` then gives
`fastEntails_iff`; `classify_spec` and `classifyF_spec` give every
subsumer of every requested name from one run.

The parts:

- `mkIx`: indexes built once per ontology: universal and existential
  clauses by their left name, gcis by each body name, the super-roles of
  every role term.
- `fwdF`, `backF`, `demF`: the propagation sets and demands through the
  indexes, equal to `fwd`, `back` and `demands`.
- `branchesF`: the branches of a seed. It fires gcis from a queue of the
  gcis whose body gained a name, instead of scanning every gci at each
  step. Its result contains every member of `branches` and holds closed
  types only.
- `loop`: the worklist saturation. The state keeps the records seen so
  far (a hash set), the records still to process, the seen records by
  each name of their context, and the demands of the seen records by
  their filler. Processing a record applies the child rule to it and the
  augment rule with it as the parent and as the child, against the seen
  records. The measure `2 * unseen + todo` falls at every step.
- `elimF`: elimination in rounds; each record keeps, for each demand, the
  list of records that could witness it.
- `elimK` (P2c): elimination as `elimF`, but each demand looks up its
  candidate witnesses by exact context (`witnessedK`) in a hash map from
  the sorted context to its records. `fastAlive` uses it.
- `classifyF` (P2c): the readout. For each requested name it gives `none`
  when no alive record holds the name, and otherwise filters the names of
  one such type against hash sets of the others.

Unlike `Gstar`, the candidate set need not be least: `entails_iff_of`
asks only that it is closed under the rules and holds closed types.
-/

namespace ContextCalculus.SRI.Proc

open ContextCalculus.SRI

variable {n m : Nat}

/-! ## Lists of names and indexes by name -/

/-- Lists of values by name. -/
abbrev Idx (n : Nat) (β : Type) := Std.HashMap (Fin n) (List β)

def Idx.get {β : Type} (ix : Idx n β) (k : Fin n) : List β := ix.getD k []

def Idx.add {β : Type} (ix : Idx n β) (k : Fin n) (v : β) : Idx n β :=
  ix.insert k (v :: ix.get k)

def Idx.ofList {β : Type} (L : List (Fin n × β)) : Idx n β :=
  L.foldl (fun ix p => ix.add p.1 p.2) ∅

/-! ## Indexes of the ontology -/

structure Ix (n m : Nat) where
  /-- `a ↦ (S, c)` for each `allRight a S c`. -/
  allBy : Idx n (RT m × Fin n)
  /-- `a ↦ (R, b)` for each `exRight a R b`. -/
  exBy : Idx n (RT m × Fin n)
  /-- The gcis in clause order. -/
  gciArr : Array (List (Fin n) × List (Fin n))
  /-- `a ↦ i` for each gci `i` with `a` in its body. -/
  gciBy : Idx n Nat
  /-- The gcis with an empty body. -/
  gciTop : List Nat
  /-- The super-roles of `.pos r` and of `.inv r`. -/
  upPos : Array (List (RT m))
  upInv : Array (List (RT m))

def mkIx (O : Ontology (Fin n) (Fin m)) : Ix n m where
  allBy := Idx.ofList (alls O)
  exBy := Idx.ofList (exs O)
  gciArr := (gcis O).toArray
  gciBy := Idx.ofList ((gcis O).zipIdx.flatMap fun q => q.1.1.map fun a => (a, q.2))
  gciTop := ((gcis O).zipIdx.filter fun q => q.1.1.isEmpty).map (·.2)
  upPos := Array.ofFn fun r : Fin m => upFix O (.pos r) (2 * m + 2) [.pos r]
  upInv := Array.ofFn fun r : Fin m => upFix O (.inv r) (2 * m + 2) [.inv r]

def Ix.up (ix : Ix n m) : RT m → List (RT m)
  | .pos r => ix.upPos.getD r.val []
  | .inv r => ix.upInv.getD r.val []

/-! ## Propagation and demands through the indexes -/

def fwdF (ix : Ix n m) (t : Ty n) (R : RT m) : Ty n :=
  let up := ix.up R
  ofL ((toL t).flatMap fun a =>
    (ix.allBy.get a).filterMap fun q => if q.1 ∈ up then some q.2 else none)

def backF (ix : Ix n m) (s : Ty n) (R : RT m) : Ty n :=
  fwdF ix s R.flip

def demF (ix : Ix n m) (t : Ty n) : List (Fin n × RT m × Fin n) :=
  (toL t).flatMap fun a => (ix.exBy.get a).map fun q => (a, q.1, q.2)

/-! ## Branches through a queue of triggered gcis -/

/-- The head parts a fired gci may add: sublists of the head names not
yet present, nonempty when no head name is present. -/
def choicesF (head : List (Fin n)) (cur : Ty n) : List (List (Fin n)) :=
  let h' := head.filter fun x => decide (x ∉ cur)
  if head.any fun x => decide (x ∈ cur) then h'.sublists
  else h'.sublists.filter fun Y => !Y.isEmpty

/-- The gci `i` fires when it is not done and its body holds. -/
def fireable (ix : Ix n m) (cur : Ty n) (done : List Nat) (i : Nat) :
    Option (List (Fin n) × List (Fin n)) :=
  match ix.gciArr[i]? with
  | none => none
  | some q => if decide (i ∉ done) && q.1.all (fun x => decide (x ∈ cur)) then some q else none

/-- Fire the queued gcis. The queue holds every gci that is not done and
whose body holds (and maybe others). The fuel bounds the number of fired
gcis; if it runs out, fall back to `branches`. -/
def fbAux (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) (σ : Ty n) :
    Nat → Ty n → List Nat → List Nat → List (Ty n)
  | _, cur, _, [] => [cur]
  | 0, cur, done, i :: rest =>
    match fireable ix cur done i with
    | none => fbAux O ix σ 0 cur done rest
    | some _ => branches O σ
  | f + 1, cur, done, i :: rest =>
    match fireable ix cur done i with
    | none => fbAux O ix σ (f + 1) cur done rest
    | some q => (choicesF q.2 cur).flatMap fun Y =>
        fbAux O ix σ f (cur ∪ Y.toFinset) (i :: done) (Y.flatMap ix.gciBy.get ++ rest)
termination_by fuel _ _ queue => (fuel, queue.length)

/-- The current type of `fbAuxH`: a hash set of its names for membership
tests and a list of them for the result. -/
structure Cur (n : Nat) where
  h : Std.HashSet (Fin n)
  acc : List (Fin n)
  ok : ∀ x, x ∈ acc ↔ x ∈ h

/-- The type the current state stands for. -/
def Cur.ty (c : Cur n) : Ty n := ofL c.acc

def Cur.ofTy (σ : Ty n) : Cur n :=
  ⟨Std.HashSet.ofList (toL σ), toL σ, fun x => by
    rw [Std.HashSet.mem_ofList, List.contains_iff_mem]⟩

def Cur.add (c : Cur n) (y : Fin n) : Cur n :=
  ⟨c.h.insert y, y :: c.acc, fun x => by
    rw [List.mem_cons, Std.HashSet.mem_insert, beq_iff_eq]
    exact or_congr eq_comm (c.ok x)⟩

def Cur.addAll (c : Cur n) (Y : List (Fin n)) : Cur n := Y.foldl Cur.add c

/-- `fireable` with hash-set membership. -/
def fireableH (ix : Ix n m) (cur : Cur n) (done : Std.HashSet Nat) (i : Nat) :
    Option (List (Fin n) × List (Fin n)) :=
  match ix.gciArr[i]? with
  | none => none
  | some q => if !done.contains i && q.1.all (fun x => cur.h.contains x) then some q else none

/-- `choicesF` with hash-set membership. -/
def choicesH (head : List (Fin n)) (cur : Cur n) : List (List (Fin n)) :=
  let h' := head.filter fun x => !cur.h.contains x
  if head.any fun x => cur.h.contains x then h'.sublists
  else h'.sublists.filter fun Y => !Y.isEmpty

/-- `fbAux` with the current type and the fired gcis in hash sets. It
returns the same list (`fbAuxH_eq`). -/
def fbAuxH (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) (σ : Ty n) :
    Nat → Cur n → Std.HashSet Nat → List Nat → List (Ty n)
  | _, cur, _, [] => [cur.ty]
  | 0, cur, done, i :: rest =>
    match fireableH ix cur done i with
    | none => fbAuxH O ix σ 0 cur done rest
    | some _ => branches O σ
  | f + 1, cur, done, i :: rest =>
    match fireableH ix cur done i with
    | none => fbAuxH O ix σ (f + 1) cur done rest
    | some q => (choicesH q.2 cur).flatMap fun Y =>
        fbAuxH O ix σ f (cur.addAll Y) (done.insert i) (Y.flatMap ix.gciBy.get ++ rest)
termination_by fuel _ _ queue => (fuel, queue.length)

def branchesF (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) (σ : Ty n) : List (Ty n) :=
  fbAuxH O ix σ (ix.gciArr.size + 1) (Cur.ofTy σ) ∅ (ix.gciTop ++ (toL σ).flatMap ix.gciBy.get)

/-! ## The worklist saturation -/

instance : Hashable (Rec n) where
  hash r := mixHash (hash (toL r.K)) (mixHash (hash (toL r.A)) (hash (toL r.t)))

/-- The saturation state. -/
structure St (n m : Nat) where
  seen : Std.HashSet (Rec n)
  todo : List (Rec n)
  /-- `b ↦ r` for each seen `r` with `b ∈ r.K`. -/
  kidx : Idx n (Rec n)
  /-- `b ↦ (r, R, insert b (fwd r.t R))` for each seen `r` and demand
  `(a, R, b)` of `r.t`. -/
  fidx : Idx n (Rec n × RT m × Ty n)
  /-- The seeds `(K, A)`, by their sorted lists, whose records are all seen. -/
  seeds : Std.HashSet (List (Fin n) × List (Fin n))

def St.empty : St n m := ⟨∅, [], ∅, ∅, ∅⟩

/-- Add a record unless it is seen: mark it seen, queue it, index it. -/
def addRec (ix : Ix n m) (st : St n m) (x : Rec n) : St n m :=
  if st.seen.contains x then st else
  { st with
    seen := st.seen.insert x
    todo := x :: st.todo
    kidx := (toL x.K).foldl (fun k b => k.add b x) st.kidx
    fidx := (demF ix x.t).foldl
      (fun f d => f.add d.2.2 (x, d.2.1, ins d.2.2 (fwdF ix x.t d.2.1))) st.fidx }

/-- Add the records `(K, A, t)` of a seed `(K, A)`, for every branch `t`
of `K ∪ A`, unless the seed is done; then mark it done. -/
def addSeed (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) (st : St n m) (s : Ty n × Ty n) :
    St n m :=
  if st.seeds.contains (toL s.1, toL s.2) then st else
  ((branchesF O ix (uni s.1 s.2)).map fun t => (⟨s.1, s.2, t⟩ : Rec n)).foldl (addRec ix)
    { st with seeds := st.seeds.insert (toL s.1, toL s.2) }

/-- The seeds the rules give from `r` and the seen records: the child
rule, the augment rule with `r` as the parent and with `r` as the child. -/
def seedsOf (ix : Ix n m) (st : St n m) (r : Rec n) : List (Ty n × Ty n) :=
  let fs := (demF ix r.t).map fun d => (d, ins d.2.2 (fwdF ix r.t d.2.1))
  let ch := fs.map fun p => (p.2, (∅ : Ty n))
  let ap := fs.flatMap fun p =>
    ((st.kidx.get p.1.2.2).filter fun r' => sub r'.K p.2).map fun r' =>
      (r.K, uni r.A (backF ix r'.t p.1.2.1))
  let ac := (toL r.K).flatMap fun b =>
    ((st.fidx.get b).filter fun e => sub r.K e.2.2).map fun e =>
      (e.1.K, uni e.1.A (backF ix r.t e.2.1))
  ch ++ ap ++ ac

/-- Twice the number of unseen records plus the queue length. -/
noncomputable def St.measure (st : St n m) : Nat := by
  classical
  exact 2 * (Finset.univ.filter fun r : Rec n => r ∉ st.seen).card + st.todo.length

theorem addRec_measure (ix : Ix n m) (st : St n m) (x : Rec n) :
    (addRec ix st x).measure ≤ st.measure := by
  classical
  unfold addRec
  split
  · exact le_rfl
  · next hx =>
    simp only [St.measure]
    have hsub : (Finset.univ.filter fun r : Rec n => r ∉ st.seen.insert x) ⊂
        Finset.univ.filter fun r : Rec n => r ∉ st.seen := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨x, ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, fun h => hx (Std.HashSet.mem_iff_contains.1 h)⟩
        · rw [Finset.mem_filter]
          exact fun h => h.2 (Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true x)))
      · intro r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Std.HashSet.mem_insert,
          not_or]
        exact And.right
    have := Finset.card_lt_card hsub
    simp only [List.length_cons]
    omega

theorem foldl_addRec_measure (ix : Ix n m) :
    ∀ (L : List (Rec n)) (st : St n m), (L.foldl (addRec ix) st).measure ≤ st.measure
  | [], _ => le_rfl
  | x :: L, st => (foldl_addRec_measure ix L _).trans (addRec_measure ix st x)

theorem addSeed_measure (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) (st : St n m)
    (s : Ty n × Ty n) : (addSeed O ix st s).measure ≤ st.measure := by
  unfold addSeed
  split
  · exact le_rfl
  · exact foldl_addRec_measure ix _ _

theorem foldl_addSeed_measure (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) :
    ∀ (L : List (Ty n × Ty n)) (st : St n m), (L.foldl (addSeed O ix) st).measure ≤ st.measure
  | [], _ => le_rfl
  | x :: L, st => (foldl_addSeed_measure O ix L _).trans (addSeed_measure O ix st x)

/-- Process queued records until none is left. -/
def loop (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) (st : St n m) : St n m :=
  match h : st.todo with
  | [] => st
  | r :: rest => loop O ix ((seedsOf ix st r).foldl (addSeed O ix) { st with todo := rest })
termination_by st.measure
decreasing_by
  refine Nat.lt_of_le_of_lt (foldl_addSeed_measure O ix _ _) ?_
  simp only [St.measure, h, List.length_cons]
  omega

/-- The root seeds of the requested names. -/
def roots (req : List (Fin n)) : List (Ty n × Ty n) :=
  req.map fun a => (({a} : Ty n), (∅ : Ty n))

/-- The candidate set as a list. -/
def candidates (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) (req : List (Fin n)) :
    List (Rec n) :=
  (loop O ix ((roots req).foldl (addSeed O ix) St.empty)).seen.toList

/-! ## Elimination -/

/-- For each demand of `r`, the records of the type index that witness it. -/
def supports (ix : Ix n m) (tIdx : Idx n (Rec n)) (r : Rec n) : List (List (Rec n)) :=
  (demF ix r.t).map fun d =>
    let F := fwdF ix r.t d.2.1
    (tIdx.get d.2.2).filter fun r' => decide (F ⊆ r'.t) && decide (backF ix r'.t d.2.1 ⊆ r.t)

def okIn (E : Std.HashSet (Rec n)) (ss : List (List (Rec n))) : Bool :=
  ss.all fun l => l.any fun r' => E.contains r'

/-- Drop the records with an unwitnessed demand until none is dropped. -/
def elimLoop (L : List (Rec n × List (List (Rec n)))) : List (Rec n × List (List (Rec n))) :=
  let E : Std.HashSet (Rec n) := Std.HashSet.ofList (L.map Prod.fst)
  let L' := L.filter fun p => okIn E p.2
  if h : L'.length < L.length then elimLoop L' else L
termination_by L.length
decreasing_by exact h

def typeIdx (G : List (Rec n)) : Idx n (Rec n) :=
  Idx.ofList (G.flatMap fun r => (toL r.t).map fun b => (b, r))

def elimF (ix : Ix n m) (G : List (Rec n)) : List (Rec n) :=
  let tIdx := typeIdx G
  (elimLoop (G.map fun r => (r, supports ix tIdx r))).map Prod.fst

/-! ## Elimination by exact context -/

/-- The records by their context, keyed by its sorted list of names. -/
def ctxIdx (G : List (Rec n)) : Std.HashMap (List (Fin n)) (List (Rec n)) :=
  G.foldl (fun ix r => ix.insert (toL r.K) (r :: ix.getD (toL r.K) [])) ∅

/-- For each demand of `r`, the records whose context is the child
context of the demand and whose back set fits `r`. -/
def supportsK (ix : Ix n m) (kIdx : Std.HashMap (List (Fin n)) (List (Rec n))) (r : Rec n) :
    List (List (Rec n)) :=
  (demF ix r.t).map fun d =>
    (kIdx.getD (toL (ins d.2.2 (fwdF ix r.t d.2.1))) []).filter fun r' =>
      sub (backF ix r'.t d.2.1) r.t

def elimK (ix : Ix n m) (G : List (Rec n)) : List (Rec n) :=
  let kIdx := ctxIdx G
  (elimLoop (G.map fun r => (r, supportsK ix kIdx r))).map Prod.fst

/-! ## The answers -/

/-- The alive records of the fast procedure. -/
def fastAlive (O : Ontology (Fin n) (Fin m)) (req : List (Fin n)) : List (Rec n) :=
  let ix := mkIx O
  elimK ix (candidates O ix req)

/-- The fast procedure's verdict on `a ⊑ b`. -/
def fastEntails (O : Ontology (Fin n) (Fin m)) (req : List (Fin n)) (a b : Fin n) : Bool :=
  (fastAlive O req).all fun r => !decide (a ∈ r.t) || decide (b ∈ r.t)

/-- The names in every listed type (all names for the empty list). -/
def interAll : List (Rec n) → Ty n
  | [] => Finset.univ
  | r :: rs => rs.foldl (fun acc r' => acc ∩ r'.t) r.t

/-- Every requested name with its subsumers, from one run. -/
def classify (O : Ontology (Fin n) (Fin m)) (req : List (Fin n)) :
    List (Fin n × List (Fin n)) :=
  let eIdx := typeIdx (fastAlive O req)
  req.map fun a => (a, toL (interAll (eIdx.get a)))

/-- Each listed type with its hash set, by each of its names. -/
def hashIdx (L : List (Rec n)) : Idx n (Ty n × Std.HashSet (Fin n)) :=
  Idx.ofList (L.flatMap fun r =>
    let h := Std.HashSet.ofList (toL r.t)
    (toL r.t).map fun b => (b, (r.t, h)))

/-- The members of `L` in every listed hash set. -/
def meetH (L : List (Fin n)) (rest : List (Ty n × Std.HashSet (Fin n))) : List (Fin n) :=
  rest.foldl (fun cur q => cur.filter fun b => q.2.contains b) L

/-- Every requested name with its subsumers, from one run: `none` when no
alive record holds the name (it is unsatisfiable), otherwise the names of
one alive type with the name that are in every other such type. -/
def classifyF (O : Ontology (Fin n) (Fin m)) (req : List (Fin n)) :
    List (Fin n × Option (List (Fin n))) :=
  let hIdx := hashIdx (fastAlive O req)
  req.map fun a => (a, match hIdx.get a with
    | [] => none
    | q :: rest => some (meetH (toL q.1) rest))

/-! ## Proofs: indexes -/

section Proofs

variable {O : Ontology (Fin n) (Fin m)}

theorem Idx.mem_get_add {β : Type} {ix : Idx n β} {k k' : Fin n} {v x : β} :
    x ∈ (ix.add k v).get k' ↔ (k = k' ∧ x = v) ∨ x ∈ ix.get k' := by
  unfold Idx.add Idx.get
  rw [Std.HashMap.getD_insert]
  by_cases h : k = k'
  · subst h; simp
  · simp [h]

theorem Idx.mem_foldl_add {β γ : Type} (f : γ → Fin n) (g : γ → β) {k : Fin n} {x : β} :
    ∀ (L : List γ) (ix : Idx n β),
      x ∈ (L.foldl (fun ix c => ix.add (f c) (g c)) ix).get k ↔
        x ∈ ix.get k ∨ ∃ c ∈ L, f c = k ∧ g c = x
  | [], ix => by simp
  | c :: L, ix => by
    rw [List.foldl_cons, Idx.mem_foldl_add f g L, Idx.mem_get_add]
    constructor
    · rintro ((⟨h1, h2⟩ | h) | ⟨c', hc', h⟩)
      · exact Or.inr ⟨c, List.mem_cons_self .., h1, h2.symm⟩
      · exact Or.inl h
      · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h⟩
    · rintro (h | ⟨c', hc', h1, h2⟩)
      · exact Or.inl (Or.inr h)
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact Or.inl (Or.inl ⟨h1, h2.symm⟩)
        · exact Or.inr ⟨c', hc', h1, h2⟩

theorem Idx.mem_ofList {β : Type} {L : List (Fin n × β)} {k : Fin n} {x : β} :
    x ∈ (Idx.ofList L).get k ↔ (k, x) ∈ L := by
  unfold Idx.ofList
  rw [Idx.mem_foldl_add (fun p => p.1) (fun p => p.2) L ∅]
  simp only [Idx.get, Std.HashMap.getD_empty, List.not_mem_nil, false_or]
  constructor
  · rintro ⟨c, hc, rfl, rfl⟩; exact hc
  · intro h; exact ⟨_, h, rfl, rfl⟩

theorem mem_allBy {a c : Fin n} {S : RT m} :
    (S, c) ∈ (mkIx O).allBy.get a ↔ Clause.allRight a S c ∈ O := by
  simp only [mkIx, Idx.mem_ofList, mem_alls]

theorem mem_exBy {a b : Fin n} {R : RT m} :
    (R, b) ∈ (mkIx O).exBy.get a ↔ Clause.exRight a R b ∈ O := by
  simp only [mkIx, Idx.mem_ofList, mem_exs]

theorem gciArr_get (i : Nat) : (mkIx O).gciArr[i]? = (gcis O)[i]? := by
  simp only [mkIx, List.getElem?_toArray]

theorem mem_gciBy {x : Fin n} {i : Nat} :
    i ∈ (mkIx O).gciBy.get x ↔ ∃ q, (gcis O)[i]? = some q ∧ x ∈ q.1 := by
  simp only [mkIx, Idx.mem_ofList, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨q, j⟩, hq, a, ha, rfl, rfl⟩
    exact ⟨q, List.mem_zipIdx_iff_getElem?.1 hq, ha⟩
  · rintro ⟨q, hq, hx⟩
    exact ⟨⟨q, i⟩, List.mem_zipIdx_iff_getElem?.2 hq, x, hx, rfl, rfl⟩

theorem mem_gciTop {i : Nat} :
    i ∈ (mkIx O).gciTop ↔ ∃ q, (gcis O)[i]? = some q ∧ q.1 = [] := by
  simp only [mkIx, List.mem_map, List.mem_filter, List.isEmpty_iff]
  constructor
  · rintro ⟨⟨q, j⟩, ⟨hq, he⟩, rfl⟩
    exact ⟨q, List.mem_zipIdx_iff_getElem?.1 hq, he⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨⟨q, i⟩, ⟨List.mem_zipIdx_iff_getElem?.2 hq, he⟩, rfl⟩

theorem mem_up {R S : RT m} : S ∈ (mkIx O).up R ↔ RoleLe O R S := by
  have h0 : ∀ R : RT m, S ∈ upFix O R (2 * m + 2) [R] ↔ RoleLe O R S := fun R =>
    mem_upFix _ _ (fun T hT => by
      rw [List.mem_singleton] at hT; subst hT; exact Relation.ReflTransGen.refl)
      (List.mem_singleton_self _)
  cases R with
  | pos r =>
    simp only [Ix.up, mkIx, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      r.isLt, dite_true, Option.getD_some]
    exact h0 _
  | inv r =>
    simp only [Ix.up, mkIx, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      r.isLt, dite_true, Option.getD_some]
    exact h0 _

theorem fwdF_eq (t : Ty n) (R : RT m) : fwdF (mkIx O) t R = fwd O t R := by
  ext c
  rw [mem_fwd]
  simp only [fwdF, ofL_eq, List.mem_toFinset, List.mem_flatMap, List.mem_filterMap, mem_toL]
  constructor
  · rintro ⟨a, ha, ⟨S, c'⟩, hq, he⟩
    split at he
    · next hS =>
      cases he
      exact ⟨a, S, mem_allBy.1 hq, ha, mem_up.1 hS⟩
    · cases he
  · rintro ⟨a, S, hcl, ha, hS⟩
    exact ⟨a, ha, (S, c), mem_allBy.2 hcl, by simp [mem_up.2 hS]⟩

theorem backF_eq (s : Ty n) (R : RT m) : backF (mkIx O) s R = back O s R := by
  ext c
  rw [backF, fwdF_eq, mem_fwd, mem_back]

theorem mem_demF {t : Ty n} {d : Fin n × RT m × Fin n} :
    d ∈ demF (mkIx O) t ↔ d ∈ demands O t := by
  obtain ⟨a, R, b⟩ := d
  rw [mem_demands]
  simp only [demF, List.mem_flatMap, List.mem_map, mem_toL, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', ⟨R', b'⟩, hq, rfl, rfl, rfl⟩
    exact ⟨mem_exBy.1 hq, ha'⟩
  · rintro ⟨hcl, ha⟩
    exact ⟨a, ha, (R, b), mem_exBy.2 hcl, rfl, rfl, rfl⟩

/-! ## Proofs: branches -/

/-- Every type `branchesAux` returns is generated from the current seed:
each name it adds comes from a head whose body was already present. -/
theorem branchesAux_sub_guided {σ : Ty n} : ∀ (fuel : Nat) (cur : Ty n) (done : List Nat)
    (t : Ty n), t ∈ branchesAux O fuel cur done → done.Nodup →
    (∀ i ∈ done, i < (gcis O).length) → (gcis O).length + 1 ≤ fuel + done.length →
    (∀ q ∈ (gcis O).zipIdx, q.2 ∈ done → ∃ b ∈ q.1.2, b ∈ cur) →
    cur ⊆ guided O t σ → t ⊆ guided O t σ := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur done t _ hnd hlt hfuel _
    exact (fuel_absurd hnd hlt (by omega)).elim
  | succ fuel ih =>
    intro cur done t ht hnd hlt hfuel hdone hcg
    rw [branchesAux] at ht
    split at ht
    next => rw [List.mem_singleton] at ht; subst ht; exact hcg
    next q hq =>
      have hqmem := List.mem_of_find?_eq_some hq
      have hqp := List.find?_some hq
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hqp
      have hlen := List.snd_lt_of_mem_zipIdx hqmem
      obtain ⟨Y, hY, ht⟩ := List.mem_flatMap.1 ht
      have hnd' : (q.2 :: done).Nodup := List.nodup_cons.2 ⟨hqp.1, hnd⟩
      have hlt' : ∀ i ∈ q.2 :: done, i < (gcis O).length := by
        intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact hlen
        · exact hlt i hi
      have hfuel' : (gcis O).length + 1 ≤ fuel + (q.2 :: done).length := by
        simp only [List.length_cons]; omega
      have hdone' : ∀ q' ∈ (gcis O).zipIdx, q'.2 ∈ q.2 :: done → ∃ b ∈ q'.1.2, b ∈ cur ∪ Y := by
        intro q' hq' hd
        rcases List.mem_cons.1 hd with he | hd
        · obtain rfl := zipIdx_eq hq' hqmem he
          exact choices_head hY
        · obtain ⟨b, hb, hbc⟩ := hdone q' hq' hd
          exact ⟨b, hb, Finset.mem_union_left _ hbc⟩
      have hsub := (branchesAux_closed _ _ _ _ ht hnd' hlt' hfuel' hdone').2
      refine ih _ _ t ht hnd' hlt' hfuel' hdone' (Finset.union_subset hcg ?_)
      intro x hx
      obtain ⟨⟨l, hl, rfl⟩, -⟩ := mem_choices.1 hY
      refine guided_closed (gci_of_mem_zipIdx hqmem) (fun a ha => hcg (hqp.2 a ha)) ?_
      exact Finset.mem_inter.2 ⟨List.mem_toFinset.2 (hl.subset (List.mem_toFinset.1 hx)),
        hsub (Finset.mem_union_right _ hx)⟩

/-- A type in `branches σ` is the guided closure of `σ` inside itself. -/
theorem guided_of_mem_branches {σ t : Ty n} (h : t ∈ branches O σ) : guided O t σ = t :=
  Finset.Subset.antisymm (guided_le (branches_closed h).2)
    (branchesAux_sub_guided _ σ [] t h List.nodup_nil (by simp) (by simp) (by simp)
      subset_guided)

/-- Every gci that is not done and whose body holds is queued. -/
def QInv (O : Ontology (Fin n) (Fin m)) (cur : Ty n) (done queue : List Nat) : Prop :=
  ∀ j q, (gcis O)[j]? = some q → j ∉ done → (∀ x ∈ q.1, x ∈ cur) → j ∈ queue

theorem fireable_some {cur : Ty n} {done : List Nat} {i : Nat} {q : List (Fin n) × List (Fin n)}
    (h : fireable (mkIx O) cur done i = some q) :
    (gcis O)[i]? = some q ∧ i ∉ done ∧ ∀ x ∈ q.1, x ∈ cur := by
  unfold fireable at h
  rw [gciArr_get] at h
  split at h
  · cases h
  · next q' hq' =>
    split at h
    · next hc =>
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
      exact ⟨hq', hc⟩
    · cases h

theorem QInv.skip {cur : Ty n} {done rest : List Nat} {i : Nat} (hQ : QInv O cur done (i :: rest))
    (h : fireable (mkIx O) cur done i = none) : QInv O cur done rest := by
  intro j q hq hj hb
  rcases List.mem_cons.1 (hQ j q hq hj hb) with rfl | hr
  · exfalso
    unfold fireable at h
    rw [gciArr_get, hq] at h
    simp only at h
    split at h
    · cases h
    · next hc =>
      apply hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      exact ⟨hj, hb⟩
  · exact hr

theorem QInv.fire {cur : Ty n} {done rest : List Nat} {i : Nat} (hQ : QInv O cur done (i :: rest))
    (Y : List (Fin n)) :
    QInv O (cur ∪ Y.toFinset) (i :: done) (Y.flatMap (mkIx O).gciBy.get ++ rest) := by
  intro j q hq hj hb
  rw [List.mem_cons, not_or] at hj
  by_cases hc : ∀ x ∈ q.1, x ∈ cur
  · rcases List.mem_cons.1 (hQ j q hq hj.2 hc) with h | h
    · exact absurd h hj.1
    · exact List.mem_append_right _ h
  · push Not at hc
    obtain ⟨x, hx, hxc⟩ := hc
    have hxY : x ∈ Y := by
      rcases Finset.mem_union.1 (hb x hx) with h | h
      · exact absurd h hxc
      · exact List.mem_toFinset.1 h
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨x, hxY, mem_gciBy.2 ⟨q, hq, hx⟩⟩)

theorem choicesF_spec {head : List (Fin n)} {cur : Ty n} {Y : List (Fin n)}
    (hY : Y ∈ choicesF head cur) : (∀ x ∈ Y, x ∈ head) ∧ ∃ b ∈ head, b ∈ cur ∨ b ∈ Y := by
  unfold choicesF at hY
  have hsub : ∀ Y, Y ∈ (head.filter fun x => decide (x ∉ cur)).sublists → ∀ x ∈ Y, x ∈ head :=
    fun Y hY x hx => (List.mem_filter.1 ((List.mem_sublists.1 hY).subset hx)).1
  split at hY
  · next ha =>
    obtain ⟨b, hb, hbc⟩ := List.any_eq_true.1 ha
    exact ⟨hsub Y hY, b, hb, Or.inl (of_decide_eq_true hbc)⟩
  · obtain ⟨hY, hne⟩ := List.mem_filter.1 hY
    refine ⟨hsub Y hY, ?_⟩
    cases Y with
    | nil => simp at hne
    | cons y Y => exact ⟨y, hsub _ hY y (List.mem_cons_self ..), Or.inr (List.mem_cons_self ..)⟩

/-- Soundness of `fbAux`: every returned type is closed. -/
theorem fbAux_closed {σ : Ty n} : ∀ (fuel : Nat) (cur : Ty n) (done queue : List Nat) (t : Ty n),
    t ∈ fbAux O (mkIx O) σ fuel cur done queue →
    (∀ j ∈ done, ∀ q, (gcis O)[j]? = some q → ∃ b ∈ q.2, b ∈ cur) →
    QInv O cur done queue → Closed O t := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur done queue
    induction queue with
    | nil =>
      intro t ht hD hQ
      rw [fbAux, List.mem_singleton] at ht
      subst ht
      intro body head hcl hbody
      obtain ⟨i, hi⟩ := exists_mem_zipIdx hcl
      have hi' := List.mem_zipIdx_iff_getElem?.1 hi
      by_cases hid : i ∈ done
      · exact hD i hid _ hi'
      · exact absurd (hQ i _ hi' hid hbody) (List.not_mem_nil)
    | cons i rest ih =>
      intro t ht hD hQ
      rw [fbAux] at ht
      split at ht
      · next h => exact ih t ht hD (hQ.skip h)
      · exact (branches_closed ht).1
  | succ f ihf =>
    intro cur done queue
    induction queue with
    | nil =>
      intro t ht hD hQ
      rw [fbAux, List.mem_singleton] at ht
      subst ht
      intro body head hcl hbody
      obtain ⟨i, hi⟩ := exists_mem_zipIdx hcl
      have hi' := List.mem_zipIdx_iff_getElem?.1 hi
      by_cases hid : i ∈ done
      · exact hD i hid _ hi'
      · exact absurd (hQ i _ hi' hid hbody) (List.not_mem_nil)
    | cons i rest ih =>
      intro t ht hD hQ
      rw [fbAux] at ht
      split at ht
      · next h => exact ih t ht hD (hQ.skip h)
      · next q h =>
        obtain ⟨hq, -, -⟩ := fireable_some h
        obtain ⟨Y, hY, ht⟩ := List.mem_flatMap.1 ht
        refine ihf _ _ _ t ht ?_ (hQ.fire Y)
        intro j hj q' hq'
        rcases List.mem_cons.1 hj with rfl | hj
        · rw [hq] at hq'
          cases hq'
          obtain ⟨-, b, hb, hbc⟩ := choicesF_spec hY
          refine ⟨b, hb, ?_⟩
          rcases hbc with h | h
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ (List.mem_toFinset.2 h)
        · obtain ⟨b, hb, hbc⟩ := hD j hj q' hq'
          exact ⟨b, hb, Finset.mem_union_left _ hbc⟩

/-- Completeness of `fbAux`: the guided closure of the seed inside any
closed `T ⊇ σ` is returned. -/
theorem fbAux_guided {T σ : Ty n} (hT : Closed O T) (hσ : σ ⊆ T) :
    ∀ (fuel : Nat) (cur : Ty n) (done queue : List Nat), σ ⊆ cur → cur ⊆ guided O T σ →
    (∀ j ∈ done, ∀ q, (gcis O)[j]? = some q → q.2.toFinset ∩ T ⊆ cur) →
    QInv O cur done queue → guided O T σ ∈ fbAux O (mkIx O) σ fuel cur done queue := by
  have hnil : ∀ (fuel : Nat) (cur : Ty n) (done : List Nat), σ ⊆ cur → cur ⊆ guided O T σ →
      (∀ j ∈ done, ∀ q, (gcis O)[j]? = some q → q.2.toFinset ∩ T ⊆ cur) →
      QInv O cur done [] → guided O T σ ∈ fbAux O (mkIx O) σ fuel cur done [] := by
    intro fuel cur done hσc hcg hD hQ
    rw [fbAux, List.mem_singleton]
    refine Finset.Subset.antisymm (guided_least hσc fun body head hcl hbody => ?_) hcg
    obtain ⟨i, hi⟩ := exists_mem_zipIdx hcl
    have hi' := List.mem_zipIdx_iff_getElem?.1 hi
    by_cases hid : i ∈ done
    · exact hD i hid _ hi'
    · exact absurd (hQ i _ hi' hid hbody) (List.not_mem_nil)
  intro fuel
  induction fuel with
  | zero =>
    intro cur done queue
    induction queue with
    | nil => exact hnil 0 cur done
    | cons i rest ih =>
      intro hσc hcg hD hQ
      rw [fbAux]
      split
      · next h => exact ih hσc hcg hD (hQ.skip h)
      · exact guided_mem_branches hT hσ
  | succ f ihf =>
    intro cur done queue
    induction queue with
    | nil => exact hnil (f + 1) cur done
    | cons i rest ih =>
      intro hσc hcg hD hQ
      rw [fbAux]
      split
      · next h => exact ih hσc hcg hD (hQ.skip h)
      · next q h =>
        obtain ⟨hq, -, hbody⟩ := fireable_some h
        have hcl : Clause.gci q.1 q.2 ∈ O := mem_gcis.1 (List.mem_of_getElem? hq)
        have hcT : cur ⊆ T := hcg.trans (guided_le hσ)
        let Y := (q.2.filter fun x => decide (x ∉ cur)).filter fun x => decide (x ∈ T)
        have hYm : ∀ x, x ∈ Y ↔ x ∈ q.2 ∧ x ∉ cur ∧ x ∈ T := by
          intro x; simp only [Y, List.mem_filter, decide_eq_true_eq]; tauto
        have hY : Y ∈ choicesF q.2 cur := by
          unfold choicesF
          have hsl : Y ∈ (q.2.filter fun x => decide (x ∉ cur)).sublists :=
            List.mem_sublists.2 List.filter_sublist
          split
          · exact hsl
          · next ha =>
            refine List.mem_filter.2 ⟨hsl, ?_⟩
            obtain ⟨b, hb, hbT⟩ := hT _ _ hcl (fun a ha => hcT (hbody a ha))
            have hbc : b ∉ cur := fun hbc => ha (List.any_eq_true.2 ⟨b, hb, decide_eq_true hbc⟩)
            have : b ∈ Y := (hYm b).2 ⟨hb, hbc, hbT⟩
            cases hYe : Y with
            | nil => rw [hYe] at this; simp at this
            | cons _ _ => rfl
        refine List.mem_flatMap.2 ⟨Y, hY, ihf _ _ _ (hσc.trans Finset.subset_union_left)
          (Finset.union_subset hcg ?_) ?_ (hQ.fire Y)⟩
        · intro x hx
          obtain ⟨hxh, -, hxT⟩ := (hYm x).1 (List.mem_toFinset.1 hx)
          exact guided_closed hcl (fun a ha => hcg (hbody a ha))
            (Finset.mem_inter.2 ⟨List.mem_toFinset.2 hxh, hxT⟩)
        · intro j hj q' hq' x hx
          rcases List.mem_cons.1 hj with rfl | hj
          · rw [hq] at hq'
            cases hq'
            obtain ⟨hxh, hxT⟩ := Finset.mem_inter.1 hx
            by_cases hxc : x ∈ cur
            · exact Finset.mem_union_left _ hxc
            · exact Finset.mem_union_right _
                (List.mem_toFinset.2 ((hYm x).2 ⟨List.mem_toFinset.1 hxh, hxc, hxT⟩))
          · exact Finset.mem_union_left _ (hD j hj q' hq' hx)

theorem QInv.init (σ : Ty n) :
    QInv O σ [] ((mkIx O).gciTop ++ (toL σ).flatMap (mkIx O).gciBy.get) := by
  intro j q hq _ hb
  cases hq1 : q.1 with
  | nil => exact List.mem_append_left _ (mem_gciTop.2 ⟨q, hq, hq1⟩)
  | cons x xs =>
    have hx : x ∈ q.1 := by rw [hq1]; exact List.mem_cons_self ..
    exact List.mem_append_right _
      (List.mem_flatMap.2 ⟨x, mem_toL.2 (hb x hx), mem_gciBy.2 ⟨q, hq, hx⟩⟩)

/-- Every type `fbAux` returns holds the seed. -/
theorem fbAux_sup {ix : Ix n m} {σ : Ty n} : ∀ (fuel : Nat) (cur : Ty n) (done queue : List Nat)
    (t : Ty n), t ∈ fbAux O ix σ fuel cur done queue → σ ⊆ cur → σ ⊆ t := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur done queue
    induction queue with
    | nil =>
      intro t ht hσ
      rw [fbAux, List.mem_singleton] at ht
      subst ht
      exact hσ
    | cons i rest ih =>
      intro t ht hσ
      rw [fbAux] at ht
      split at ht
      · exact ih t ht hσ
      · exact (branches_closed ht).2
  | succ f ihf =>
    intro cur done queue
    induction queue with
    | nil =>
      intro t ht hσ
      rw [fbAux, List.mem_singleton] at ht
      subst ht
      exact hσ
    | cons i rest ih =>
      intro t ht hσ
      rw [fbAux] at ht
      split at ht
      · exact ih t ht hσ
      · obtain ⟨Y, -, ht⟩ := List.mem_flatMap.1 ht
        exact ihf _ _ _ t ht (hσ.trans Finset.subset_union_left)

/-! ### The hash-set version of `fbAux` -/

theorem Cur.contains_eq (c : Cur n) (x : Fin n) : c.h.contains x = decide (x ∈ c.ty) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Cur.ty, ofL_eq, List.mem_toFinset, c.ok,
    Std.HashSet.mem_iff_contains]

theorem Cur.ofTy_ty (σ : Ty n) : (Cur.ofTy σ).ty = σ := by
  ext x
  simp only [Cur.ty, Cur.ofTy, ofL_eq, List.mem_toFinset, mem_toL]

theorem Cur.add_ty (c : Cur n) (y : Fin n) : (c.add y).ty = insert y c.ty := by
  ext x
  simp only [Cur.ty, Cur.add, ofL_eq, List.mem_toFinset, List.mem_cons, Finset.mem_insert]

theorem Cur.addAll_ty : ∀ (Y : List (Fin n)) (c : Cur n), (c.addAll Y).ty = c.ty ∪ Y.toFinset
  | [], c => by simp [Cur.addAll]
  | y :: Y, c => by
    show ((c.add y).addAll Y).ty = _
    rw [Cur.addAll_ty Y, Cur.add_ty]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.toFinset_cons]
    tauto

theorem fireableH_eq (ix : Ix n m) (c : Cur n) {dh : Std.HashSet Nat} {dl : List Nat}
    (hd : ∀ j, j ∈ dh ↔ j ∈ dl) (i : Nat) : fireableH ix c dh i = fireable ix c.ty dl i := by
  have h1 : dh.contains i = decide (i ∈ dl) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hd, Std.HashSet.mem_iff_contains]
  unfold fireableH fireable
  simp only [Cur.contains_eq, h1, decide_not]

theorem choicesH_eq (head : List (Fin n)) (c : Cur n) : choicesH head c = choicesF head c.ty := by
  unfold choicesH choicesF
  simp only [Cur.contains_eq, decide_not]

theorem fbAuxH_eq {ix : Ix n m} {σ : Ty n} : ∀ (fuel : Nat) (c : Cur n) (dh : Std.HashSet Nat)
    (dl queue : List Nat), (∀ j, j ∈ dh ↔ j ∈ dl) →
    fbAuxH O ix σ fuel c dh queue = fbAux O ix σ fuel c.ty dl queue := by
  intro fuel
  induction fuel with
  | zero =>
    intro c dh dl queue hd
    induction queue with
    | nil => rw [fbAuxH, fbAux]
    | cons i rest ih =>
      rw [fbAuxH, fbAux, fireableH_eq ix c hd]
      cases fireable ix c.ty dl i with
      | none => exact ih
      | some q => rfl
  | succ f ihf =>
    intro c dh dl queue hd
    induction queue with
    | nil => rw [fbAuxH, fbAux]
    | cons i rest ih =>
      rw [fbAuxH, fbAux, fireableH_eq ix c hd]
      cases fireable ix c.ty dl i with
      | none => exact ih
      | some q =>
        dsimp only
        rw [choicesH_eq]
        congr 1
        funext Y
        rw [ihf (c.addAll Y) (dh.insert i) (i :: dl) _ ?_, Cur.addAll_ty]
        intro j
        rw [Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq, hd]
        exact or_congr eq_comm Iff.rfl

theorem branchesF_eq (ix : Ix n m) (σ : Ty n) : branchesF O ix σ =
    fbAux O ix σ (ix.gciArr.size + 1) σ [] (ix.gciTop ++ (toL σ).flatMap ix.gciBy.get) := by
  rw [branchesF, fbAuxH_eq _ _ _ [] _ (fun j => by simp), Cur.ofTy_ty]

theorem branchesF_sup {ix : Ix n m} {σ t : Ty n} (h : t ∈ branchesF O ix σ) : σ ⊆ t := by
  rw [branchesF_eq] at h
  exact fbAux_sup _ _ _ _ t h (Finset.Subset.refl _)

theorem branchesF_closed {σ t : Ty n} (h : t ∈ branchesF O (mkIx O) σ) : Closed O t := by
  rw [branchesF_eq] at h
  exact fbAux_closed _ _ _ _ t h (by simp) (QInv.init σ)

theorem mem_branchesF {σ t : Ty n} (h : t ∈ branches O σ) : t ∈ branchesF O (mkIx O) σ := by
  obtain ⟨hc, hσ⟩ := branches_closed h
  have := fbAux_guided hc hσ ((mkIx O).gciArr.size + 1) σ [] _ (Finset.Subset.refl _)
    subset_guided (by simp) (QInv.init σ)
  rw [guided_of_mem_branches h] at this
  rw [branchesF_eq]
  exact this

/-! ## Proofs: the saturation -/

/-- The child rule holds at `x` for the records satisfying `P`. -/
def ChildOK (O : Ontology (Fin n) (Fin m)) (P : Rec n → Prop) (x : Rec n) : Prop :=
  ∀ a R b, (a, R, b) ∈ demands O x.t → ∀ s ∈ branches O (insert b (fwd O x.t R)),
    P ⟨insert b (fwd O x.t R), ∅, s⟩

/-- The augment rule holds for the parent `x` and the child `y`. -/
def AugOK (O : Ontology (Fin n) (Fin m)) (P : Rec n → Prop) (x y : Rec n) : Prop :=
  ∀ a R b, (a, R, b) ∈ demands O x.t → b ∈ y.K → y.K ⊆ insert b (fwd O x.t R) →
    ∀ t' ∈ branches O (x.K ∪ (x.A ∪ back O y.t R)), P ⟨x.K, x.A ∪ back O y.t R, t'⟩

theorem ChildOK.mono {P P' : Rec n → Prop} (h : ∀ x, P x → P' x) {x : Rec n}
    (hx : ChildOK O P x) : ChildOK O P' x :=
  fun a R b hd s hs => h _ (hx a R b hd s hs)

theorem AugOK.mono {P P' : Rec n → Prop} (h : ∀ x, P x → P' x) {x y : Rec n}
    (hx : AugOK O P x y) : AugOK O P' x y :=
  fun a R b hd hb hK t' ht' => h _ (hx a R b hd hb hK t' ht')

/-- The context index covers the seen records. -/
def KI (st : St n m) : Prop := ∀ y ∈ st.seen, ∀ b ∈ y.K, y ∈ st.kidx.get b

/-- The demand index covers the demands of the seen records. -/
def FI (O : Ontology (Fin n) (Fin m)) (st : St n m) : Prop :=
  ∀ y ∈ st.seen, ∀ a R b, (a, R, b) ∈ demands O y.t →
    (y, R, insert b (fwd O y.t R)) ∈ st.fidx.get b

/-- Every record of a done seed is seen. -/
def SI (O : Ontology (Fin n) (Fin m)) (st : St n m) : Prop :=
  ∀ K A : Ty n, (toL K, toL A) ∈ st.seeds → ∀ t ∈ branches O (K ∪ A), (⟨K, A, t⟩ : Rec n) ∈ st.seen

/-- `st'` extends `st`: it keeps the seen records, its new seen records
have closed types that hold their context, and its queue is the queue of
`st` with the new records. -/
structure Ext (O : Ontology (Fin n) (Fin m)) (st st' : St n m) : Prop where
  mono : ∀ z ∈ st.seen, z ∈ st'.seen
  new : ∀ z ∈ st'.seen, z ∈ st.seen ∨ (Closed O z.t ∧ z.K ⊆ z.t)
  todo : ∀ z, z ∈ st'.todo ↔ z ∈ st.todo ∨ (z ∈ st'.seen ∧ z ∉ st.seen)

theorem Ext.refl (st : St n m) : Ext O st st :=
  ⟨fun _ h => h, fun _ h => Or.inl h, fun z => by tauto⟩

theorem Ext.trans {st0 st1 st2 : St n m} (h1 : Ext O st0 st1) (h2 : Ext O st1 st2) :
    Ext O st0 st2 where
  mono z hz := h2.mono z (h1.mono z hz)
  new z hz := (h2.new z hz).elim (fun h => h1.new z h) Or.inr
  todo z := by
    rw [h2.todo, h1.todo]
    have m1 := h1.mono z
    have m2 := h2.mono z
    tauto

theorem addRec_seen {ix : Ix n m} {st : St n m} {x z : Rec n} :
    z ∈ (addRec ix st x).seen ↔ z = x ∨ z ∈ st.seen := by
  unfold addRec
  split
  · next h =>
    have hx := Std.HashSet.mem_iff_contains.2 h
    constructor
    · exact Or.inr
    · rintro (rfl | h); exacts [hx, h]
  · simp only [Std.HashSet.mem_insert, beq_iff_eq]
    constructor <;> rintro (h | h) <;> first | exact Or.inl h.symm | exact Or.inr h

theorem addRec_todo {ix : Ix n m} {st : St n m} {x z : Rec n} :
    z ∈ (addRec ix st x).todo ↔ z ∈ st.todo ∨ (z = x ∧ x ∉ st.seen) := by
  unfold addRec
  split
  · next h =>
    have hx := Std.HashSet.mem_iff_contains.2 h
    constructor
    · exact Or.inl
    · rintro (h | ⟨-, h⟩); exacts [h, absurd hx h]
  · next h =>
    have hx : x ∉ st.seen := fun hx => h (Std.HashSet.mem_iff_contains.1 hx)
    simp only [List.mem_cons]
    constructor
    · rintro (h | h); exacts [Or.inr ⟨h, hx⟩, Or.inl h]
    · rintro (h | ⟨h, -⟩); exacts [Or.inr h, Or.inl h]

theorem addRec_seeds {ix : Ix n m} {st : St n m} {x : Rec n} :
    (addRec ix st x).seeds = st.seeds := by
  unfold addRec; split <;> rfl

theorem addRec_ext {ix : Ix n m} {st : St n m} {x : Rec n} (hx : Closed O x.t ∧ x.K ⊆ x.t) :
    Ext O st (addRec ix st x) where
  mono z hz := addRec_seen.2 (Or.inr hz)
  new z hz := (addRec_seen.1 hz).elim (fun h => Or.inr (h ▸ hx)) Or.inl
  todo z := by
    rw [addRec_todo, addRec_seen]
    by_cases hz : z = x
    · subst hz; tauto
    · simp only [hz, false_and, false_or, or_false]
      tauto

theorem addRec_kidx {ix : Ix n m} {st : St n m} {x : Rec n} (h : KI st) :
    KI (addRec ix st x) := by
  intro y hy b hb
  unfold addRec at hy ⊢
  split
  · next hc => rw [if_pos hc] at hy; exact h y hy b hb
  · next hc =>
    rw [if_neg hc] at hy
    simp only [Std.HashSet.mem_insert, beq_iff_eq] at hy
    rw [Idx.mem_foldl_add (fun b => b) (fun _ => x)]
    rcases hy with rfl | hy
    · exact Or.inr ⟨b, mem_toL.2 hb, rfl, rfl⟩
    · exact Or.inl (h y hy b hb)

theorem addRec_fidx {st : St n m} {x : Rec n} (h : FI O st) : FI O (addRec (mkIx O) st x) := by
  intro y hy a R b hd
  unfold addRec at hy ⊢
  split
  · next hc => rw [if_pos hc] at hy; exact h y hy a R b hd
  · next hc =>
    rw [if_neg hc] at hy
    simp only [Std.HashSet.mem_insert, beq_iff_eq] at hy
    dsimp only
    rw [Idx.mem_foldl_add (fun d : Fin n × RT m × Fin n => d.2.2)
      (fun d : Fin n × RT m × Fin n => (x, d.2.1, ins d.2.2 (fwdF (mkIx O) x.t d.2.1)))]
    rcases hy with rfl | hy
    · exact Or.inr ⟨(a, R, b), mem_demF.2 hd, rfl, by rw [ins_eq, fwdF_eq]⟩
    · exact Or.inl (h y hy a R b hd)

theorem foldl_seen {ix : Ix n m} {z : Rec n} :
    ∀ (L : List (Rec n)) (st : St n m),
      z ∈ (L.foldl (addRec ix) st).seen ↔ z ∈ L ∨ z ∈ st.seen
  | [], st => by simp
  | x :: L, st => by
    rw [List.foldl_cons, foldl_seen L, addRec_seen, List.mem_cons]
    tauto

/-- The invariants `addRec` keeps, over a list of records. -/
theorem foldl_addRec {L : List (Rec n)} (hL : ∀ x ∈ L, Closed O x.t ∧ x.K ⊆ x.t) :
    ∀ (st : St n m), KI st → FI O st →
      let st' := L.foldl (addRec (mkIx O)) st
      Ext O st st' ∧ KI st' ∧ FI O st' ∧ st'.seeds = st.seeds := by
  induction L with
  | nil => intro st hk hf; exact ⟨Ext.refl st, hk, hf, rfl⟩
  | cons x L ih =>
    intro st hk hf
    obtain ⟨he, hk', hf', hsd⟩ := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
      (addRec (mkIx O) st x) (addRec_kidx hk) (addRec_fidx hf)
    exact ⟨(addRec_ext (hL x (List.mem_cons_self ..))).trans he, hk', hf',
      hsd.trans addRec_seeds⟩

/-- The invariants `addSeed` keeps; afterwards the seed is done, and the
seeds done before stay done. -/
theorem addSeed_spec (st : St n m) (s : Ty n × Ty n) (hk : KI st) (hf : FI O st)
    (hs : SI O st) :
    let st' := addSeed O (mkIx O) st s
    Ext O st st' ∧ KI st' ∧ FI O st' ∧ SI O st' ∧ (toL s.1, toL s.2) ∈ st'.seeds ∧
      ∀ k ∈ st.seeds, k ∈ st'.seeds := by
  unfold addSeed
  split
  · next hc => exact ⟨Ext.refl st, hk, hf, hs, Std.HashSet.mem_iff_contains.2 hc, fun _ h => h⟩
  · set st1 : St n m := { st with seeds := st.seeds.insert (toL s.1, toL s.2) }
    set L := (branchesF O (mkIx O) (uni s.1 s.2)).map fun t => (⟨s.1, s.2, t⟩ : Rec n)
    have hL : ∀ x ∈ L, Closed O x.t ∧ x.K ⊆ x.t := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      refine ⟨branchesF_closed ht, ?_⟩
      have := branchesF_sup ht
      rw [uni_eq] at this
      exact Finset.subset_union_left.trans this
    -- the seeds invariant of `st1` holds after adding the records of `L`
    have hs1 : ∀ K A : Ty n, (toL K, toL A) ∈ st1.seeds → ∀ t ∈ branches O (K ∪ A),
        (⟨K, A, t⟩ : Rec n) ∈ (L.foldl (addRec (mkIx O)) st1).seen := by
      intro K A hka t ht
      rw [foldl_seen]
      rcases Std.HashSet.mem_insert.1 hka with he | hka
      · obtain ⟨h1, h2⟩ := Prod.mk.inj (beq_iff_eq.1 he)
        obtain rfl := toL_inj h1
        obtain rfl := toL_inj h2
        refine Or.inl (List.mem_map.2 ⟨t, ?_, rfl⟩)
        rw [uni_eq]
        exact mem_branchesF ht
      · exact Or.inr (hs K A hka t ht)
    obtain ⟨he, hk', hf', hsd⟩ := foldl_addRec hL st1 hk hf
    have h01 : Ext O st st1 :=
      ⟨fun _ h => h, fun _ h => Or.inl h, fun _ => ⟨Or.inl, fun h => h.elim id fun h => absurd h.1 h.2⟩⟩
    refine ⟨h01.trans he, hk', hf', fun K A hka => hs1 K A (hsd ▸ hka),
      hsd ▸ Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true _)),
      fun k hk => hsd ▸ Std.HashSet.mem_insert.2 (Or.inr hk)⟩

theorem foldl_addSeed (L : List (Ty n × Ty n)) :
    ∀ (st : St n m), KI st → FI O st → SI O st →
      let st' := L.foldl (addSeed O (mkIx O)) st
      Ext O st st' ∧ KI st' ∧ FI O st' ∧ SI O st' ∧
        ∀ s ∈ L, ∀ t ∈ branches O (s.1 ∪ s.2), (⟨s.1, s.2, t⟩ : Rec n) ∈ st'.seen := by
  induction L with
  | nil => intro st hk hf hs; exact ⟨Ext.refl st, hk, hf, hs, by simp⟩
  | cons x L ih =>
    intro st hk hf hs
    obtain ⟨he1, hk1, hf1, hs1, hx1, -⟩ := addSeed_spec st x hk hf hs
    obtain ⟨he, hk', hf', hs', hL⟩ := ih _ hk1 hf1 hs1
    refine ⟨he1.trans he, hk', hf', hs', fun s hs t ht => ?_⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact he.mono _ (hs1 _ _ hx1 t ht)
    · exact hL s hs t ht

theorem seedsOf_child {st : St n m} {r : Rec n} {a b : Fin n} {R : RT m}
    (hd : (a, R, b) ∈ demands O r.t) :
    (insert b (fwd O r.t R), (∅ : Ty n)) ∈ seedsOf (mkIx O) st r := by
  simp only [seedsOf, List.mem_append, List.mem_map, List.mem_flatMap]
  refine Or.inl (Or.inl ⟨((a, R, b), ins b (fwdF (mkIx O) r.t R)),
    ⟨(a, R, b), mem_demF.2 hd, rfl⟩, by rw [ins_eq, fwdF_eq]⟩)

theorem seedsOf_augP {st : St n m} {r w : Rec n} (hk : KI st) (hw : w ∈ st.seen)
    {a b : Fin n} {R : RT m} (hd : (a, R, b) ∈ demands O r.t) (hb : b ∈ w.K)
    (hK : w.K ⊆ insert b (fwd O r.t R)) :
    (r.K, r.A ∪ back O w.t R) ∈ seedsOf (mkIx O) st r := by
  simp only [seedsOf, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter]
  refine Or.inl (Or.inr ⟨((a, R, b), ins b (fwdF (mkIx O) r.t R)),
    ⟨(a, R, b), mem_demF.2 hd, rfl⟩, w, ⟨hk w hw b hb, ?_⟩, by rw [uni_eq, backF_eq]⟩)
  rw [sub_eq, ins_eq, fwdF_eq]
  exact decide_eq_true hK

theorem seedsOf_augC {st : St n m} {r z : Rec n} (hf : FI O st) (hz : z ∈ st.seen)
    {a b : Fin n} {R : RT m} (hd : (a, R, b) ∈ demands O z.t) (hb : b ∈ r.K)
    (hK : r.K ⊆ insert b (fwd O z.t R)) :
    (z.K, z.A ∪ back O r.t R) ∈ seedsOf (mkIx O) st r := by
  simp only [seedsOf, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter]
  refine Or.inr ⟨b, mem_toL.2 hb, (z, R, insert b (fwd O z.t R)), ⟨hf z hz a R b hd, ?_⟩,
    by rw [uni_eq, backF_eq]⟩
  rw [sub_eq]
  exact decide_eq_true hK

/-- The loop invariant: the indexes cover the seen records, every record
of a done seed is seen, and every seen record that is not queued
satisfies the rules, alone and in pairs with the other such records. -/
structure Inv (O : Ontology (Fin n) (Fin m)) (req : List (Fin n)) (st : St n m) : Prop where
  closed : ∀ x ∈ st.seen, Closed O x.t
  ksub : ∀ x ∈ st.seen, x.K ⊆ x.t
  todo : ∀ x ∈ st.todo, x ∈ st.seen
  kidx : KI st
  fidx : FI O st
  seeds : SI O st
  child : ∀ x ∈ st.seen, x ∉ st.todo → ChildOK O (· ∈ st.seen) x
  aug : ∀ x ∈ st.seen, ∀ y ∈ st.seen, x ∉ st.todo → y ∉ st.todo → AugOK O (· ∈ st.seen) x y
  root : ∀ a ∈ req, ∀ t ∈ branches O {a}, (⟨{a}, ∅, t⟩ : Rec n) ∈ st.seen

/-- One step of the loop keeps the invariant. -/
theorem Inv.step {req : List (Fin n)} {st : St n m} (hI : Inv O req st) {r : Rec n}
    {rest : List (Rec n)} (h : st.todo = r :: rest) :
    Inv O req ((seedsOf (mkIx O) st r).foldl (addSeed O (mkIx O)) { st with todo := rest }) := by
  set L := seedsOf (mkIx O) st r
  set st1 : St n m := { st with todo := rest }
  set st2 := L.foldl (addSeed O (mkIx O)) st1
  obtain ⟨he, hk2, hf2, hs2, hcov⟩ := foldl_addSeed (O := O) L st1 hI.kidx hI.fidx hI.seeds
  have hmono : ∀ z, z ∈ st.seen → z ∈ st2.seen := fun z hz => he.mono z hz
  have hdone : ∀ z, z ∈ st2.seen → z ∉ st2.todo → z ∈ st.seen ∧ z ∉ rest := by
    intro z hz hnt
    rw [he.todo] at hnt
    simp only [st1, not_or, not_and, not_not] at hnt
    exact ⟨hnt.2 hz, hnt.1⟩
  have hold : ∀ z, z ∉ rest → z ≠ r → z ∉ st.todo := by
    intro z h1 h2 h3
    rw [h] at h3
    rcases List.mem_cons.1 h3 with h3 | h3
    · exact h2 h3
    · exact h1 h3
  refine ⟨?_, ?_, ?_, hk2, hf2, hs2, ?_, ?_, ?_⟩
  · intro z hz
    rcases he.new z hz with hz | hz
    · exact hI.closed z hz
    · exact hz.1
  · intro z hz
    rcases he.new z hz with hz | hz
    · exact hI.ksub z hz
    · exact hz.2
  · intro z hz
    rcases (he.todo z).1 hz with hz | ⟨hz, -⟩
    · exact hmono z (hI.todo z (by rw [h]; exact List.mem_cons_of_mem _ hz))
    · exact hz
  · intro z hz hnt
    obtain ⟨hzs, hzr⟩ := hdone z hz hnt
    by_cases hzr' : z = r
    · subst hzr'
      intro a R b hd s hs
      have := hcov _ (seedsOf_child hd) s (by rw [Finset.union_empty]; exact hs)
      exact this
    · exact (hI.child z hzs (hold z hzr hzr')).mono hmono
  · intro z hz w hw hzt hwt
    obtain ⟨hzs, hzr⟩ := hdone z hz hzt
    obtain ⟨hws, hwr⟩ := hdone w hw hwt
    by_cases hz' : z = r
    · subst hz'
      exact fun a R b hd hb hK t' ht' => hcov _ (seedsOf_augP hI.kidx hws hd hb hK) t' ht'
    · by_cases hw' : w = r
      · subst hw'
        exact fun a R b hd hb hK t' ht' => hcov _ (seedsOf_augC hI.fidx hzs hd hb hK) t' ht'
      · exact (hI.aug z hzs w hws (hold z hzr hz') (hold w hwr hw')).mono hmono
  · exact fun a ha t ht => hmono _ (hI.root a ha t ht)

theorem loop_spec {req : List (Fin n)} :
    ∀ st : St n m, Inv O req st →
      Inv O req (loop O (mkIx O) st) ∧ (loop O (mkIx O) st).todo = [] := by
  intro st
  induction hm : st.measure using Nat.strong_induction_on generalizing st with
  | _ k ih =>
    intro hI
    rw [loop]
    split
    · next h => exact ⟨hI, h⟩
    · next r rest h =>
      refine ih _ ?_ _ rfl (hI.step h)
      rw [← hm]
      refine Nat.lt_of_le_of_lt (foldl_addSeed_measure _ _ _ _) ?_
      simp only [St.measure, h, List.length_cons]
      omega

theorem Inv.init (req : List (Fin n)) :
    Inv O req ((roots req).foldl (addSeed O (mkIx O)) St.empty) := by
  have he0 : ∀ z : Rec n, z ∉ (St.empty : St n m).seen := fun z => Std.HashSet.not_mem_empty
  obtain ⟨he, hk, hf, hs, hcov⟩ := foldl_addSeed (O := O) (roots req) (St.empty : St n m)
    (fun z hz => absurd hz (he0 z)) (fun z hz => absurd hz (he0 z))
    (fun K A hka => absurd hka Std.HashSet.not_mem_empty)
  have hnew : ∀ z ∈ ((roots req).foldl (addSeed O (mkIx O)) (St.empty : St n m)).seen,
      Closed O z.t ∧ z.K ⊆ z.t := fun z hz => (he.new z hz).resolve_left (he0 z)
  have htodo : ∀ z ∈ ((roots req).foldl (addSeed O (mkIx O)) (St.empty : St n m)).seen,
      z ∈ ((roots req).foldl (addSeed O (mkIx O)) (St.empty : St n m)).todo :=
    fun z hz => (he.todo z).2 (Or.inr ⟨hz, he0 z⟩)
  refine ⟨fun z hz => (hnew z hz).1, fun z hz => (hnew z hz).2, ?_, hk, hf, hs,
    fun z hz hnt => absurd (htodo z hz) hnt, fun z hz _ _ hnt _ => absurd (htodo z hz) hnt, ?_⟩
  · intro z hz
    rcases (he.todo z).1 hz with hz | ⟨hz, -⟩
    · exact absurd hz (List.not_mem_nil)
    · exact hz
  · intro a ha t ht
    refine hcov (({a} : Ty n), (∅ : Ty n)) (List.mem_map.2 ⟨a, ha, rfl⟩) t ?_
    rw [Finset.union_empty]; exact ht

theorem mem_candidates {req : List (Fin n)} {r : Rec n} :
    r ∈ candidates O (mkIx O) req ↔
      r ∈ (loop O (mkIx O) ((roots req).foldl (addSeed O (mkIx O)) St.empty)).seen :=
  Std.HashSet.mem_toList

/-- The candidate set is closed under the rules. -/
theorem candidates_rulesClosed (req : List (Fin n)) :
    RulesClosed O req (candidates O (mkIx O) req).toFinset := by
  obtain ⟨hI, hnil⟩ := loop_spec _ (Inv.init (O := O) req)
  have hm : ∀ r, r ∈ (candidates O (mkIx O) req).toFinset ↔
      r ∈ (loop O (mkIx O) ((roots req).foldl (addSeed O (mkIx O)) St.empty)).seen :=
    fun r => List.mem_toFinset.trans mem_candidates
  have hnt : ∀ r : Rec n, r ∉ (loop O (mkIx O)
      ((roots req).foldl (addSeed O (mkIx O)) St.empty)).todo := by
    intro r; rw [hnil]; exact List.not_mem_nil
  refine ⟨fun a ha t ht => (hm _).2 (hI.root a ha t ht), ?_, ?_, ?_⟩
  · intro r hr a R b hd s hs
    exact (hm _).2 (hI.child r ((hm r).1 hr) (hnt r) a R b hd s hs)
  · intro r hr r' hr' a R b hd hb hK t' ht'
    exact (hm _).2 (hI.aug r ((hm r).1 hr) r' ((hm r').1 hr') (hnt r) (hnt r') a R b hd hb hK
      t' ht')
  · intro r hr
    exact hI.closed r ((hm r).1 hr)

/-- The candidate records hold their context. -/
theorem candidates_ksub (req : List (Fin n)) :
    ∀ r ∈ (candidates O (mkIx O) req).toFinset, r.K ⊆ r.t := by
  obtain ⟨hI, -⟩ := loop_spec _ (Inv.init (O := O) req)
  intro r hr
  exact hI.ksub r (mem_candidates.1 (List.mem_toFinset.1 hr))

/-! ## Proofs: elimination -/

theorem mem_typeIdx {G : List (Rec n)} {b : Fin n} {r : Rec n} :
    r ∈ (typeIdx G).get b ↔ r ∈ G ∧ b ∈ r.t := by
  simp only [typeIdx, Idx.mem_ofList, List.mem_flatMap, List.mem_map, Prod.mk.injEq, mem_toL]
  constructor
  · rintro ⟨r', hr', b', hb', rfl, rfl⟩; exact ⟨hr', hb'⟩
  · rintro ⟨hr, hb⟩; exact ⟨r, hr, b, hb, rfl, rfl⟩

/-- The precomputed supports decide witnessing inside any subset of `G`. -/
theorem okIn_iff {G : List (Rec n)} {E : Std.HashSet (Rec n)} (hE : ∀ r', r' ∈ E → r' ∈ G)
    (r : Rec n) :
    okIn E (supports (mkIx O) (typeIdx G) r) = true ↔
      ∀ d ∈ demands O r.t, ∃ r', r' ∈ E ∧ d.2.2 ∈ r'.t ∧ fwd O r.t d.2.1 ⊆ r'.t ∧
        back O r'.t d.2.1 ⊆ r.t := by
  simp only [okIn, supports, List.all_map, List.all_eq_true, Function.comp_apply,
    List.any_eq_true, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, mem_typeIdx,
    fwdF_eq, backF_eq, Std.HashSet.contains_iff_mem]
  constructor
  · intro h d hd
    obtain ⟨r', ⟨⟨-, hb⟩, hf, hbk⟩, hrE⟩ := h d (mem_demF.2 hd)
    exact ⟨r', hrE, hb, hf, hbk⟩
  · intro h d hd
    obtain ⟨r', hrE, hb, hf, hbk⟩ := h d (mem_demF.1 hd)
    exact ⟨r', ⟨⟨hE r' hrE, hb⟩, hf, hbk⟩, hrE⟩

theorem mem_ofList_iff {L : List (Rec n)} {r : Rec n} : r ∈ Std.HashSet.ofList L ↔ r ∈ L := by
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem]

theorem elimLoop_spec {G : List (Rec n)} :
    ∀ L : List (Rec n × List (List (Rec n))),
      (∀ p ∈ L, p.1 ∈ G ∧ p.2 = supports (mkIx O) (typeIdx G) p.1) →
      (∀ S : Finset (Rec n), (∀ r ∈ S, r ∈ G) → (∀ r ∈ S, witnessed O S r) →
        ∀ r ∈ S, r ∈ L.map Prod.fst) →
      (∀ p ∈ elimLoop L, p.1 ∈ G ∧ p.2 = supports (mkIx O) (typeIdx G) p.1) ∧
      (∀ p ∈ elimLoop L, okIn (Std.HashSet.ofList ((elimLoop L).map Prod.fst)) p.2 = true) ∧
      (∀ S : Finset (Rec n), (∀ r ∈ S, r ∈ G) → (∀ r ∈ S, witnessed O S r) →
        ∀ r ∈ S, r ∈ (elimLoop L).map Prod.fst) := by
  intro L
  induction hl : L.length using Nat.strong_induction_on generalizing L with
  | _ k ih =>
    intro hP hS
    rw [elimLoop]
    split
    · next h =>
      refine ih _ (hl ▸ h) _ rfl (fun p hp => hP p (List.mem_of_mem_filter hp)) ?_
      intro S hSG hw r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hS S hSG hw r hr)
      refine List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, ?_⟩, rfl⟩
      have hE : ∀ r', r' ∈ Std.HashSet.ofList (L.map Prod.fst) → r' ∈ G := by
        intro r' hr'
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 (mem_ofList_iff.1 hr')
        exact (hP p' hp').1
      rw [(hP p hp).2, okIn_iff hE]
      intro d hd
      obtain ⟨r', hr', h1, h2, h3⟩ := hw p.1 hr d hd
      exact ⟨r', mem_ofList_iff.2 (hS S hSG hw r' hr'), h1, h2, h3⟩
    · next h =>
      refine ⟨hP, fun p hp => ?_, hS⟩
      by_contra hne
      exact h (List.length_filter_lt_length_iff_exists.2 ⟨p, hp, by simpa using hne⟩)

theorem elimF_isElim (G : List (Rec n)) : IsElim O G.toFinset (elimF (mkIx O) G).toFinset := by
  have hspec := elimLoop_spec (O := O) (G := G)
    (G.map fun r => (r, supports (mkIx O) (typeIdx G) r))
    (fun p hp => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
      exact ⟨hr, rfl⟩)
    (fun S hSG _ r hr => by
      rw [List.map_map]
      exact List.mem_map.2 ⟨r, hSG r hr, rfl⟩)
  obtain ⟨hP, hok, hgr⟩ := hspec
  have hmem : ∀ r, r ∈ (elimF (mkIx O) G).toFinset ↔ ∃ p ∈ elimLoop (G.map fun r =>
      (r, supports (mkIx O) (typeIdx G) r)), p.1 = r := by
    intro r
    simp only [elimF, List.mem_toFinset, List.mem_map]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := (hmem r).1 hr
    exact List.mem_toFinset.2 (hP p hp).1
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := (hmem r).1 hr
    have hE : ∀ r', r' ∈ Std.HashSet.ofList ((elimLoop (G.map fun r =>
        (r, supports (mkIx O) (typeIdx G) r))).map Prod.fst) → r' ∈ G := by
      intro r' hr'
      obtain ⟨p', hp', rfl⟩ := List.mem_map.1 (mem_ofList_iff.1 hr')
      exact (hP p' hp').1
    have h := hok p hp
    rw [(hP p hp).2, okIn_iff hE] at h
    intro d hd
    obtain ⟨r', hr', h1, h2, h3⟩ := h d hd
    exact ⟨r', (hmem r').2 (List.mem_map.1 (mem_ofList_iff.1 hr')), h1, h2, h3⟩
  · intro S hS hw r hr
    exact (hmem r).2 (List.mem_map.1
      (hgr S (fun r hr => List.mem_toFinset.1 (hS hr)) hw r hr))

/-! ## Proofs: elimination by exact context -/

theorem mem_ctxIdx_foldl {k : List (Fin n)} {x : Rec n} :
    ∀ (G : List (Rec n)) (ix : Std.HashMap (List (Fin n)) (List (Rec n))),
      x ∈ (G.foldl (fun ix r => ix.insert (toL r.K) (r :: ix.getD (toL r.K) [])) ix).getD k [] ↔
        x ∈ ix.getD k [] ∨ (x ∈ G ∧ toL x.K = k)
  | [], ix => by simp
  | r :: G, ix => by
    rw [List.foldl_cons, mem_ctxIdx_foldl G, Std.HashMap.getD_insert]
    by_cases h : toL r.K = k
    · subst h
      simp only [beq_self_eq_true, if_true, List.mem_cons]
      constructor
      · rintro ((rfl | h) | ⟨hx, hk⟩)
        · exact Or.inr ⟨Or.inl rfl, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr hx, hk⟩
      · rintro (h | ⟨rfl | hx, hk⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨hx, hk⟩
    · have h' : (toL r.K == k) = false := by simpa using h
      simp only [h', Bool.false_eq_true, if_false, List.mem_cons]
      constructor
      · rintro (h1 | ⟨hx, hk⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨Or.inr hx, hk⟩
      · rintro (h1 | ⟨rfl | hx, hk⟩)
        · exact Or.inl h1
        · exact absurd hk h
        · exact Or.inr ⟨hx, hk⟩

theorem mem_ctxIdx {G : List (Rec n)} {K : Ty n} {x : Rec n} :
    x ∈ (ctxIdx G).getD (toL K) [] ↔ x ∈ G ∧ x.K = K := by
  unfold ctxIdx
  rw [mem_ctxIdx_foldl]
  simp only [Std.HashMap.getD_empty, List.not_mem_nil, false_or]
  exact and_congr_right fun _ => ⟨toL_inj, fun h => h ▸ rfl⟩

/-- The precomputed supports decide witnessing by exact context inside
any subset of `G`. -/
theorem okInK_iff {G : List (Rec n)} {E : Std.HashSet (Rec n)} (hE : ∀ r', r' ∈ E → r' ∈ G)
    (r : Rec n) :
    okIn E (supportsK (mkIx O) (ctxIdx G) r) = true ↔
      ∀ d ∈ demands O r.t, ∃ r', r' ∈ E ∧ r'.K = insert d.2.2 (fwd O r.t d.2.1) ∧
        back O r'.t d.2.1 ⊆ r.t := by
  simp only [okIn, supportsK, List.all_map, List.all_eq_true, Function.comp_apply,
    List.any_eq_true, List.mem_filter, sub_eq, ins_eq, decide_eq_true_eq, fwdF_eq, backF_eq, mem_ctxIdx,
    Std.HashSet.contains_iff_mem]
  constructor
  · intro h d hd
    obtain ⟨r', ⟨⟨-, hK⟩, hbk⟩, hrE⟩ := h d (mem_demF.2 hd)
    exact ⟨r', hrE, hK, hbk⟩
  · intro h d hd
    obtain ⟨r', hrE, hK, hbk⟩ := h d (mem_demF.1 hd)
    exact ⟨r', ⟨⟨hE r' hrE, hK⟩, hbk⟩, hrE⟩

theorem elimLoopK_spec {G : List (Rec n)} :
    ∀ L : List (Rec n × List (List (Rec n))),
      (∀ p ∈ L, p.1 ∈ G ∧ p.2 = supportsK (mkIx O) (ctxIdx G) p.1) →
      (∀ S : Finset (Rec n), (∀ r ∈ S, r ∈ G) → (∀ r ∈ S, witnessedK O S r) →
        ∀ r ∈ S, r ∈ L.map Prod.fst) →
      (∀ p ∈ elimLoop L, p.1 ∈ G ∧ p.2 = supportsK (mkIx O) (ctxIdx G) p.1) ∧
      (∀ p ∈ elimLoop L, okIn (Std.HashSet.ofList ((elimLoop L).map Prod.fst)) p.2 = true) ∧
      (∀ S : Finset (Rec n), (∀ r ∈ S, r ∈ G) → (∀ r ∈ S, witnessedK O S r) →
        ∀ r ∈ S, r ∈ (elimLoop L).map Prod.fst) := by
  intro L
  induction hl : L.length using Nat.strong_induction_on generalizing L with
  | _ k ih =>
    intro hP hS
    rw [elimLoop]
    split
    · next h =>
      refine ih _ (hl ▸ h) _ rfl (fun p hp => hP p (List.mem_of_mem_filter hp)) ?_
      intro S hSG hw r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hS S hSG hw r hr)
      refine List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, ?_⟩, rfl⟩
      have hE : ∀ r', r' ∈ Std.HashSet.ofList (L.map Prod.fst) → r' ∈ G := by
        intro r' hr'
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 (mem_ofList_iff.1 hr')
        exact (hP p' hp').1
      rw [(hP p hp).2, okInK_iff hE]
      intro d hd
      obtain ⟨r', hr', h1, h2⟩ := hw p.1 hr d hd
      exact ⟨r', mem_ofList_iff.2 (hS S hSG hw r' hr'), h1, h2⟩
    · next h =>
      refine ⟨hP, fun p hp => ?_, hS⟩
      by_contra hne
      exact h (List.length_filter_lt_length_iff_exists.2 ⟨p, hp, by simpa using hne⟩)

theorem elimK_isElimK (G : List (Rec n)) :
    IsElimK O G.toFinset (elimK (mkIx O) G).toFinset := by
  have hspec := elimLoopK_spec (O := O) (G := G)
    (G.map fun r => (r, supportsK (mkIx O) (ctxIdx G) r))
    (fun p hp => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
      exact ⟨hr, rfl⟩)
    (fun S hSG _ r hr => by
      rw [List.map_map]
      exact List.mem_map.2 ⟨r, hSG r hr, rfl⟩)
  obtain ⟨hP, hok, hgr⟩ := hspec
  have hmem : ∀ r, r ∈ (elimK (mkIx O) G).toFinset ↔ ∃ p ∈ elimLoop (G.map fun r =>
      (r, supportsK (mkIx O) (ctxIdx G) r)), p.1 = r := by
    intro r
    simp only [elimK, List.mem_toFinset, List.mem_map]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := (hmem r).1 hr
    exact List.mem_toFinset.2 (hP p hp).1
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := (hmem r).1 hr
    have hE : ∀ r', r' ∈ Std.HashSet.ofList ((elimLoop (G.map fun r =>
        (r, supportsK (mkIx O) (ctxIdx G) r))).map Prod.fst) → r' ∈ G := by
      intro r' hr'
      obtain ⟨p', hp', rfl⟩ := List.mem_map.1 (mem_ofList_iff.1 hr')
      exact (hP p' hp').1
    have h := hok p hp
    rw [(hP p hp).2, okInK_iff hE] at h
    intro d hd
    obtain ⟨r', hr', h1, h2⟩ := h d hd
    exact ⟨r', (hmem r').2 (List.mem_map.1 (mem_ofList_iff.1 hr')), h1, h2⟩
  · intro S hS hw r hr
    exact (hmem r).2 (List.mem_map.1
      (hgr S (fun r hr => List.mem_toFinset.1 (hS hr)) hw r hr))

/-! ## The final statements -/

theorem fastAlive_isElimK (req : List (Fin n)) :
    IsElimK O (candidates O (mkIx O) req).toFinset (fastAlive O req).toFinset :=
  elimK_isElimK _

/-- **Exactness of the fast procedure on requested names.** -/
theorem fastEntails_iff (hA : IsALCHI O) {req : List (Fin n)} {a : Fin n} (ha : a ∈ req)
    (b : Fin n) : fastEntails O req a b = true ↔ EntailsSub O a b := by
  rw [← entails_iff_ofK hA (candidates_rulesClosed req) (candidates_ksub req)
    (fastAlive_isElimK req) ha b]
  simp only [fastEntails, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, List.mem_toFinset]
  exact forall₂_congr fun _ _ => imp_iff_not_or.symm

theorem mem_foldl_inter {b : Fin n} :
    ∀ (L : List (Rec n)) (acc : Ty n),
      b ∈ L.foldl (fun acc r' => acc ∩ r'.t) acc ↔ b ∈ acc ∧ ∀ r ∈ L, b ∈ r.t
  | [], acc => by simp
  | r :: L, acc => by
    rw [List.foldl_cons, mem_foldl_inter L, Finset.mem_inter]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem mem_interAll {b : Fin n} : ∀ L : List (Rec n), b ∈ interAll L ↔ ∀ r ∈ L, b ∈ r.t
  | [] => by simp [interAll]
  | r :: L => by
    rw [interAll, mem_foldl_inter]
    simp

theorem classify_fst (req : List (Fin n)) : (classify O req).map Prod.fst = req := by
  simp [classify, List.map_map, Function.comp_def]

/-- **Classification.** Each requested name comes with exactly its
subsumers. -/
theorem classify_spec (hA : IsALCHI O) {req : List (Fin n)} :
    ∀ p ∈ classify O req, p.1 ∈ req ∧ ∀ b, b ∈ p.2 ↔ EntailsSub O p.1 b := by
  intro p hp
  simp only [classify, List.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  refine ⟨ha, fun b => ?_⟩
  rw [← entails_iff_ofK hA (candidates_rulesClosed req) (candidates_ksub req)
    (fastAlive_isElimK req) ha b]
  simp only [mem_toL, mem_interAll, mem_typeIdx, List.mem_toFinset]
  exact ⟨fun h r hr har => h r ⟨hr, har⟩, fun h r hr => h r hr.1 hr.2⟩

theorem mem_hashIdx {L : List (Rec n)} {a : Fin n} {q : Ty n × Std.HashSet (Fin n)} :
    q ∈ (hashIdx L).get a ↔ ∃ r ∈ L, a ∈ r.t ∧ q = (r.t, Std.HashSet.ofList (toL r.t)) := by
  simp only [hashIdx, Idx.mem_ofList, List.mem_flatMap, List.mem_map, Prod.mk.injEq, mem_toL]
  constructor
  · rintro ⟨r, hr, b, hb, rfl, rfl⟩; exact ⟨r, hr, hb, rfl⟩
  · rintro ⟨r, hr, hb, rfl⟩; exact ⟨r, hr, a, hb, rfl, rfl⟩

theorem mem_meetH {b : Fin n} :
    ∀ (rest : List (Ty n × Std.HashSet (Fin n))) (L : List (Fin n)),
      b ∈ meetH L rest ↔ b ∈ L ∧ ∀ q ∈ rest, q.2.contains b = true
  | [], L => by simp [meetH]
  | q :: rest, L => by
    simp only [meetH, List.foldl_cons] at *
    rw [← meetH, mem_meetH rest, List.mem_filter]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- **Classification with unsatisfiability.** Each requested name comes
with `none` exactly when it is unsatisfiable, and otherwise with exactly
its subsumers. -/
theorem classifyF_spec (hA : IsALCHI O) {req : List (Fin n)} :
    ∀ p ∈ classifyF O req, p.1 ∈ req ∧
      (p.2 = none ↔
        ∀ (D : Type) [Nonempty D] (I : Interp D (Fin n) (Fin m)), models I O → ∀ x, ¬ I.c p.1 x) ∧
      ∀ L, p.2 = some L → ∀ b, b ∈ L ↔ EntailsSub O p.1 b := by
  intro p hp
  simp only [classifyF, List.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  have hG := candidates_rulesClosed (O := O) req
  have hKt := candidates_ksub (O := O) req
  have hE := fastAlive_isElimK (O := O) req
  -- the index entries of `a` are the alive types holding `a`
  have hidx : ∀ q, q ∈ (hashIdx (fastAlive O req)).get a ↔
      ∃ r ∈ (fastAlive O req).toFinset, a ∈ r.t ∧ q = (r.t, Std.HashSet.ofList (toL r.t)) := by
    intro q
    rw [mem_hashIdx]
    simp only [List.mem_toFinset]
  refine ⟨ha, ?_, ?_⟩
  · rw [← unsat_iff_ofK hA hG hKt hE ha]
    dsimp only
    split
    · next h =>
      simp only [true_iff]
      intro r hr har
      have := (hidx _).2 ⟨r, hr, har, rfl⟩
      rw [h] at this
      exact List.not_mem_nil this
    · next q rest h =>
      simp only [reduceCtorEq, false_iff, not_forall, not_not]
      have hq : q ∈ (hashIdx (fastAlive O req)).get a := by rw [h]; exact List.mem_cons_self ..
      obtain ⟨r, hr, har, -⟩ := (hidx q).1 hq
      exact ⟨r, hr, har⟩
  · intro L hL b
    rw [← entails_iff_ofK hA hG hKt hE ha b]
    dsimp only at hL
    split at hL
    · cases hL
    · next q rest h =>
      cases hL
      have hall : ∀ q', q' ∈ q :: rest ↔ ∃ r ∈ (fastAlive O req).toFinset, a ∈ r.t ∧
          q' = (r.t, Std.HashSet.ofList (toL r.t)) := by
        intro q'; rw [← h]; exact hidx q'
      have hct : ∀ q' ∈ q :: rest, (q'.2.contains b = true ↔ b ∈ q'.1) := by
        intro q' hq'
        obtain ⟨r, -, -, rfl⟩ := (hall q').1 hq'
        simp only [Std.HashSet.contains_ofList, List.contains_iff_mem, mem_toL]
      rw [mem_meetH, mem_toL]
      constructor
      · rintro ⟨hb, hrest⟩ r hr har
        have hq' := (hall _).2 ⟨r, hr, har, rfl⟩
        rcases List.mem_cons.1 hq' with he | hm
        · rw [show r.t = q.1 from congrArg Prod.fst he]; exact hb
        · exact (hct _ (List.mem_cons_of_mem _ hm)).1 (hrest _ hm)
      · intro hb
        have hb' : ∀ q' ∈ q :: rest, b ∈ q'.1 := by
          intro q' hq'
          obtain ⟨r, hr, har, rfl⟩ := (hall q').1 hq'
          exact hb r hr har
        refine ⟨hb' q (List.mem_cons_self ..), fun q' hq' => ?_⟩
        exact (hct _ (List.mem_cons_of_mem _ hq')).2 (hb' q' (List.mem_cons_of_mem _ hq'))

end Proofs

end ContextCalculus.SRI.Proc

#print axioms ContextCalculus.SRI.Proc.candidates_rulesClosed
#print axioms ContextCalculus.SRI.Proc.candidates_ksub
#print axioms ContextCalculus.SRI.Proc.fastAlive_isElimK
#print axioms ContextCalculus.SRI.Proc.fastEntails_iff
#print axioms ContextCalculus.SRI.Proc.classify_spec
#print axioms ContextCalculus.SRI.Proc.classifyF_spec
