import ContextCalculus.SRIQN.HintFast

/-!
# Rejection reasons for a sparse hint (stage H2, diagnostic)

`explainS` reports the first core element, certificate row and condition
on which the checks of `HF.checkRedS` fail. It is a diagnostic for hint
producers (`--explain`) and is not part of any proved statement: a hint is
certified only by the proved check.
-/

namespace ContextCalculus.SRIQN.HF

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (cnt flipL)
open ContextCalculus.SRIQ.Fast (buildIdx getL rc)
open ContextCalculus.SRIQ.Proc (QNbr)

variable {n m : Nat}

def rtS : RoleT (Fin m) → String
  | .pos r => s!"+{r.val}"
  | .inv r => s!"-{r.val}"

def namesS (l : List (Fin n)) : String := " ".intercalate (l.map fun a => toString a.val)

/-- All role terms, by code. -/
def roleTs (m : Nat) : List (RoleT (Fin m)) :=
  (List.finRange (2 * m)).map fun c => SRIQ.Fast.ofRc c.val c.isLt

/-- The first failing condition of the star of a centre of type `t`; the
neighbours carry a description. -/
def starWhy (ix : SIx n m) (t : Finset (Fin n)) (N : List (String × QNbr n m)) : Option String :=
  let M := mask t
  let tl := t.sort (· ≤ ·)
  let N' := N.map (·.2)
  let gTop := ix.gTop.find? fun h => !(h.any (memM M))
  match gTop with
  | some h => some s!"gci  -> {namesS h} (empty body) has no head name in the type"
  | none =>
  let gbad := tl.findSome? fun a => ((getL ix.gBy a.val).find? fun g =>
    g.1.all (memM M) && !(g.2.any (memM M)))
  match gbad with
  | some g => some s!"gci {namesS g.1} -> {namesS g.2}: the body holds and no head name does"
  | none =>
  let ebad := N.findSome? fun (d, e) =>
    let up := (roleTs m |>.filter fun R => decide (R ∈ e.1)).findSome? fun R => ((getL ix.stepsBy (rc R)).find? fun S => decide (S ∉ e.1)).map
      fun S => s!"{d}: the label holds {rtS R} but not its super-role {rtS S}"
    match up with
    | some w => some w
    | none =>
      let f1 := tl.findSome? fun a => ((getL ix.allBy a.val).find? fun p =>
          decide (p.1 ∈ e.1) && !decide (p.2 ∈ e.2)).map
        fun p => s!"{d}: all {a.val} {rtS p.1} {p.2.val} needs {p.2.val} at the neighbour"
      match f1 with
      | some w => some w
      | none => ((e.2.sort (· ≤ ·)).findSome? fun a => ((getL ix.allBy a.val).find? fun p =>
          decide (p.1.flip ∈ e.1) && !memM M p.2).map
        fun p => s!"{d}: all {a.val} {rtS p.1} {p.2.val} at the neighbour needs {p.2.val} here")
  match ebad with
  | some w => some w
  | none =>
  let lo := tl.findSome? fun a => ((getL ix.lowBy a.val).find? fun q => !decide (q.1 ≤ cnt N' q.2.1 q.2.2)).map
    fun q => s!"atleast {a.val} {q.1} {rtS q.2.1} {q.2.2.val}: only {cnt N' q.2.1 q.2.2} neighbours"
  match lo with
  | some w => some w
  | none => tl.findSome? fun a => ((getL ix.uppBy a.val).find? fun q => !decide (cnt N' q.2.1 q.2.2 ≤ q.1)).map
    fun q => s!"atmost {a.val} {q.1} {rtS q.2.1} {q.2.2.val}: {cnt N' q.2.1 q.2.2} neighbours"

/-- **Why a sparse hint is rejected**: the first failing condition, or
`none` when the object-part checks pass (the data-star test is then the
remaining reason). `loops`: the Self route (loops only at nominal core
elements). -/
def explainS (A : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n)) (h : HintS n m) (loops : Bool) :
    Option String :=
  let ix := mkSIx A
  let nm := maskL n N
  let adj := h.adj
  let kb := h.kidIdx
  if h.k = 0 then some "the core is empty (blocks 0)" else
  let own := buildIdx n some ((List.finRange h.k).flatMap fun b =>
    ((h.tyF b).sort (· ≤ ·)).filterMap fun a => if memM nm a then some (a.val, b) else none)
  let nbad := N.findSome? fun a => match getL own a.val with
    | [] => some s!"nominal index {a.val} is at no core element"
    | b :: rest => if rest.all (· = b) then none else
        some s!"nominal index {a.val} is at core elements {" ".intercalate ((b :: rest).eraseDups.map fun c => toString c.val)}"
  match nbad with
  | some w => some w
  | none =>
  let lbad := if loops then (List.finRange h.k).find? fun c =>
      !decide (labOf (getL adj c.val) c = ∅) && !fAny (h.tyF c) (memM nm) else none
  match lbad with
  | some c => some s!"core element {c.val} has a loop and no nominal index (Self route)"
  | none =>
  let cbad := (List.finRange h.k).findSome? fun b =>
    let nb := ((merged (getL adj b.val)).filter fun e => decide (e.2 ≠ ∅)).map fun e =>
      (s!"core element {b.val}, edge to core element {e.1.val}", (e.2, h.tyF e.1))
    let kd := (getL kb b.val).zipIdx.map fun (e, i) => (s!"core element {b.val}, kid {i}", e)
    (starWhy ix (h.tyF b) (nb ++ kd)).map fun w =>
      if w.startsWith "core element" then w else s!"core element {b.val}: {w}"
  match cbad with
  | some w => some w
  | none =>
  if h.kids.isEmpty then none else
  let G := h.recs.map fun r => ((r.ty, r.par) : Proc.NRec n m h.k)
  let kbad := h.kids.find? fun e => !memB G (anchorRec e.1 e.2)
  match kbad with
  | some e => some s!"a kid of core element {e.1.val} (type {namesS (e.2.2.sort (· ≤ ·))}): its anchor record is not in the rec table"
  | none =>
  h.recs.zipIdx.findSome? fun (r, i) =>
    let w := s!"record {i}"
    if fAny r.ty (memM nm) then some s!"{w}: the type holds a nominal index" else
    let anc := match r.par with
      | .inr (c, _) => !decide (labOf r.ce c = ∅)
      | .inl _ => false
    if anc then some s!"{w}: a core entry to its own anchor" else
    match (merged r.ce).find? fun e => countedB ix (h.tyF e.1) (flipL e.2) r.ty with
    | some e => some s!"{w}: the core entry to core element {e.1.val} counts for an at-most clause there"
    | none =>
    let ces := ((merged r.ce).filter fun e => decide (e.2 ≠ ∅)).map fun e =>
      (s!"{w}, core entry {e.1.val}", (e.2, h.tyF e.1))
    let ks := r.kids.zipIdx.map fun (e, j) => (s!"{w}, kid {j}", e)
    match starWhy ix r.ty (((s!"{w}, parent", parentE h.tyF r.par)) :: ces ++ ks) with
    | some x => some (if x.startsWith "record" then x else s!"{w}: {x}")
    | none =>
      (r.kids.zipIdx.find? fun (x, _) => !memB G (childRecN r.ty x)).map fun (_, j) =>
        s!"{w}, kid {j}: its record is not in the rec table"

end ContextCalculus.SRIQN.HF
