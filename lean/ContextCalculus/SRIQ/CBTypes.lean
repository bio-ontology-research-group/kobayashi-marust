/-!
# Derivation certificates for the two-sided fast SHIQ route (stage C1f)

`docs/V1.7.0-C1F-CLOSURE.md`, section 3. A clause `⟨L, P, B, H, Q⟩`
speaks of a predecessor `y` and an element `x`: if every role (code) of
`L` holds from `y` to `x`, the names `P` hold at `y` and the names `B`
at `x`, then some name of `H` holds at `x` or some name of `Q` at `y`.
Names are naturals (the indices of `Fin n`), roles their codes
(`2 r`, `2 r + 1`). A step names its rule, the ontology clauses it uses
(by position in the ontology), its premises (by position in the
certificate, before the step) and its conclusion. The checker and its
soundness proof are in `CBCert.lean`.
-/

namespace ContextCalculus.SRIQ.CB

structure CCl where
  L : Array Nat
  P : Array Nat
  B : Array Nat
  H : Array Nat
  Q : Array Nat
deriving Inhabited, Repr, BEq

inductive CRule where
  /-- the gci at ontology position `i` -/
  | gci (i : Nat)
  | taut (p : Nat)
  /-- `allRight a S c` at position `i`, from `y` to `x` -/
  | fwd (i : Nat)
  /-- `allRight a S c` at position `i`, from `x` back to `y` -/
  | bwd (i : Nat)
  /-- a clause about one element, used at the predecessor -/
  | up (j : Nat)
  | resX (j k p : Nat)
  | resY (j k p : Nat)
  /-- the lower clause at position `i` and a clause about its witness -/
  | pred (i j : Nat)
  /-- `atMost a 0 S e` at position `i`, toward `x` or toward `y` -/
  | amo0a (i : Nat)
  | amo0b (i : Nat)
  /-- an at-most clause (`iu`), a lower clause with a larger number (`il`)
  and a clause saying that its witnesses hold the at-most filler (`je`) -/
  | clash (iu il je : Nat)
  /-- functional sibling: the counted successor is the witness of `il` -/
  | sib (iu il je jr : Nat)
  /-- functional parent: the predecessor is the witness of `il` -/
  | par (iu il je jr : Nat)
deriving Inhabited, Repr

structure CStep where
  rule : CRule
  c : CCl
deriving Inhabited

end ContextCalculus.SRIQ.CB
