import ContextCalculus.SRIQ.FastDefs
import SRIQFast.Core

/-! The candidate set of the prototype generator as the input of the
certified check (`ContextCalculus.SRIQ.Fast.closedB`). Unproved glue: the
check does not trust it. -/

namespace SRIQFast

open ContextCalculus
open ContextCalculus.SRIQ.Fast (Cand Key FNode Entry Spec ofRc)

def toTy (n : Nat) (a : Array Nat) : Finset (Fin n) :=
  (a.toList.filterMap fun x => if h : x < n then some ⟨x, h⟩ else none).toFinset

def toRT (m : Nat) (c : Nat) : Option (SRI.RoleT (Fin m)) :=
  if h : c < 2 * m then some (ofRc c h) else none

def toLab (m : Nat) (a : Array Nat) : Finset (SRI.RoleT (Fin m)) :=
  (a.toList.filterMap (toRT m)).toFinset

def toCand (n m : Nat) (st : St) (roots : Array Nat) : Cand n m :=
  { keys := st.ctxs.map fun c => ⟨toTy n c.key.seed, toLab m c.key.lab, toTy n c.key.pi⟩
    nodes := st.nodes.map fun nd =>
      ⟨nd.ctx, toTy n nd.ty, (nd.pool.zip nd.kids).toList.map fun p =>
        ⟨⟨toLab m p.1.lab, toTy n p.1.fill⟩, p.2⟩⟩
    members := st.ctxs.map (·.nodes)
    roots := roots.toList }

end SRIQFast
