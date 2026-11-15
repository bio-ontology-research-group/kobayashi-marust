import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.ReferenceReadout
import SRIQFast.Core
import SRIQFast.Brute
import SRIQFast.ToCand
import SRIQFast.CB
import ContextCalculus.OWLFrontend.SRIQFastRoute
import ContextCalculus.SRIQ.ElimMarkers
import ContextCalculus.SRIQ.MergeNames

/-! Development probe for stage C1c: the unproved demand-driven SHIQ
prototype (`SRIQFast`). `km-sriq-fast-probe <file.ofn>` runs the parser,
`translateSRIQ`, the simple-role check and `encTransQ` as `km-sriq-probe`
does, then the prototype, and prints sizes, phase times and node counts on
stderr and a summary line on stdout. Exit `0` when it answers, `3` when it
declines, `4` when generation hit the node cap.

`km-sriq-fast-probe --sriq <file>` reads normal-form clauses directly
(one clause per line; format in `C1C-PROTOTYPE.md`, section 1) and
classifies every name.

Environment:
- `KM_SRIQF_ROWS=1`: print every row as `km-sriq-probe` does.
- `KM_SRIQF_REF=1`: also run the proved `classifyQO` and compare.
- `KM_SRIQF_CLASSES=1`: request the class IRIs only (as
  `KM_SRIQ_PROBE_CLASSES`).
- `--checked`: answer through the certified route `fastClassifyA`
  (`closedFastB`, then the worklist elimination and readout);
  `KM_SRIQF_OLDCHECK=1` uses the finset check `closedB` and `fastRows`.
- `KM_SRIQF_SHIQ=slow` (`isSHIQB`) or `unproved` (`isSHIQFast`): the
  simple-role check; the default is the proved `isSHIQFastB`.
- `KM_SRIQF_ELIM=0`: skip the elimination of body markers (`elimChecked`,
  which the certified route applies after `encTransQ`).
- `KM_SRIQF_DUMP=<path>`: write the ontology the generator sees in the
  `--sriq` format; `KM_SRIQF_DIAG=1`: statistics on the generated contexts.
- `KM_SRIQF_INHERIT=0`, `KM_SRIQF_SKIPCOVERED=0`, `KM_SRIQF_MAXNODES=k`:
  variants of the procedure. -/

open ContextCalculus ContextCalculus.OWLFrontend
open SRIQFast

def rtCode {m : Nat} : SRI.RoleT (Fin m) → Nat
  | .pos r => 2 * r.val
  | .inv r => 2 * r.val + 1

/-- `isSHIQB` with the super-roles from one breadth-first search per
transitive role (`isSHIQB` iterates `upStep` `2m + 1` times per role,
seconds on inputs with hundreds of roles). Same answer: chains are
inclusions or transitivity, and no transitive role lies below a counting
role or its inverse, with the inclusions closed under flips. -/
def isSHIQFast {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : Bool :=
  let chainsOK := O.all fun cl => match cl with
    | .chain [_] _ => true
    | .chain [T, T'] S => T == S && T' == S
    | .chain _ _ => false
    | _ => true
  let subs : Array (Array Nat) := O.foldl (fun subs cl => match cl with
    | .chain [R] S =>
      (subs.modify (rtCode R) (·.push (rtCode S))).modify (rtCode R ^^^ 1) (·.push (rtCode S ^^^ 1))
    | _ => subs) (Array.replicate (2 * m) #[])
  let trans : List Nat := O.filterMap fun cl => match cl with
    | .chain [_, _] S => some (rtCode S)
    | _ => none
  let counted : Std.HashSet Nat := O.foldl (fun h cl => match cl with
    | .atLeast _ _ R _ | .atMost _ _ R _ => h.insert (rtCode R)
    | _ => h) ∅
  chainsOK && trans.all fun T =>
    (upClose subs T).all fun R => !(counted.contains R || counted.contains (R ^^^ 1))

/-- The clauses of an ALCHIQ ontology on `Nat` indices. -/
def toQC {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : Except String (Array QC) :=
  O.foldlM (fun acc cl => match cl with
    | .gci b h => .ok (acc.push (.gci (b.map (·.val)).toArray (h.map (·.val)).toArray))
    | .exRight a R b => .ok (acc.push (.ex a.val (rtCode R) b.val))
    | .allRight a S c => .ok (acc.push (.all a.val (rtCode S) c.val))
    | .atLeast a k R b => .ok (acc.push (.ge a.val k (rtCode R) b.val))
    | .atMost a k S e => .ok (acc.push (.le a.val k (rtCode S) e.val))
    | .chain [R] S => .ok (acc.push (.sub (rtCode R) (rtCode S)))
    | .chain _ _ => .error "role chain of length other than one after encTransQ") #[]

def envFlag (k : String) (dflt : Bool) : IO Bool := do
  match ← IO.getEnv k with
  | some "1" => return true
  | some "0" => return false
  | _ => return dflt

def readCfg : IO Cfg := do
  let maxNodes := ((← IO.getEnv "KM_SRIQF_MAXNODES").bind String.toNat?).getD 0
  return { inherit := ← envFlag "KM_SRIQF_INHERIT" true
           skipCovered := ← envFlag "KM_SRIQF_SKIPCOVERED" true
           forcedBack := ← envFlag "KM_SRIQF_FORCEDBACK" true
           lazyEager := ← envFlag "KM_SRIQF_LAZYEAGER" false
           funcMerge := ← envFlag "KM_SRIQF_FUNCMERGE" true
           piFull := ← envFlag "KM_SRIQF_PIFULL" false
           checkedMerge := ← envFlag "KM_SRIQF_CHECKEDMERGE" true
           staticBack := ← envFlag "KM_SRIQF_STATICBACK" false
           lazyBackTrig := ← envFlag "KM_SRIQF_LAZYTRIG" true
           maxNodes }

structure Result where
  rows : Array (Nat × Option Ty)
  aborted : Bool
  /-- checked mode: `some true` when `closedB` accepted and the certified
  rows were used, `some false` when it declined -/
  checked : Option Bool := none

/-- The certified rows as prototype rows. -/
def certRows {n : Nat} (rs : List (Fin n × Option (List (Fin n)))) : Array (Nat × Option Ty) :=
  (rs.map fun p => (p.1.val, p.2.map fun L => sortDedup (L.map (·.val)).toArray)).toArray

/-- Compare rows on the names below `bound` (the requested names). -/
def cmpRows (a b : Array (Nat × Option Ty)) (bound : Nat) : List String := Id.run do
  let mut out := []
  let cut : Option Ty → Option Ty := fun o => o.map fun t => t.filter (· < bound)
  for (x, y) in a.zip b do
    if x.1 != y.1 then out := s!"order {x.1} {y.1}" :: out
    else if cut x.2 != cut y.2 then
      out := s!"name {x.1}: fast={repr (cut x.2)} ref={repr (cut y.2)}" :: out
  return out.reverse

open ContextCalculus.SRIQ.Fast in
/-- Diagnostic: time of each closure condition over all nodes. -/
def checkProf {n m : Nat} (ix : Ix n m) (U : Cand n m) : IO Unit := do
  let mut tms : Array Nat := #[0, 0, 0, 0, 0, 0, 0]
  let p0 ← IO.monoNanosNow
  let r2 ← IO.lazyPure fun _ => (List.range U.keys.size).all fun k => decide (BranchCov ix U k (keyOf U k).seed)
  let p1 ← IO.monoNanosNow
  tms := tms.set! 6 (p1 - p0)
  let N := U.nodes.size
  let tm (nm : String) (f : Unit → Bool) : IO Unit := do
    let a ← IO.monoMsNow
    let r ← IO.lazyPure f
    let b ← IO.monoMsNow
    IO.eprintln s!"checkprof {nm}: {r} {b - a}ms"
  tm "wf" fun _ => decide (∀ i < N, nodeOK ix U i ∧ ∀ e ∈ (nd U i).pool, entryOK ix U (nd U i).ty e)
  tm "r3" fun _ => decide (∀ i < N, ∀ q ∈ lowAt ix (nd U i).ty, 1 ≤ q.2.1 → ¬ skipQ (keyOf U (nd U i).ctx) q → inPool U i (dflt ix q))
  tm "r4" fun _ => decide (∀ i < N, BackOK ix U i)
  tm "r5" fun _ => decide (∀ i < N, ∀ u ∈ uppAt ix (nd U i).ty, u.2.1 < pot ix U i u.2.2.1 u.2.2.2 → MergeOK ix U i u.2.1 u.2.2.1 u.2.2.2)
  tm "r6" fun _ => decide (∀ i < N, WitOK ix U i)
  let Cc := mkCache ix U
  let mut tot := 0
  let mut mx := 0
  let mut mxi := 0
  let mut slow := 0
  for i in [0:N] do
    let a ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => suppB ix U Cc Cc.ok i
    let b ← IO.monoNanosNow
    tot := tot + (b - a)
    if b - a > 1000000 then slow := slow + 1
    if b - a > mx then mx := b - a; mxi := i
  IO.eprintln s!"checkprof supp: total={tot/1000000}ms max={mx/1000000}ms at {mxi} slow(>1ms)={slow} cands={(candsA U Cc Cc.ok mxi).length} needs={(needsV ix U mxi).length}"
  IO.eprintln s!"checkprof: r2ok={r2} ms: wf={tms[0]!/1000000} r3={tms[1]!/1000000} r4={tms[2]!/1000000} r5={tms[3]!/1000000} r6={tms[4]!/1000000} r2={tms[6]!/1000000}"

open ContextCalculus.SRIQ.Fast in
/-- Diagnostic: dfsG with a step counter. -/
partial def dfsCnt {α κ : Type} (cnt : κ → α → Bool) (cs : List α) (fuel : Nat) (needs lims : List (κ × Nat)) (steps : Nat) : Bool × Nat :=
  match needs.find? (fun x => decide (0 < x.2)) with
  | none => (true, steps + 1)
  | some x =>
    match fuel with
    | 0 => (false, steps + 1)
    | f + 1 => cs.foldl (fun (acc : Bool × Nat) c =>
        if acc.1 then acc else
        if cnt x.1 c && lims.all (fun y => !cnt y.1 c || decide (0 < y.2)) then
          dfsCnt cnt cs f (subG cnt c needs) (subG cnt c lims) acc.2
        else acc) (false, steps + 1)

open ContextCalculus.SRIQ.Fast in
def elimStats {n m : Nat} (Es : Array (NodeE n m)) (A : Array Bool) : IO Unit := do
  let mut tot := 0
  let mut mx := 0
  let mut fails := 0
  let mut hist : Array Nat := Array.replicate 8 0
  for E in Es do
    let ss := dedupKey id ((E.cands.filter fun p => A[p.1]?.getD false).map (·.2.2))
    let pre := E.nS.all (fun x => ss.any (cntS x.1))
    if !pre then fails := fails + 1; continue
    let (r, st) := dfsCnt cntS ss ((E.nS.map (·.2)).sum + 1) E.nS E.lS 0
    if !r then fails := fails + 1
    tot := tot + st
    mx := max mx st
    let b := min 7 (Nat.log2 (st + 1) / 2)
    hist := hist.modify b (· + 1)
  IO.eprintln s!"dfsstats: total_steps={tot} max={mx} fails={fails} hist4={hist}"

/-- Diagnostic: where the nodes and contexts of a generation state come from. -/
def genDiag (st : St) : IO Unit := do
  -- nodes per context
  let mut hist : Array Nat := Array.replicate 12 0
  for c in st.ctxs do
    let b := min 11 (Nat.log2 (c.nodes.size + 1))
    hist := hist.modify b (· + 1)
  IO.eprintln s!"diag: nodes-per-ctx log2 histogram {hist}"
  -- contexts that share (seed, lab) but differ in pi; share lab only
  let mut bySL : Std.HashMap (Ty × Ty) Nat := ∅
  let mut byL : Std.HashMap Ty Nat := ∅
  for c in st.ctxs do
    bySL := bySL.insert (c.key.seed, c.key.lab) (bySL.getD (c.key.seed, c.key.lab) 0 + 1)
    byL := byL.insert c.key.lab (byL.getD c.key.lab 0 + 1)
  IO.eprintln s!"diag: ctxs={st.ctxs.size} seed_lab={bySL.size} labs={byL.size}"
  -- parents per context
  let mut ph : Array Nat := Array.replicate 16 0
  for c in st.ctxs do
    ph := ph.modify (min 15 (Nat.log2 (c.parents.size + 1))) (· + 1)
  IO.eprintln s!"diag: parents-per-ctx log2 histogram {ph}"
  -- the largest contexts
  let top3 (N : Nat) (f : Nat → Nat) : Array Nat := Id.run do
    let mut best : Array Nat := #[]
    for _ in [0:3] do
      let mut bi := N
      let mut bv := 0
      for i in [0:N] do
        if !best.contains i && (bi == N || f i > bv) then bi := i; bv := f i
      if bi < N then best := best.push bi
    return best
  let ctxs := st.ctxs
  let nodes := st.nodes
  let order := top3 ctxs.size fun k => ctxs[k]!.nodes.size
  for k in order do
    let c := st.ctxs[k]!
    IO.eprintln s!"diag: ctx {k} nodes={c.nodes.size} parents={c.parents.size} seed={c.key.seed} lab={c.key.lab} pi={c.key.pi}"
    for v in c.nodes.extract 0 12 do
      let nd := st.nodes[v]!
      IO.eprintln s!"diag:   node {v} |ty|={nd.ty.size} extra={(nd.ty.filter fun x => !mem c.key.seed x).toList.take 40} pool={nd.pool.size} back={nd.back}"
  for k in top3 ctxs.size (fun k => if ctxs[k]!.nodes.size > 1 then ctxs[k]!.parents.size else 0) do
    let c := ctxs[k]!
    IO.eprintln s!"diag: multi-node ctx {k} nodes={c.nodes.size} parents={c.parents.size} seed={c.key.seed.toList.take 10} lab={c.key.lab} pi={c.key.pi}"
    for v in c.nodes.extract 0 6 do
      let nd := nodes[v]!
      IO.eprintln s!"diag:   mnode {v} extra={(nd.ty.filter fun x => !mem c.key.seed x).toList.take 30} back={nd.back} sup={nd.sup}"
  let byPool := top3 nodes.size fun v => nodes[v]!.pool.size
  for v in byPool do
    let nd := st.nodes[v]!
    let c := st.ctxs[nd.ctx]!
    IO.eprintln s!"diag: big pool node {v} ctx={nd.ctx} pool={nd.pool.size} |ty|={nd.ty.size} ctx_nodes={c.nodes.size} seed={c.key.seed.toList.take 10} lab={c.key.lab} backDone={nd.backDone.size}"
  -- seeds: how many contexts per fill-only part? (seed minus names that are universal fillers)
  let mut seedSz : Array Nat := Array.replicate 16 0
  for c in st.ctxs do
    seedSz := seedSz.modify (min 15 (Nat.log2 (c.key.seed.size + 1))) (· + 1)
  IO.eprintln s!"diag: seed size log2 histogram {seedSz}"
  if let some k0 := (← IO.getEnv "KM_SRIQF_DIAGCTX").bind String.toNat? then
    for k in [k0:min st.ctxs.size (k0 + 40)] do
      let c := st.ctxs[k]!
      IO.eprintln s!"diagctx {k} n={c.nodes.size} par={c.parents.size} lab={c.key.lab} pi={c.key.pi} seed={c.key.seed}"

/-- Run the prototype on an ALCHIQ ontology, printing statistics. -/
def runFast {n m : Nat} (E : SRIQ.Ontology (Fin n) (Fin m)) (req : Array Nat)
    (reqF : List (Fin n) := []) (checked : Bool := false) : IO (Option Result) := do
  let cfg ← readCfg
  match toQC E with
  | .error e => IO.eprintln s!"declined: {e}"; return none
  | .ok cls =>
    let t0 ← IO.monoMsNow
    let fullRel ← envFlag "KM_SRIQF_FULLREL" true
    let lazy ← envFlag "KM_SRIQF_LAZY" false
    let O ← IO.lazyPure fun _ => mkOnto n m cls fullRel lazy (req.foldl (fun a x => max a (x + 1)) 0)
    let t1 ← IO.monoMsNow
    let topDisj := O.gciTop.foldl (fun a i => if (O.gcis[i]!).2.size ≥ 2 then a + 1 else a) 0
    IO.eprintln s!"onto: lazy_disjunctions={O.lazyDef.size} names={O.n} gcis={O.gcis.size} top_disjunctions={topDisj} lower={O.low.size} upper={O.upp.size}"
    if (← IO.getEnv "KM_SRIQF_STATSONLY") == some "1" then
      -- classify the head names of top disjunctions
      let mut headCnt : Std.HashMap Nat Nat := ∅
      for (_, h) in O.gcis do
        for x in h do headCnt := headCnt.insert x (headCnt.getD x 0 + 1)
      let mut kinds : Std.HashMap String Nat := ∅
      for i in O.gciTop do
        let (_, h) := O.gcis[i]!
        if h.size < 2 then continue
        let ks := h.toList.map fun x =>
          let inBody := !(O.gciBy[x]!).isEmpty
          let nl := (O.lowBy[x]!).size; let nu := (O.uppBy[x]!).size; let na := (O.allBy[x]!).size
          if headCnt.getD x 0 == 1 && !inBody && na == 0 && nl + nu == 1 then
            (if nu == 1 then "U" else "L") else "X"
        let k := String.intercalate "" (ks.mergeSort (· ≤ ·))
        kinds := kinds.insert k (kinds.getD k 0 + 1)
      IO.eprintln s!"top_kinds: {kinds.toList}"
      return none
    let (st, roots, alive, es) ← generateRounds O cfg req
    let t2 ← IO.monoMsNow
    let specs := st.nodes.foldl (fun a nd => a + nd.pool.size) 0
    let multi := st.ctxs.foldl (fun a c => if c.nodes.size > 1 then a + 1 else a) 0
    let maxNodesCtx := st.ctxs.foldl (fun a c => max a c.nodes.size) 0
    let seeds := (st.ctxs.foldl (fun (h : Std.HashSet (Array Nat × Array Nat)) c => h.insert (c.key.seed, c.key.lab)) ∅).size
    let avgSeed := (st.ctxs.foldl (fun a c => a + c.key.seed.size) 0) / max 1 st.ctxs.size
    let avgTy := (st.nodes.foldl (fun a nd => a + nd.ty.size) 0) / max 1 st.nodes.size
    IO.eprintln s!"ctx: seed_lab_pairs={seeds} avg_seed={avgSeed} avg_type={avgTy}"
    IO.eprintln s!"gen: ctxs={st.ctxs.size} nodes={st.nodes.size} specs={specs} merges={st.nMerge} pw_requests={st.nPW} back_variants={st.nBackVar} pw_variants={st.nPWVar} lazy_variants={st.nLazyVar} superseded={st.nSup} rounds={st.nRounds} branch_calls={st.nBranchCalls} branches={st.nBranches} max_branches={st.maxBranches} multi_node_ctxs={multi} max_nodes_per_ctx={maxNodesCtx} aborted={st.aborted} index_ms={t1-t0} gen_elim_ms={t2-t1}"
    if (← IO.getEnv "KM_SRIQF_DIAG") == some "1" then genDiag st
    if st.aborted then
      return some { rows := #[], aborted := true }
    let t3 ← IO.monoMsNow
    let nAlive := alive.foldl (fun a b => if b then a + 1 else a) 0
    IO.eprintln s!"elim(last round): alive={nAlive} checks={es.checks} searches={es.searches}"
    let rows ← IO.lazyPure fun _ => readout st alive roots req
    let t4 ← IO.monoMsNow
    IO.eprintln s!"readout_ms={t4-t3} fast_total_ms={t4-t0}"
    if !checked then return some { rows, aborted := false }
    -- checked mode: the certified check, elimination and readout
    if (← IO.getEnv "KM_SRIQF_OLDCHECK") != some "1" then
      let c0 ← IO.monoMsNow
      let ix ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.mkIx E
      let ixf ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.mkIxF E ix
      let CA ← IO.lazyPure fun _ => toCandA st roots
      let c1 ← IO.monoMsNow
      IO.eprintln s!"checked: indexes+convert nodes={CA.nodes.size} ms={c1 - c0}"
      let rep := ((← IO.getEnv "KM_SRIQF_REPEAT").bind String.toNat?).getD 0
      for r in [0:rep] do
        let ok' ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.closedFastB ix ixf (if r > 1000000 then toCandA st roots else CA) reqF
        if !ok' then IO.eprintln "repeat: declined"
      let ok ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.closedFastB ix ixf CA reqF
      let c2 ← IO.monoMsNow
      IO.eprintln s!"checked: closedB={ok} convert_ms={c1 - c0} check_ms={c2 - c1}"
      if !ok then return some { rows, aborted := false, checked := some false }
      if (← IO.getEnv "KM_SRIQF_ELIMPROF") == some "1" then
        let e0 ← IO.monoMsNow
        let Es ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.nodeEs ix CA
        let e1 ← IO.monoMsNow
        let P ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.parentsOf CA
        let e2 ← IO.monoMsNow
        let ncand := Es.foldl (fun a E => a + E.cands.length) 0
        let nneed := Es.foldl (fun a E => a + E.needs.length) 0
        let A ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.elimW CA Es P (Array.replicate CA.nodes.size true) (Array.replicate CA.nodes.size true) (List.range CA.nodes.size).reverse []
        let e3 ← IO.monoMsNow
        elimStats Es (Array.replicate CA.nodes.size true)
        elimStats Es A
        IO.eprintln s!"elimprof: nodeEs_ms={e1-e0} parents_ms={e2-e1} elimW_ms={e3-e2} cands={ncand} needs={nneed} alive={A.toList.count true}"
      let crows ← IO.lazyPure fun _ => certRows (ContextCalculus.SRIQ.Fast.fastRowsA ix CA reqF)
      let c3 ← IO.monoMsNow
      let same := cmpRows crows rows reqF.length |>.isEmpty
      IO.eprintln s!"checked: elim_readout_ms={c3 - c2} same_as_prototype={same} checked_total_ms={c3 - c0}"
      return some { rows := crows, aborted := false, checked := some true }
    let c0 ← IO.monoMsNow
    let ix ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.mkIx E
    IO.eprintln s!"checked: indexes ups={ix.upArr.size} ms={(← IO.monoMsNow) - c0}"
    let U ← IO.lazyPure fun _ => toCand ix st roots
    IO.eprintln s!"checked: converted nodes={U.nodes.size} ctxs={U.keys.size} ms={(← IO.monoMsNow) - c0}"
    if (← IO.getEnv "KM_SRIQF_CHECKPROF") == some "1" then checkProf ix U
    let c1 ← IO.monoMsNow
    let ok ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.closedB ix U reqF
    let c2 ← IO.monoMsNow
    IO.eprintln s!"checked: closedB={ok} convert_ms={c1-c0} check_ms={c2-c1}"
    if !ok then return some { rows, aborted := false, checked := some false }
    let crows ← IO.lazyPure fun _ => certRows (ContextCalculus.SRIQ.Fast.fastRows ix U reqF)
    let c3 ← IO.monoMsNow
    let same := cmpRows crows rows reqF.length |>.isEmpty
    IO.eprintln s!"checked: elim_readout_ms={c3-c2} same_as_prototype={same} checked_total_ms={c3-c0}"
    return some { rows := crows, aborted := false, checked := some true }

/-- The consequence-based saturation of stage C1f (unproved rows). -/
def runCB {n m : Nat} (E : SRIQ.Ontology (Fin n) (Fin m)) (req : Array Nat) (reqF : List (Fin n)) (checked : Bool := false) : IO (Option Result) := do
  match toQC E with
  | .error e => IO.eprintln s!"declined: {e}"; return none
  | .ok cls =>
    let t0 ← IO.monoMsNow
    let budget := ((← IO.getEnv "KM_SRIQF_CBMS").bind String.toNat?).getD 120000
    let r ← CBGen.saturate n m cls req (deadline := (← IO.monoMsNow) + budget)
    let t1 ← IO.monoMsNow
    let nItems := r.st.ctxs.foldl (fun a c => a + c.itemLog.size) 0
    IO.eprintln s!"cb: steps={r.steps.size} ctxs={r.st.ctxs.size} items={nItems} groups={r.st.groups.size} combcut={r.st.combCut} aborted={r.st.aborted} ms={t1-t0}"
    if r.st.aborted then return (if checked then none else some { rows := #[], aborted := true })
    if (← IO.getEnv "KM_SRIQF_CBDUMP") == some "1" then
      for h : i in [0:r.steps.size] do
        let st := r.steps[i]
        IO.eprintln s!"step {i}: {repr st.rule} L={st.c.L} P={st.c.P} B={st.c.B} H={st.c.H} Q={st.c.Q}"
    let cbRows := CBGen.rows r req
    if (← IO.getEnv "KM_SRIQF_CBWIT") != some "0" then
      let W := CBGen.mkWIx (CBGen.mkIx n m cls) r.st (req.foldl (fun a x => max a (x + 1)) 0)
      let (C, cut) ← IO.lazyPure fun _ => CBGen.witness W r.st req
      let t2 ← IO.monoMsNow
      IO.eprintln s!"cbwit: ctxs={C.keys.size} nodes={C.nodes.size} cut={cut} ms={t2-t1}"
      let ix ← IO.lazyPure fun _ => ContextCalculus.SRIQ.Fast.mkIx E
      let wrows ← IO.lazyPure fun _ => certRows (ContextCalculus.SRIQ.Fast.fastRowsA ix C reqF)
      let t3 ← IO.monoMsNow
      -- the two sides meet on the requested names
      let mut bad := 0
      let mut badEx : List String := []
      for i in [0:cbRows.size] do
        let (a, d) := cbRows[i]!
        match d, (wrows[i]?.map (·.2)).join with
        | none, _ => pure ()
        | some ds, some ws =>
          let extra := ws.filter fun b => b < reqF.length && !mem ds b
          if !extra.isEmpty then
            bad := bad + 1
            if badEx.length < 5 then badEx := s!"{a}: witness holds {extra.toList.take 5}" :: badEx
        | some _, none =>
          bad := bad + 1
          if badEx.length < 5 then badEx := s!"{a}: no live witness root" :: badEx
      let alive := (ContextCalculus.SRIQ.Fast.aliveFast ix C).toList.count true
      IO.eprintln s!"cbwit: alive={alive} rows_ms={t3-t2} unmet_rows={bad} {badEx}"
      if checked then
        let c0 ← IO.monoMsNow
        let C := { C with cert := r.steps }
        let res ← IO.lazyPure fun _ => ContextCalculus.SRIQ.CB.cbClassify E reqF C
        let c1 ← IO.monoMsNow
        match res with
        | some rs =>
          IO.eprintln s!"cbroute: accepted ms={c1 - c0}"
          return some { rows := certRows rs, aborted := false, checked := some true }
        | none =>
          let okc ← IO.lazyPure fun _ => ContextCalculus.SRIQ.CB.checkCert (ContextCalculus.SRIQ.Fast.mkIxF E ix) E.toArray r.steps
          let okw ← IO.lazyPure fun _ => ContextCalculus.SRIQ.CB.witB ix (ContextCalculus.SRIQ.Fast.mkIxF E ix) C reqF
          IO.eprintln s!"cbroute: declined cert={okc} wit={okw} ms={(← IO.monoMsNow) - c0}"
          if !okc then
            let ixf := ContextCalculus.SRIQ.Fast.mkIxF E ix
            let OA := E.toArray
            let mut shown := 0
            for h : i in [0:r.steps.size] do
              let st := r.steps[i]
              if shown < 3 && !ContextCalculus.SRIQ.CB.ruleOK ixf OA r.steps i st.c st.rule then
                shown := shown + 1
                IO.eprintln s!"cbbad: step {i}: {repr st.rule} L={st.c.L} P={st.c.P} B={st.c.B} H={st.c.H} Q={st.c.Q}"
          return none
    return some { rows := cbRows, aborted := false }

/-- The rows of `classifyQO` as `(name, none | subsumers)`. -/
def refRows {n m : Nat} (E : SRIQ.Ontology (Fin n) (Fin m)) (req : List (Fin n)) :
    Array (Nat × Option Ty) :=
  ((QProc.classifyQO E req).map fun p =>
    (p.1.val, p.2.map fun L => sortDedup (L.map (·.val)).toArray)).toArray

/-! ## The `--sriq` text format -/

def parseRT (s : String) : Option (SRI.RoleT Nat) :=
  if s.startsWith "-" then (s.drop 1).toString.toNat?.map .inv
  else (if s.startsWith "+" then (s.drop 1).toString else s).toNat?.map .pos

def parseLine (ws : List String) : Except String (Option (SRIQ.Clause Nat Nat)) := do
  let nat (s : String) : Except String Nat := match s.toNat? with
    | some k => .ok k | none => .error s!"bad number {s}"
  let rt (s : String) : Except String (SRI.RoleT Nat) := match parseRT s with
    | some r => .ok r | none => .error s!"bad role {s}"
  match ws with
  | [] => return none
  | "gci" :: rest =>
    let (b, h) := rest.span (· != "|")
    let b ← b.mapM nat
    let h ← (h.drop 1).mapM nat
    return some (.gci b h)
  | ["ex", a, R, b] => return some (.exRight (← nat a) (← rt R) (← nat b))
  | ["all", a, R, b] => return some (.allRight (← nat a) (← rt R) (← nat b))
  | ["ge", a, k, R, b] => return some (.atLeast (← nat a) (← nat k) (← rt R) (← nat b))
  | ["le", a, k, R, b] => return some (.atMost (← nat a) (← nat k) (← rt R) (← nat b))
  | ["sub", R, S] => return some (.chain [← rt R] (← rt S))
  | ["trans", R] => let r ← rt R; return some (.chain [r, r] r)
  | w :: _ => if w.startsWith "#" then return none else .error s!"bad line {ws}"

def mainSriq (path : String) (checkedArg : Bool := false) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let lines := text.splitOn "\n" |>.map fun l => (l.splitOn " ").filter (· != "")
  let some hdr := lines.head? | IO.eprintln "empty"; return 2
  let (n, m) ← match hdr with
    | ["n", a, "m", b] => pure (a.toNat!, b.toNat!)
    | _ => do IO.eprintln "first line: n <N> m <M>"; return 2
  let mut cls : Array (SRIQ.Clause Nat Nat) := #[]
  let mut nreq := n
  let mut reqList : Option (List Nat) := none
  for l in lines.drop 1 do
    if let ["req", r] := l then
      nreq := r.toNat!
      continue
    if l.head? == some "reqs" then
      reqList := some ((l.drop 1).map String.toNat!)
      continue
    match parseLine l with
    | .error e => IO.eprintln e; return 2
    | .ok none => pure ()
    | .ok (some c) => cls := cls.push c
  let some O := cls.toList.mapM (SRIQT.toFin n m) | IO.eprintln "index out of range"; return 2
  if !isSHIQB O then
    IO.eprintln "declined: not SHIQ"; return 3
  let E := SRIQ.Proc.encTransQ O
  let req : List (Fin (n + E.1)) := match reqList with
    | some rl => ((List.finRange n).filter (fun x => rl.contains x.val)).map (Fin.castAdd E.1)
    | none => ((List.finRange n).filter (·.val < nreq)).map (Fin.castAdd E.1)
  let checked := checkedArg || (← envFlag "KM_SRIQF_CHECKED" false)
  -- the elimination of body markers, as the certified route (names below `nreq` kept)
  let E2 := if reqList.isNone && (← envFlag "KM_SRIQF_ELIM" true) then
    SRIQ.Elim.elimChecked E.2 nreq else E.2
  let E2 := if reqList.isNone && (← envFlag "KM_SRIQF_MERGE" true) then
    SRIQ.Merge.mergeChecked E2 nreq else E2
  if E2.length != E.2.length then IO.eprintln s!"elim: clauses={E.2.length}->{E2.length}"
  let cb ← envFlag "KM_SRIQF_CB" false
  let r0 ← if cb then runCB E2 (req.map (·.val)).toArray req checked else pure none
  let some res ← (match r0 with
    | some r => pure (some r)
    | none => if cb && !checked then pure none else runFast E2 (req.map (·.val)).toArray req checked) | return 3
  if res.aborted then IO.println "aborted"; return 4
  if res.checked == some false then IO.println "declined: closedB"; return 3
  let showRows (rs : Array (Nat × Option Ty)) (tag : String) : IO Unit := do
    for (a, o) in rs do
      match o with
      | none => IO.println s!"{tag} {a} unsat"
      | some t => IO.println s!"{tag} {a} {(t.filter (· < nreq)).toList}"
  if (← IO.getEnv "KM_SRIQF_ROWS") == some "1" then showRows res.rows "fast"
  let mut status : UInt32 := 0
  if (← IO.getEnv "KM_SRIQF_BRUTE") == some "1" then
    let t0 ← IO.monoMsNow
    let some qcs := (toQC E.2).toOption | return 2
    let br ← IO.lazyPure fun _ => Brute.rows (mkOnto (n + E.1) m qcs) (req.map (·.val)).toArray
    let t1 ← IO.monoMsNow
    IO.eprintln s!"brute_ms={t1-t0}"
    let d := cmpRows res.rows br nreq
    if d.isEmpty then IO.println "BRUTE-AGREE"
    else
      IO.println "BRUTE-DISAGREE"
      for x in d do IO.println x
      showRows br "brute"
      status := 1
  if (← IO.getEnv "KM_SRIQF_REF") == some "1" then
    let t0 ← IO.monoMsNow
    let ref ← IO.lazyPure fun _ => refRows E.2 req
    let t1 ← IO.monoMsNow
    IO.eprintln s!"ref_ms={t1-t0}"
    let d := cmpRows res.rows ref nreq
    if d.isEmpty then IO.println "AGREE"
    else
      IO.println "DISAGREE"
      for x in d do IO.println x
      showRows ref "ref"
      return 1
  return status

def rtStr {m : Nat} : SRI.RoleT (Fin m) → String
  | .pos r => toString r.val
  | .inv r => s!"-{r.val}"

/-- Write an ALCHIQ ontology (after `encTransQ`) in the `--sriq` format,
requesting the names below `nreq`. -/
def dumpSriq {n m : Nat} (path : String) (nn mm : Nat) (O : SRIQ.Ontology (Fin n) (Fin m)) (nreq : Nat) :
    IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  h.putStrLn s!"n {nn} m {mm}"
  h.putStrLn s!"req {nreq}"
  for cl in O do
    match cl with
    | .gci b hd => h.putStrLn s!"gci {String.intercalate " " (b.map (toString ·.val))} | {String.intercalate " " (hd.map (toString ·.val))}"
    | .exRight a R b => h.putStrLn s!"ex {a.val} {rtStr R} {b.val}"
    | .allRight a S c => h.putStrLn s!"all {a.val} {rtStr S} {c.val}"
    | .atLeast a k R b => h.putStrLn s!"ge {a.val} {k} {rtStr R} {b.val}"
    | .atMost a k S e => h.putStrLn s!"le {a.val} {k} {rtStr S} {e.val}"
    | .chain [R] S => h.putStrLn s!"sub {rtStr R} {rtStr S}"
    | .chain _ _ => h.putStrLn "# chain"
  h.flush

def mainOfn (path : String) (checkedArg : Bool) : IO UInt32 := do
    let t0 ← IO.monoMsNow
    let text ← IO.FS.readFile path
    match OWL.parse text with
    | .error e => IO.eprintln s!"declined: parse: {e}"; return 3
    | .ok O =>
      let t1 ← IO.monoMsNow
      let req := if (← IO.getEnv "KM_SRIQF_CLASSES") == some "1" then O.classNames
        else probeRequest O
      match ← IO.lazyPure fun _ => translateSRIQ O req with
      | none => IO.eprintln "declined: not SHIQ"; return 3
      | some T =>
        let t2 ← IO.monoMsNow
        let shiqMode := (← IO.getEnv "KM_SRIQF_SHIQ").getD "proved"
        let ok ← IO.lazyPure fun _ => if shiqMode == "slow" then isSHIQB T.ontology
          else if shiqMode == "unproved" then isSHIQFast T.ontology
          else isSHIQFastB T.ontology
        let t2b ← IO.monoMsNow
        IO.eprintln s!"named={T.named.length} concepts={T.conceptCount} roles={T.roleCount} clauses={T.ontology.length} shiq={ok} parse_ms={t1-t0} translate_ms={t2-t1} shiq_ms={t2b-t2}"
        if !ok then
          IO.eprintln "declined: non-simple role in a number restriction or functionality axiom"
          return 3
        let t3 ← IO.monoMsNow
        let E ← IO.lazyPure fun _ => SRIQ.Proc.encTransQ T.ontology
        let t4 ← IO.monoMsNow
        IO.eprintln s!"fresh={E.1} enc_clauses={E.2.length} names={T.conceptCount + E.1} enc_ms={t4-t3}"
        let req := sriqRequest T E.1
        let EO : SRIQ.Ontology (Fin (T.conceptCount + E.1)) (Fin T.roleCount) ←
          if (← envFlag "KM_SRIQF_ELIM" true) then do
            -- as the certified route `owlSHIQFast`: `elimChecked`
            let e0 ← IO.monoMsNow
            let S := SRIQ.Elim.elimHint E.2 T.named.length
            let ok := SRIQ.Elim.hintOK E.2 T.named.length S
            let E2 := SRIQ.Elim.elimChecked E.2 T.named.length
            let nS := S.foldl (fun a o => if o.isSome then a + 1 else a) 0
            IO.eprintln s!"elim: names={nS} hint_ok={ok} clauses={E.2.length}->{E2.length} ms={(← IO.monoMsNow) - e0}"
            pure E2
          else pure E.2
        let EO ← if (← envFlag "KM_SRIQF_MERGE" true) then do
            let e0 ← IO.monoMsNow
            let h := SRIQ.Merge.mergeHint EO T.named.length
            let ok := SRIQ.Merge.mergeOK EO T.named.length h.1 h.2
            let nM := (List.range h.1.size).foldl (fun a i => if h.1[i]! != i then a + 1 else a) 0
            let E3 := SRIQ.Merge.mergeChecked EO T.named.length
            IO.eprintln s!"merge: names={nM} hint_ok={ok} ms={(← IO.monoMsNow) - e0}"
            pure E3
          else pure EO
        if let some dp := ← IO.getEnv "KM_SRIQF_DUMP" then
          dumpSriq dp (T.conceptCount + E.1) T.roleCount EO T.named.length
          IO.eprintln s!"dumped {dp}"
        let checked := checkedArg || (← envFlag "KM_SRIQF_CHECKED" false)
        let cb ← envFlag "KM_SRIQF_CB" false
        let r0 ← if cb then runCB EO (req.map (·.val)).toArray req checked else pure none
        let some res ← (match r0 with
          | some r => pure (some r)
          | none => if cb && !checked then pure none else runFast EO (req.map (·.val)).toArray req checked) | return 3
        if res.aborted then IO.println "aborted"; return 4
        if res.checked == some false then IO.println "declined: closedB"; return 3
        let named := T.named.length
        let sups := res.rows.foldl (fun s r => match r.2 with
          | some t => s + (t.filter (· < named)).size | none => s) 0
        let unsat := res.rows.foldl (fun s r => if r.2.isNone then s + 1 else s) 0
        let t5 ← IO.monoMsNow
        IO.println s!"rows={res.rows.size} sups={sups} unsat={unsat} total_ms={t5-t0}"
        if (← IO.getEnv "KM_SRIQF_ROWS") == some "1" then
          let names := T.named.toArray
          for (a, o) in res.rows do
            let sub := names[a]?.getD "?"
            match o with
            | none => IO.println s!"row {sub} unsat"
            | some t =>
              let ss := (t.filter (· < named)).toList.map fun j => names[j]?.getD "?"
              IO.println s!"row {sub} {String.intercalate " " ss}"
        if (← IO.getEnv "KM_SRIQF_REF") == some "1" then
          let ref ← IO.lazyPure fun _ => refRows E.2 req
          let d := cmpRows res.rows ref named
          if d.isEmpty then IO.println "AGREE" else
            IO.println "DISAGREE"
            for x in d do IO.println x
            return 1
        -- skip freeing the generated structures at exit (seconds on large inputs)
        (← IO.getStdout).flush
        IO.Process.exit 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--sriq", p] => mainSriq p
  | ["--checked", "--sriq", p] => mainSriq p true
  | ["--checked", path] => mainOfn path true
  | [path] => mainOfn path false
  | _ => IO.eprintln "usage: km-sriq-fast-probe [--checked] <file.ofn> | [--checked] --sriq <file>"; return 2
