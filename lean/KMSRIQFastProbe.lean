import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.ReferenceReadout
import SRIQFast.Core
import SRIQFast.Brute

/-! Development probe for stage C1c: the unproved demand-driven SHIQ
prototype (`SRIQFast`). `km-sriq-fast-probe <file.ofn>` runs the parser,
`translateSRIQ`, the simple-role check and `encTransQ` as `km-sriq-probe`
does, then the prototype, and prints sizes, phase times and node counts on
stderr and a summary line on stdout. Exit `0` when it answers, `3` when it
declines, `4` when generation hit the node cap.

`km-sriq-fast-probe --sriq <file>` reads normal-form clauses directly
(format in `SRIQFast/README` of the report: one clause per line) and
classifies every name.

Environment:
- `KM_SRIQF_ROWS=1`: print every row as `km-sriq-probe` does.
- `KM_SRIQF_REF=1`: also run the proved `classifyQO` and compare.
- `KM_SRIQF_CLASSES=1`: request the class IRIs only (as
  `KM_SRIQ_PROBE_CLASSES`).
- `KM_SRIQF_INHERIT=0`, `KM_SRIQF_SKIPCOVERED=0`, `KM_SRIQF_MAXNODES=k`:
  variants of the procedure. -/

open ContextCalculus ContextCalculus.OWLFrontend
open SRIQFast

def rtCode {m : Nat} : SRI.RoleT (Fin m) → Nat
  | .pos r => 2 * r.val
  | .inv r => 2 * r.val + 1

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
           maxNodes }

structure Result where
  rows : Array (Nat × Option Ty)
  aborted : Bool

/-- Run the prototype on an ALCHIQ ontology, printing statistics. -/
def runFast {n m : Nat} (E : SRIQ.Ontology (Fin n) (Fin m)) (req : Array Nat) : IO (Option Result) := do
  let cfg ← readCfg
  match toQC E with
  | .error e => IO.eprintln s!"declined: {e}"; return none
  | .ok cls =>
    let t0 ← IO.monoMsNow
    let fullRel ← envFlag "KM_SRIQF_FULLREL" false
    let lazy ← envFlag "KM_SRIQF_LAZY" true
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
    IO.eprintln s!"gen: ctxs={st.ctxs.size} nodes={st.nodes.size} specs={specs} merges={st.nMerge} pw_requests={st.nPW} back_variants={st.nBackVar} pw_variants={st.nPWVar} lazy_variants={st.nLazyVar} rounds={st.nRounds} branch_calls={st.nBranchCalls} branches={st.nBranches} max_branches={st.maxBranches} multi_node_ctxs={multi} max_nodes_per_ctx={maxNodesCtx} aborted={st.aborted} index_ms={t1-t0} gen_elim_ms={t2-t1}"
    if st.aborted then
      return some { rows := #[], aborted := true }
    let t3 ← IO.monoMsNow
    let nAlive := alive.foldl (fun a b => if b then a + 1 else a) 0
    IO.eprintln s!"elim(last round): alive={nAlive} checks={es.checks} searches={es.searches}"
    let rows ← IO.lazyPure fun _ => readout st alive roots req
    let t4 ← IO.monoMsNow
    IO.eprintln s!"readout_ms={t4-t3} fast_total_ms={t4-t0}"
    return some { rows, aborted := false }

/-- The rows of `classifyQO` as `(name, none | subsumers)`. -/
def refRows {n m : Nat} (E : SRIQ.Ontology (Fin n) (Fin m)) (req : List (Fin n)) :
    Array (Nat × Option Ty) :=
  ((QProc.classifyQO E req).map fun p =>
    (p.1.val, p.2.map fun L => sortDedup (L.map (·.val)).toArray)).toArray

/-- Compare rows on the names below `bound` (the requested names). -/
def cmpRows (a b : Array (Nat × Option Ty)) (bound : Nat) : List String := Id.run do
  let mut out := []
  let cut : Option Ty → Option Ty := fun o => o.map fun t => t.filter (· < bound)
  for (x, y) in a.zip b do
    if x.1 != y.1 then out := s!"order {x.1} {y.1}" :: out
    else if cut x.2 != cut y.2 then
      out := s!"name {x.1}: fast={repr (cut x.2)} ref={repr (cut y.2)}" :: out
  return out.reverse

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

def mainSriq (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let lines := text.splitOn "\n" |>.map fun l => (l.splitOn " ").filter (· != "")
  let some hdr := lines.head? | IO.eprintln "empty"; return 2
  let (n, m) ← match hdr with
    | ["n", a, "m", b] => pure (a.toNat!, b.toNat!)
    | _ => do IO.eprintln "first line: n <N> m <M>"; return 2
  let mut cls : List (SRIQ.Clause Nat Nat) := []
  let mut nreq := n
  for l in lines.drop 1 do
    if let ["req", r] := l then
      nreq := r.toNat!
      continue
    match parseLine l with
    | .error e => IO.eprintln e; return 2
    | .ok none => pure ()
    | .ok (some c) => cls := cls ++ [c]
  let some O := cls.mapM (SRIQT.toFin n m) | IO.eprintln "index out of range"; return 2
  if !isSHIQB O then
    IO.eprintln "declined: not SHIQ"; return 3
  let E := SRIQ.Proc.encTransQ O
  let req : List (Fin (n + E.1)) := ((List.finRange n).filter (·.val < nreq)).map (Fin.castAdd E.1)
  let some res ← runFast E.2 (req.map (·.val)).toArray | return 3
  if res.aborted then IO.println "aborted"; return 4
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

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--sriq", p] => mainSriq p
  | [path] =>
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
        let ok := isSHIQB T.ontology
        IO.eprintln s!"named={T.named.length} concepts={T.conceptCount} roles={T.roleCount} clauses={T.ontology.length} shiq={ok} parse_ms={t1-t0} translate_ms={t2-t1}"
        if !ok then
          IO.eprintln "declined: non-simple role in a number restriction or functionality axiom"
          return 3
        let t3 ← IO.monoMsNow
        let E ← IO.lazyPure fun _ => SRIQ.Proc.encTransQ T.ontology
        let t4 ← IO.monoMsNow
        IO.eprintln s!"fresh={E.1} enc_clauses={E.2.length} names={T.conceptCount + E.1} enc_ms={t4-t3}"
        let req := sriqRequest T E.1
        let some res ← runFast E.2 (req.map (·.val)).toArray | return 3
        if res.aborted then IO.println "aborted"; return 4
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
        return 0
  | _ => IO.eprintln "usage: km-sriq-fast-probe <file.ofn> | --sriq <file>"; return 2
