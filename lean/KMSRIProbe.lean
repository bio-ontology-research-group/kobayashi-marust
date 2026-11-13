import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.SRIReference
import ContextCalculus.OWLFrontend.ReferenceReadout

/-! Development probe: time the v1.6.3 SHI route on one file.
`km-sri-probe <file.ofn>` prints names, rows, and phase times. -/

open ContextCalculus ContextCalculus.OWLFrontend


def bump (c : IO.Ref (Array Nat)) (i v : Nat) : IO Unit := c.modify (·.modify i (· + v))

open ContextCalculus.SRI.Proc in
/-- Profile of the candidate loop: the same steps as `loop`, with clocks
around the seed generation and the seed expansion, and counters of seeds
and cache hits. -/
partial def profLoop {n m : Nat} (O : ContextCalculus.SRI.Ontology (Fin n) (Fin m)) (ix : Ix n m)
    (st : St n m) (c : IO.Ref (Array Nat)) (stopAt : Nat) : IO (St n m) := do
  match st.todo with
  | [] => return st
  | r :: rest =>
    bump c 0 (1)
    if (← IO.monoMsNow) > stopAt then
      IO.eprintln s!"prof stopped: queued={st.todo.length}"
      return st
    let f0 ← IO.monoNanosNow
    let fs ← IO.lazyPure fun _ => (demF ix r.t).map fun d => ins d.2.2 (fwdF ix r.t d.2.1)
    bump c 5 ((← IO.monoNanosNow) - f0); bump c 6 fs.length
    bump c 7 (fs.foldl (fun a F => a + F.card) 0)
    let g0 ← IO.monoNanosNow
    let L ← IO.lazyPure fun _ => seedsOf ix st r
    let g1 ← IO.monoNanosNow
    bump c 1 ((g1 - g0)); bump c 2 (L.length)
    let mut st' := { st with todo := rest }
    for sd in L do
      if st'.seeds.contains (toL sd.1, toL sd.2) then
        bump c 3 (1)
      else
        let s0 ← IO.monoNanosNow
        st' ← IO.lazyPure fun _ => addSeed O ix st' sd
        bump c 4 (((← IO.monoNanosNow) - s0))
    profLoop O ix st' c stopAt

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: km-sri-probe <file>"; return 2
  let t0 ← IO.monoMsNow
  let text ← IO.FS.readFile path
  match OWL.parse text with
  | .error e => IO.eprintln s!"parse: {e}"; return 3
  | .ok O =>
    let t1 ← IO.monoMsNow
    let req := probeRequest O
    match translateSRI O req with
    | none => IO.eprintln "not SRI"; return 3
    | some T =>
      let t2 ← IO.monoMsNow
      let gl := T.ontology.foldl (fun (acc : Nat × Nat) cl => match cl with
        | .gci [] h => if h.length ≥ 2 then (acc.1 + 1, acc.2) else acc
        | .gci _ h => if h.length ≥ 2 then (acc.1, acc.2 + 1) else acc
        | _ => acc) (0, 0)
      IO.eprintln s!"global_disj={gl.1} local_disj={gl.2}"
      IO.eprintln s!"named={T.named.length} concepts={T.conceptCount} roles={T.roleCount} clauses={T.ontology.length} shi={isSHIB T.ontology} parse_ms={t1-t0} translate_ms={t2-t1}"
      if (← IO.getEnv "KM_SRI_BF") == some "1" then
        let b0 ← IO.monoMsNow
        let E ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.encTrans T.ontology
        IO.eprintln s!"bf fresh={E.1} clauses={E.2.length} enc_ms={(← IO.monoMsNow) - b0}"
        let rq := sriRequest T E.1
        let b1 ← IO.monoMsNow
        let ix ← IO.lazyPure fun _ => (ContextCalculus.SRI.Proc.mkIx E.2).allBy
        IO.eprintln s!"bf allBy_ms={(← IO.monoMsNow) - b1}"
        let b2 ← IO.monoMsNow
        let ix ← IO.lazyPure fun _ => (ContextCalculus.SRI.Proc.mkIx E.2).upPos
        IO.eprintln s!"bf upPos_ms={(← IO.monoMsNow) - b2} {ix.size}"
        let ix ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.mkIx E.2
        let byLens := ix.gciBy.toList.map (·.2.length)
        let alls := ix.allBy.toList.map (·.2.length)
        IO.eprintln s!"bf gcis={ix.gciArr.size} top={ix.gciTop.length} maxGciBy={byLens.foldl max 0} sumGciBy={byLens.foldl (· + ·) 0} maxAllBy={alls.foldl max 0} maxBody={ix.gciArr.foldl (fun a q => max a q.1.length) 0} maxHead={ix.gciArr.foldl (fun a q => max a q.2.length) 0}"
        let mut worst : Nat × Nat × Nat := (0, 0, 0)
        let mut tot := 0
        for a in rq.take 300 do
          let s0 ← IO.monoNanosNow
          let L ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.branchesF E.2 ix {a}
          let d := (← IO.monoNanosNow) - s0
          tot := tot + d
          let sz := L.foldl (fun m t => max m t.card) 0
          if d > worst.1 then worst := (d, a.val, sz)
        IO.eprintln s!"bf first300_ms={tot/1000000} worst_us={worst.1/1000} worst_name={worst.2.1} worst_size={worst.2.2}"
        return 0
      if (← IO.getEnv "KM_SRI_PROF") == some "1" then
        let E := ContextCalculus.SRI.Proc.encTrans T.ontology
        let rq := sriRequest T E.1
        let ix ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.mkIx E.2
        let c ← IO.mkRef (Array.replicate 8 0)
        let tp0 ← IO.monoMsNow
        let lim := ((← IO.getEnv "KM_SRI_PROF_S").bind String.toNat?).getD 100000
        let st0 ← IO.lazyPure fun _ => (ContextCalculus.SRI.Proc.roots rq).foldl
          (ContextCalculus.SRI.Proc.addSeed E.2 ix) ContextCalculus.SRI.Proc.St.empty
        let tp1 ← IO.monoMsNow
        let st ← profLoop E.2 ix st0 c (tp0 + 1000 * lim)
        let tp2 ← IO.monoMsNow
        let g (i : Nat) : IO Nat := return (← c.get)[i]!
        IO.eprintln s!"prof roots_ms={tp1-tp0} loop_ms={tp2-tp1} records={st.seen.size} steps={← g 0} seeds_listed={← g 2} seed_hits={← g 3} distinct_seeds={st.seeds.size}"
        IO.eprintln s!"prof seedsOf_ms={(← g 1)/1000000} expand_ms={(← g 4)/1000000} fwd_ms={(← g 5)/1000000} demands={← g 6} sum_ctx={← g 7}"
        let recs := st.seen.toList
        IO.eprintln s!"prof max_K={recs.foldl (fun a r => max a r.K.card) 0} max_A={recs.foldl (fun a r => max a r.A.card) 0} max_t={recs.foldl (fun a r => max a r.t.card) 0} sum_t={recs.foldl (fun a r => a + r.t.card) 0}"
        return 0
      if (← IO.getEnv "KM_SRI_COUNT") == some "1" then
        -- `IO.lazyPure` keeps each phase at its place between the clock reads.
        let E := ContextCalculus.SRI.Proc.encTrans T.ontology
        let rq := sriRequest T E.1
        let ix ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.mkIx E.2
        let tc0 ← IO.monoMsNow
        let c ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.candidates E.2 ix rq
        IO.eprintln s!"candidates={c.length} cand_ms={(← IO.monoMsNow) - tc0}"
        let te0 ← IO.monoMsNow
        let kI ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.ctxIdxI c
        let te1 ← IO.monoMsNow
        let A := ContextCalculus.SRI.Proc.withBack ix c
        let sp ← IO.lazyPure fun _ => c.zipIdx.map fun q => (q.2, ContextCalculus.SRI.Proc.supportsI ix A kI q.1)
        let te2 ← IO.monoMsNow
        let el ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.elimLoop sp
        let te3 ← IO.monoMsNow
        IO.eprintln s!"elim ctxIdx_ms={te1-te0} supports_ms={te2-te1} loop_ms={te3-te2} alive={el.length} supports={sp.foldl (fun a p => a + p.2.foldl (fun b l => b + l.length) 0) 0}"
        let te0 ← IO.monoMsNow
        let al ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.elimI ix c
        IO.eprintln s!"alive={al.length} elim_ms={(← IO.monoMsNow) - te0}"
        let tr0 ← IO.monoMsNow
        let rows ← IO.lazyPure fun _ =>
          let hIdx := ContextCalculus.SRI.Proc.hashIdx al
          rq.map fun a =>
            match hIdx.get a with
            | [] => (1, 0)
            | q :: rest => (0, (ContextCalculus.SRI.Proc.meetH (ContextCalculus.SRI.Proc.toL q.1) rest).length)
        IO.eprintln s!"readout_unsat={rows.foldl (· + ·.1) 0} readout_sups={rows.foldl (· + ·.2) 0} readout_ms={(← IO.monoMsNow) - tr0}"
        let tf0 ← IO.monoMsNow
        let cf ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.classifyF E.2 rq
        IO.eprintln s!"classifyF_rows={cf.length} classifyF_unsat={(cf.filter (·.2.isNone)).length} classifyF_ms={(← IO.monoMsNow) - tf0}"
        let tsz := c.foldl (fun acc r => max acc r.t.card) 0
        IO.eprintln s!"max_type={tsz}"
        let ks := (c.map fun r => ContextCalculus.SRI.Proc.toL r.K).eraseDups
        let as := c.foldl (fun acc r => max acc (ContextCalculus.SRI.Proc.toL r.A).length) 0
        IO.eprintln s!"records={c.length} contexts={ks.length} max_aug={as} fresh={E.1}"
      if (← IO.getEnv "KM_SRI_ROUTE") == some "1" then
        let r0 ← IO.monoMsNow
        let T2 ← IO.lazyPure fun _ => translateSRI O req
        let r1 ← IO.monoMsNow
        match T2 with
        | none => pure ()
        | some T2 =>
          let E := ContextCalculus.SRI.Proc.encTrans T2.ontology
          let rq ← IO.lazyPure fun _ => sriRequest T2 E.1
          let r2 ← IO.monoMsNow
          let cf ← IO.lazyPure fun _ => ContextCalculus.SRI.Proc.classifyF E.2 rq
          let r3 ← IO.monoMsNow
          let rows ← IO.lazyPure fun _ => sriRows T2 cf
          let r4 ← IO.monoMsNow
          IO.eprintln s!"route translate_ms={r1-r0} enc_req_ms={r2-r1} classifyF_ms={r3-r2} rows_ms={r4-r3} rows={rows.length}"
      let t2b ← IO.monoMsNow
      match (← IO.lazyPure fun _ => owlSRIReference O req) with
      | none => IO.eprintln "declined (chains)"; return 3
      | some a =>
        let total := a.rows.foldl (fun s r => s + r.sups.length) 0
        let t3 ← IO.monoMsNow
        IO.println s!"rows={a.rows.length} sups={total} route_ms={t3-t2b}"
        return 0
