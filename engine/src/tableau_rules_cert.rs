//! Lean certificates for the rule-route answers (`KM_RULES_LEAN_CERT`).
//!
//! The rule worker's `Tableau` records, while it searches, the closed tableau
//! of every failed test (a refutation) and turns the completion graph of every
//! successful test into a finite interpretation (a model). The document
//! written here is checked by `lean/RulesCertCheck.lean`
//! (`WireRulesCertificate.check_sound`, docs/DL-SAFE-RULES.md "Lean
//! coverage"). Nothing in this module decides an answer: a missing or
//! rejected certificate makes the worker fail closed.
//!
//! Recording follows the careful (merge-capable) expansion exactly: every
//! Horn firing, nominal merge and fresh witness becomes a step; a branch
//! closes on a clash or an empty-head clause; a disjunction becomes a split
//! with one child per head atom in clause order. Loop-back alternatives of
//! the pairwise path are dropped from refutations, since the fresh-successor
//! alternative alone is a sound step.

use super::*;
use serde::Serialize;

#[derive(Clone, Debug)]
pub(crate) enum RStep {
    Horn { clause: usize, asg: Vec<usize> },
    Witness { node: usize, role: R, fil: CLit },
    Nominal { concept: C, left: usize, right: usize },
}

#[derive(Clone, Debug)]
pub(crate) enum REnd {
    Clash { node: usize, concept: C },
    Bottom { clause: usize, asg: Vec<usize> },
    Split { clause: usize, asg: Vec<usize>, children: Vec<RProof> },
    /// The search failed in a way the recorder did not capture.
    Invalid,
}

#[derive(Clone, Debug)]
pub(crate) struct RProof {
    pub steps: Vec<RStep>,
    pub end: REnd,
}

impl RProof {
    fn valid(&self) -> bool {
        match &self.end {
            REnd::Invalid => false,
            REnd::Split { children, .. } => children.iter().all(RProof::valid),
            _ => true,
        }
    }
    fn size(&self) -> usize {
        self.steps.len() + 1 + match &self.end {
            REnd::Split { children, .. } => children.iter().map(RProof::size).sum(),
            _ => 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Claim {
    Inconsistent,
    Unsat(C),
    Sub(C, C),
}

impl Claim {
    pub(crate) fn root(self) -> Vec<CLit> {
        match self {
            Claim::Inconsistent => vec![],
            Claim::Unsat(a) => vec![CLit::pos(a)],
            Claim::Sub(a, b) => vec![CLit::pos(a), CLit::neg(b)],
        }
    }
}

/// A finite interpretation in the wire layout of `WireModel`.
#[derive(Clone, Debug, Default)]
pub(crate) struct FModelOut {
    pub labels: Vec<Vec<C>>,
    pub succ: Vec<Vec<(R, usize)>>,
    /// Map from completion-graph node to model element (the test root).
    pub root: usize,
}

/// The recorder state of one test plus the evidence of all tests.
#[derive(Default)]
pub(crate) struct CertSink {
    pub steps: Vec<RStep>,
    pub finish: Option<REnd>,
    pub last: Option<RProof>,
    pub last_disjunction: Option<usize>,
    pub refutations: Vec<(Claim, RProof)>,
    pub models: Vec<(FModelOut, Vec<(C, usize)>)>,
    /// Answers without a certificate: the reason for each.
    pub uncertified: Vec<String>,
}

impl Tableau {
    pub(super) fn rec_on(&self) -> bool {
        self.cert.is_some()
    }

    pub(super) fn rec_mark(&self) -> usize {
        self.cert.as_ref().map_or(0, |c| c.lock().unwrap().steps.len())
    }

    pub(super) fn rec_step(&self, step: RStep) {
        if let Some(c) = &self.cert {
            c.lock().unwrap().steps.push(step);
        }
    }

    pub(super) fn rec_asg(&self, g: &Graph, cl: &Clause, subst: &Subst) -> Vec<usize> {
        let max = clause_vars(cl).into_iter().max().map_or(0, |v| v as usize + 1);
        (0..max).map(|v| subst.get(v as Var).map_or(0, |n| g.find(n))).collect()
    }

    pub(super) fn rec_horn(&self, g: &Graph, ci: usize, cl: &Clause, subst: &Subst) {
        if self.rec_on() {
            let asg = self.rec_asg(g, cl, subst);
            self.rec_step(RStep::Horn { clause: ci, asg });
        }
    }

    pub(super) fn rec_bottom(&self, g: &Graph, ci: usize, cl: &Clause, subst: &Subst) {
        if let Some(c) = &self.cert {
            let asg = self.rec_asg(g, cl, subst);
            c.lock().unwrap().finish = Some(REnd::Bottom { clause: ci, asg });
        }
    }

    pub(super) fn rec_clash(&self, g: &Graph) {
        if let Some(c) = &self.cert {
            let found = (0..g.n()).filter(|&n| g.alive(n)).find_map(|n| {
                g.concepts[n]
                    .iter()
                    .find(|l| !l.neg && g.concepts[n].contains(&l.complement()))
                    .map(|l| (n, l.c))
            });
            c.lock().unwrap().finish = Some(match found {
                Some((node, concept)) => REnd::Clash { node, concept },
                None => REnd::Invalid,
            });
        }
    }

    /// Close the current proof node: steps since `mark` plus the recorded end.
    pub(super) fn rec_close(&self, mark: usize) {
        if let Some(c) = &self.cert {
            let mut c = c.lock().unwrap();
            let len = c.steps.len();
            let steps = c.steps.split_off(mark.min(len));
            let end = c.finish.take().unwrap_or(REnd::Invalid);
            c.last = Some(RProof { steps, end });
        }
    }

    pub(super) fn rec_take_last(&self) -> RProof {
        self.cert
            .as_ref()
            .and_then(|c| c.lock().unwrap().last.take())
            .unwrap_or(RProof { steps: Vec::new(), end: REnd::Invalid })
    }

    pub(super) fn rec_split(&self, mark: usize, clause: usize, asg: Vec<usize>, children: Vec<RProof>) {
        if let Some(c) = &self.cert {
            let mut c = c.lock().unwrap();
            let len = c.steps.len();
            let steps = c.steps.split_off(mark.min(len));
            c.last = Some(RProof { steps, end: REnd::Split { clause, asg, children } });
        }
    }

    /// A deterministic continuation failed: prefix its proof with the steps
    /// recorded since `mark`.
    pub(super) fn rec_prepend(&self, mark: usize) {
        if let Some(c) = &self.cert {
            let mut c = c.lock().unwrap();
            let len = c.steps.len();
            let mut steps = c.steps.split_off(mark.min(len));
            let last = c.last.take().unwrap_or(RProof { steps: Vec::new(), end: REnd::Invalid });
            steps.extend(last.steps);
            c.last = Some(RProof { steps, end: last.end });
        }
    }

    fn rec_reset(&self) {
        if let Some(c) = &self.cert {
            let mut c = c.lock().unwrap();
            c.steps.clear();
            c.finish = None;
            c.last = None;
        }
    }

    /// `find_model` with the evidence of its verdict recorded for `claim`
    /// (refuted) or, on success, a finite model whose element for the test
    /// root carries `witness`.
    pub(crate) fn cert_test(&self, claim: Claim, witness: Option<C>) -> Option<Graph> {
        let root = claim.root();
        if !self.rec_on() {
            return self.find_model(&root);
        }
        self.rec_reset();
        let found = self.find_model(&root);
        let mut evidence = None;
        match &found {
            None => {
                let proof = self.rec_take_last();
                if proof.valid() {
                    evidence = Some(Err((claim, proof)));
                } else {
                    self.cert_uncertified(format!("{claim:?}: refutation not recorded"));
                }
            }
            Some(g) => match self.finite_model(g) {
                Some(model) => {
                    let mut ws = Vec::new();
                    if let Some(a) = witness {
                        ws.push((a, model.root));
                    }
                    evidence = Some(Ok((model, ws)));
                }
                None => self.cert_uncertified(format!(
                    "{claim:?}: the completion graph does not fold to a finite model"
                )),
            },
        }
        if let Some(c) = &self.cert {
            let mut c = c.lock().unwrap();
            c.steps.clear();
            c.last = None;
            match evidence {
                Some(Err(r)) => c.refutations.push(r),
                Some(Ok(m)) => c.models.push(m),
                None => {}
            }
        }
        found
    }

    pub(crate) fn cert_uncertified(&self, reason: String) {
        if let Some(c) = &self.cert {
            c.lock().unwrap().uncertified.push(reason);
        }
    }

    /// The completion graph as a finite interpretation: first as it is, then
    /// with every blocked node folded onto its blocker. `None` when neither
    /// satisfies the clauses.
    fn finite_model(&self, g: &Graph) -> Option<FModelOut> {
        let clauses: Vec<&Clause> = self.clauses.iter().map(|i| &i.cl).collect();
        let plain = graph_model(g, &|n| Some(n));
        if model_satisfies(&plain, &clauses, &self.nominals) {
            return Some(plain);
        }
        // Fold: a directly blocked node whose strict ancestors are all
        // unblocked is replaced by its blocker; the rest of a blocked subtree
        // is dropped.
        let n = g.n();
        let mut redirect: Vec<Option<Node>> = (0..n).map(Some).collect();
        for s in 0..n {
            if !g.alive(s) {
                redirect[s] = None;
                continue;
            }
            let ancestors = g.ancestors(s);
            if ancestors.iter().any(|&a| self.node_blocked(g, a)) {
                redirect[s] = None;
            } else if self.node_blocked(g, s) {
                redirect[s] = self.blocker_of(g, s);
            }
        }
        let folded = graph_model(g, &|x| redirect[x]);
        if model_satisfies(&folded, &clauses, &self.nominals) {
            return Some(folded);
        }
        None
    }

    fn blocker_of(&self, g: &Graph, s: Node) -> Option<Node> {
        if !self.pairwise {
            return g.ancestors(s).into_iter().find(|&t| {
                g.blockable[t]
                    && if self.number || !self.nominals.is_empty() || self.eqblock {
                        g.concepts[s] == g.concepts[t]
                    } else {
                        g.concepts[s].is_subset(&g.concepts[t])
                    }
            });
        }
        let p = g.pred[s]?;
        let (el_ps, el_sp) = (g.edge_label(p, s), g.edge_label(s, p));
        g.ancestors(s).into_iter().find(|&s2| {
            g.blockable[s2]
                && g.pred[s2].is_some_and(|p2| {
                    g.concepts[s] == g.concepts[s2]
                        && g.concepts[p] == g.concepts[p2]
                        && el_ps == g.edge_label(p2, s2)
                        && el_sp == g.edge_label(s2, p2)
                })
        })
    }
}

/// Build a model from the alive nodes kept by `map` (node → representative
/// node, `None` = dropped). Kept nodes are those with `map(n) == Some(n)`.
fn graph_model(g: &Graph, map: &dyn Fn(Node) -> Option<Node>) -> FModelOut {
    let mut index = vec![usize::MAX; g.n()];
    let mut nodes = Vec::new();
    for n in 0..g.n() {
        if g.alive(n) && map(n) == Some(n) {
            index[n] = nodes.len();
            nodes.push(n);
        }
    }
    let target = |x: Node| -> Option<usize> {
        let x = map(g.find(x))?;
        let i = index[x];
        (i != usize::MAX).then_some(i)
    };
    let mut labels = Vec::with_capacity(nodes.len());
    for &n in &nodes {
        let mut l: Vec<C> = g.concepts[n].iter().filter(|l| !l.neg).map(|l| l.c).collect();
        l.sort_unstable();
        labels.push(l);
    }
    let mut succ: Vec<Vec<(R, usize)>> = vec![Vec::new(); nodes.len()];
    for &(r, s, t) in &g.edges {
        if !(g.alive(s) && g.alive(t)) {
            continue;
        }
        let Some(si) = index.get(s).copied().filter(|&i| i != usize::MAX && map(s) == Some(s)) else {
            continue;
        };
        if let Some(ti) = target(t) {
            succ[si].push((r, ti));
        }
    }
    for s in &mut succ {
        s.sort_unstable();
        s.dedup();
    }
    let root = target(0).unwrap_or(0);
    FModelOut { labels, succ, root }
}

/// Mirror of `FModel.check` in `RulesRouteModel.lean`: every clause holds under
/// every assignment, and every nominal names exactly one element.
pub(crate) fn model_satisfies(m: &FModelOut, clauses: &[&Clause], nominals: &[C]) -> bool {
    let n = m.labels.len();
    if n == 0 {
        return false;
    }
    let labels: Vec<HashSet<C>> = m.labels.iter().map(|l| l.iter().copied().collect()).collect();
    let edges: HashSet<(R, usize, usize)> = m
        .succ
        .iter()
        .enumerate()
        .flat_map(|(s, out)| out.iter().map(move |&(r, t)| (r, s, t)))
        .collect();
    let mut pred: Vec<Vec<(R, usize)>> = vec![Vec::new(); n];
    for &(r, s, t) in &edges {
        pred[t].push((r, s));
    }
    for &c in nominals {
        if labels.iter().filter(|l| l.contains(&c)).count() != 1 {
            return false;
        }
    }
    let lit = |d: usize, l: CLit| labels[d].contains(&l.c) != l.neg;
    let holds = |a: &Atom, asg: &[Option<usize>]| -> Option<bool> {
        Some(match a {
            Atom::Concept { lit: l, t } => lit(asg[*t as usize]?, *l),
            Atom::Role { r, s, t } => edges.contains(&(*r, asg[*s as usize]?, asg[*t as usize]?)),
            Atom::Exists { r, fil, t } => {
                m.succ[asg[*t as usize]?].iter().any(|&(rr, w)| rr == *r && lit(w, *fil))
            }
            Atom::Eq { s, t } => asg[*s as usize]? == asg[*t as usize]?,
        })
    };
    let mut budget: u64 = 200_000_000;
    fn go(
        cl: &Clause, vars: &[Var], asg: &mut Vec<Option<usize>>, n: usize,
        m: &FModelOut, pred: &[Vec<(R, usize)>],
        holds: &dyn Fn(&Atom, &[Option<usize>]) -> Option<bool>, budget: &mut u64,
    ) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        if cl.body.iter().any(|a| holds(a, asg) == Some(false)) {
            return true;
        }
        if cl.head.iter().any(|a| holds(a, asg) == Some(true)) {
            return true;
        }
        let Some((&v, rest)) = vars.split_first() else {
            return false;
        };
        let mut cands: Option<Vec<usize>> = None;
        for a in &cl.body {
            if let Atom::Role { r, s, t } = a {
                if *t == v && *s != v {
                    if let Some(sv) = asg[*s as usize] {
                        cands = Some(m.succ[sv].iter().filter(|p| p.0 == *r).map(|p| p.1).collect());
                        break;
                    }
                }
                if *s == v && *t != v {
                    if let Some(tv) = asg[*t as usize] {
                        cands = Some(pred[tv].iter().filter(|p| p.0 == *r).map(|p| p.1).collect());
                        break;
                    }
                }
            }
        }
        let cands = cands.unwrap_or_else(|| (0..n).collect());
        for d in cands {
            asg[v as usize] = Some(d);
            let ok = go(cl, rest, asg, n, m, pred, holds, budget);
            asg[v as usize] = None;
            if !ok {
                return false;
            }
        }
        true
    }
    for cl in clauses {
        let vars = clause_vars(cl);
        let width = vars.iter().max().map_or(0, |v| *v as usize + 1);
        let mut asg = vec![None; width];
        if !go(cl, &vars, &mut asg, n, m, &pred, &holds, &mut budget) {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------- wire

#[derive(Serialize)]
struct WLit {
    concept: C,
    neg: bool,
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
enum WAtom {
    Concept { literal: WLit, node: Var },
    Role { role: R, source: Var, target: Var },
    #[serde(rename = "exists_")]
    Exists { role: R, filler: WLit, node: Var },
    Eq { left: Var, right: Var },
}

#[derive(Serialize)]
struct WClause {
    body: Vec<WAtom>,
    head: Vec<WAtom>,
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
enum WStep {
    Horn { clause: usize, assignment: Vec<usize> },
    Witness { node: usize, role: R, filler: WLit },
    Nominal { concept: C, left: usize, right: usize },
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
enum WProof {
    Clash { steps: Vec<WStep>, node: usize, concept: C },
    Bottom { steps: Vec<WStep>, clause: usize, assignment: Vec<usize> },
    Split { steps: Vec<WStep>, clause: usize, assignment: Vec<usize>, children: Vec<WProof> },
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
enum WClaim {
    Inconsistent,
    Unsat { concept: C },
    Sub { sub: C, sup: C },
}

#[derive(Serialize)]
struct WRefutation {
    claim: WClaim,
    proof: WProof,
}

#[derive(Serialize)]
struct WModel {
    node_count: usize,
    labels: Vec<Vec<C>>,
    succ: Vec<Vec<(R, usize)>>,
    pred: Vec<Vec<(R, usize)>>,
    ext: Vec<Vec<usize>>,
    witnesses: Vec<(C, usize)>,
}

#[derive(Serialize)]
struct WCertificate {
    version: u32,
    oguard: C,
    nominals: Vec<C>,
    ontology: Vec<WClause>,
    queries: Vec<C>,
    consistent: bool,
    unsatisfiable: Vec<C>,
    subsumptions: Vec<(C, C)>,
    premise_subsumptions: Vec<(C, C)>,
    premise_unsatisfiable: Vec<C>,
    refutations: Vec<WRefutation>,
    models: Vec<WModel>,
}

fn wlit(l: CLit) -> WLit {
    WLit { concept: l.c, neg: l.neg }
}

fn watom(a: &Atom) -> WAtom {
    match a {
        Atom::Concept { lit, t } => WAtom::Concept { literal: wlit(*lit), node: *t },
        Atom::Role { r, s, t } => WAtom::Role { role: *r, source: *s, target: *t },
        Atom::Exists { r, fil, t } => WAtom::Exists { role: *r, filler: wlit(*fil), node: *t },
        Atom::Eq { s, t } => WAtom::Eq { left: *s, right: *t },
    }
}

fn wstep(s: &RStep) -> WStep {
    match s {
        RStep::Horn { clause, asg } => WStep::Horn { clause: *clause, assignment: asg.clone() },
        RStep::Witness { node, role, fil } => WStep::Witness { node: *node, role: *role, filler: wlit(*fil) },
        RStep::Nominal { concept, left, right } => {
            WStep::Nominal { concept: *concept, left: *left, right: *right }
        }
    }
}

fn wproof(p: &RProof) -> WProof {
    let steps = p.steps.iter().map(wstep).collect();
    match &p.end {
        REnd::Clash { node, concept } => WProof::Clash { steps, node: *node, concept: *concept },
        REnd::Bottom { clause, asg } => WProof::Bottom { steps, clause: *clause, assignment: asg.clone() },
        REnd::Split { clause, asg, children } => WProof::Split {
            steps,
            clause: *clause,
            assignment: asg.clone(),
            children: children.iter().map(wproof).collect(),
        },
        REnd::Invalid => WProof::Clash { steps, node: usize::MAX, concept: C::MAX },
    }
}

/// The published answer a certificate covers.
pub(crate) struct Answer<'a> {
    pub oguard: C,
    pub queries: &'a [C],
    pub consistent: bool,
    pub unsatisfiable: &'a [C],
    pub subsumptions: &'a [(C, C)],
    pub premise_subsumptions: &'a [(C, C)],
    pub premise_unsatisfiable: &'a [C],
}

/// Summary counts of a written certificate.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct CertStats {
    pub refutations: usize,
    pub models: usize,
    pub proof_nodes: usize,
    pub bytes: usize,
}

impl Tableau {
    /// Serialize the collected evidence for `answer`. Fails when an answer
    /// has no certificate.
    pub(crate) fn certificate_document(&self, answer: &Answer) -> Result<(Vec<u8>, CertStats), String> {
        let sink = self.cert.as_ref().ok_or("certificate recording is off")?.lock().unwrap();
        if let Some(reason) = sink.uncertified.first() {
            return Err(format!(
                "no rule-route certificate for {} answer(s); first: {reason}",
                sink.uncertified.len()
            ));
        }
        let ontology = self
            .clauses
            .iter()
            .map(|i| WClause {
                body: i.cl.body.iter().map(watom).collect(),
                head: i.cl.head.iter().map(watom).collect(),
            })
            .collect();
        let refutations: Vec<WRefutation> = sink
            .refutations
            .iter()
            .map(|(claim, p)| WRefutation {
                claim: match *claim {
                    Claim::Inconsistent => WClaim::Inconsistent,
                    Claim::Unsat(a) => WClaim::Unsat { concept: a },
                    Claim::Sub(a, b) => WClaim::Sub { sub: a, sup: b },
                },
                proof: wproof(p),
            })
            .collect();
        let models = sink
            .models
            .iter()
            .map(|(m, w)| {
                let mut pred = vec![Vec::new(); m.labels.len()];
                for (s, out) in m.succ.iter().enumerate() {
                    for &(r, t) in out {
                        pred[t].push((r, s));
                    }
                }
                let width = m.labels.iter().flatten().max().map_or(0, |c| *c as usize + 1);
                let mut ext = vec![Vec::new(); width];
                for (d, labels) in m.labels.iter().enumerate() {
                    for &c in labels {
                        ext[c as usize].push(d);
                    }
                }
                WModel {
                    ext,
                    node_count: m.labels.len(),
                    labels: m.labels.clone(),
                    succ: m.succ.clone(),
                    pred,
                    witnesses: w.clone(),
                }
            })
            .collect();
        let doc = WCertificate {
            version: 1,
            oguard: answer.oguard,
            nominals: self.nominals.clone(),
            ontology,
            queries: answer.queries.to_vec(),
            consistent: answer.consistent,
            unsatisfiable: answer.unsatisfiable.to_vec(),
            subsumptions: answer.subsumptions.to_vec(),
            premise_subsumptions: answer.premise_subsumptions.to_vec(),
            premise_unsatisfiable: answer.premise_unsatisfiable.to_vec(),
            refutations,
            models,
        };
        let bytes = serde_json::to_vec(&doc).map_err(|e| e.to_string())?;
        let stats = CertStats {
            refutations: sink.refutations.len(),
            models: sink.models.len(),
            proof_nodes: sink.refutations.iter().map(|(_, p)| p.size()).sum(),
            bytes: bytes.len(),
        };
        Ok((bytes, stats))
    }
}

/// Write the certificate to `KM_RULES_LEAN_CERT` (a `.json` file or a
/// directory) and, when `KM_RULES_LEAN_CHECKER` is set, require the Lean
/// checker to accept it. Returns `Ok(())` when certification is off.
pub(crate) fn write_and_check(t: &Tableau, answer: &Answer) -> Result<(), String> {
    let Some(target) = std::env::var_os("KM_RULES_LEAN_CERT") else {
        return Ok(());
    };
    let started = std::time::Instant::now();
    let (bytes, stats) = t.certificate_document(answer)?;
    let target = std::path::PathBuf::from(target);
    let file = if target.extension().is_some_and(|e| e == "json") {
        target
    } else {
        std::fs::create_dir_all(&target).map_err(|e| e.to_string())?;
        static NONCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let n = NONCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        target.join(format!("rules-cert-{}-{n}.json", std::process::id()))
    };
    std::fs::write(&file, &bytes).map_err(|e| e.to_string())?;
    let written = started.elapsed();
    if let Some(checker) = std::env::var_os("KM_RULES_LEAN_CHECKER") {
        let output = std::process::Command::new(&checker)
            .arg(&file)
            .output()
            .map_err(|e| format!("cannot run the rules Lean checker: {e}"))?;
        if !output.status.success() {
            return Err(format!(
                "the Lean checker rejected the rule-route certificate {}: {}",
                file.display(),
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
    }
    if std::env::var_os("KM_TIMING").is_some() || std::env::var_os("KM_TAB_STATS").is_some() {
        eprintln!(
            "KM_TIMING rules-lean-cert refutations={} models={} proof_nodes={} bytes={} write={:.3}s check={:.3}s file={}",
            stats.refutations,
            stats.models,
            stats.proof_nodes,
            stats.bytes,
            written.as_secs_f64(),
            (started.elapsed() - written).as_secs_f64(),
            file.display()
        );
    }
    Ok(())
}

/// Complete and write the certificate of a published taxonomy
/// (`KM_RULES_CLASSIFY`). Pairs and classes taken from the CB taxonomy
/// (`set_known`) become premises. Every other published subsumption and
/// unsatisfiable class needs a refutation, every satisfiable query a model
/// element, and every unpublished pair between queries a model element that
/// separates it; missing evidence is produced by one more recorded test. A
/// test whose verdict contradicts the published answer is an error.
pub(crate) fn certify_classification(
    t: &Tableau,
    oguard: C,
    queries: &[C],
    consistent: bool,
    unsat: &[C],
    subs: &[(C, C)],
    known_subs: &HashSet<(C, C)>,
    known_unsat: &HashSet<C>,
) -> Result<(), String> {
    let unsat_set: HashSet<C> = unsat.iter().copied().collect();
    let sub_set: HashSet<(C, C)> = subs.iter().copied().collect();
    let premise_subs: Vec<(C, C)> = subs.iter().copied().filter(|p| known_subs.contains(p)).collect();
    let premise_unsat: Vec<C> = unsat.iter().copied().filter(|a| known_unsat.contains(a)).collect();
    let proved = |claim: Claim| -> bool {
        let sink = t.cert.as_ref().unwrap().lock().unwrap();
        sink.refutations.iter().any(|(c, _)| *c == claim || *c == Claim::Inconsistent)
    };
    if consistent {
        for &a in unsat {
            if !known_unsat.contains(&a) && !proved(Claim::Unsat(a))
                && t.cert_test(Claim::Unsat(a), Some(a)).is_some()
            {
                return Err(format!("published unsatisfiable class {a} has a model"));
            }
        }
        for &(a, b) in subs {
            if !known_subs.contains(&(a, b)) && !proved(Claim::Sub(a, b)) && !proved(Claim::Unsat(a))
                && t.cert_test(Claim::Sub(a, b), Some(a)).is_some()
            {
                return Err(format!("published subsumption {a} ⊑ {b} has a countermodel"));
            }
        }
        for &a in queries {
            if unsat_set.contains(&a) {
                continue;
            }
            let witness_labels = |t: &Tableau| -> Vec<HashSet<C>> {
                let sink = t.cert.as_ref().unwrap().lock().unwrap();
                sink.models
                    .iter()
                    .flat_map(|(m, ws)| {
                        ws.iter()
                            .filter(move |(c, _)| *c == a)
                            .map(move |&(_, node)| m.labels[node].iter().copied().collect())
                    })
                    .collect()
            };
            let mut labels = witness_labels(t);
            if labels.is_empty() {
                if t.cert_test(Claim::Unsat(a), Some(a)).is_none() {
                    return Err(format!("satisfiable query {a} has a refutation"));
                }
                labels = witness_labels(t);
            }
            for &b in queries {
                if b == a || sub_set.contains(&(a, b)) || labels.iter().any(|l| !l.contains(&b)) {
                    continue;
                }
                if t.cert_test(Claim::Sub(a, b), Some(a)).is_none() {
                    return Err(format!("unpublished subsumption {a} ⊑ {b} is entailed"));
                }
            }
        }
    }
    write_and_check(t, &Answer {
        oguard,
        queries,
        consistent,
        unsatisfiable: unsat,
        subsumptions: subs,
        premise_subsumptions: &premise_subs,
        premise_unsatisfiable: &premise_unsat,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn con(c: C, t: Var) -> Atom {
        Atom::Concept { lit: CLit::pos(c), t }
    }

    /// 0 = O, 1 = {a}, 2 = A, 3 = B. ABox A(a), rule A(x) ∧ O(x) → B(x).
    fn rule_clauses(bottom: bool) -> Vec<Clause> {
        let mut clauses = vec![
            Clause::new(vec![con(1, 0)], vec![con(2, 0)]),
            Clause::new(vec![con(1, 0)], vec![con(0, 0)]),
            Clause::new(vec![con(2, 0), con(0, 0)], vec![con(3, 0)]),
        ];
        if bottom {
            clauses.push(Clause::new(vec![con(3, 0)], vec![]));
        }
        clauses
    }

    fn tableau(clauses: Vec<Clause>) -> Tableau {
        let mut t = Tableau::new(clauses);
        t.set_nominals(vec![1]);
        t.enable_certificates().unwrap();
        t
    }

    #[test]
    fn inconsistent_rule_input_records_a_closed_proof() {
        let t = tableau(rule_clauses(true));
        assert!(t.cert_test(Claim::Inconsistent, None).is_none());
        let sink = t.cert.as_ref().unwrap().lock().unwrap();
        assert!(sink.uncertified.is_empty());
        assert_eq!(sink.refutations.len(), 1);
        let (claim, proof) = &sink.refutations[0];
        assert_eq!(*claim, Claim::Inconsistent);
        assert!(proof.valid());
        assert!(matches!(proof.end, REnd::Bottom { clause: 3, .. }));
    }

    #[test]
    fn consistent_rule_input_records_a_model_that_satisfies_the_clauses() {
        let t = tableau(rule_clauses(false));
        assert!(t.cert_test(Claim::Unsat(2), Some(2)).is_some());
        let sink = t.cert.as_ref().unwrap().lock().unwrap();
        assert_eq!(sink.models.len(), 1);
        let (model, witnesses) = &sink.models[0];
        let clauses = rule_clauses(false);
        let refs: Vec<&Clause> = clauses.iter().collect();
        assert!(model_satisfies(model, &refs, &[1]));
        assert_eq!(witnesses, &vec![(2, model.root)]);
        // Removing B from the named element violates the rule.
        let mut broken = model.clone();
        for labels in &mut broken.labels {
            labels.retain(|&c| c != 3);
        }
        assert!(!model_satisfies(&broken, &refs, &[1]));
    }

    #[test]
    fn disjunction_records_one_child_per_head_atom() {
        // {a} ⊑ C, C ⊑ A ∨ B, A ⊑ ⊥, B ⊑ ⊥ (4 = C).
        let clauses = vec![
            Clause::new(vec![con(1, 0)], vec![con(4, 0)]),
            Clause::new(vec![con(4, 0)], vec![con(2, 0), con(3, 0)]),
            Clause::new(vec![con(2, 0)], vec![]),
            Clause::new(vec![con(3, 0)], vec![]),
        ];
        let t = tableau(clauses);
        assert!(t.cert_test(Claim::Inconsistent, None).is_none());
        let sink = t.cert.as_ref().unwrap().lock().unwrap();
        let (_, proof) = &sink.refutations[0];
        match &proof.end {
            REnd::Split { clause, children, .. } => {
                assert_eq!(*clause, 1);
                assert_eq!(children.len(), 2);
                assert!(children.iter().all(RProof::valid));
            }
            other => panic!("expected a split, got {other:?}"),
        }
    }
}
