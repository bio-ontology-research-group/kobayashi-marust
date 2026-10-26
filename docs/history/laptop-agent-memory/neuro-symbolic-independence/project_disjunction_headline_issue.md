---
name: project_disjunction_headline_issue
description: "NeSy paper's headline Disjunction-SROIQ JustWMC result is unreproducible / overclaimed; mixture does not genuinely spread"
metadata: 
  node_type: memory
  type: project
  originSessionId: 8013a140-9c7d-4310-a78e-c7c6c789bcd4
---

CRITICAL finding (2026-06-03) on the NeSy paper's central RS-genuine experiment (sroiq-nesy, Table tab:disjunction, sec:exp:disjunction). See [[project_nesy2026_revision_plan]].

**The paper claims** JustWMC latent NLL **7.71** (Brier 0.097, mode_acc 1.00), framed as "mixture-of-UCI spreads calibrated mass across the 4 RS modes, which single-UCI cannot."

**Reality, verified by fresh epochs=40 reruns on the local GPU:**
- Independent reproduces EXACTLY (NLL 7.12, mode_acc 0). WMC roughly (17.8 vs paper 20.13).
- The COMMITTED `train_just_wmc` (kappa=0.5, no selector entropy) gives JustWMC NLL **18.1** (mode_acc 1.0, gt_match 0.39) -- WORSE than Independent. Git history: the runner was committed once (May 31 reorg); "7.71" appears ONLY in main.tex, never in any committed result file. So the paper number was never produced by committed code.
- Root cause of collapse: the objective `-log sum_k pi_k WMC(mu_k)` is MINIMIZED by one confident on-constraint head, so the learned selector pi collapses (pi -> [~0,0.9,0,0]); gt_match always equals the eval-set majority-mode frequency (= the collapse signature).

**What the regularized variants give (added train_ours in experiments/run_disjunction_multiseed.py, with selector-entropy + stronger KL diversity):**
- kappa=2,eta=1: NLL 8.09, Brier 0.090, mode_acc 1.0, gt_match 0.39, jWMC 0.20, ECE 0.445, mode-cov-TV 0.75 == roughly the PAPER's numbers, but RS metrics show it is SMOOTHED single-mode collapse, not spread.
- kappa=3,eta=3: NLL 5.60, jWMC 0.14, mode_acc 0.84 -- partial.
- fix_pi (uniform mixture): NLL 5.77, ECE 0.219 (best calib) BUT jWMC 0.052, mode_acc 0.00 -- DEGENERATE "predict 0.5 everywhere" (= Independent behavior), not crisp modes.

**Conclusion:** the paper's NUMBERS are ~reproducible only as calibration-via-smoothing; the INTERPRETATION (genuine multimodal joint / mass on all 4 modes) is NOT supported by any configuration tried. There is a fundamental tension: mode_acc=1.0 (committed argmax) and calibrated NLL->4.16 (uncommitted 0.5 marginal) cannot both hold for a mixture of factorised heads under these metrics. thm:rsia is a REPRESENTABILITY result; LEARNABILITY of genuine spread is the open gap. The new RS metrics (concept-ECE, mode-coverage-TV, jWMC) are what expose this.

Multiseed driver, rs_metrics.py, baselines (Independent/SemanticLoss/DeepProbLog-equiv/ours/BEARS) all built and validated; #RS=4 confirmed from the SDD. User chose "Both: reframe now, attempt genuine."

**RESOLVED (2026-06-03), run on unimatrix01 (cluster), 5 seeds, epochs=40. Final Disjunction-SROIQ table (mean±std):**
- Independent: NLL 6.94±0.25, Brier 0.10, cECE 0.23, modeTV 1.00, modeAcc 0.00 (incoherent: low NLL but predictions not valid modes)
- SemanticLoss: NLL 17.75±1.32, cECE 0.50, modeTV 0.75, modeAcc 1.00 (single-mode collapse, confidently wrong = RS pathology)
- DeepProbLog-equiv: NLL 17.67±1.34 (== SemanticLoss; both factorised+WMC)
- ours (gradient mixture, kappa=2/eta=1): NLL 10.77±3.97, cECE 0.43, modeTV 0.75, modeAcc 1.00 (less overconfident but does NOT genuinely spread -> LEARNABILITY GAP)
- BEARS: NLL 8.32±4.21, modeTV 0.52 (smears off-constraint)
- **constructed (heads ANCHORED to SDD-enumerated modes, uniform pi): NLL 4.17±0.00 == Bayes-opt 6log2=4.159, Brier 0.00, cECE 0.00, modeTV 0.02** -- GENUINE calibrated multimodal posterior, deterministic across seeds.

**Honest narrative (stronger than original paper):** single-UCI collapses (RS); gradient-trained mixtures can't learn the multimodal joint (representability != learnability, cf van Krieken 2024 disconnected landscape); but the SDD's symbolic structure lets us CONSTRUCT the RS-aware mixture (constructive realization of thm:rsia) that achieves the Bayes-optimal calibrated posterior. NOTE: mode_acc is the WRONG metric for a genuinely-spread model (marginal=0.5 -> argmax ambiguous -> mode_acc 0 is CORRECT); jWMC over the full 69-atom dist is low for `constructed` only because ~52 auxiliary atoms are left unconstrained (latent metrics NLL/TV/ECE/Brier are the meaningful ones). Method `train_anchored` + method name "constructed" in experiments/run_disjunction_multiseed.py. Results on cluster ~/sroiq-rerun/results/disj_*.json.
