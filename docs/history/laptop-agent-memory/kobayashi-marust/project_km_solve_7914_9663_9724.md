---
name: project_km_solve_7914_9663_9724
description: Active plan to solve ORE 7914/9663/9724 by porting Konclude OR pipeline + saturation; Stage 0 done
metadata: 
  node_type: memory
  type: project
  originSessionId: fd362b49-8768-4405-a591-fc4dd91cbf9f
---

Plan doc in repo: `docs/SOLVE-7914-9663-9724.md` (durable, refined from approved
plan-mode plan `~/.claude/plans/recursive-dazzling-lagoon.md`). Track = `konclude_ht`
hypertableau kernel, NOT QoSat (that's [[project_km_saturation_first]] / docs/KPSET-PLAN.md).

Target order: 7914, then 9663, then 9724. Baseline 576/584 ok, 0 unsound, 5 unsolved
(3215/7914/9663/9724/14817).

**Stage 0 DONE (2026-07-11):** stale untracked s01/s10/satellites.rs deleted; failing
test `apply_representative_bind_variable_rule_creates_representative_path` was a WRONG
EXPECTATION (asserted path_prop_id 0; Konclude inits mNextVariableID=1 CProcessingDataBox.cpp:143
so first id=1; impl faithful) — fixed assertion to 1; suite now **1450 passed / 0 failed / 7 ignored** on ws.

**Decisive 7914 diagnostic:** Konclude DELAYS every disjunction (152 or-delay-queue vs
64 or-task-fork, forks alternatives=2-4) and resolves deterministically via
implication-replacement (impConcept, completion cpp 16471-16476 = the `impl` concepts
seen on subject node) + single-option CORONLYOPTION (executeORBranching cpp 16927-16957).
KM instead forks eagerly on subject 13031 (five ORs all containing tag 5229, all operands
present=false at first touch) → node explosion → defer. So **Stage 1a = OR planning
pipeline is primary**; Stage 1b (sat-cache absorption) secondary.

**Stage 1a next:** port initializeORProcessing (completion cpp 16448-16482) +
planORProcessing (16545-16724) + executeORBranching (16797-17010) +
CBranchingORProcessingRestrictionSpecification into u03.rs (plan_or_processing:1093 STUB,
initialize_or_processing:693 deviates w/ invented lazy-OR), u09.rs (apply_or_rule:627
passes INVALID spec; execute_or_branching:314 stubs has_saturated_clashed_flag=false,
real one at u22.rs:794), u34.rs (trigger install/search). 7 synthetic unit tests FIRST.
Gate: suite green + subject 13031 no choice 43541 + full 7914 on unimatrix01.

Doc uncommitted (user asked to document, not commit). See [[project_km_saturation_first]],
[[feedback_port_from_konclude]], [[feedback_no_heavy_laptop]].
