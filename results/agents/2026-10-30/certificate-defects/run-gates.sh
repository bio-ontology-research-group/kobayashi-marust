#!/usr/bin/env bash
# Run the five certification gates end to end on fix/v155-certificate-defects.
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work
R=$W/worktrees/fix-certificate-defects
S=$W/agent-scratch/certificate-defects/gates
mkdir -p $S
export KM_WORK_ROOT=$W/agent-scratch/certificate-defects/gate
export KM_CERT_KEEP_NATIVE_CHECKERS=1
export LEAN_STACK_SIZE_KB=262144
export PATH=$HOME/.elan/bin:$PATH
for gate in ${GATES:-elc cb ht routing rules}; do
  for attempt in 1 2 3; do
    start=$(date +%s)
    bash $R/lean/run-$gate-certification-gate.sh > $S/$gate.log 2>&1
    rc=$?
    end=$(date +%s)
    echo "$gate attempt $attempt rc=$rc $((end-start))s: $(tail -1 $S/$gate.log)"
    [ $rc = 0 ] && break
    grep -q "failed to create thread\|resource exhausted\|cannot allocate" $S/$gate.log || break
    cp $S/$gate.log $S/$gate.attempt$attempt.log
    sleep 30
  done
done
echo gates-done
