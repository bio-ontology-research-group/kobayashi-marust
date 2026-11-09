#!/bin/bash
# self_ab.sh BIN : the SELF family, after (BIN) and before (BIN with the old refusal).
T=$(dirname $(readlink -f $0))
$T/seeds.sh $1 self-after
DIFF_EXTRA=KM_BRIDGE_SAT_REFUSE_SELF=1 $T/seeds.sh $1 self-before
