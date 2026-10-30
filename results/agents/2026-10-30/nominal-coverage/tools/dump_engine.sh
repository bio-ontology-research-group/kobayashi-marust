#!/bin/bash
# KM_ENGINE stand-in: keep the first CB engine input in $DUMP_TO, then fail.
if [ ! -e "$DUMP_TO" ]; then cat > "$DUMP_TO"; else cat > /dev/null; fi
exit 1
