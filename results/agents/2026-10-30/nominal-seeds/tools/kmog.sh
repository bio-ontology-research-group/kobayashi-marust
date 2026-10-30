#!/bin/bash
# km wrapper that hides the :OBJ guard class from the classification output.
"$KMOG_BIN" "$@" | grep -v ':OBJ'
exit ${PIPESTATUS[0]}
