#!/usr/bin/env bash
exec cc "$@" -Wl,--defsym=pidfd_spawnp=0 -Wl,--defsym=pidfd_getpid=0
