#!/usr/bin/python3.9
"""Capture the existing consistency worker's input and stderr, then exec it.

This diagnostic adds I/O and therefore cannot supply acceptance timings.
"""
import hashlib
import os
from pathlib import Path
import sys

binary = Path(os.environ['KM_RULES_TRACE_BINARY'])
assert hashlib.sha256(binary.read_bytes()).hexdigest() == os.environ['KM_RULES_TRACE_SHA256']
destination = Path(os.environ['KM_RULES_TRACE_DIR'])
stem = 'rules-worker-' + str(os.getpid())
source = destination / (stem + '.json')
with source.open('xb') as output:
    while True:
        block = sys.stdin.buffer.read(65536)
        if not block:
            break
        output.write(block)
with source.open('rb') as input_file:
    os.dup2(input_file.fileno(), 0)
with (destination / (stem + '.stderr')).open('xb') as error_file:
    os.dup2(error_file.fileno(), 2)
os.execv(str(binary), [str(binary), 'tableau', *sys.argv[1:]])
