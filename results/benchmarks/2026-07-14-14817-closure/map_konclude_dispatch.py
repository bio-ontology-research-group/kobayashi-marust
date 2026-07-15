#!/usr/bin/env python3
import json
import re
import sys

log_path, tin_path = sys.argv[1:3]
names = []
with open(log_path, encoding="utf-8", errors="replace") as stream:
    for line in stream:
        if "KCLASSDBG satisfiable dispatch" not in line:
            continue
        names.append(re.search(r"class=(.*)$", line).group(1).strip())
        if len(names) == 184:
            break
with open(tin_path, encoding="utf-8") as stream:
    tin = json.load(stream)
indices = {name: index for index, name in enumerate(tin["concepts"])}

def local_name(iri):
    return iri.rsplit("#", 1)[-1].rsplit("/", 1)[-1]

mapped = [indices.get(local_name(name)) for name in names]
print(f"count={len(mapped)} missing={sum(index is None for index in mapped)}")
print(",".join(str(index) for index in mapped if index is not None))
