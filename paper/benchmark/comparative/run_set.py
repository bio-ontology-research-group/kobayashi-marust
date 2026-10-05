"""Explicit measurement receipts selected for a comparative audit."""
import json
from pathlib import Path

DEFAULT = {
    'inventory': 'artifact-inventory-v145-candidate.json',
    'classification': '53200614', 'classification_km': '53201541', 'classification_konclude': '53201252',
    'updates_java': '53201374', 'updates_km': '53201943', 'updates_native': '53201456',
    'updates_whelk': '53204205', 'updates_konclude': '53202853', 'retained_konclude': '53203235',
    'justifications_km': '53201976', 'justifications_java': '53201375', 'justifications_native': '53201976',
    'justifications_external': '53203745', 'justifications_whelk': '53204206',
    'updates_preparation': '53201177', 'queries_preparation': '53201195',
}

def load(root, filename=None):
    values=dict(DEFAULT)
    if filename:
        overrides=json.loads((Path(root)/filename).read_text())
        if set(overrides)-set(DEFAULT):raise ValueError('unknown run-set fields')
        if any(not isinstance(value,str) or not value for value in overrides.values()):raise ValueError('invalid run-set value')
        values.update(overrides)
    return values
