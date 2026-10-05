"""Compare source-bound canonical outputs without promoting unknown consistency."""
import argparse
import json
from pathlib import Path


def compare(left, right):
    for record in (left, right):
        if record.get('status') != 'ok':
            raise ValueError('canonicalization did not succeed')
        for key in ('source_sha256', 'source_signature_sha256', 'relation_sha256',
                    'raw_sha256', 'strict_adapter_sha256', 'fingerprint_script_sha256'):
            value = record.get(key)
            if not isinstance(value, str) or len(value) != 64 or any(c not in '0123456789abcdef' for c in value):
                raise ValueError('missing or invalid hash: ' + key)
        if 'reported_consistency' not in record or record['reported_consistency'] is not None and type(record['reported_consistency']) is not bool:
            raise ValueError('invalid reported consistency')
    for key in ('source_sha256', 'source_signature_sha256', 'algorithm', 'fingerprint_script_sha256'):
        if left.get(key) != right.get(key):
            raise ValueError('incompatible comparison: ' + key)
    a, b = left['reported_consistency'], right['reported_consistency']
    output = {'source_sha256': left['source_sha256'],
              'left_raw_sha256': left['raw_sha256'], 'right_raw_sha256': right['raw_sha256'],
              'left_consistency': a, 'right_consistency': b}
    if a is not None and b is not None and a != b:
        return dict(output, status='consistency_disagreement', agreement=False)
    if a is False and b is False:
        return dict(output, status='inconsistent_agreement', agreement=True, scope='consistency')
    if a is False or b is False:
        return dict(output, status='incomparable_unknown_consistency', agreement=None)
    equal = left['relation_sha256'] == right['relation_sha256']
    if a is None or b is None:
        return dict(output, status='conditional_taxonomy_agreement' if equal else 'conditional_taxonomy_disagreement',
                    agreement=None, taxonomy_agreement=equal, scope='taxonomy conditional on consistency')
    return dict(output, status='agreement' if equal else 'taxonomy_disagreement',
                agreement=equal, scope='consistency_and_taxonomy')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('left', type=Path)
    parser.add_argument('right', type=Path)
    args = parser.parse_args()
    print(json.dumps(compare(json.loads(args.left.read_text()), json.loads(args.right.read_text())), indent=2))
