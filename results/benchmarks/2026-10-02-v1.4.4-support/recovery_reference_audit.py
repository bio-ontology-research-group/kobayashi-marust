"""Compare recovery outputs with source-bound, independently checked references."""
import hashlib
import json


def check_reference(reference, source_bytes, output_bytes):
    if hashlib.sha256(source_bytes).hexdigest() != reference['source_sha256']:
        raise ValueError('Recovery reference belongs to a different source input')
    output = json.loads(output_bytes)
    if reference['kind'] == 'checked-output-hash':
        equal = hashlib.sha256(output_bytes).hexdigest() == reference['output_sha256']
    elif reference['kind'] == 'hermit-taxonomy':
        equal = (
            output['consistent'] == reference['consistent']
            and set(output['unsatisfiable']) == set(reference['unsatisfiable'])
            and {tuple(p) for p in output['subsumptions']}
            == {tuple(p) for p in reference['subsumptions']}
        )
    else:
        raise ValueError('Unknown recovery reference kind')
    return {
        'independent_reference_kind': reference['kind'],
        'independent_source_verified': True,
        'independent_reference_equal': equal and output['dropped'] == 0,
    }
