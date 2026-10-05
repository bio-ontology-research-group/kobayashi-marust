"""Extract source supports from pinned native explanation JSON contracts."""


def support(response, baseline):
    if response.get('status') != 'entailed':
        raise ValueError('native generator did not establish entailment')
    justifications = response.get('justifications')
    if not isinstance(justifications, list) or len(justifications) != 1:
        raise ValueError('expected exactly one native justification')
    first = justifications[0]
    if baseline == 'rustdl':
        if response.get('schema_version') != 1 or response.get('laconic') is not False:
            raise ValueError('unexpected RustDL source justification schema')
        text = first.get('ofn')
        if not isinstance(text, str) or not text.strip():
            raise ValueError('missing Functional Syntax support')
        return text
    if baseline == 'km':
        if response.get('schemaVersion') != 2:
            raise ValueError('unexpected KM justification schema')
        prefixes = response.get('prefixDeclarations')
        axioms = first.get('axioms')
        if not isinstance(prefixes, list) or not all(isinstance(p, str) for p in prefixes):
            raise ValueError('missing KM prefix declarations')
        if not isinstance(axioms, list) or first.get('axiomCount') != len(axioms):
            raise ValueError('missing KM source axioms')
        if any(not isinstance(a.get('functionalSyntax'), str) for a in axioms):
            raise ValueError('missing source rendering')
        return '\n'.join(prefixes) + '\nOntology(\n' + '\n'.join(a['functionalSyntax'] for a in axioms) + '\n)\n'
    raise ValueError('unknown native justification contract')
