"""Source-axiom deletion for classification-only explanation adapters."""
import base64
from pathlib import Path


def load_export(directory):
    directory=Path(directory)
    if (directory/'COMPLETE').read_text()!='source axiom roundtrip passed\n':
        raise ValueError('unverified source export')
    lines=(directory/'axioms.tsv').read_text().splitlines()
    if not lines or lines[0]!='M\tschema\t1' or lines[-1]!='Z\tcomplete':
        raise ValueError('incomplete axiom export')
    axioms=[]
    for line in lines[1:-1]:
        kind,index,encoded=line.split('\t')
        if kind!='A' or int(index)!=len(axioms):raise ValueError('invalid axiom ordering')
        axioms.append(base64.b64decode(encoded,validate=True).decode('utf-8'))
    return (directory/'background.ofn-fragment').read_text(),axioms


def render(background, axioms, indices):
    return 'Ontology(\n'+background+'\n'.join(axioms[i] for i in indices)+'\n)\n'


def minimize(count, oracle):
    """Each oracle must return a definitive bool; errors abort the explanation."""
    checks=0
    def entails(indices):
        nonlocal checks
        answer=oracle(tuple(indices));checks+=1
        if type(answer) is not bool:raise ValueError('oracle did not return definitive entailment')
        return answer
    active=list(range(count))
    if not entails(active):raise ValueError('full module does not entail query')
    for index in range(count):
        trial=[i for i in active if i!=index]
        if entails(trial):active=trial
    if not entails(active):raise ValueError('final support lost entailment')
    return active,checks
