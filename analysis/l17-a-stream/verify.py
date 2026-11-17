"""Separate result critic using the saved declarations and raw OPS only."""
import json,gzip,hashlib
from paths import HERE
from specification import integer,materialize,agrees
from raw import replay

def literal_left(runs,tokens):
    left='0'.join('10'*n for n in runs);time=shift=0
    for token in tokens:
        if token=='01':left+='10';time+=2;shift+=2
        elif token=='101':
            assert left.endswith('1010')
            left=left[:-4]+'0101010';time+=13;shift+=3
        else:raise AssertionError('bad token')
    return left,time,shift

def main():
    data=json.loads((HERE/'claims.json').read_text());cases=json.loads((HERE/'cases.json').read_text())
    with gzip.open(HERE/'raw-results.jsonl.gz','rt') as f:actual=[json.loads(x) for x in f]
    assert len(cases)==len(actual);trace_count=0
    for c,r in zip(cases,actual):
        m=c['metadata']
        if 'rule' in m:
            row=data['rules'][m['rule']];p=m['p'];v=m['v']
            def render(terms):return ''.join(w*n for w,n in materialize(terms,p,v))
            assert render(row['target'])==c['target']
            if not m['embedded']:
                assert render(row['source'])==c['source'];assert integer(row['steps'],p)==c['steps']
        elif c['label']=='scanner':
            left,t,h=literal_left(m['runs'],m['tokens'])
            assert c['target']==left+m['v'] and c['steps']==t and c['head']==h
        req=dict(q=c['q'],head=0,ones=[c['start']+i for i,b in enumerate(c['source']) if b=='1'],limit=c['steps'])
        py=replay(req)
        expected=dict(q=c['qq'],head=c['head'],steps=c['steps'],halted=False,ones=[c['target_start']+i for i,b in enumerate(c['target']) if b=='1'])
        assert agrees(r,expected) and agrees(py,expected)
        if c['steps']<=1000:assert r['reads']==py['reads'];trace_count+=1
    out=dict(passed=True,cases=len(cases),full_trace_comparisons=trace_count,scanner_critic='literal local word substitution, not the run-stack actor',claims_sha256=hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest())
    (HERE/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
