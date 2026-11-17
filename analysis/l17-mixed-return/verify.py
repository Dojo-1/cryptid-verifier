"""Declarative critic and separate literal replay; no return-actor import."""
import json,gzip,hashlib
from paths import HERE
from specification import integer,materialize,agrees
from raw import replay
def main():
    rows=json.loads((HERE/'claims.json').read_text())['rules'];cases=json.loads((HERE/'cases.json').read_text())
    with gzip.open(HERE/'raw-results.jsonl.gz','rt') as f:actual=[json.loads(x) for x in f]
    assert len(cases)==len(actual);traces=0
    for c,r in zip(cases,actual):
        m=c['metadata']
        if 'rule' in m:
            row=rows[m['rule']];p=m['p'];v=m['v']
            def render(x):return ''.join(w*n for w,n in materialize(x,p,v))
            assert c['source']==m['pad']+render(row['source'])+m['extra'];assert c['target']==m['pad']+render(row['target'])+m['extra'];assert c['steps']==integer(row['steps'],p)
            assert c['q']==row['source_q'] and c['qq']==row['target_q'];assert c['head']==integer(row['shift'],p)
        py=replay(dict(q=c['q'],head=0,limit=c['steps'],ones=[c['start']+i for i,b in enumerate(c['source']) if b=='1']))
        expected=dict(q=c['qq'],head=c['head'],steps=c['steps'],halted=False,ones=[c['target_start']+i for i,b in enumerate(c['target']) if b=='1'])
        assert agrees(r,expected) and agrees(py,expected)
        if c['steps']<=1000:assert r['reads']==py['reads'];traces+=1
    corners=json.loads((HERE/'named-corner-cases.json').read_text())
    with gzip.open(HERE/'named-corners-raw.jsonl.gz','rt') as f:corner_raw=[json.loads(x) for x in f]
    assert len(corners)==len(corner_raw)
    for c,r in zip(corners,corner_raw):
        m=c['metadata'];p=m['p'];cc=m['c'];v=m['v'];a=p+1
        assert c['target']=='1'*(2*p-6)+'01'*(cc+12)+'11'+v
        assert c['steps']==(4*a+6*cc+152 if m['embedded'] else 2*p+4*cc+126)
        py=replay(dict(q=c['q'],head=0,limit=c['steps'],ones=[c['start']+i for i,b in enumerate(c['source']) if b=='1']))
        expected=dict(q=2,head=c['head'],steps=c['steps'],halted=False,ones=[c['target_start']+i for i,b in enumerate(c['target']) if b=='1'])
        assert agrees(r,expected) and agrees(py,expected);assert r['reads']==py['reads']
    out=dict(passed=True,main_cases=len(cases),supplementary_cases=len(corners),total_endpoints=len(cases)+len(corners),main_full_traces=traces,supplementary_full_traces=len(corners),claims_sha256=hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest(),scope='Separate literal and declarative code paths,same author;not an external reproduction or Lean build.')
    (HERE/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
