"""Reproduce the fixed exploratory r=1 screen, separate from rule validation."""
from __future__ import annotations
import json
from pathlib import Path
from reference import OPS


def probe(a,c):
    bits='01'*a+'10'*c+'11'
    tape={i:1 for i,b in enumerate(bits) if b=='1'};q=2;h=0;status='budget'
    for t in range(1,200001):
        op=OPS[q][tape.get(h,0)]
        if op is None:status='halt';t-=1;break
        v,m,q=op
        if v:tape[h]=1
        else:tape.pop(h,None)
        h+=m
        if t>2*a+15 and q==2 and h<=min(tape,default=h):status='section';break
    word=''.join(str(tape.get(i,0)) for i in range(h,max(tape,default=h)+1)) if status=='section' else None
    pos=0;parts=[]
    while word and pos<len(word):
        candidates=[]
        for w in ('01','10','1','0'):
            n=0
            while word.startswith(w,pos+n*len(w)):n+=1
            if n:candidates.append((n*len(w),-len(w),w,n))
        _,_,w,n=max(candidates);parts.append([w,n]);pos+=n*len(w)
    return {'a':a,'c':c,'status':status,'transitions':t,'head':h,'target_parts':parts,'target_literal':word}


def main():
    root=Path(__file__).resolve().parent
    actual=[probe(a,c) for a in range(5,13) for c in range(1,9)]
    expected=json.loads((root/'remaining-tail-probes.json').read_text())['rows']
    assert actual==expected,'Historical exploratory probes differ'
    print('Reproduced all',len(actual),'exploratory raw endpoints at the original limits.')


if __name__=='__main__':main()
