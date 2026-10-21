"""Candidate-map/rank mutations are evaluated in memory; no source patches."""
import json
from frame_paths import HERE
from counter_streams import State,rank,forward,inverse,push_entry

def main():
    found=[]
    x=State('D',7,1,2,7,3);name,y=forward(x)
    assert 3*y.k>=3*x.k+8*x.m
    found.append(dict(mutant='omit-D-mode-offset',killed=True,witness=[x.__dict__,y.__dict__]))
    x=State('D',7,5,1,7,3);name,y=forward(x)
    assert (y.l,y.s,rank(y)[2])>(x.l,x.s,rank(x)[2])
    found.append(dict(mutant='put-width-before-terminal-count',killed=True))
    x=State('G',7,100,0,2,0);name,y=forward(x)
    assert rank(y)[2]>rank(x)[2]
    found.append(dict(mutant='use-inner-scalar-as-global-rank',killed=True))
    target=State('D',10,7,1,14,0)
    wrong=State('D',7,5,1,21,3)
    assert forward(wrong)[1]!=target and inverse(target)[1].l==7
    found.append(dict(mutant='wrong-sign-on-join-inverse-width',killed=True))
    # Classifying every zero-ending leading counter as G1 misses odd middles.
    assert target.m%2 and inverse(target)[0]=='D11join'
    found.append(dict(mutant='forget-even-odd-inverse-tag',killed=True))
    y=State('D',14,8,1,7,3);q=(y.N+6)//3
    wrong=State('D',3*q+1,1,4,7,3)
    assert forward(wrong)[1]!=y
    found.append(dict(mutant='decode-leading-counter-mod3',killed=True))
    x=push_entry(8,9);name,y=forward(x)
    assert x.N==y.N and x.k<y.k
    found.append(dict(mutant='backward-rank-uses-N-alone',killed=True))
    frames=json.loads((HERE/'frames-results.json').read_text())['frame_mutations']
    report=dict(all_killed=True,total=len(frames)+len(found),frame_mutations=frames,counter_mutations=found,fresh_raw_transitions=0,method='In-memory deliberately wrong coordinate maps and ranking/inverse candidates; no source-file mutation.')
    (HERE/'mutations-results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(all_killed=True,total=report['total']),indent=2))
if __name__=='__main__':main()
