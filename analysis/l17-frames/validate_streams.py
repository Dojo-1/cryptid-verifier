"""Counter actor against frozen declarative rows, inverse and rank checks."""
import json,hashlib,random,itertools,time,sys
from dataclasses import asdict
from collections import Counter
from frame_paths import HERE,HARDENING
from counter_streams import State,forward,inverse,rank,push_entry,trace,finite_bound
from specification import Claims,equal_words


def word(x):
    return [('1',x.N),('01',x.k),('1',x.m)]*(x.mode=='D') + ([('1',x.N),('01',x.k),('0',1)] if x.mode=='G' else []) + [('01',x.l),('1',x.s)]

def check(x,claims):
    name,y=forward(x)
    if y is None:return name,None
    q=x.N//3;p=dict(q=q,k=x.k,l=x.l,s=x.s)
    if name in ('D1','D2'):p['m']=x.m
    spec=claims.instantiate(name,p,'')
    assert equal_words(word(x),spec['source']) and equal_words(word(y),spec['target']),(name,x,y)
    assert rank(y)<rank(x),(name,'rank',x,y)
    assert inverse(y)==(name,x),(name,'inverse',x,y)
    # A different, backward well-founded orientation.
    assert (x.N,x.k)<(y.N,y.k),(name,'reverse ancestry rank',x,y)
    return name,y

def main():
    began=time.monotonic();claims=Claims(HERE.parent/'l17-general-d/claims.json');rng=random.Random(21102026)
    counts=Counter();samples=0;images={};roots=0
    # Each row boundary, all source residue classes and seeded large states.
    rows=[]
    for q,k,m,l,s in itertools.product((0,1,2,3,7,25),(1,4,5,7,8,16),(1,2,3,4,5,12),(1,2,7,8,12),(0,1,2,3,6,9)):
        N=3*q+(1 if m!=2 else 2)
        if N>=2:rows.append(State('D',N,k,m,l,s))
    for q,k,l,s in itertools.product((0,1,2,3,7,25),(0,1,4,7,16),(1,2,7,8,12),(0,3,9)):
        for r in (0,1,2):
            N=3*q+r
            if N>=2:rows.append(State('G',N,k,0,l,s))
    for _ in range(4000):
        N=rng.randrange(2,81) if _<3000 else (1<<rng.randrange(128,2048))+rng.randrange(10000)
        mode=rng.choice(('D','G'));k=rng.randrange(1 if mode=='D' else 0,17);m=rng.randrange(1,13) if mode=='D' else 0
        rows.append(State(mode,N,k,m,rng.randrange(1,13),rng.randrange(10)))
    for x in rows:
        name,y=check(x,claims);counts[name]+=1;samples+=1
        if y is not None:
            if y in images:assert images[y]==x
            else:images[y]=x
        back=inverse(x)
        if back is not None:
            n,p=back;assert forward(p)==(n,x)
    root_rows=[]
    for a,c in itertools.product(range(7,81),range(7,81)):
        x=push_entry(a,c);assert inverse(x) is None;roots+=1
        if (a,c) in ((7,7),(8,7),(9,7),(11,12),(17,19)):
            chain,end,why=trace(x);assert len(chain)<=finite_bound(x)
            # Opposite stream returns to the identical root.
            y=end;steps=0
            while (back:=inverse(y)) is not None:
                _,y=back;steps+=1;assert steps<=len(chain)
            assert y==x and steps==len(chain)
            root_rows.append(dict(a=a,c=c,rows=len(chain),stop=why))
    excursions=Counter();first={};maxrows=0
    for a,c in itertools.product(range(7,81),range(7,81)):
        chain,end,why=trace(push_entry(a,c));maxrows=max(maxrows,len(chain));excursions[why]+=1
        if why not in first:first[why]=dict(a=a,c=c,rows=len(chain),end=asdict(end))
        assert why!='row budget';assert len(chain)<=finite_bound(push_entry(a,c))
    result=dict(passed=True,states_checked=samples,row_counts=dict(counts),distinct_internal_images=len(images),push_entries_with_no_predecessor=roots,excursion_stops=dict(excursions),first_stops=first,maximum_internal_excursion_rows=maxrows,roundtrip_examples=root_rows,claims_sha256=hashlib.sha256((HERE.parent/'l17-general-d/claims.json').read_bytes()).hexdigest(),raw_machine_runs=0,elapsed_seconds=time.monotonic()-began)
    (HERE/'streams-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
