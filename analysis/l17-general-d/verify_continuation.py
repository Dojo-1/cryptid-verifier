"""Separate declarative replay; no actor, Word or scalar-generator imports."""
import json,hashlib,time,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-collapse'))
from verify_search import coarse,parse_reset,matches
from verify_symbolic import next_state
from specification import Claims,equal_words

def decode(x):return int(x['a'],16),[(p,int(n,16)) for p,n in x['tail']]

def main():
    began=time.monotonic();limit=json.loads((HERE/'verification-protocol.json').read_text())['maximum_wall_seconds']
    old=HERE.parent/'l17-collapse';raw=(old/'guard.json').read_bytes();base=json.loads(raw)
    a,w=decode(base['stop']);index=int(base['stop']['index'],16);start=index
    spec=json.loads((old/'reset-spec.json').read_text());claims=Claims(HERE.parent/'l17-hardening/claims.json')
    phases=[];checkcount=0
    for prefix,reportfile,inputfile in (('recovery','recovery.json',old/'guard.json'),('continuation','continuation.json',HERE/'boundary.json')):
        report=json.loads((HERE/reportfile).read_text());assert hashlib.sha256(inputfile.read_bytes()).hexdigest()==report['source_sha256']
        assert index==report['prior_rewrites'];codes=(HERE/(prefix+'-choices.txt')).read_bytes()
        assert hashlib.sha256(codes).hexdigest()==report['choices_sha256']
        edges={int(r['index'],16):r for r in report['word_edges']};checks={int(c['rounds'],16):c for c in report['checkpoints']}
        pointer=wordcount=0
        while index<report['stop_index']:
            if time.monotonic()-began>limit:raise TimeoutError('registered independent replay wall budget')
            if index in edges:
                row=edges[index];assert pointer==int(row['coarse_rounds_before'],16)
                assert a==int(row['a_before'],16) and equal_words(w,[(p,int(n,16)) for p,n in row['tail_before']])
                a,w,name=next_state(a,w,claims);assert name==row['rule']
                assert a==int(row['a_after'],16) and equal_words(w,[(p,int(n,16)) for p,n in row['tail_after']])
                index+=1;wordcount+=1
            else:
                N,k,s=parse_reset(a,w);target,added=coarse(N,k,s,chr(codes[pointer]),spec)
                N,k,s=target;a=0;w=[('1',N),('01',k),('1',s)];pointer+=1;index+=added
                if pointer in checks:
                    c=checks[pointer];assert index==int(c['index'],16)
                    assert target==tuple(int(c[n],16) for n in ('N','k','s'));checkcount+=1
        assert pointer==len(codes)==report['coarse_rounds'] and wordcount==len(edges)
        matches(a,w,report['stop']);assert index==report['stop_index']
        if prefix=='recovery':
            boundary=json.loads((HERE/'boundary.json').read_text());matches(a,w,boundary)
            A=a;assert A.bit_length()==977821 and A%729==548
        phases.append(dict(name=prefix,coarse_rounds=pointer,primitive_word_edges=wordcount,stop=index,passed=True))
        print(prefix,'verified through',index,flush=True)
    result=dict(passed=True,start=start,end=index,primitive_rewrites=index-start,phases=phases,matched_sparse_checkpoints=checkcount,actor_imported=False,word_class_imported=False,time_head_totals_recomputed=False,claims_sha256=hashlib.sha256((HERE.parent/'l17-hardening/claims.json').read_bytes()).hexdigest(),reset_spec_sha256=hashlib.sha256((old/'reset-spec.json').read_bytes()).hexdigest(),elapsed_seconds=time.monotonic()-began)
    (HERE/'continuation-recheck.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
