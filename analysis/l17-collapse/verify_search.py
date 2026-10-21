"""Independent declarative replay, importing neither orbit actor nor word class."""
from pathlib import Path
from collections import Counter
import json,hashlib,time,sys
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-stack'))
from verify_symbolic import next_state
from specification import Claims,trim,skip,matching_prefix,equal_words,integer


def decode(row):return int(row['a'],16),[(w,int(n,16)) for w,n in row['tail']]


def matches(a,w,row):
    aa,ww=decode(row);assert a==aa and equal_words(w,ww)


def parse_reset(a,w):
    assert a==0
    N=matching_prefix(w,'1');tail=skip(w,N);k=matching_prefix(tail,'01')//2;tail=skip(tail,2*k)
    s=matching_prefix(tail,'1');assert not trim(skip(tail,s))
    assert N>=20 and k>=0 and s>=0 and (k>0 or s==0)
    return N,k,s


def coarse(N,k,s,code,spec):
    item=spec['rules'][code];params={'q':N//3,'k':k,'s':s,'z':s-3 if code=='C' else s//3}
    for key,(lo,hi) in item['guards'].items():assert params[key]>=lo and (hi is None or params[key]<=hi)
    assert [N,k,s]==[integer(t,params) for t in item['source']]
    target=tuple(integer(t,params) for t in item['target']);nn,kk,ss=target
    assert nn>N and kk>=0 and ss>=0 and (kk>0 or ss==0)
    count=item['primitive_rewrites']['base']+sum(params[key]>0 for key in item['primitive_rewrites']['indicators'])
    return target,count


def main():
    began=time.monotonic();limit=json.loads((HERE/'verification-protocol.json').read_text())['maximum_wall_seconds']
    oldpath=HERE.parent/'l17-stack'/'deeper.json';old=json.loads(oldpath.read_text())
    a,w=decode(old['stop']);index=int(old['stop']['index'],16);initial=index
    claims=Claims(HERE.parent/'l17-hardening'/'claims.json');source=json.loads((HERE/'search.json').read_text())
    assert hashlib.sha256(oldpath.read_bytes()).hexdigest()==source['source_sha256']
    choices=(HERE/'choices.txt').read_bytes();assert hashlib.sha256(choices).hexdigest()==source['choices_sha256']
    counts=Counter();checks={int(c['index'],16):c for c in source['checkpoints']};checked=0
    for c in choices:
        if time.monotonic()-began>limit:raise TimeoutError('Registered verification wall budget')
        a,w,name=next_state(a,w,claims);assert chr(c)==source['codes'][name];index+=1;counts[name]+=1
        if index in checks:matches(a,w,checks[index]);checked+=1
    matches(a,w,source['stop']);assert index==int(source['stop']['index'],16)
    print('primitive phase verified through',index,flush=True)
    spec=json.loads((HERE/'reset-spec.json').read_text());phase_summaries=[]
    for prefix,inputfile in (('fast','search.json'),('guard','fast.json')):
        phase=json.loads((HERE/(prefix+'.json')).read_text());assert index==phase['prior_rewrites']
        assert hashlib.sha256((HERE/inputfile).read_bytes()).hexdigest()==phase['source_sha256']
        codes=(HERE/(prefix+'-choices.txt')).read_bytes();assert hashlib.sha256(codes).hexdigest()==phase['choices_sha256']
        wordrows={int(r['index'],16):r for r in phase['word_edges']};round_checks={int(r['rounds'],16):r for r in phase['checkpoints']}
        pointer=0;wordcount=0
        while index<phase['stop_index']:
            if time.monotonic()-began>limit:raise TimeoutError('Registered verification wall budget')
            if index in wordrows:
                row=wordrows[index];assert pointer==int(row['coarse_rounds_before'],16)
                assert a==int(row['a_before'],16) and equal_words(w,[(p,int(n,16)) for p,n in row['tail_before']])
                a,w,name=next_state(a,w,claims);assert name==row['rule']
                assert a==int(row['a_after'],16) and equal_words(w,[(p,int(n,16)) for p,n in row['tail_after']])
                index+=1;wordcount+=1;counts[name]+=1
            else:
                N,k,s=parse_reset(a,w);target,added=coarse(N,k,s,chr(codes[pointer]),spec)
                N,k,s=target;a=0;w=trim([('1',N),('01',k),('1',s)]);pointer+=1;index+=added
                if pointer in round_checks:
                    check=round_checks[pointer];assert index==int(check['index'],16)
                    assert target==tuple(int(check[n],16) for n in ('N','k','s'));checked+=1
        assert pointer==len(codes)==phase['coarse_rounds'] and wordcount==len(wordrows)
        assert index==phase['stop_index'];matches(a,w,phase['stop'])
        phase_summaries.append({'phase':prefix,'coarse_rounds':pointer,'word_edges':wordcount,'stop':index,'passed':True})
        print(prefix,'verified through',index,flush=True)
    result={'passed':True,'start_rewrite':initial,'end_rewrite':index,'total_added_primitive_rewrites':index-initial,
        'word_primitive_choices':len(choices),'coarse_phases':phase_summaries,'matched_sparse_checkpoints':checked,
        'reset_spec_sha256':hashlib.sha256((HERE/'reset-spec.json').read_bytes()).hexdigest(),
        'actor_imported':False,'word_class_imported':False,'time_head_totals_recomputed':False,'elapsed_seconds':time.monotonic()-began}
    (HERE/'search-recheck.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':main()
