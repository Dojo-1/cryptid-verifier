"""Second registered state-only phase; preserve every claim choice compactly."""
from __future__ import annotations
import json,time,hashlib
from collections import Counter
from extend import HERE,encoded,Word,shape
from discover import extended_state_edge,critical_check
from specification import Claims

CODES={'E':'E','Z':'Z','P':'P','Q':'Q','N':'N','F100':'A','F111':'B','F1100':'C',**{'S'+str(i):str(i) for i in range(1,7)}}


def main():
    proto=json.loads((HERE/'deeper-protocol.json').read_text());path=HERE/'replay-compact.json'
    source=json.loads(path.read_text())['stop'];a=int(source['a'],16)
    w=Word(tuple((p,int(n,16)) for p,n in source['tail']));start=int(source['index'],16)
    claims=Claims(HERE.parent/'l17-hardening'/'claims.json');begin=time.monotonic()
    choices=bytearray();counts=Counter();checkpoints=[];events=[];olddepth=0;maxdepth=0
    for i in range(start,proto['maximum_global_rewrites']):
        if time.monotonic()-begin>proto['maximum_wall_seconds']:reason='wall budget';break
        if max([a.bit_length()]+[n.bit_length() for _,n in w.parts])>proto['maximum_counter_bits']:reason='counter bit budget';break
        s=shape(w)
        if s['kind']=='pure':
            maxdepth=max(s['depth'],maxdepth)
            if olddepth!=s['depth'] and max(olddepth,s['depth'])>1:
                events.append(encoded({'index':i,'a':a,'tail':w.to_json(),'shape':s}))
            olddepth=s['depth']
            if s['depth']>=3:reason='three pure layers';break
        out=extended_state_edge(a,w)
        if out is None:reason='unsupported';break
        critical_check(a,w,out,claims)
        if out[2]=='F1100' or out[2].startswith('S'):
            events.append(encoded({'index':i,'a':a,'tail':w.to_json(),'rule':out[2]}))
        a,w,name,_,_=out;choices.extend(CODES[name].encode());counts[name]+=1
        if (i+1)%10000==0:checkpoints.append(encoded({'index':i+1,'a':a,'tail':w.to_json(),'shape':shape(w)}))
    else:i+=1;reason='rewrite budget'
    (HERE/'deeper-choices.txt').write_bytes(choices)
    report={'status':'State-only conditional arithmetic; counts and shifts omitted, not a new Lean proof.',
        'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'prior_rewrites':start,
        'new_checked_state_edges':sum(counts.values()),'rule_counts':dict(counts),'maximum_pure_tail_depth':maxdepth,
        'choice_codes':CODES,'choices_sha256':hashlib.sha256(choices).hexdigest(),'events':events,'checkpoints':checkpoints,
        'stop':encoded({'reason':reason,'index':i,'a':a,'tail':w.to_json(),'shape':shape(w)}),'elapsed_seconds':time.monotonic()-begin}
    (HERE/'deeper.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('new_checked_state_edges','rule_counts','maximum_pure_tail_depth','elapsed_seconds')}))
    print('STOP',reason,i,'a bits',a.bit_length(),'tail shape',{k:v for k,v in shape(w).items() if k!='leading_ones'})


if __name__=='__main__':main()
