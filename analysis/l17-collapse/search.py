"""Registered search for the first later failure of immediate collapse."""
from __future__ import annotations
import json,hashlib,time,sys
from pathlib import Path
from collections import Counter
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-stack'))
from extend import Word,encoded,shape
from discover import extended_state_edge,critical_check
from specification import Claims,matching_prefix

CODES={'E':'E','Z':'Z','P':'P','Q':'Q','N':'N','F100':'A','F111':'B','F1100':'C',**{'S'+str(i):str(i) for i in range(1,7)}}


def main():
    proto=json.loads((HERE/'protocol.json').read_text());bounds=proto['budgets']
    src=HERE.parent/'l17-stack'/'deeper.json';data=src.read_bytes()
    assert hashlib.sha256(data).hexdigest()==proto['source_sha256']
    source=json.loads(data)['stop'];a=int(source['a'],16)
    w=Word(tuple((p,int(n,16)) for p,n in source['tail']));start=int(source['index'],16)
    claims=Claims(HERE.parent/'l17-hardening'/'claims.json');began=time.monotonic()
    counts=Counter();choices=bytearray();events=[];checkpoints=[];trigger=None;local=[];maxdepth=1
    for i in range(start,bounds['maximum_global_rewrites']):
        if time.monotonic()-began>bounds['maximum_search_wall_seconds']:reason='wall budget';break
        if max([a.bit_length()]+[n.bit_length() for _,n in w.parts])>bounds['maximum_counter_bits']:reason='counter bit budget';break
        s=shape(w)
        if s['kind']=='pure':maxdepth=max(maxdepth,s['depth'])
        if trigger is not None and i>trigger:
            if s['kind']=='pure' and s['depth']<=1:reason='triggered excursion returned';break
            if i-trigger>bounds['maximum_local_rewrites_after_first_guard_failure']:reason='local rewrite budget';break
            if s['kind']=='pure' and s['depth']>=3:reason='three pure layers';break
        out=extended_state_edge(a,w)
        if out is None:reason='unsupported';break
        critical_check(a,w,out,claims)
        aa,ww,name,params,cut=out
        if name=='F1100':
            c=matching_prefix(w.parts,'10')//2
            events.append(encoded({'source_index':i,'a':a,'tail':w.to_json(),'c':c,'a_mod3':a%3,
                'target_a':aa,'target_tail':ww.to_json(),'target_shape':shape(ww)}))
            print('F1100',i,'a bits',a.bit_length(),'c',c,'a mod3',a%3,flush=True)
            if a%3!=0 and trigger is None:trigger=i
        if trigger is not None:
            local.append(encoded({'index':i,'rule':name,'a_before':a,'tail_before':w.to_json(),
                'a_after':aa,'tail_after':ww.to_json(),'parameters':params,'shape_after':shape(ww)}))
        a,w=aa,ww;counts[name]+=1;choices.extend(CODES[name].encode())
        if (i+1)%bounds['checkpoint_interval']==0:checkpoints.append(encoded({'index':i+1,'a':a,'tail':w.to_json(),'shape':shape(w)}))
    else:i+=1;reason='rewrite budget'
    (HERE/'choices.txt').write_bytes(choices)
    result={'status':'Guarded state-only conditional continuation. No new Lean proof or global stack result.',
        'source_sha256':hashlib.sha256(data).hexdigest(),'prior_rewrites':start,'new_checked_edges':sum(counts.values()),
        'counts':dict(counts),'codes':CODES,'choices_sha256':hashlib.sha256(choices).hexdigest(),
        'trigger_index':trigger,'maximum_pure_tail_depth':maxdepth,'events':events,'checkpoints':checkpoints,'local_trace':local,
        'stop':encoded({'reason':reason,'index':i,'a':a,'tail':w.to_json(),'shape':shape(w)}),'elapsed_seconds':time.monotonic()-began}
    (HERE/'search.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('new_checked_edges','counts','trigger_index','maximum_pure_tail_depth','elapsed_seconds')}),flush=True)
    print('STOP',reason,i,'a bits',a.bit_length(),'kind',shape(w)['kind'],flush=True)


if __name__=='__main__':main()
