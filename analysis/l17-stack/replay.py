"""Full count/shift replay of the state-only search, then first-layer follow-up."""
from __future__ import annotations
import json,hashlib,time
from collections import Counter
from extend import HERE,Word,encoded,rewrite,claim_for,shape
from specification import Claims,equal_words


def main():
    proto=json.loads((HERE/'replay-protocol.json').read_text())
    source=json.loads((HERE/'extension.json').read_text())['stop']
    a=int(source['a'],16);w=Word(tuple((p,int(n,16)) for p,n in source['tail']))
    total=int(source['steps'],16);shift=int(source['shift'],16);start=int(source['index'],16)
    discovery=json.loads((HERE/'discovery.json').read_text())['stop'];hit=int(discovery['index'],16)
    claims=Claims(HERE.parent/'l17-hardening'/'claims.json')
    begin=time.monotonic();counts=Counter();checkpoints=[];events=[];digest=hashlib.sha256()
    olddepth=1;maxdepth=1;confirmed_discovery=False
    for i in range(start,proto['maximum_global_rewrites']):
        if time.monotonic()-begin>proto['maximum_wall_seconds']:reason='wall budget';break
        if a.bit_length()>proto['maximum_counter_bits']:reason='counter bit budget';break
        if i==hit:
            assert a==int(discovery['a'],16)
            assert equal_words(w.parts,[(p,int(n,16)) for p,n in discovery['tail']])
            confirmed_discovery=True
        s=shape(w)
        if s['kind']=='pure':
            maxdepth=max(maxdepth,s['depth'])
            if s['depth']!=olddepth:
                if max(s['depth'],olddepth)>1:
                    events.append(encoded({'index':i,'a':a,'tail':w.to_json(),'shape':s,'steps':total,'shift':shift}))
                olddepth=s['depth']
            if s['depth']>=4:reason='four pure layers';break
        out=rewrite(a,w)
        if isinstance(out,dict):reason='unsupported';break
        claim=claim_for(a,w,out,claims)
        assert equal_words([('01',a)]+list(w.parts),claim['source']),(i,'source')
        assert equal_words([('01',out.a)]+list(out.tail.parts),claim['target']),(i,'target')
        assert (out.steps,out.shift)==(claim['steps'],claim['shift']),(i,'count/shift')
        row={'index':i,'rule':out.rule,'a_before':a,'tail_before':w.to_json(),'a_after':out.a,'tail_after':out.tail.to_json(),
             'raw_transitions':out.steps,'shift':out.shift,'time_before':total,'head_before':shift}
        wire=json.dumps(encoded(row),sort_keys=True,separators=(',',':')).encode()
        digest.update(len(wire).to_bytes(8,'big'));digest.update(wire)
        if i>=hit or out.rule.startswith('core1100'):events.append(encoded(row))
        counts[out.rule]+=1;total+=out.steps;shift+=out.shift;a=out.a;w=out.tail
        if (i+1)%10000==0:checkpoints.append(encoded({'index':i+1,'a':a,'tail':w.to_json(),'steps':total,'shift':shift}))
    else:i+=1;reason='rewrite budget'
    report={'status':'Conditional full count/shift replay; no enormous raw simulation or new Lean proof.',
            'source_sha256':hashlib.sha256((HERE/'extension.json').read_bytes()).hexdigest(),'prior_rewrites':start,
            'new_checked_rewrites':sum(counts.values()),'confirmed_state_only_discovery':confirmed_discovery,
            'rule_counts':dict(counts),'maximum_pure_tail_depth':maxdepth,'edge_hash_sha256':digest.hexdigest(),
            'checkpoints':checkpoints,'events':events,'stop':encoded({'reason':reason,'index':i,'a':a,'tail':w.to_json(),
                'steps':total,'shift':shift,'shape':shape(w)}),'elapsed_seconds':time.monotonic()-begin}
    (HERE/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('new_checked_rewrites','confirmed_state_only_discovery','rule_counts','maximum_pure_tail_depth','elapsed_seconds')}),flush=True)
    s=shape(w)
    print('STOP',reason,i,'a bits',a.bit_length(),'prefix',w.prefix(50),'kind',s['kind'],'depth',s.get('depth'),flush=True)


if __name__=='__main__':main()
