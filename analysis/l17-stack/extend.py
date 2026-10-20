"""Bounded conditional L17 orbit extension; frozen predecessors are read-only."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import sys
import time
from collections import Counter

from paths import HERE,FRONTIER,HARDENING
sys.path[:0]=[str(FRONTIER),str(HARDENING)]
import rules
from words import Word
from specification import Claims,equal_words,skip,matching_prefix,first_bits
from trace_critic import edge_claim


def encoded(x):
    if isinstance(x,int):return ('-' if x<0 else '')+'0x'+format(abs(x),'x')
    if isinstance(x,dict):return {k:encoded(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encoded(v) for v in x]
    return x


def rewrite(a,w):
    out=rules.rewrite(a,w)
    if not isinstance(out,dict):return out
    c=w.periodic_prefix_length('10')//2
    if a>=7 and c>=1 and w.drop(2*c).prefix(4)=='1100':
        suffix=w.drop(2*c+4)
        return rules.core1100(a,c,suffix) if c>=7 else rules.core1100_small(a,c,suffix)
    return out


def claim_for(a,w,out,claims):
    if out.rule.startswith('core1100'):
        c=matching_prefix(w.parts,'10')//2
        name='F1100' if c>=7 else 'S'+str(c)
        params={'a':a,'c':c} if c>=7 else {'a':a}
        return claims.instantiate(name,params,skip(w.parts,2*c+4))
    row={'a_before':a,'tail_before':w.to_json(),'rule':out.rule}
    return edge_claim(row,claims)


def shape(w):
    """Count actual alternating blocks, not representation chunks."""
    remaining=w
    lead=remaining.periodic_prefix_length('1')
    remaining=remaining.drop(lead)
    layers=[]
    while remaining.parts:
        c=remaining.periodic_prefix_length('01')//2
        if not c:return {'kind':'gap','prefix':w.prefix(20),'initial_layers':layers}
        remaining=remaining.drop(2*c)
        r=remaining.periodic_prefix_length('1')
        remaining=remaining.drop(r)
        layers.append([c,r])
    return {'kind':'pure','leading_ones':lead,'depth':len(layers),'layers':layers}


def main():
    protocol=json.loads((HERE/'protocol.json').read_text())
    bounds=protocol['budgets']
    source=FRONTIER/'symbolic-extension.json'
    old=json.loads(source.read_text())['trace']
    a=old['stop']['a'];w=Word(tuple(map(tuple,old['stop']['tail'])))
    total=old['steps'];shift=old['shift'];start=len(old['records'])
    claims=Claims(HERE.parent/'l17-hardening'/'claims.json')
    began=time.monotonic();counts=Counter();first={};checkpoints=[];events=[]
    digest=hashlib.sha256();maxdepth=0;olddepth=None;maxbits=0
    stop=None
    for index in range(start,bounds['maximum_total_contextual_rewrites_including_existing_prefix']):
        if time.monotonic()-began>bounds['maximum_symbolic_wall_seconds']:
            stop={'reason':'wall budget','index':index};break
        bits=max([a.bit_length()]+[n.bit_length() for _,n in w.parts])
        maxbits=max(maxbits,bits)
        if bits>bounds['maximum_counter_bits']:
            stop={'reason':'counter bit budget','index':index};break
        current=shape(w)
        if current['kind']=='pure':
            depth=current['depth'];maxdepth=max(depth,maxdepth)
            if depth!=olddepth:
                if depth>1 or (olddepth is not None and olddepth>1):
                    events.append(encoded({'index':index,'a':a,'tail':w.to_json(),'shape':current,'steps':total,'shift':shift}))
                olddepth=depth
            if depth>=4:
                stop={'reason':'four pure tail layers','index':index};break
        out=rewrite(a,w)
        if isinstance(out,dict):stop={'reason':'unsupported','index':index,'details':out};break
        claim=claim_for(a,w,out,claims)
        assert equal_words([('01',a)]+list(w.parts),claim['source']),(index,'source')
        assert equal_words([('01',out.a)]+list(out.tail.parts),claim['target']),(index,'target')
        assert (out.steps,out.shift)==(claim['steps'],claim['shift']),(index,'time/shift')
        counts[out.rule]+=1
        row={'index':index,'rule':out.rule,'a_before':a,'tail_before':w.to_json(),
             'a_after':out.a,'tail_after':out.tail.to_json(),'raw_transitions':out.steps,'shift':out.shift}
        wire=json.dumps(encoded(row),sort_keys=True,separators=(',',':')).encode()
        digest.update(len(wire).to_bytes(8,'big'));digest.update(wire)
        if out.rule not in first:
            first[out.rule]=encoded(row)
        total+=out.steps;shift+=out.shift;a=out.a;w=out.tail
        if (index+1)%bounds['checkpoint_interval']==0:
            checkpoints.append(encoded({'index':index+1,'a':a,'tail':w.to_json(),'steps':total,'shift':shift,'shape':shape(w)}))
    else:stop={'reason':'rewrite budget','index':index+1}
    stop.update({'a':a,'tail':w.to_json(),'steps':total,'shift':shift,'shape':shape(w)})
    report={'status':'Conditional arithmetic, not raw simulation, Lean proof, or a stack bound.',
        'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'claims_sha256':hashlib.sha256((HERE.parent/'l17-hardening'/'claims.json').read_bytes()).hexdigest(),
        'integer_encoding':'All JSON integer values below use signed hexadecimal strings.',
        'prior_rewrites':start,'new_checked_rewrites':sum(counts.values()),'rule_counts':dict(counts),
        'maximum_pure_tail_depth':maxdepth,'maximum_counter_bits':maxbits,
        'edge_hash_sha256':digest.hexdigest(),'first_use':first,'layer_events':events,
        'checkpoints':checkpoints,'stop':encoded(stop),'elapsed_seconds':time.monotonic()-began}
    (HERE/'extension.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('new_checked_rewrites','rule_counts','maximum_pure_tail_depth','maximum_counter_bits','elapsed_seconds')}),flush=True)
    print('STOP',stop['reason'],'index',stop['index'],'a bits',a.bit_length(),'prefix',w.prefix(40),flush=True)
    print('tail chunks',len(w.parts),'first1100',first.get('core1100',{}).get('index'),flush=True)


if __name__=='__main__':main()
