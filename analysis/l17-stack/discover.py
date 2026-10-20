"""State-only search: avoid quadratic countdown times while locating rare tails."""
from __future__ import annotations
import json,time,hashlib
from collections import Counter
from pathlib import Path
from extend import HERE,encoded,shape,Word,rules
from specification import Claims,matching_prefix,skip,first_bits,equal_words,materialize


def state_edge(a,w):
    p=w.periodic_prefix_length('01')//2
    if p:return a+p,w.drop(2*p),'N',{'a':a,'q':p},2*p
    first=w.prefix(3)
    if a==0 and first[0]=='1':return 1,w,'E',{},1
    if first[:2]=='00':return 0,w.drop(2).prepend(('1',2*a+4)),'Z',{'a':a},2
    if first[:2]=='11' and a>=1:
        q=w.periodic_prefix_length('1')//3
        if q:return a+5*q,w.drop(3*q),'Q',{'a':a,'q':q},3*q
        return a+4,w.drop(2).prepend(('0',1)),'P',{'a':a},2
    pairs=w.periodic_prefix_length('10')//2
    remaining=w.drop(2*pairs)
    if pairs and remaining.prefix(1)=='0':
        c=pairs-1
        if a<7:return None
        v=w.drop(2*c+3)
        return 0,v.prepend(('1',2*a-12),('01',7),('1',2*c+3)),'F100',{'a':a,'c':c},2*c+3
    prefix=remaining.prefix(3)
    if prefix=='100' and a>=7:
        c=pairs;v=w.drop(2*c+3)
        return 0,v.prepend(('1',2*a-12),('01',7),('1',2*c+3)),'F100',{'a':a,'c':c},2*c+3
    if prefix=='111' and pairs>=1 and a>=5:
        c=pairs;v=w.drop(2*c+3)
        return 0,v.prepend(('1',2*a-8),('01',c+6),('0',1)),'F111',{'a':a,'c':c},2*c+3
    return None


def extended_state_edge(a,w):
    out=state_edge(a,w)
    if out is not None:return out
    c=w.periodic_prefix_length('10')//2
    if a<7 or c<1 or w.drop(2*c).prefix(4)!='1100':return None
    v=w.drop(2*c+4)
    if c>=7:
        return 0,v.prepend(('1',2*a-12),('01',7),('1',2*c-13),('01',7),('1',3)),'F1100',{'a':a,'c':c},2*c+4
    # The frozen actor supplies state only; no enormous countdown arithmetic.
    ep=rules.core1100_small(a,c,v)
    return ep.a,ep.tail,'S'+str(c),{'a':a},2*c+4


def critical_check(a,w,out,claims):
    aa,ww,name,params,cut=out
    # Parse source independently; ensure the selected cut does not hide input bits.
    expected_cut={'E':1,'Z':2,'P':2}.get(name)
    if name=='N':assert params['q']==matching_prefix(w.parts,'01')//2;expected_cut=2*params['q']
    if name=='Q':assert params['q']==matching_prefix(w.parts,'1')//3;expected_cut=3*params['q']
    if name.startswith('S') or name=='F1100':
        c=matching_prefix(w.parts,'10')//2
        expected_cut=2*c+4
        assert first_bits(skip(w.parts,2*c),4)=='1100'
        if name.startswith('S'):assert c==int(name[1:])
        else:assert c==params['c']
    elif name.startswith('F'):
        expected_cut=2*params['c']+3
        assert first_bits(skip(w.parts,2*params['c']),3)==('100' if name=='F100' else '111')
    assert cut==expected_cut
    claim=claims.rules[name]
    assert set(params)==set(claim['guards'])
    for key,(lo,hi) in claim['guards'].items():assert params[key]>=lo and (hi is None or params[key]<=hi)
    v=skip(w.parts,cut)
    before=materialize(claim['source'],params,v);after=materialize(claim['target'],params,v)
    assert equal_words([('01',a)]+list(w.parts),before)
    assert equal_words([('01',aa)]+list(ww.parts),after)


def main():
    proto=json.loads((HERE/'discovery-protocol.json').read_text())
    source=json.loads((HERE/'extension.json').read_text())['stop']
    a=int(source['a'],16);w=Word(tuple((p,int(n,16)) for p,n in source['tail']))
    start=int(source['index'],16);claims=Claims(HERE.parent/'l17-hardening'/'claims.json')
    begin=time.monotonic();counts=Counter();maxdepth=0;maxbits=0;checkpoints=[]
    for i in range(start,proto['maximum_global_rewrites']):
        if time.monotonic()-begin>proto['maximum_wall_seconds']:reason='wall budget';break
        bits=max([a.bit_length()]+[n.bit_length() for _,n in w.parts]);maxbits=max(bits,maxbits)
        if bits>proto['maximum_counter_bits']:reason='counter bit budget';break
        s=shape(w)
        if s['kind']=='pure':maxdepth=max(maxdepth,s['depth'])
        if s['kind']=='pure' and s['depth']>1:reason='new layer';break
        out=state_edge(a,w)
        if out is None:reason='unsupported';break
        critical_check(a,w,out,claims)
        a,w,name,_,_=out;counts[name]+=1
        if (i+1)%10000==0:
            checkpoints.append(encoded({'index':i+1,'a':a,'tail':w.to_json(),'shape':shape(w)}))
    else:i+=1;reason='rewrite budget'
    stop=encoded({'reason':reason,'index':i,'a':a,'tail':w.to_json(),'shape':shape(w)})
    report={'status':proto['discovery_omits'],'source':'extension.json','source_sha256':hashlib.sha256((HERE/'extension.json').read_bytes()).hexdigest(),
            'prior_rewrites':start,'new_checked_state_edges':sum(counts.values()),'rule_counts':dict(counts),
            'maximum_counter_bits':maxbits,'maximum_pure_tail_depth':maxdepth,'checkpoints':checkpoints,
            'stop':stop,'elapsed_seconds':time.monotonic()-begin}
    (HERE/'discovery.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('new_checked_state_edges','rule_counts','maximum_pure_tail_depth','maximum_counter_bits','elapsed_seconds')}),flush=True)
    print('STOP',reason,i,'a bits',a.bit_length(),'tail',encoded(w.to_json()),flush=True)


if __name__=='__main__':main()
