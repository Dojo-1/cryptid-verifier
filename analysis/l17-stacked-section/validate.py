"""Bounded validation and derived arithmetic trace for the stacked-section rules."""
from __future__ import annotations
from collections import Counter
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import random
from block_sim import BlockTM
from reference import run,OPS
from rules import core100,core111,residue,rewrite,trajectory,Endpoint
from words import Word

ROOT=Path(__file__).resolve().parent
RAW_LIMIT=200000


def expected(endpoint,head=0):
    bits=endpoint.word().expand()
    return {head+endpoint.shift+i:int(bit) for i,bit in enumerate(bits) if bit=='1'}


def check(source,endpoint,head=0,widths=(2,6)):
    if endpoint.steps>RAW_LIMIT:raise ValueError('reference probe exceeds recorded bound')
    bits=source.expand();direct=run(bits,endpoint.steps,head=head)
    want=expected(endpoint,head)
    assert (direct['q'],direct['head'],direct['steps'],direct['tape'])==(2,head+endpoint.shift,endpoint.steps,want)
    evidence=[]
    for width in widths:
        fast=BlockTM(source,width,head=head);result=fast.run(endpoint.steps)
        assert result['complete'] and not result['halted']
        assert (result['q'],result['head'],result['steps'],fast.sparse())==(2,head+endpoint.shift,endpoint.steps,want)
        evidence.append({'width':width,'events':result['events'],'swept_blocks':result['swept_blocks']})
    return evidence


KERNELS=[
    {'name':'A01','origin':0,'input':'01','q':0,'head':0,'steps':2,'output':'10','target_q':0,'target_head':2,'read_bounds':[0,1]},
    {'name':'D10','origin':0,'input':'10','q':3,'head':1,'steps':4,'output':'10','target_q':3,'target_head':-1,'read_bounds':[0,1]},
    {'name':'C01','origin':0,'input':'01','q':2,'head':1,'steps':2,'output':'11','target_q':2,'target_head':-1,'read_bounds':[0,1]},
    {'name':'segment11','origin':-4,'input':'101010','q':0,'head':0,'steps':11,'output':'010100','target_q':0,'target_head':1,'read_bounds':[-4,1]},
    {'name':'segment43','origin':-16,'input':'1010101010100111','q':2,'head':-3,'steps':43,'output':'1101010101010101','target_q':2,'target_head':-16,'read_bounds':[-15,-2]},
    {'name':'segment22','origin':-12,'input':'1010101001010','q':3,'head':-4,'steps':22,'output':'1101010101010','target_q':2,'target_head':-12,'read_bounds':[-11,-2]},
    {'name':'A00','origin':0,'input':'00','q':0,'head':0,'steps':2,'output':'11','target_q':2,'target_head':0,'read_bounds':[0,1]},
    {'name':'A11','origin':0,'input':'11','q':0,'head':0,'steps':3,'output':'10','target_q':3,'target_head':-1,'read_bounds':[0,1]},
]


def kernels():
    evidence=[]
    for k in KERNELS:
        tape={k['origin']+i:int(v) for i,v in enumerate(k['input']) if v=='1'}
        q,h=k['q'],k['head'];reads=[]
        for _ in range(k['steps']):
            reads.append([chr(q+65),h,tape.get(h,0)])
            assert k['read_bounds'][0]<=h<=k['read_bounds'][1]
            value,move,q=OPS[q][tape.get(h,0)]
            if value:tape[h]=value
            else:tape.pop(h,None)
            h+=move
        target={k['origin']+i:int(v) for i,v in enumerate(k['output']) if v=='1'}
        assert (q,h,tape)==(k['target_q'],k['target_head'],target)
        evidence.append(dict(k,reads=reads))
    return evidence


def main():
    rng=random.Random(20261020);residue_rows=[];counts=Counter();max_steps=0
    for a in range(7,121):
        if a%3==0:continue
        target=residue(a)
        info=check(Word((('01',a),('1',1))),target)
        residue_rows.append({'a':a,'rule':target.rule,'steps':target.steps,'shift':target.shift,'target':target.tail.to_json(),'block_checks':info})
        max_steps=max(max_steps,target.steps)
    larger=[]
    for i in range(64):
        j=rng.randrange(38,57);r=rng.choice((1,2));a=3*j+(7 if r==1 else 8);head=rng.randrange(-1000,1001)
        target=residue(a);info=check(Word((('01',a),('1',1))),target,head)
        larger.append({'a':a,'head':head,'steps':target.steps,'block_checks':info});max_steps=max(max_steps,target.steps)
    contextual=[]
    for kind in ('core100','core111'):
        for _ in range(256):
            a=rng.randrange(7 if kind=='core100' else 5,65)
            c=rng.randrange(0 if kind=='core100' else 1,33)
            suffix=''.join(rng.choice('01') for _ in range(rng.randrange(41)))
            tail=Word.literal(suffix)
            target=core100(a,c,tail) if kind=='core100' else core111(a,c,tail)
            source=Word((('01',a),('10',c),('100' if kind=='core100' else '111',1))+tail.parts)
            info=check(source,target)
            contextual.append({'kind':kind,'a':a,'c':c,'suffix':suffix,'steps':target.steps,'block_checks':info})
            max_steps=max(max_steps,target.steps)
    rewrite_rows=[];unsupported=0
    for _ in range(1000):
        a=rng.randrange(41);bits=''.join(rng.choice('01') for _ in range(rng.randrange(65)))
        tail=Word.literal(bits);target=rewrite(a,tail)
        if isinstance(target,dict):unsupported+=1;continue
        check(tail.prepend(('01',a)),target)
        counts[target.rule]+=1
        rewrite_rows.append({'a':a,'tail':tail.to_json(),'rule':target.rule,'steps':target.steps})
    random_reference=[]
    for width in (2,6):
        for _ in range(150):
            bits=''.join(rng.choice('01') for _ in range(rng.randrange(81)))
            q=rng.randrange(6);steps=rng.randrange(1001);head=rng.randrange(-20,21)
            direct=run(bits,steps,q,head);fast=BlockTM(Word.literal(bits),width,q,head);result=fast.run(steps)
            assert (direct['steps'],direct['q'],direct['head'],direct['halted'],direct['tape'])==(result['steps'],result['q'],result['head'],result['halted'],fast.sparse())
            random_reference.append({'width':width,'word':bits,'q':q,'steps':steps,'head':head})
    derived=trajectory(6575648756,Word((('1',1),)),100)
    output={'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
            'status':'Finite full-tape checks plus explicit sweep derivation; no Lean verification performed here.',
            'reference_probe_limit':RAW_LIMIT,'maximum_residue_or_context_reference_steps':max_steps,
            'residue_grid':residue_rows,'larger_translated_checks':larger,
            'contextual_core_checks':contextual,'random_contextual_rewrites':rewrite_rows,
            'rewrite_rule_counts':dict(counts),'random_unsupported_cases':unsupported,
            'independent_block_checks':random_reference,'kernel_witnesses':kernels(),
            'derived_next_frontier':{'status':'Arithmetic consequence of proposed contextual rules; not raw simulation or a new Lean certificate.',
                                     'source':'C(6575648756,1), supplied by Claude as the next boundary conditional on his divisible-by-three rule.',
                                     'trace':derived},
            'new_halting_or_nonhalting_theorems':0}
    (ROOT/'validation-results.json').write_text(json.dumps(output,indent=2)+'\n')
    print('Residue grid:',len(residue_rows),'larger/translated:',len(larger),'contextual cores:',len(contextual))
    print('Contextual rewrites:',len(rewrite_rows),dict(counts),'explicit unsupported:',unsupported)
    print('Independent random block checks:',len(random_reference),'kernels:',len(KERNELS))
    print('Derived arithmetic trace stop:',json.dumps(derived['stop']))
    print('All fixed reference limits respected; maximum residue/core count:',max_steps)


if __name__=='__main__':main()
