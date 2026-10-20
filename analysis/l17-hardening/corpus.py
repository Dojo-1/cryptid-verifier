"""ACAF Ambigator: fixed historical cases plus new boundary/context streams."""
from __future__ import annotations
import json
import random
from pathlib import Path


def unpack(parts):return ''.join(w*n for w,n in parts)


def contextual_rule(a,tail,name):
    s=unpack(tail)
    if name=='normalize01':
        q=0
        while s.startswith('01',2*q):q+=1
        return 'N',{'a':a,'q':q},s[2*q:]
    if name=='entry1':return 'E',{},s[1:]
    if name=='reset00':return 'Z',{'a':a},s[2:]
    if name=='pair11':return 'P',{'a':a},s[2:]
    if name=='countdown111':
        n=len(s)-len(s.lstrip('1'));q=n//3
        return 'Q',{'a':a,'q':q},s[3*q:]
    terminal='100' if name=='core100' else '111'
    padded=s+'0000'
    for c in range(len(s)//2+2):
        prefix='10'*c+terminal
        if padded.startswith(prefix):return 'F100' if name=='core100' else 'F111',{'a':a,'c':c},s[len(prefix):]
    raise ValueError('Cannot independently parse saved contextual input')


def tail_case(a,b,c,r):
    if b==0:return 'T0',{'a':a,'c':c,'r':r},''
    if b==2:return 'T2',{'a':a,'c':c,'r':r},''
    if r==0:return 'F100',{'a':a,'c':c},''
    if r==1:
        if c>=7:return 'F1100',{'a':a,'c':c},''
        return 'S'+str(c),{'a':a},''
    return 'F111',{'a':a,'c':c},'1'*(r-2)


def frozen_cases(root,claims):
    root=Path(root);cases=[]
    def add(rule,p,v,origin,head=0):
        case=claims.instantiate(rule,p,v);case.update(machine=claims.machine,origin=origin,head=head)
        cases.append(case)
    main=json.loads((root/'validation-results.json').read_text())
    for field in ('residue_grid','larger_translated_checks'):
        for row in main[field]:
            a=row['a'];kind='R1' if a%3==1 else 'R2';j=(a-(7 if kind=='R1' else 8))//3
            add(kind,{'j':j},'','frozen/'+field,row.get('head',0))
    for row in main['contextual_core_checks']:
        add('F100' if row['kind']=='core100' else 'F111',{'a':row['a'],'c':row['c']},row['suffix'],'frozen/core_context')
    for row in main['random_contextual_rewrites']:
        rule,p,v=contextual_rule(row['a'],row['tail'],row['rule']);add(rule,p,v,'frozen/rewrite')
    tails=json.loads((root/'tail-family-checks.json').read_text())
    for row in tails['grid']:
        rule,p,v=tail_case(row['a'],row['b'],row['c'],row['r']);add(rule,p,v,'frozen/one_tail_grid')
    for field in ('new_core_arbitrary_suffix_checks','new_core_larger_checks'):
        for row in tails[field]:add('F1100',{'a':row['a'],'c':row['c']},row['suffix'],'frozen/'+field)
    small=json.loads((root/'small-tail-checks.json').read_text())
    for field in ('grid','larger_arbitrary_suffix_checks'):
        for row in small[field]:add('S'+str(row['c']),{'a':row['a']},row.get('suffix',''),'frozen/short/'+field)
    if len(cases)!=4333:raise ValueError('Frozen endpoint inventory differs from the recorded 4333')
    return cases


def acaf_cases(claims,seed,count=2048):
    rng=random.Random(seed);names=list(claims.rules);cases=[]
    for i in range(count):
        name=names[i%len(names)];p={}
        for key,(lower,upper) in claims.rules[name]['guards'].items():
            if key=='j':value=rng.choice((0,1,2,3,7,15,31,38,50))
            elif key=='q':value=lower+rng.choice((0,1,2,3,7,15,24))
            elif key=='r':value=rng.choice((0,1,2,3,4,7,15,31))
            else:value=lower+rng.choice((0,1,2,3,7,15,63,127))
            p[key]=min(value,upper) if upper is not None else value
        length=rng.choice((0,1,2,3,7,8,15,31,64));density=rng.choice((0,0.125,0.5,0.875,1))
        v=''.join('1' if rng.random()<density else '0' for _ in range(length))
        # Align the actor's collapsed countdown with the individual P/D/Q section.
        # The raw critic's general context statement is unchanged.
        if name in ('P','D','Q') and v:v='0'+v[1:]
        case=claims.instantiate(name,p,v)
        if case['steps']>200000:raise ValueError('Generator exceeds the prospective raw bound')
        case.update(machine=claims.machine,origin='acaf/new',head=rng.choice((-1000000,-997,-1,0,1,997,1000000)),
                    generator={'index':i,'suffix_length':length,'suffix_density':density,'seed':seed})
        cases.append(case)
    return cases


def guard_cases(claims):
    rows=[]
    names=['F100','F111','F1100']+['S'+str(c) for c in range(1,7)]+['R1','R2']
    for name in names:
        guards=claims.rules[name]['guards']
        for key,(lower,_) in guards.items():
            for offset in (-1,-2):
                p={k:b[0] for k,b in guards.items()};p[key]=lower+offset
                rows.append({'rule':name,'parameters':p,'suffix':'01011','violated':key})
    return rows


def huge_cases(claims,seed,count=64):
    rng=random.Random(seed^0x7ACE);names=['F100','F111','F1100','S1','S2','S3','S4','S5','S6','R1','R2','Q','N','Z']
    rows=[]
    for i in range(count):
        name=names[i%len(names)];bits=(64,127,1024,4096)[i%4]
        p={k:(1<<bits)+rng.randrange(256) for k in claims.rules[name]['guards']}
        v='001101' if name in ('Q','N','Z') else '010011001101'
        case=claims.instantiate(name,p,v);case.update(machine=claims.machine,origin='acaf/huge',bits=bits)
        rows.append(case)
    return rows


def kernels(root):
    root=Path(root)
    a=json.loads((root/'validation-results.json').read_text())['kernel_witnesses']
    b=[json.loads((root/'tail-family-checks.json').read_text())['kernel_witness']]
    c=json.loads((root/'small-tail-checks.json').read_text())['kernel_witnesses']
    return a+b+c


def window_requests(root,machine,seed,variants=12):
    rng=random.Random(seed^0xC0A7);records=[]
    for index,k in enumerate(kernels(root)):
        base={k['origin']+i for i,b in enumerate(k['input']) if b=='1'}
        target={k['origin']+i for i,b in enumerate(k['output']) if b=='1'}
        left,right=k['read_bounds']
        for v in range(variants):
            context={x for x in range(left-12,right+13) if not(left<=x<=right) and rng.randrange(2)}
            source=(base-{x for x in base if not(left<=x<=right)})|context
            expected=(target-{x for x in target if not(left<=x<=right)})|context
            records.append({'request':{'machine':machine,'q':k['q'],'head':k['head'],'limit':k['steps'],'ones':sorted(source),'trace':True},
                'expected':{'q':k['target_q'],'head':k['target_head'],'steps':k['steps'],'halted':False,'ones':sorted(expected)},
                'kernel':index,'variant':v,'read_bounds':[left,right],
                'hypothesis':'Every cell outside the actual read window is arbitrary and is preserved.'})
    return records
