"""Controlled live-source mutation and bounded counterexample reduction."""
from __future__ import annotations
import ast
import hashlib
from pathlib import Path
import sys
import types
from actor_bridge import Actor


MUTATIONS=[
 ('F100-leading','core100','2*a-12','2*a-10','tape'),
 ('F100-time','core100','4*a+4*c+50','4*a+4*c+49','time'),
 ('F100-shift','core100','4*a+4*c+50,-2','4*a+4*c+50,-1','head'),
 ('F100-context','core100','tail.prepend','Word().prepend','context'),
 ('F111-leading','core111','2*a-8','2*a-6','tape'),
 ('F111-pairs','core111',"('01',c+6)","('01',c+7)",'tape'),
 ('F111-zero','core111',"('0',1)","('0',0)",'interior-zero'),
 ('F111-guard','core111','c<1','c<0','guard-contract'),
 ('F1100-middle','core1100','2*c-13','2*c-11','tape'),
 ('F1100-stack','core1100',"('1',3)","('1',4)",'stack-tail'),
 ('F1100-time','core1100','4*a+4*c+92','4*a+4*c+90','time'),
 ('short-c3-pairs','core1100_small','Endpoint(a+7,','Endpoint(a+6,','tape'),
 ('short-c6-zero','core1100_small',"('01',6),('0',1)","('01',6),('0',0)",'interior-zero'),
 ('short-c4-middle','core1100_small',"('01',1),('1',1),('01',5)","('01',1),('1',0),('01',5)",'interior-one'),
 ('residue-leading','residue','20*j+15','21*j+15','residue-coefficient'),
 ('residue-time','residue','60*j*j','61*j*j','time'),
 ('residue-shift','residue','-14*j-13','-14*j-12','head'),
 ('rewrite-reset','rewrite','2*a+4','2*a+6','dispatch'),
]


def alter_function(source,function,old,new):
    tree=ast.parse(source)
    node=next(n for n in ast.walk(tree) if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.name==function)
    lines=source.splitlines(keepends=True);text=''.join(lines[node.lineno-1:node.end_lineno])
    if old not in text:raise ValueError('Mutation anchor absent: '+function+' '+old)
    text=text.replace(old,new)
    return ''.join(lines[:node.lineno-1])+text+''.join(lines[node.end_lineno:])


def module(source,name):
    obj=types.ModuleType(name);obj.__file__='<controlled-live-mutation>'
    sys.modules[name]=obj
    exec(compile(source,obj.__file__,'exec'),obj.__dict__)
    return obj


def complexity(case):return sum(case['parameters'].values())+len(case['suffix'])


def shrink(case,claims,fails,limit=128):
    current=case;attempts=0;history=[]
    while attempts<limit:
        proposals=[];name=current['rule'];p=current['parameters'];v=current['suffix']
        for key,value in p.items():
            lower=claims.rules[name]['guards'][key][0]
            for candidate in (lower,lower+(value-lower)//2,value-1):
                if lower<=candidate<value:
                    newp=dict(p);newp[key]=candidate;proposals.append((newp,v))
        if v:
            proposals.extend((p,s) for s in ('',v[:len(v)//2],v[len(v)//2:],v[:-1]))
            for i,b in enumerate(v):
                if b=='1':proposals.append((p,v[:i]+'0'+v[i+1:]))
        changed=False;seen=set()
        for parameters,suffix in proposals:
            key=(tuple(sorted(parameters.items())),suffix)
            if key in seen:continue
            seen.add(key)
            candidate=claims.instantiate(name,parameters,suffix)
            if complexity(candidate)>=complexity(current):continue
            attempts+=1
            if fails(candidate):
                history.append({'parameters':parameters,'suffix':suffix});current=candidate;changed=True;break
            if attempts>=limit:break
        if not changed:break
    return current,{'attempts':attempts,'limit':limit,'reductions':history,'minimality':'Greedy under the declared moves and budget, not globally minimal.'}


def campaign(root,claims,cases,guards):
    root=Path(root);source=(root/'rules.py').read_text();records=[];baseline=Actor(root)
    for i,(name,function,old,new,kind) in enumerate(MUTATIONS):
        changed=alter_function(source,function,old,new);mutated=module(changed,'l17_rule_mutant_'+str(i));actor=Actor(root,mutated)
        def failed(case):
            try:return actor.compare(case,__import__('specification').equal_words)['status']=='mismatch'
            except (ValueError,TypeError,IndexError):return True
        first=None
        for index,case in enumerate(cases):
            if failed(case):first=(index,case);break
        guard=None
        if first is None:
            for candidate in guards:
                try:actor.endpoint(candidate)
                except (ValueError,TypeError,IndexError):continue
                guard=candidate;break
        record={'name':name,'kind':kind,'source_sha256':hashlib.sha256(changed.encode()).hexdigest(),
                'status':'killed' if first or guard else 'survived'}
        if first:
            minimized,work=shrink(first[1],claims,failed)
            record.update(first_case_index=first[0],original={'rule':first[1]['rule'],'parameters':first[1]['parameters'],'suffix':first[1]['suffix']},
                          minimized={'rule':minimized['rule'],'parameters':minimized['parameters'],'suffix':minimized['suffix']},shrink=work)
        elif guard:
            minimized=dict(guard,suffix='');actor.endpoint(minimized)
            record.update(guard_witness=guard,minimized_guard_witness=minimized,shrink={'attempts':1,'limit':128},
                          interpretation='Rejection contract changed; no assertion that the relaxed mathematical statement is false.')
        records.append(record)
    # Word dropping is a live implementation mutant, not a modified expected value.
    changed=alter_function((root/'words.py').read_text(),'drop','if n<0:',"n+=1\n        if n<0:")
    words=module(changed,'l17_words_mutant');mutated=module(source,'l17_rule_mutant_word_dependency');mutated.Word=words.Word
    actor=Actor(root,mutated,words)
    def word_failed(case):
        try:return actor.compare(case,__import__('specification').equal_words)['status']=='mismatch'
        except (ValueError,TypeError,IndexError):return True
    first=next(((i,c) for i,c in enumerate(cases) if word_failed(c)),None)
    record={'name':'word-drop-one-cell','kind':'representation','source_sha256':hashlib.sha256(changed.encode()).hexdigest(),'status':'killed' if first else 'survived'}
    if first:
        small,work=shrink(first[1],claims,word_failed)
        record.update(first_case_index=first[0],original={'rule':first[1]['rule'],'parameters':first[1]['parameters'],'suffix':first[1]['suffix']},
                      minimized={'rule':small['rule'],'parameters':small['parameters'],'suffix':small['suffix']},shrink=work)
    records.append(record)
    # Reintroduce the specific historical leading-zero block-encoding bug.
    block_source=(root/'block_sim.py').read_text();changed=alter_function(block_source,'encode','keep_zero=True','keep_zero=False')
    block=module(changed,'l17_block_mutant');bits='0001011011010001010111100110001110000110111'
    def block_failed(bits):
        sim=block.BlockTM(baseline.Word.literal(bits),2);sim.run(0)
        return sorted(sim.sparse())!=[i for i,b in enumerate(bits) if b=='1']
    original=bits;attempts=0
    if block_failed(bits):
        while attempts<128:
            changed_any=False
            for width in (max(1,len(bits)//2),1):
                for start in range(0,len(bits)-width+1):
                    test=bits[:start]+bits[start+width:];attempts+=1
                    if block_failed(test):bits=test;changed_any=True;break
                    if attempts>=128:break
                if changed_any or attempts>=128:break
            if not changed_any:break
    records.append({'name':'block-leading-zero-regression','kind':'historical-encoding',
                    'source_sha256':hashlib.sha256(changed.encode()).hexdigest(),
                    'status':'killed' if block_failed(original) else 'survived',
                    'original_word':original,'minimized_word':bits,'steps':0,'width':2,
                    'shrink':{'attempts':attempts,'limit':128,'minimality':'Greedy deletion, not global minimality.'}})
    return records
