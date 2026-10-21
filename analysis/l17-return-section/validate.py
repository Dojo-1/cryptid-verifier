"""Bounded raw check of a four-counter return across a two-layer excursion."""
from __future__ import annotations
import hashlib,json,random,sys,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
FRONTIER=HERE.parent/'l17-stacked-section'
if not FRONTIER.is_dir():FRONTIER=HERE.parent/'l17-frontier'
sys.path[:0]=[str(FRONTIER),str(HERE.parent/'l17-hardening')]
from words import Word
import rules
from specification import Claims,equal_words,expand,agrees,request,want,matching_prefix
from backend import execute,set_budget


def composed(u,d,v):
    if type(u) is not int or type(d) is not int or u<0 or d<0:
        raise ValueError('u,d must be nonnegative integers')
    first=rules.core1100(3*u+9,d+7,v)
    entry=rules.rewrite(first.a,first.tail)
    countdown=rules.rewrite(entry.a,entry.tail)
    normal=rules.rewrite(countdown.a,countdown.tail)
    assert [entry.rule,countdown.rule,normal.rule]==['entry1','countdown111','normalize01']
    return normal.a,normal.tail,sum(x.steps for x in (first,entry,countdown,normal)),sum(x.shift for x in (first,entry,countdown,normal))


def excursion_checks():
    full=json.loads((HERE.parent/'l17-stack'/'replay-compact.json').read_text())
    deep=json.loads((HERE.parent/'l17-stack'/'deeper.json').read_text())
    sources=[];targets={}
    for row in full['events']:
        if row.get('rule')=='core1100':
            sources.append((int(row['index'],16),int(row['a_before'],16),row['tail_before']))
        if 'rule' in row:targets[int(row['index'],16)]={'a':row['a_before'],'tail':row['tail_before']}
    for row in deep['events']:
        if row.get('rule')=='F1100':sources.append((int(row['index'],16),int(row['a'],16),row['tail']))
        if 'shape' in row:targets[int(row['index'],16)]=row
    results=[]
    for index,a,parts in sources:
        w=Word(tuple((p,int(n,16)) for p,n in parts))
        c=matching_prefix(w.parts,'10')//2
        assert a%3==0 and a>=9 and c>=7
        assert equal_words(w.parts,[('1',1),('01',c),('1',1)])
        u=(a-9)//3;d=c-7;aa,tail,steps,shift=composed(u,d,Word())
        target=targets[index+4]
        assert aa==int(target['a'],16)
        assert equal_words(tail.parts,[(p,int(n,16)) for p,n in target['tail']])
        count_check='Not accumulated in this state-only phase'
        if index==226797:
            edges=[r for r in full['events'] if r.get('rule') and index<=int(r['index'],16)<index+4]
            assert len(edges)==4
            assert sum(int(r['raw_transitions'],16) for r in edges)==steps
            assert sum(int(r['shift'],16) for r in edges)==shift
            count_check='Full recorded time and shift agree'
        results.append({'source_index':index,'target_index':index+4,'source_a_bits':a.bit_length(),'source_c':c,
            'source_a_mod3':a%3,'target_b':2*d+1,'target_k':7,'target_s':3,'passed':True,'time_check':count_check})
    return results


def mutations(cases,actuals):
    names=['a-offset','b-offset','tail-length','quadratic-time','head-shift','drop-context']
    results=[]
    for kind in names:
        killed=None
        for i,(case,actual) in enumerate(zip(cases,actuals)):
            u=case['parameters']['u'];d=case['parameters']['d'];v=case['suffix']
            a=10*u+18+(1 if kind=='a-offset' else 0)
            b=2*d+1+(2 if kind=='b-offset' else 0)
            pairs=6 if kind=='tail-length' else 7
            t=60*u*u+156*u+4*d+242-(u*u if kind=='quadratic-time' else 0)
            h=-14*u-18+(1 if kind=='head-shift' else 0)
            if kind=='drop-context':v=''
            word='01'*a+'1'*b+'01'*pairs+'111'+v
            predicted={'q':2,'head':h,'steps':t,'halted':False,'ones':[h+j for j,b in enumerate(word) if b=='1']}
            if not agrees(actual,predicted):killed=i;break
        assert killed is not None,kind
        results.append({'mutant':kind,'killed':True,'case':killed})
    return results


def main():
    claims=Claims(HERE/'claims.json');rng=random.Random(310017)
    params=[(u,d,('','1','001101')[i%3]) for i,(u,d) in enumerate((u,d) for u in range(9) for d in range(11))]
    params += [(rng.randint(9,45),rng.randint(0,90),''.join(rng.choice('01') for _ in range(rng.randrange(25)))) for _ in range(64)]
    cases=[];requests=[];expected=[]
    for i,(u,d,v) in enumerate(params):
        claim=claims.instantiate('RETURN',{'u':u,'d':d},v)
        a,tail,steps,shift=composed(u,d,Word.literal(v))
        assert equal_words([('01',a)]+list(tail.parts),claim['target'])
        assert (steps,shift)==(claim['steps'],claim['shift'])
        assert steps<=200000
        case=dict(claim,machine=claims.machine);cases.append(case)
        requests.append(request(case,i));expected.append(want(case))
    assert len(requests)<=200
    source=HERE.parent/'l17-hardening'/'raw_comparator.cpp';binary=HERE/'comparator'
    build=subprocess.run(['g++','-std=c++17','-O2',str(source),'-o',str(binary)],capture_output=True,text=True,check=True)
    set_budget(20000000,HERE/'raw-budget.jsonl')
    actuals,meta=execute(binary,requests,HERE/'raw.jsonl.gz')
    failures=[i for i,(out,pred) in enumerate(zip(actuals,expected)) if not agrees(out,pred)]
    if failures:
        (HERE/'failure.json').write_text(json.dumps({'cases':failures},indent=2)+'\n');raise AssertionError(failures)
    huge=[]
    for i in range(32):
        u=(1<<(128+31*i))+i;d=(1<<(128+23*i))+i;v=Word((('001101',1<<i),('1',1)))
        a,w,t,h=composed(u,d,v);claim=claims.instantiate('RETURN',{'u':u,'d':d},v.parts)
        assert equal_words([('01',a)]+list(w.parts),claim['target']) and (t,h)==(claim['steps'],claim['shift'])
        huge.append({'u_bits':u.bit_length(),'d_bits':d.bit_length(),'passed':True})
    guards=[]
    for u,d in [(-1,0),(0,-1),(True,0),(0,True),(0.0,0)]:
        try:composed(u,d,Word())
        except ValueError:guards.append({'arguments':[u,d],'rejected':True})
        else:raise AssertionError(('invalid guard',u,d))
    result={'status':'Mathematical composition and bounded raw checks; not Lean formalized, no global closure result.',
        'claims_sha256':hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest(),
        'comparator_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'build_stderr':build.stderr,
        'raw_endpoints':len(actuals),'raw_metadata':meta,'huge_checks':huge,'guard_checks':guards,
        'mutations':mutations(cases,actuals),'excursions':excursion_checks()}
    (HERE/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    (HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'raw_endpoints':len(actuals),'raw_transitions':meta['defined_transitions'],'mutants':len(result['mutations']),
        'huge_checks':len(huge),'matched_excursions':result['excursions']},indent=2))


if __name__=='__main__':main()
