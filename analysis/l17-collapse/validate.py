"""Bounded collapse campaign: fixed queues, consumed claims, literal machine."""
from __future__ import annotations
import hashlib,json,subprocess
from search import HERE,Word,encoded,shape
from actors import immediate,ranked,resonance,long_return
from critic import single,ranked as rank_spec
from specification import Claims,equal_words,request,want,agrees
from backend import execute,set_budget


def compare(out,case):
    assert equal_words([('01',out['a'])]+list(out['tail'].parts),case['target'])
    assert (out['steps'],out['shift'])==(case['steps'],case['shift'])


def campaign():
    claims=Claims(HERE/'claims.json');cases=[];guards=[]
    for name in ('P0','P1','P2'):
        for h in (0,1,2,3,5):
            for d in (0,1,2,7):
                for v in ('','001101'):
                    if name=='P1' and d==0:
                        for fn in (lambda:claims.instantiate(name,{'h':h,'d':d},v),lambda:immediate(name,h,d,Word.literal(v))):
                            try:fn()
                            except ValueError:pass
                            else:raise AssertionError('Excluded guard accepted')
                        guards.append({'rule':name,'h':h,'d':d,'suffix':v,'rejected':True});continue
                    case=single(claims,name,{'h':h,'d':d},v);compare(immediate(name,h,d,Word.literal(v)),case);cases.append(case)
    for N in (2,3,4,5,8,11,17,26):
        for k in (1,3,7):
            for z in (1,2):
                v='1' if (N+k+z)%2 else '001101'
                case=rank_spec(claims,N,k,z,v);compare(ranked(N,k,z,Word.literal(v)),case);cases.append(case)
    for k in (1,7,12):
        for z in (0,1,3,10):
            case=single(claims,'RES',{'k':k,'z':z},'');compare(resonance(k,z),case);cases.append(case)
    return claims,cases,guards


def long_checks(claims):
    rows=[]
    for i in range(24):
        t=i if i<8 else (1<<(128+(i-8)*31))+i
        e=i if i<8 else (1<<(128+(i-8)*17))+i
        v=Word.literal('001101')
        case=claims.instantiate('LONG',{'t':t,'e':e},v.parts)
        compare(long_return(t,e,v),case)
        rows.append({'t_bits':t.bit_length(),'e_bits':e.bit_length(),'passed':True,'raw_simulated':False})
    trace=json.loads((HERE/'fast.json').read_text());first=trace['local_trace'][0]
    a=int(first['a_before'],16);assert a%243==230;t=(a-230)//243;e=61
    case=claims.instantiate('LONG',{'t':t,'e':e},'');out=long_return(t,e);compare(out,case)
    stop=trace['stop'];assert out['a']==int(stop['a'],16)
    assert equal_words(out['tail'].parts,[(p,int(n,16)) for p,n in stop['tail']])
    row={'source_index':trace['trigger_index'],'return_index':trace['stop_index'],'source_a_bits':a.bit_length(),
        'source_a_mod243':a%243,'e':e,'t':hex(t),'steps':hex(case['steps']),'shift':hex(case['shift']),
        'target_a':hex(out['a']),'target_b':123,'passed':True,'raw_simulated':False}
    return rows,row


def mutants(cases,actuals):
    results=[]
    for key in ('time-minus-one','head-plus-one','missing-first-one','missing-context','wrong-state','wrong-final-bit'):
        witness=None
        for case,actual in zip(cases,actuals):
            pred=want(case);pred={k:(list(v) if isinstance(v,list) else v) for k,v in pred.items()}
            if key=='time-minus-one':pred['steps']-=1
            if key=='head-plus-one':pred['head']+=1
            if key=='wrong-state':pred['q']=1
            if key=='missing-first-one' and pred['ones']:pred['ones'].pop(0)
            if key=='wrong-final-bit' and pred['ones']:pred['ones'].pop()
            if key=='missing-context':
                if case['suffix']!='001101':continue
                pred['ones']=[x for x in pred['ones'] if x<max(pred['ones'])-5]
            if not agrees(actual,pred):witness=actual['id'];break
        assert witness is not None,key
        results.append({'mutant':key,'killed':True,'case':witness})
    return results


def main():
    claims,allcases,guards=campaign()
    cases=[];excluded=[]
    for i,case in enumerate(allcases):
        case=dict(case,id=i,machine=claims.machine)
        if case['steps']>200000:excluded.append({'id':i,'rule':case['rule'],'parameters':case['parameters'],'predicted_steps':case['steps'],'reason':'Outside fixed raw horizon; arithmetic-only'});continue
        cases.append(case)
    assert len(cases)<=256
    source=HERE.parent/'l17-hardening'/'raw_comparator.cpp';binary=HERE/'comparator'
    build=subprocess.run(['g++','-std=c++17','-O2',str(source),'-o',str(binary)],capture_output=True,text=True,check=True)
    req=[request(case,case['id']) for case in cases]
    set_budget(20000000,HERE/'raw-budget.jsonl');actuals,meta=execute(binary,req,HERE/'raw.jsonl.gz')
    for case,out in zip(cases,actuals):
        assert agrees(out,want(case)),case['id']
        if case['steps']:
            lo,hi=case['read_bound'];assert lo<=out['read_min']<=out['read_max']<=hi,(case['id'],'window')
        else:assert out['read_min'] is None and out['read_max'] is None
    long_rows,witness=long_checks(claims)
    (HERE/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    result={'status':'Mathematical collapse/ranking compositions, bounded raw checks; not new Lean proofs or a global invariant.',
        'claims_sha256':hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest(),'comparator_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'build_stderr':build.stderr,'candidate_cases':len(allcases),'raw_cases':len(cases),'excluded_by_horizon':excluded,'excluded_guard_checks':guards,
        'raw_metadata':meta,'read_window_checks':len(cases),'mutations':mutants(cases,actuals),'long_arithmetic_checks':long_rows,'long_reached_witness':witness}
    (HERE/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'candidate_cases':len(allcases),'raw_cases':len(cases),'excluded':len(excluded),'guards':len(guards),
        'raw_transitions':meta['defined_transitions'],'mutants':len(result['mutations']),'long_arithmetic_checks':len(long_rows),'matched_reached_long':witness['passed']},indent=2),flush=True)


if __name__=='__main__':main()
