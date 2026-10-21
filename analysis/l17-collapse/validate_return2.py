"""Reached two-decision return and an explicit candidate-invariant exit."""
from __future__ import annotations
import hashlib,json,subprocess
from search import HERE,Word
from extend import rules
from actors import cycle
from specification import Claims,equal_words,request,want,agrees
from backend import execute,set_budget


def short(v,e,suffix=Word()):
    if type(v) is not int or type(e) is not int or v<0 or e<0:raise ValueError('v,e>=0 integers required')
    f=rules.core1100(9*v+11,e+9,suffix)
    first=cycle(18*v+10,7,2*e+5,suffix);assert first['r']==1
    last=cycle(60*v+24,14,2*e+2,suffix);assert last['r']==0
    return dict(last,steps=f.steps+first['steps']+last['steps'],shift=f.shift+first['shift']+last['shift'])


def candidate_exit(suffix=Word()):
    w=suffix.prepend(('1',1),('01',8),('1',4))
    f=rules.rewrite(9,w);assert f.rule=='core111'
    e=rules.rewrite(f.a,f.tail);assert e.rule=='entry1'
    q=rules.rewrite(e.a,e.tail);assert q.rule=='countdown111'
    return {'a':q.a,'tail':q.tail,'steps':f.steps+e.steps+q.steps,'shift':f.shift+e.shift+q.shift}


def compare(out,claim):
    assert equal_words([('01',out['a'])]+list(out['tail'].parts),claim['target'])
    assert (out['steps'],out['shift'])==(claim['steps'],claim['shift'])


def main():
    claims=Claims(HERE/'return2-claims.json');cases=[]
    for v in range(4):
        for e in range(4):
            claim=claims.instantiate('SHORT',{'v':v,'e':e},'001101');compare(short(v,e,Word.literal('001101')),claim)
            claim.update({'machine':claims.machine,'id':2000+len(cases),'read_bound':[-182*v-84,18*v+2*e+43]});cases.append(claim)
    claim=claims.instantiate('EXIT',{},'');compare(candidate_exit(),claim)
    claim.update({'machine':claims.machine,'id':2000+len(cases),'read_bound':[-24,36]});cases.append(claim)
    ledger=HERE/'raw-budget.jsonl';used=sum(json.loads(x)['executed_defined_transitions'] for x in ledger.read_text().splitlines())
    assert len(cases)+json.loads((HERE/'validation.json').read_text())['raw_cases']<=256
    set_budget(20000000-used,ledger)
    source=HERE.parent/'l17-hardening'/'raw_comparator.cpp';binary=HERE/'comparator'
    if not binary.exists():subprocess.run(['g++','-std=c++17','-O2',str(source),'-o',str(binary)],check=True)
    actuals,meta=execute(binary,[request(c,c['id']) for c in cases],HERE/'return2-raw.jsonl.gz')
    for c,a in zip(cases,actuals):
        assert agrees(a,want(c)),c['id']
        lo,hi=c['read_bound'];assert lo<=a['read_min']<=a['read_max']<=hi
    huge=[]
    for i in range(8):
        v=(1<<(128+31*i))+i;e=(1<<(128+17*i))+i
        compare(short(v,e),claims.instantiate('SHORT',{'v':v,'e':e},''));huge.append({'v_bits':v.bit_length(),'e_bits':e.bit_length(),'passed':True})
    guard=json.loads((HERE/'guard.json').read_text());event=guard['events'][0];A=int(event['a_before'],16)
    assert A%9==2;v=(A-11)//9;e=59;out=short(v,e);compare(out,claims.instantiate('SHORT',{'v':v,'e':e},''))
    target=next(r for r in guard['word_edges'] if int(r['index'],16)==1803916)
    assert out['a']==int(target['a_after'],16) and equal_words(out['tail'].parts,[(p,int(n,16)) for p,n in target['tail_after']])
    (HERE/'return2-cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    result={'status':'Bounded raw validation and conditional arithmetic; not Lean formalized.','claims_sha256':hashlib.sha256((HERE/'return2-claims.json').read_bytes()).hexdigest(),
            'raw_cases':len(cases),'raw_metadata':meta,'huge_checks':huge,'matched_reached_source':1803910,'matched_reached_target':1803917,
            'candidate_exit':{'source':[9,1,8,4],'target':[16,1,15,1],'steps':295,'shift':-25,'blank_reachability_asserted':False}}
    (HERE/'return2-validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'raw_cases':len(cases),'raw_transitions':meta['defined_transitions'],'reached_match':True,'candidate_exit_raw_checked':True},indent=2))


if __name__=='__main__':main()
