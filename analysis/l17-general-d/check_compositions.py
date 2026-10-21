"""Declarative primitive compositions, separate from the actor and Word code."""
import json,gzip,hashlib,sys
from gd_paths import HERE
sys.path.insert(0,str(HERE.parent/'l17-stack'))
from verify_symbolic import next_state
from specification import Claims,skip,matching_prefix,equal_words
from gd_critic import single,ranked_exit

def old_step(a,w,claims):
    aa,ww,name=next_state(a,w,claims)
    if name=='N':p={'a':a,'q':matching_prefix(w,'01')//2};cut=2*p['q']
    elif name=='Q':p={'a':a,'q':matching_prefix(w,'1')//3};cut=3*p['q']
    elif name=='E':p={};cut=1
    elif name in ('P','Z'):p={'a':a};cut=2
    else:
        c=matching_prefix(w,'10')//2
        if name=='F100':
            # The longest (10) prefix may include the last10 of terminal100.
            from specification import first_bits
            if first_bits(skip(w,2*c),1)=='0':c-=1
        p={'a':a,'c':c};cut=2*c+(4 if name=='F1100' else 3)
    claim=claims.instantiate(name,p,skip(w,cut))
    assert equal_words([('01',a)]+w,claim['source']) and equal_words([('01',aa)]+ww,claim['target'])
    return aa,ww,name,claim['steps'],claim['shift']

def check(case,new,old):
    name=case['rule'];p=case['parameters'];a=0;w=case['source'];total=head=0
    if name=='JOIN':return False # Kernel proof plus literal checks, not the old section dispatcher.
    if name in ('RET39','RET729'):
        assert w[0][0]=='01';a=w[0][1];w=w[1:]
    if name in ('M0','K0'):sequence=[]
    elif name in ('RET39','RET729'):sequence=['F1100']+['E','Q','F111']*3+['E','Q','P','Z']*2+['E','Q','N']
    else:
        sequence=['E']+(['Q'] if p['q'] else [])
        if name=='D0':sequence+=['N']
        elif name in ('D1','D12'):sequence+=['F111']
        elif name in ('D2','G2','G2k'):sequence+=['P','Z']
        elif name=='G0':sequence+=(['N'] if p['k'] else [])+['Z']
        elif name=='G1':sequence+=['F100']
        elif name in ('D11','D11join'):pass
        elif name=='JOIN':return False # Validated by kernels/induction and bounded literal checks.
        else:raise ValueError(name)
    for required in sequence:
        a,w,name,steps,shift=old_step(a,w,old);assert name==required,(case['rule'],required,name)
        total+=steps;head+=shift
    if case['rule']=='D11join':
        suffix=[('1',p['s']-2)]
        v=case['suffix'];v=[(v,1)] if isinstance(v,str) and v else ([] if isinstance(v,str) else v)
        joined=new.instantiate('JOIN',{'a':1+5*p['q'],'c':p['k'],'l':p['l']},suffix+v)
        assert equal_words([('01',a)]+w,joined['source'])
        a=0;w=joined['target'];total+=joined['steps'];head+=joined['shift']
    assert equal_words([('01',a)]+w,case['target']),(case['rule'],'composition endpoint')
    assert (total,head)==(case['steps'],case['shift']),(case['rule'],'composition time/head')
    return True

def main():
    new=Claims(HERE/'claims.json');old=Claims(HERE.parent/'l17-hardening/claims.json')
    cases=json.loads((HERE/'cases.json').read_text());checked=0
    for c in cases:checked+=check(c,new,old)
    for t in (0,1,2,10,100,2**128+5,2**2048+17):check(single(new,'RET39',{'t':t},'001101'),new,old)
    family=Claims(HERE/'return-family-claims.json');family_count=0
    for t in (0,1,2**512+17):
        for c in (11,12,39,75,2**128+1):
            case=single(family,'RET729',{'t':t,'c':c},'001101');check(case,new,old);family_count+=1
    d=json.loads((HERE/'boundary.json').read_text());A=int(d['a'],16);assert A%729==548;t=(A-548)//729
    case=single(new,'RET39',{'t':t},'');check(case,new,old)
    run=json.loads((HERE/'continuation.json').read_text());source=int(d['index'],16);at=source+21
    checkpoint=next(r for r in run['word_edges'] if int(r['index'],16)==at)
    assert equal_words(case['target'],[('01',int(checkpoint['a_before'],16))]+[(p,int(n,16)) for p,n in checkpoint['tail_before']])
    out=ranked_exit(2*A-12,7,65);assert [r['r'] for r in out['path']]==[1,1,1,2,2,0]
    witness=dict(source_rewrite=source,return_to_one_tail_rewrite=at,reset_rewrite=source+24,A_bits=A.bit_length(),A_mod729=A%729,t_hex=hex(t),target_a_hex=hex(1000000*t+740902),target_b=56,target_k=7,target_s=3,steps_hex=hex(case['steps']),shift_hex=hex(case['shift']),raw_simulated=False,conditional_on_contextual_rules=True)
    with gzip.GzipFile(filename='',mode='wb',fileobj=(HERE/'return39-witness.json.gz').open('wb'),mtime=0) as f:f.write((json.dumps(witness,indent=2)+'\n').encode())
    result=dict(passed=True,old_rule_compositions=checked,JOIN_literal_only_cases=sum(c['rule']=='JOIN' for c in cases),RET39_arithmetic_checks=8,RET729_arithmetic_checks=family_count,return_family_claims_sha256=hashlib.sha256((HERE/'return-family-claims.json').read_bytes()).hexdigest(),matched_huge_reached_endpoint=True,source_to_first_one_tail_rewrites=21,D_decisions=[1,1,1,2,2,0],rank_exit=out['exit'],raw_simulated_large_RETURN=False,new_claims_sha256=hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest(),old_claims_sha256=hashlib.sha256((HERE.parent/'l17-hardening/claims.json').read_bytes()).hexdigest(),actor_imported=False,word_class_imported=False)
    (HERE/'composition-checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
