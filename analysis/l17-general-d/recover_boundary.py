"""Recover first outside-both push from the frozen two-million reset state."""
import sys,json,time,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-collapse'))
from fast import scalar,make_word,reset
from search import Word,encoded,shape,extended_state_edge,critical_check,Claims

def main():
    proto=json.loads((HERE/'protocol.json').read_text());bud=proto['budgets']
    path=HERE.parent/'l17-collapse'/'guard.json';raw=path.read_bytes();old=json.loads(raw)
    start=index=int(old['stop']['index'],16);assert start==2000000
    a=int(old['stop']['a'],16);w=Word(tuple((p,int(n,16)) for p,n in old['stop']['tail']))
    state=reset(a,w);assert state is not None
    choices=bytearray();events=[];edges=[];checks=[];rounds=0;began=time.monotonic();trigger=None
    claims=Claims(HERE.parent/'l17-hardening'/'claims.json')
    while index<bud['maximum_global_rewrites']:
        if time.monotonic()-began>bud['maximum_wall_seconds']:reason='wall budget';break
        if state is not None:
            N,k,s=state
            if N.bit_length()>bud['maximum_counter_bits']:reason='bit budget';break
            if rounds>=bud['maximum_coarse_rounds']:reason='round budget';break
            pred=scalar(N,k,s)
            if pred is not None:
                state=pred[:3];index+=pred[3];rounds+=1;choices.extend(pred[4].encode())
                if rounds%10000==0:checks.append(encoded({'index':index,'rounds':rounds,'N':state[0],'k':state[1],'s':state[2]}))
                continue
            a=0;w=make_word(*state);state=None
        out=extended_state_edge(a,w)
        if out is None:reason='unsupported';break
        critical_check(a,w,out,claims)
        aa,ww,name,params,cut=out
        row=encoded({'index':index,'rule':name,'a_before':a,'tail_before':w.to_json(),'a_after':aa,'tail_after':ww.to_json(),'params':params,'coarse_rounds_before':rounds})
        if name=='F1100':
            events.append(row);print('push',index,'bits',a.bit_length(),'c',params['c'],'a mod243',a%243,flush=True)
            if a%3!=0 and params['c']%3!=2:
                trigger=index
                (HERE/'boundary.json').write_text(json.dumps(encoded({'index':index,'a':a,'tail':w.to_json(),'bits':a.bit_length(),'a_mod243':a%243}),indent=2)+'\n')
                assert a.bit_length()==977821 and a%243==62 and params['c']==39
                reason='recovered Claude boundary';break
        edges.append(row);a,w=aa,ww;index+=1;state=reset(a,w)
    else:reason='rewrite budget'
    if state is not None:a=0;w=make_word(*state)
    (HERE/'recovery-choices.txt').write_bytes(choices)
    report={'source_sha256':hashlib.sha256(raw).hexdigest(),'prior_rewrites':start,'stop_index':index,'coarse_rounds':rounds,'choices_sha256':hashlib.sha256(choices).hexdigest(),'checkpoints':checks,'word_edges':edges,'events':events,'stop':encoded({'reason':reason,'index':index,'a':a,'tail':w.to_json()}),'elapsed_seconds':time.monotonic()-began}
    (HERE/'recovery.json').write_text(json.dumps(report,indent=2)+'\n')
    print('STOP',reason,index,'coarse rounds',rounds,'seconds',report['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
