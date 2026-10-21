"""Guarded continuation; no speculative 1101 or short-middle endpoint."""
import sys,json,time,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-collapse'))
from fast import scalar,make_word,reset
from search import Word,encoded,shape,extended_state_edge,critical_check,Claims

def main():
    proto=json.loads((HERE/'continuation-protocol.json').read_text())
    path=HERE/proto['source'];raw=path.read_bytes();old=json.loads(raw)
    start=index=int(old['index'],16);a=int(old['a'],16);w=Word(tuple((p,int(n,16)) for p,n in old['tail']))
    state=None;choices=bytearray();events=[];edges=[];checks=[];rounds=0;began=time.monotonic();excursion=None;pushes=[]
    claims=Claims(HERE.parent/'l17-hardening'/'claims.json')
    while index<proto['maximum_global_rewrites']:
        if time.monotonic()-began>proto['maximum_wall_seconds']:reason='wall budget';break
        if state is not None:
            N,k,s=state
            if N.bit_length()>proto['maximum_counter_bits']:reason='bit budget';break
            if rounds>=proto['maximum_coarse_rounds']:reason='round budget';break
            pred=scalar(N,k,s)
            if pred is not None:
                if index+pred[3]<=proto['maximum_global_rewrites']:
                    state=pred[:3];index+=pred[3];rounds+=1;choices.extend(pred[4].encode())
                    if rounds%10000==0:checks.append(encoded({'index':index,'rounds':rounds,'N':state[0],'k':state[1],'s':state[2]}))
                    continue
            a=0;w=make_word(*state);state=None
        info=shape(w)
        if info['kind']=='pure' and info['depth']>=3:reason='three pure layers';break
        if excursion is not None and index-excursion>proto['maximum_excursion_rewrites']:reason='excursion budget';break
        out=extended_state_edge(a,w)
        if out is None:reason='unsupported';break
        critical_check(a,w,out,claims)
        aa,ww,name,params,cut=out
        row=encoded({'index':index,'rule':name,'a_before':a,'tail_before':w.to_json(),'a_after':aa,'tail_after':ww.to_json(),'params':params,'coarse_rounds_before':rounds})
        if name=='F1100':
            events.append(row);excursion=index
            print('push',index,'bits',a.bit_length(),'c',params['c'],'a mod243',a%243,flush=True)
        edges.append(row);a,w=aa,ww;index+=1;state=reset(a,w)
        if state is not None and excursion is not None:
            pushes.append({'push_index':excursion,'return_index':index,'post_push_rewrites':index-excursion-1})
            excursion=None
    else:reason='rewrite budget'
    if state is not None:a=0;w=make_word(*state)
    (HERE/'continuation-choices.txt').write_bytes(choices)
    report={'source_sha256':hashlib.sha256(raw).hexdigest(),'prior_rewrites':start,'stop_index':index,'coarse_rounds':rounds,'choices_sha256':hashlib.sha256(choices).hexdigest(),'checkpoints':checks,'word_edges':edges,'events':events,'returns':pushes,'stop':encoded({'reason':reason,'index':index,'a':a,'tail':w.to_json(),'shape':shape(w)}),'elapsed_seconds':time.monotonic()-began}
    (HERE/'continuation.json').write_text(json.dumps(report,indent=2)+'\n')
    print('STOP',reason,index,'a bits',a.bit_length(),'tail parts',len(w.parts),'seconds',report['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
