"""Exact scalar reset map, calibrated against the old contextual word engine."""
from __future__ import annotations
import json,time,hashlib,random
from collections import Counter
from search import HERE,Word,encoded,shape,extended_state_edge,critical_check,Claims


def scalar(N,k,s):
    if N<20 or k<0 or s<0 or (k==0 and s!=0):raise ValueError('Noncanonical reset state')
    q,r=divmod(N,3)
    if r==1:
        if s==1:return None
        if s==0:return 10*q-10,7,2*k+3,3,'A'
        if s==2:return 10*q-6,k+6,0,3,'B'
        return 10*q-6,k+7,s-3,3,'C'
    if r==2:
        if k==0:return 10*q+14,0,0,4,'D'
        if k==1:return 10*q+15+s,0,0,4,'E'
        return 10*q+15,k-1,s,4,'F'
    qs,rs=divmod(s,3)
    constant=2*k+10*qs+([6,-10,14][rs])
    n=10*q+constant
    kk,ss=(7,3) if rs==1 else (0,0)
    rewrites=2+(k>0)+(qs>0)+(2 if rs==2 else 1)
    return n,kk,ss,rewrites,'GHI'[rs]


def make_word(N,k,s):return Word((('1',N),('01',k),('1',s)))


def reset(a,w):
    info=shape(w)
    if a!=0 or info['kind']!='pure' or info['depth']>1 or info['leading_ones']<20:return None
    if info['layers']:k,s=info['layers'][0]
    else:k,s=0,0
    return info['leading_ones'],k,s


def calibration(claims):
    rng=random.Random(194572);rows=[]
    for i in range(500):
        N=rng.randrange(20,3000) if i<350 else (1<<rng.randrange(128,1024))+rng.randrange(10000)
        k=rng.randrange(0,100);s=rng.randrange(0,100) if k else 0
        pred=scalar(N,k,s)
        if pred is None:
            rows.append({'case':i,'stops_before_push':True});continue
        a=0;w=make_word(N,k,s);nsteps=0
        while True:
            out=extended_state_edge(a,w);assert out is not None
            critical_check(a,w,out,claims)
            a,w=out[:2];nsteps+=1
            done=reset(a,w)
            if done is not None:break
            assert nsteps<12
        assert done==pred[:3] and nsteps==pred[3],(i,done,pred,nsteps)
        rows.append({'case':i,'N_bits':N.bit_length(),'k':k,'s':s,'branch':pred[4],'rewrites':nsteps,'passed':True})
    (HERE/'scalar-calibration.json').write_text(json.dumps(rows,indent=2)+'\n')
    return len(rows)


def main(protocol_name='fast-protocol.json',prefix='fast'):
    proto=json.loads((HERE/protocol_name).read_text());bounds=proto['budgets']
    src=(HERE/proto.get('input_report','search.json')).read_bytes();assert hashlib.sha256(src).hexdigest()==proto['source_sha256']
    source=json.loads(src)['stop'];a=int(source['a'],16);w=Word(tuple((p,int(n,16)) for p,n in source['tail']))
    index=int(source['index'],16);start=index
    claims=Claims(HERE.parent/'l17-hardening'/'claims.json')
    if 'calibration_source_sha256' in proto:
        assert hashlib.sha256((HERE/'scalar-calibration.json').read_bytes()).hexdigest()==proto['calibration_source_sha256']
        calibrated=500
    else:calibrated=calibration(claims)
    began=time.monotonic();choices=bytearray();events=[];checkpoints=[];word_edges=[];trigger=None;local=[];counts=Counter()
    rounds=0;state=reset(a,w)
    while index<bounds['maximum_global_rewrites']:
        if time.monotonic()-began>bounds['maximum_wall_seconds']:reason='wall budget';break
        if state is not None and trigger is None:
            N,k,s=state
            if N.bit_length()>bounds['maximum_counter_bits']:reason='counter bit budget';break
            if rounds>=bounds['maximum_coarse_rounds']:reason='coarse round budget';break
            pred=scalar(N,k,s)
            if pred is not None:
                if index+pred[3]>bounds['maximum_global_rewrites']:reason='global rewrite budget';break
                N,k,s,added,code=pred;assert N>=state[0]
                state=(N,k,s);index+=added;rounds+=1;choices.extend(code.encode());counts[code]+=1
                if rounds%10000==0:checkpoints.append(encoded({'index':index,'N':N,'k':k,'s':s,'rounds':rounds}))
                continue
            a=0;w=make_word(*state);state=None
        info=shape(w)
        if trigger is not None and index>trigger:
            if info['kind']=='pure' and info['depth']<=1:reason='triggered excursion returned';break
            if index-trigger>bounds['maximum_local_rewrites_after_first_failed_guard']:reason='local rewrite budget';break
            if info['kind']=='pure' and info['depth']>=3:reason='three pure layers';break
        out=extended_state_edge(a,w)
        if out is None:reason='unsupported';break
        critical_check(a,w,out,claims)
        aa,ww,name,params,cut=out
        row=encoded({'index':index,'rule':name,'a_before':a,'tail_before':w.to_json(),'a_after':aa,'tail_after':ww.to_json(),'parameters':params,'shape_after':shape(ww),'coarse_rounds_before':rounds})
        if name=='F1100':
            events.append(row)
            print('F1100',index,'a bits',a.bit_length(),'c',params['c'],'a mod3',a%3,flush=True)
            bad=a%3!=0
            if proto.get('trigger_mode')=='outside_both':bad=bad and params['c']%3!=2
            if bad and trigger is None:trigger=index
        if trigger is not None:local.append(row)
        word_edges.append(row);a,w=aa,ww;index+=1
        if trigger is None:state=reset(a,w)
    else:reason='global rewrite budget'
    if state is not None:a=0;w=make_word(*state)
    (HERE/(prefix+'-choices.txt')).write_bytes(choices)
    result={'status':'State-only scalar discovery; calibrated coarse map plus guarded old word edges; no new Lean chain or global invariant.',
        'source_sha256':hashlib.sha256(src).hexdigest(),'prior_rewrites':start,'stop_index':index,'coarse_rounds':rounds,'counts':dict(counts),
        'scalar_calibrations':calibrated,'choices_sha256':hashlib.sha256(choices).hexdigest(),'checkpoints':checkpoints,
        'word_edges':word_edges,'events':events,'trigger_index':trigger,'local_trace':local,
        'stop':encoded({'reason':reason,'index':index,'a':a,'tail':w.to_json(),'shape':shape(w)}),'elapsed_seconds':time.monotonic()-began}
    (HERE/(prefix+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('prior_rewrites','stop_index','coarse_rounds','trigger_index','elapsed_seconds')}),flush=True)
    print('STOP',reason,'a bits',a.bit_length(),'shape kind',shape(w)['kind'],flush=True)


if __name__=='__main__':
    import sys
    main(*sys.argv[1:])
