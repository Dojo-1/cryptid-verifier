"""Replay delivered raw evidence from the consumed claims, without actor imports."""
from __future__ import annotations
import gzip,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-hardening'))
from specification import Claims,expand,agrees
from backend import encode


def read_results(name):
    payload=gzip.open(HERE/name,'rb').read()
    meta=json.loads((HERE/(name+'.meta.json')).read_text())
    assert hashlib.sha256(payload).hexdigest()==meta['response_sha256']
    return [json.loads(line) for line in payload.splitlines()],meta


def verify():
    claims=Claims(HERE/'nesting-claims.json')
    summary=json.loads((HERE/'nesting-validation.json').read_text())
    assert hashlib.sha256((HERE/'nesting-claims.json').read_bytes()).hexdigest()==summary['claims_sha256']
    cases=json.loads((HERE/'nesting-cases.json').read_text());actuals,meta=read_results('nesting-raw.jsonl.gz')
    assert len(cases)==len(actuals)==268
    requests=[]
    for row,out in zip(cases,actuals):
        claim=claims.instantiate(row['kind'],row['parameters'],row['suffix'])
        assert row['source']==expand(claim['source']) and row['target']==expand(claim['target'])
        assert row['steps']==claim['steps']
        lo=0 if row['kind']=='NEST' else -16
        q=2 if row['kind']=='NEST' else 0
        shift=claim['shift'];target_lo=shift if row['kind']=='NEST' else -16
        assert (row['lo'],row['q'],row['head'],row['target_lo'],row['target_q'],row['target_head'])==(lo,q,0,target_lo,2,shift)
        assert type(row['id']) is int and row['id']==out['id']
        req={'id':row['id'],'machine':claims.machine,'q':q,'head':0,'limit':claim['steps'],
             'ones':[lo+i for i,b in enumerate(row['source']) if b=='1'],'trace':False}
        want={'q':2,'head':shift,'steps':claim['steps'],'halted':False,
              'ones':[target_lo+i for i,b in enumerate(row['target']) if b=='1']}
        assert agrees(out,want),row['id'];requests.append(req)
    assert hashlib.sha256(encode(requests)).hexdigest()==meta['request_sha256']
    assert sum(row['steps'] for row in actuals)==meta['defined_transitions']
    kernel_specs=json.loads((HERE/'kernel-claims.json').read_text());byname={x['name']:x for x in kernel_specs}
    descriptions=json.loads((HERE/'window-cases.json').read_text());windows,wmeta=read_results('nesting-windows.jsonl.gz')
    reqs=[]
    assert len(windows)==len(descriptions)==80
    for desc,out in zip(descriptions,windows):
        k=byname[desc['kernel']];lo=k['lo'];hi=lo+len(k['input'])-1
        assert (desc['lo'],desc['hi'])==(lo,hi)
        outside=set(desc['outside']);assert all(i<lo or i>hi for i in outside)
        req={'id':desc['id'],'machine':claims.machine,'q':k['q'],'head':k['head'],'limit':k['steps'],
             'ones':sorted(outside|{lo+i for i,b in enumerate(k['input']) if b=='1'}),'trace':True}
        want={'q':k['target_q'],'head':k['target_head'],'steps':k['steps'],'halted':False,
              'ones':sorted(outside|{lo+i for i,b in enumerate(k['target']) if b=='1'})}
        assert desc['id']==out['id'] and agrees(out,want)
        assert lo<=out['read_min']<=out['read_max']<=hi
        assert len(out['reads'])==k['steps']
        reqs.append(req)
    assert hashlib.sha256(encode(reqs)).hexdigest()==wmeta['request_sha256']
    for label in ('O0','UBSan'):
        other,m=read_results('nesting-'+label+'.jsonl.gz')
        assert other==actuals[:64]
        assert hashlib.sha256(encode(requests[:64])).hexdigest()==m['request_sha256']
    return {'raw_endpoints':len(actuals),'windows':len(windows),'compiler_comparisons':128,
            'passed':True,'actor_imported':False}


if __name__=='__main__':print(json.dumps(verify(),indent=2))
