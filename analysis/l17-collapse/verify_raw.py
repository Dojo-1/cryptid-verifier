"""Recheck both raw evidence queues using consumed declarative specifications."""
from pathlib import Path
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-hardening'))
from specification import Claims,request,want,agrees,equal_words
from backend import encode
from critic import single,ranked


def verify():
    reports=[]
    for prefix,claimfile,casefile,rawfile,resultfile in [
        ('main','claims.json','cases.json','raw.jsonl.gz','validation.json'),
        ('return2','return2-claims.json','return2-cases.json','return2-raw.jsonl.gz','return2-validation.json')]:
        claims=Claims(HERE/claimfile);result=json.loads((HERE/resultfile).read_text())
        assert hashlib.sha256((HERE/claimfile).read_bytes()).hexdigest()==result['claims_sha256']
        rows=json.loads((HERE/casefile).read_text());payload=gzip.open(HERE/rawfile,'rb').read()
        metadata=json.loads((HERE/(rawfile+'.meta.json')).read_text())
        assert hashlib.sha256(payload).hexdigest()==metadata['response_sha256']
        actuals=[json.loads(x) for x in payload.splitlines()];assert len(rows)==len(actuals)
        requests=[]
        for row,actual in zip(rows,actuals):
            params=row['parameters'];name=row['rule'];v=row['suffix']
            if name=='RANK':case=ranked(claims,**params,v=v)
            elif prefix=='main':case=single(claims,name,params,v)
            else:
                case=claims.instantiate(name,params,v)
                case['read_bound']=[-182*params['v']-84,18*params['v']+2*params['e']+43] if name=='SHORT' else [-24,36]
            assert equal_words(case['source'],row['source']) and equal_words(case['target'],row['target'])
            assert (case['steps'],case['shift'])==(row['steps'],row['shift'])
            case['machine']=claims.machine;requests.append(request(case,row['id']))
            assert actual['id']==row['id'] and agrees(actual,want(case))
            if case['steps']:
                lo,hi=case['read_bound'];assert lo<=actual['read_min']<=actual['read_max']<=hi
            else:assert actual['read_min'] is None and actual['read_max'] is None
        assert hashlib.sha256(encode(requests)).hexdigest()==metadata['request_sha256']
        assert sum(a['steps'] for a in actuals)==metadata['defined_transitions']
        reports.append({'queue':prefix,'raw_endpoints':len(actuals),'raw_transitions':metadata['defined_transitions'],'passed':True})
    return {'queues':reports,'passed':True,'actor_imported':False}


if __name__=='__main__':print(json.dumps(verify(),indent=2))
