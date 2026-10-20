"""Verify the saved raw records from the consumed claim; no actor imports."""
from pathlib import Path
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-hardening'))
from specification import Claims,request,want,agrees,equal_words
from backend import encode


def verify():
    claims=Claims(HERE/'claims.json')
    summary=json.loads((HERE/'results.json').read_text())
    assert hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest()==summary['claims_sha256']
    payload=gzip.open(HERE/'raw.jsonl.gz','rb').read()
    metadata=json.loads((HERE/'raw.jsonl.gz.meta.json').read_text())
    assert hashlib.sha256(payload).hexdigest()==metadata['response_sha256']
    actuals=[json.loads(x) for x in payload.splitlines()]
    cases=json.loads((HERE/'cases.json').read_text());requests=[]
    assert len(cases)==len(actuals)==163
    for index,(case,actual) in enumerate(zip(cases,actuals)):
        claim=claims.instantiate('RETURN',case['parameters'],case['suffix'])
        assert equal_words(claim['source'],case['source']) and equal_words(claim['target'],case['target'])
        assert (case['steps'],case['shift'])==(claim['steps'],claim['shift'])
        assert actual['id']==index
        claim['machine']=claims.machine
        requests.append(request(claim,index))
        assert agrees(actual,want(claim)),index
    assert hashlib.sha256(encode(requests)).hexdigest()==metadata['request_sha256']
    assert sum(x['steps'] for x in actuals)==metadata['defined_transitions']
    return {'raw_endpoints':len(actuals),'raw_transitions':metadata['defined_transitions'],'passed':True,'actor_imported':False}


if __name__=='__main__':print(json.dumps(verify(),indent=2))
