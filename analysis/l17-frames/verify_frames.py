"""Verify retained literal requests/responses without importing frame actors."""
import gzip,json,hashlib
from frame_paths import HERE,HARDENING
from backend import encode
from reference import OPS

def main():
    report=json.loads((HERE/'frames-results.json').read_text());requests=json.loads((HERE/'raw-requests.json').read_text())
    payload=gzip.decompress((HERE/'raw-traces.jsonl.gz').read_bytes());actual=[json.loads(x) for x in payload.splitlines()]
    assert len(requests)==len(actual)==32
    assert hashlib.sha256(encode(requests)).hexdigest()==report['raw_metadata']['request_sha256']
    assert hashlib.sha256(payload).hexdigest()==report['raw_metadata']['response_sha256']
    assert hashlib.sha256((HARDENING/'raw_comparator.cpp').read_bytes()).hexdigest()==report['comparator_source_sha256']
    checked=0
    for req,out in zip(requests,actual):
        assert req['id']==out['id'];q=req['q'];h=req['head'];ones=set(req['ones'])
        for qq,hh,b in out['reads']:
            assert (q,h,int(h in ones))==(qq,hh,b)
            value,d,q=OPS[q][b]
            if value:ones.add(h)
            else:ones.discard(h)
            h+=d;checked+=1
        assert (q,h,sorted(ones),len(out['reads']))==(out['q'],out['head'],out['ones'],out['steps'])
        assert out['halted']==(OPS[q][int(h in ones)] is None)
    result=dict(passed=True,requests=32,defined_reads_replayed=checked,imports_frame_actor=False,source_hash_bound=True,fresh_Cpp_transitions=0)
    (HERE/'frames-recheck.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
