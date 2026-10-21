"""Read-only result verifier plus a sampled dense-Python literal replay."""
import json,gzip,hashlib,sys
from gd_paths import HERE,FRONTIER
from specification import request,want,agrees,equal_words
from gd_critic import Claims,single
from backend import encode
sys.path.insert(0,str(FRONTIER))
from reference import run

def main():
    cases=json.loads((HERE/'cases.json').read_text());report=json.loads((HERE/'validation.json').read_text())
    assert report['claims_sha256']==hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest()
    assert report['comparator_source_sha256']==hashlib.sha256((HERE.parent/'l17-hardening/raw_comparator.cpp').read_bytes()).hexdigest()
    claims=Claims(HERE/'claims.json')
    for c in cases:
        spec=single(claims,c['rule'],c['parameters'],c['suffix'])
        assert equal_words(c['source'],spec['source']) and equal_words(c['target'],spec['target'])
        assert (c['steps'],c['shift'])==(spec['steps'],spec['shift'])
    checked=0
    for item in report['raw_metadata']:
        label=item['label'];payload=gzip.decompress((HERE/('raw-'+label+'.jsonl.gz')).read_bytes())
        assert hashlib.sha256(payload).hexdigest()==item['response_sha256']
        actual=[json.loads(x) for x in payload.splitlines()]
        selected=cases if label=='O2' else cases[::12]
        assert len(actual)==len(selected)
        assert hashlib.sha256(encode([request(c,c['id']) for c in selected])).hexdigest()==item['request_sha256']
        for c,a in zip(selected,actual):
            assert a['id']==c['id'] and agrees(a,want(c));checked+=1
            if c['read_bound'] is not None:assert c['read_bound'][0]<=a['read_min']<=a['read_max']<=c['read_bound'][1]
    fresh=0;pycases=0
    from specification import expand
    for c in cases[::30]:
        out=run(expand(c['source']),c['steps']);fresh+=out['steps'];pycases+=1
        literal=dict(q=out['q'],head=out['head'],steps=out['steps'],halted=out['halted'],ones=sorted(out['tape']))
        assert agrees(literal,want(c)),c['id']
    w=json.loads((HERE/'window-cases.json').read_text());acts=[json.loads(x) for x in gzip.decompress((HERE/'windows.jsonl.gz').read_bytes()).splitlines()]
    assert len(acts)==len(w['expected'])==len(w['requests'])
    assert hashlib.sha256(encode(w['requests'])).hexdigest()==report['window_metadata']['request_sha256']
    assert hashlib.sha256(gzip.decompress((HERE/'windows.jsonl.gz').read_bytes())).hexdigest()==report['window_metadata']['response_sha256']
    for expected,actual in zip(w['expected'],acts):assert agrees(actual,expected)
    result=dict(passed=True,rechecked_stored_endpoints=checked,rechecked_windows=len(acts),dense_python_cases=pycases,dense_python_fresh_defined_transitions=fresh,independent_code_path=True,independent_authorship=False)
    with (HERE/'raw-python-budget.jsonl').open('a') as ledger:ledger.write(json.dumps(dict(dense_python_cases=pycases,fresh_defined_transitions=fresh,replayed=True),sort_keys=True)+'\n')
    (HERE/'raw-recheck.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
