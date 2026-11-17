"""Matched translated requests in O2,O0 andUBSan build modes."""
import json,subprocess
from paths import HERE,BASE
from campaign import request,want
from specification import agrees
import backend
def main():
    cases=json.loads((HERE/'cases.json').read_text());selected=[];seen=set()
    for c in cases:
        if c['label'] not in seen:selected.append(c);seen.add(c['label'])
    requests=[];expected=[]
    for i,c in enumerate(selected):
        offset=(-1 if i%2 else 1)*(i+13);req=request(c,i);req['head']+=offset;req['ones']=[x+offset for x in req['ones']]
        w=want(c);w['head']+=offset;w['ones']=[x+offset for x in w['ones']];requests.append(req);expected.append(w)
    ledger=HERE/'raw-budget.jsonl';spent=sum(json.loads(s)['executed_defined_transitions'] for s in ledger.read_text().splitlines());backend.set_budget(20000000-spent,ledger)
    builds={}
    for name,flags in (('o2',['-O2']),('o0',['-O0']),('ubsan',['-O1','-g','-fsanitize=undefined','-fno-sanitize-recover=all'])):
        binary=HERE/'build'/('control-'+name);subprocess.run(['g++','-std=c++17',*flags,str(BASE/'l17-hardening/raw_comparator.cpp'),'-o',str(binary)],check=True)
        got,meta=backend.execute(binary,requests,HERE/('control-'+name+'.jsonl.gz'));assert all(agrees(r,w) for r,w in zip(got,expected));builds[name]=meta
    out=dict(passed=True,matched_translated_inputs=len(requests),builds=builds,compiler=subprocess.run(['g++','--version'],capture_output=True,text=True,check=True).stdout.splitlines()[0],scope='Same compiler and author; different modes and translated coordinates are controls, not independent authorship.')
    (HERE/'controls-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
