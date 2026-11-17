"""Supplementary guard-corner replay for the stronger named mixed lemma."""
import itertools,json
from paths import HERE
from campaign import mixed_case,request,want,budget
from specification import agrees
from raw import replay
import backend
def main():
    cases=[mixed_case(p,c,v,embedded) for p,c,v,embedded in itertools.product((4,5),(1,2),('','001101'),(False,True))]
    requests=[request(c,i) for i,c in enumerate(cases)];budget()
    actual,meta=backend.execute(HERE/'build/raw-o2',requests,HERE/'named-corners-raw.jsonl.gz')
    for c,req,r in zip(cases,requests,actual):
        py=replay(req);assert agrees(r,want(c)) and agrees(py,want(c));assert r['reads']==py['reads'];assert r['read_min']>=c['bounds'][0] and r['read_max']<=c['bounds'][1]
    (HERE/'named-corner-cases.json').write_text(json.dumps(cases,separators=(',',':'))+'\n')
    out=dict(passed=True,checks=len(cases),guard='Named mixed lemma p>=4,c>=1; original C-entry a=p+1>=5.',raw_metadata=meta,scope='Supplementary lower-guard corners;not counted in the846-case main campaign.')
    (HERE/'named-corner-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
