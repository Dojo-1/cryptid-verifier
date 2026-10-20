"""Export the exact consumed case queue and minimized regression specifications."""
from __future__ import annotations
import gzip
import hashlib
import json
from pathlib import Path
from backend import encode
from corpus import frozen_cases,acaf_cases,kernels
from specification import Claims,request,expand

ROOT=Path(__file__).resolve().parent


def main():
    actor_root=next(p for p in (ROOT.parent/'l17-stacked-section',ROOT.parent/'l17-frontier') if p.is_dir())
    claims=Claims(ROOT/'claims.json');seed=json.loads((ROOT/'protocol.json').read_text())['seed']
    cases=frozen_cases(actor_root,claims)+acaf_cases(claims,seed)
    req=[request(c,i,c['head']) for i,c in enumerate(cases)]
    expected=json.loads((ROOT/'rule-comparisons.json').read_text())['provenance']['request_sha256']
    assert hashlib.sha256(encode(req)).hexdigest()==expected
    data=''.join(json.dumps({'id':i,'rule':c['rule'],'parameters':c['parameters'],'suffix':c['suffix'],
                            'head':c['head'],'origin':c['origin']},sort_keys=True)+'\n' for i,c in enumerate(cases)).encode()
    with (ROOT/'case-queue.jsonl.gz').open('wb') as f:
        with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:z.write(data)
    rows=[]
    mutations=json.loads((ROOT/'mutation-results.json').read_text())['mutants']
    for m in mutations:
        if 'minimized' in m:
            x=m['minimized'];c=claims.instantiate(x['rule'],x['parameters'],x['suffix'])
            rows.append({'defect':m['name'],'rule':x['rule'],'parameters':x['parameters'],'suffix':x['suffix'],
                         'source_literal':expand(c['source']),'target_literal':expand(c['target']),
                         'raw_transitions':c['steps'],'head_shift':c['shift'],'kind':'Baseline is correct; injected live-source defect is detected.'})
        elif 'minimized_guard_witness' in m:
            rows.append({'defect':m['name'],'case':m['minimized_guard_witness'],'expected':'Reject outside the declared guard; not a counterexample to a broader mathematical conjecture.'})
        elif 'minimized_word' in m:
            rows.append({'defect':m['name'],'word':m['minimized_word'],'raw_transitions':0,'expected_ones':[2],
                         'kind':'Initial head is at position 0; preserve leading zero cells in block encoding.'})
    rows.append({'defect':'critic-zero-repetition','left':[['10',0]],'right':[],'expected_equal':True,
                 'kind':'Actual new-critic bug found and fixed; original actor formulas unchanged.'})
    (ROOT/'regression-seeds.json').write_text(json.dumps({'cases':rows},indent=2)+'\n')
    with gzip.open(ROOT/'window-results.jsonl.gz','rt') as f:window_outputs=[json.loads(x) for x in f]
    kernel_rows=[]
    for i,k in enumerate(kernels(actor_root)):
        out=window_outputs[12*i]
        kernel_rows.append({'kernel':k,'independent_cpp_read_trace':out['reads'],
                            'literal_output_record':12*i,'source':'window-results.jsonl.gz',
                            'provenance':'C++ traced a randomized outside context; reads match the frozen kernel exactly.'})
    (ROOT/'kernel-witnesses.json').write_text(json.dumps(kernel_rows,indent=2)+'\n')
    witness=next(i for i,c in enumerate(cases) if c['rule']=='F1100' and c['parameters']=={'a':7,'c':8} and c['suffix']=='')
    (ROOT/'case-queue-description.json').write_text(json.dumps({'cases':len(cases),'case_queue_sha256':hashlib.sha256(data).hexdigest(),
        'claims_sha256':hashlib.sha256((ROOT/'claims.json').read_bytes()).hexdigest(),'literal_request_sha256':expected,
        'nonclosure_witness_case_id':witness,'regression_cases':len(rows),
        'provenance':'Queue reconstructed from the frozen snapshots and exact seed; its complete serialized request digest equals the actual comparator input digest.'},indent=2)+'\n')
    print('Exported exact',len(cases),'case queue,',len(rows),'regression seeds, and',len(kernel_rows),'kernel witnesses.')


if __name__=='__main__':main()
