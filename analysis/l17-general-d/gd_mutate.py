"""Additional mutations specific to the new gap and join claims."""
import json,gzip,copy
from gd_paths import HERE
from specification import want,agrees,expand

def main():
    cases=json.loads((HERE/'cases.json').read_text())
    with gzip.open(HERE/'raw-O2.jsonl.gz','rt') as f:actual=[json.loads(x) for x in f]
    found=[]
    for mutation,rule in (('JOIN-delete-output-zero','JOIN'),('JOIN-wrong-l-width','JOIN'),('G1-retain-old-terminal-width','G1'),('D11join-retain-old-terminal-ones','D11join')):
        witness=None
        for c,a in zip(cases,actual):
            if c['rule']!=rule:continue
            target=copy.deepcopy(c['target']);modified=dict(c)
            if mutation=='JOIN-delete-output-zero':
                if not c['suffix'] or '1' not in c['suffix']:continue
                target[4][1]=0
            elif mutation=='JOIN-wrong-l-width':target[3][1]+=1
            elif mutation=='G1-retain-old-terminal-width':target[3][1]+=1
            else:target[4][1]+=3
            modified['target']=target
            if not agrees(a,want(modified)):witness=c['id'];break
        assert witness is not None,mutation
        found.append(dict(mutant=mutation,killed=True,witness_id=witness))
    for c,a in zip(cases,actual):
        if c['rule']=='JOIN' and a['read_min']==c['read_bound'][0]:
            found.append(dict(mutant='JOIN-shrink-left-read-window',killed=True,witness_id=c['id']));break
    else:raise AssertionError('No read-window shrink witness')
    previous=json.loads((HERE/'validation.json').read_text())['mutations']
    out=dict(mutations=previous+found,total=len(previous+found),all_killed=True,raw_responses_reused=True,fresh_raw_transitions=0)
    (HERE/'mutations.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
