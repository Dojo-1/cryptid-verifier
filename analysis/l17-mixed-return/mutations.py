"""Twenty planted in-memory errors checked against saved literal outcomes."""
import json,gzip,copy
from paths import HERE
from specification import materialize,agrees
from campaign import want
from raw import replay
def main():
    cases=json.loads((HERE/'cases.json').read_text());rows=json.loads((HERE/'claims.json').read_text())['rules']
    with gzip.open(HERE/'raw-results.jsonl.gz','rt') as f:actual=[json.loads(x) for x in f]
    out=[]
    def record(name,killed,witness):out.append(dict(name=name,killed=bool(killed),witness=witness));assert killed,name
    def pick(label,predicate=lambda c:True):return next((c,r) for c,r in zip(cases,actual) if c['label']==label and predicate(c))
    def target_mutation(label,index,value,name,predicate=lambda c:True):
        c,r=pick(label,predicate);row=copy.deepcopy(rows[label]);row['target'][index]=value;m=c['metadata'];target=''.join(w*n for w,n in materialize(row['target'],m['p'],m['v']));bad=copy.deepcopy(c);bad['target']=m['pad']+target+m['extra'];record(name,not agrees(r,want(bad)),m['p'])
    def field_mutation(label,field,change,name,predicate=lambda c:True):
        c,r=pick(label,predicate);bad=copy.deepcopy(c);bad[field]=change(c);record(name,not agrees(r,want(bad)),c['metadata'])
    target_mutation('C2_s1',5,['1','m-6'],'consume_six_instead_of_nine_ones')
    field_mutation('C2_s2','steps',lambda c:c['steps']-2*c['metadata']['p']['c'],'omit_a_D_sweep_clock')
    target_mutation('C2_large',4,['0',0],'drop_C2_internal_gap')
    field_mutation('C3','steps',lambda c:c['steps']-2*c['metadata']['p']['s'],'halve_C3_previous_run_clock')
    target_mutation('C4',5,['1','2*s-4'],'shorten_C4_middle_run',lambda c:c['metadata']['p']['s']>=2)
    target_mutation('C5_s5',5,['1','m-6'],'wrong_C5_unused_ones')
    target_mutation('C5_large',6,['01',9],'wrong_C5_output_width')
    field_mutation('kernel:C2B','qq',lambda c:2,'forget_B_exit_mode')
    field_mutation('kernel:C5B','steps',lambda c:42,'omit_C5_B_bounce')
    field_mutation('D_zero_turn','head',lambda c:-2,'wrong_empty_run_head_shift')
    field_mutation('D_three_B','head',lambda c:3,'forget_parameterized_B_scan',lambda c:c['metadata']['p']['n']>=2)
    target_mutation('D_pair2',1,['01',0],'drop_pair_before_middle_one')
    field_mutation('D_large','steps',lambda c:c['steps']+6,'wrong_D_transfer_clock')
    field_mutation('C_large','head',lambda c:c['head']+1,'C_transfer_one_cell_short')
    field_mutation('mixed-original-C','head',lambda c:0,'forget_original_C_shift')
    field_mutation('mixed-A','steps',lambda c:166,'extrapolate_166_to_all_counters',lambda c:c['metadata']['p']!=6)
    target_mutation('C_pair4',1,['010',1],'corrupt_C4_fixed_suffix')
    field_mutation('B_to_D','steps',lambda c:c['steps']+1,'charge_B111_nine_instead_of_eight')
    r=replay(dict(q=5,head=0,limit=1,ones=[0]));record('count_undefined_as_one',r['steps']!=1,'F1')
    kernel=json.loads((HERE/'kernels.json').read_text())['C2B'];src='0'+kernel['input'][1:];got=replay(dict(q=2,head=0,limit=38,ones=[kernel['lo']+i for i,b in enumerate(src) if b=='1']))
    expected=dict(q=1,head=4,steps=38,halted=False,ones=[kernel['lo']+i for i,b in enumerate(kernel['output']) if b=='1']);record('weaken_C2_previous_pair_window',not agrees(got,expected),src)
    assert len(out)==20
    result=dict(passed=True,planted=len(out),killed=sum(x['killed'] for x in out),checks=out,scope='Manual ACAF controls,same author,no on-disk source mutation.')
    (HERE/'mutation-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
