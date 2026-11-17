"""Twenty planted prediction/clock/grammar mistakes, entirely in memory."""
import copy,gzip,json
from paths import HERE
from scanner import compile_stack,left_word
from campaign import want
from specification import agrees
from raw import replay

def main():
    cases=json.loads((HERE/'cases.json').read_text())
    with gzip.open(HERE/'raw-results.jsonl.gz','rt') as f:raw=[json.loads(x) for x in f]
    checks=[]
    def record(name,killed,witness):
        checks.append(dict(name=name,killed=bool(killed),witness=witness));assert killed,name
    def pick(rule):
        return next((c,r) for c,r in zip(cases,raw) if c['metadata'].get('rule')==rule and not c['metadata']['embedded'] and c['metadata']['p'].get('h',0)>=1)
    for name,label,alter in (
      ('zero_even_positive','drop_return_gap',lambda c:c['target'].replace('0010','010',1)),
      ('zero_odd','shorten_leading_run',lambda c:c['target'][2:]),
      ('hundred_even','use_nine_terminal_ones',lambda c:c['target'][:-len(c['metadata']['v'])]+'11'+c['metadata']['v'] if c['metadata']['v'] else c['target']+'11'),
      ('hundred_odd','drop_one_X_block',lambda c:c['target'].replace('111010','',1)),
      ('eleven_even','drop_a_pair',lambda c:c['target'].replace('01','',1)),
      ('eleven_odd','wrong_leading_run',lambda c:c['target'][4:]),
    ):
        c,r=pick(name);bad=copy.deepcopy(c);bad['target']=alter(c)
        record(label,not agrees(r,want(bad)),dict(rule=name,p=c['metadata']['p']))
    c,r=next((c,r) for c,r in zip(cases,raw) if c['label']=='scanner' and c['metadata']['tokens']==['01','101'])
    for name,field,delta in (('charge101_as_two_steps','steps',-11),('move101_only_two_cells','head',-1)):
        bad=copy.deepcopy(c);bad[field]+=delta;record(name,not agrees(r,want(bad)),c['metadata'])
    runs=c['metadata']['runs'];v=c['metadata']['v'];stack=compile_stack(runs,c['metadata']['tokens'])[0]
    bad=copy.deepcopy(c);wrong=list(stack);wrong[-2]+=1;bad['target']=left_word(wrong)+v
    record('remove_only_one_old_pair',not agrees(r,want(bad)),c['metadata'])
    bad=copy.deepcopy(c);bad['target']=left_word(stack[:-2]+[stack[-2]+stack[-1]])+v
    record('omit_new_left_gap',not agrees(r,want(bad)),c['metadata'])
    bad=copy.deepcopy(c);bad['target']=left_word(compile_stack(runs,c['metadata']['tokens'][::-1])[0])+v
    record('reverse_token_order',not agrees(r,want(bad)),c['metadata'])
    c,r=next((c,r) for c,r in zip(cases,raw) if c['label']=='scanner' and c['metadata']['tokens']==['101','01']);v=c['metadata']['v'];prefix=c['target'][:-len(v)]
    bad=copy.deepcopy(c);bad['target']=prefix[:-2]+'01'+v
    record('leave01_unwritten',not agrees(r,want(bad)),c['metadata'])
    for kernel,label,field,delta in (('C6','C6_wrong_head','head',1),('D6','D6_wrong_time','steps',-8),('A100','A100_one_step_short','steps',-1),('Cpop','Cpop_wrong_head','head',1)):
        c,r=next((c,r) for c,r in zip(cases,raw) if c['label']=='kernel:'+kernel);bad=copy.deepcopy(c);bad[field]+=delta
        record(label,not agrees(r,want(bad)),kernel)
    mixed=json.loads((HERE/'mixed-boundary.json').read_text());predicted=2*6+2*7+102
    record('homogeneous_return_applied_to_mixed_tokens',predicted!=mixed['literal_C_section_return']['steps'],dict(predicted=predicted,actual=mixed['literal_C_section_return']['steps']))
    c,r=pick('zero_even_positive');bad=copy.deepcopy(c);bad['target']=c['target'].replace('00','0')
    record('trim_interior_double_zero',not agrees(r,want(bad)),c['metadata'])
    source='0010101';got=replay(dict(q=0,head=0,limit=13,ones=[-4+i for i,b in enumerate(source) if b=='1']))
    expected=dict(q=0,head=3,steps=13,halted=False,ones=[-4+i for i,b in enumerate('0101010') if b=='1'])
    record('weaken_A101_left_window',not agrees(got,expected),source)
    got=replay(dict(q=5,head=0,limit=1,ones=[0]));record('count_undefined_as_a_step',got['steps']!=1,'F reading1')
    assert len(checks)==20
    out=dict(passed=True,planted=len(checks),killed=sum(x['killed'] for x in checks),checks=checks,scope='Manual ACAF negative controls. Same-author measurements; no file mutation or solver service claimed.')
    (HERE/'mutation-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
