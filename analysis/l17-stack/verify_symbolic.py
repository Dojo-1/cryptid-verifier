"""Independent state-only replay from declarative claims, with no actor imports.

Uses neither rules.py, words.py, discover.py, extend.py, nor nesting.py.
Recorded symbolic choices and checkpoints are tested rather than overwritten.
"""
from __future__ import annotations
import hashlib,json,sys,time
from collections import Counter
from pathlib import Path
from paths import HERE,HARDENING
sys.path.insert(0,str(HARDENING))
from specification import Claims,trim,skip,first_bits,matching_prefix,equal_words,materialize


def next_state(a,tail,claims):
    q=matching_prefix(tail,'01')//2
    if q:name='N';p={'a':a,'q':q};cut=2*q
    elif a==0 and first_bits(tail,1)=='1':name='E';p={};cut=1
    elif first_bits(tail,2)=='00':name='Z';p={'a':a};cut=2
    elif a>=1 and first_bits(tail,2)=='11':
        q=matching_prefix(tail,'1')//3
        if q:name='Q';p={'a':a,'q':q};cut=3*q
        else:name='P';p={'a':a};cut=2
    else:
        c=matching_prefix(tail,'10')//2
        terminal=first_bits(skip(tail,2*c),4)
        if terminal[:3]=='100':name='F100';p={'a':a,'c':c};cut=2*c+3
        elif c>=1 and terminal[0]=='0':name='F100';p={'a':a,'c':c-1};cut=2*c+1
        elif c>=1 and terminal[:3]=='111':name='F111';p={'a':a,'c':c};cut=2*c+3
        elif c>=1 and terminal=='1100':
            name='F1100' if c>=7 else 'S'+str(c)
            p={'a':a,'c':c} if c>=7 else {'a':a};cut=2*c+4
        else:raise ValueError('Unhandled prefix '+terminal)
    schema=claims.rules[name]
    for key,(lo,hi) in schema['guards'].items():
        if type(p[key]) is not int or p[key]<lo or (hi is not None and p[key]>hi):raise ValueError('Guard '+name)
    suffix=skip(tail,cut)
    source=materialize(schema['source'],p,suffix)
    assert equal_words([('01',a)]+tail,source)
    target=trim(materialize(schema['target'],p,suffix))
    if target and target[0][0]=='01':aa=target[0][1];ww=target[1:]
    else:aa=0;ww=target
    return aa,ww,name


def state(x):return int(x['a'],16),[(p,int(n,16)) for p,n in x['tail']]


def verify_source_bindings():
    full=json.loads((HERE/'replay-compact.json').read_text())
    deep=json.loads((HERE/'deeper.json').read_text())
    assert hashlib.sha256((HERE/'extension.json').read_bytes()).hexdigest()==full['source_sha256']
    assert hashlib.sha256((HERE/'replay-compact.json').read_bytes()).hexdigest()==deep['source_sha256']
    return True


def main():
    verify_source_bindings()
    start=time.monotonic();base=json.loads((HERE/'extension.json').read_text());full=json.loads((HERE/'replay-compact.json').read_text());deep=json.loads((HERE/'deeper.json').read_text())
    claims=Claims(HARDENING/'claims.json')
    assert hashlib.sha256((HARDENING/'claims.json').read_bytes()).hexdigest()==base['claims_sha256']
    a,w=state(base['stop']);initial=int(base['stop']['index'],16);mid=int(full['stop']['index'],16);end=int(deep['stop']['index'],16)
    checks={int(x['index'],16):x for x in full['checkpoints']+deep['checkpoints']}
    checks[mid]=full['stop'];checks[end]=deep['stop']
    for r in full['events']:
        if 'rule' in r:
            checks[int(r['index'],16)]={'a':r['a_before'],'tail':r['tail_before']}
        elif 'shape' in r:checks[int(r['index'],16)]=r
    for r in deep['events']:checks[int(r['index'],16)]=r
    choices=(HERE/'deeper-choices.txt').read_bytes()
    assert hashlib.sha256(choices).hexdigest()==deep['choices_sha256']
    assert len(choices)==end-mid
    codes=deep['choice_codes'];counts=Counter();matched=0
    for index in range(initial,end+1):
        if index in checks:
            aa,ww=state(checks[index]);assert a==aa and equal_words(w,ww),(index,'checkpoint');matched+=1
        if index==end:break
        a,w,name=next_state(a,w,claims);counts[name]+=1
        if index>=mid:assert choices[index-mid]==ord(codes[name]),(index,'choice')
    report={'start_rewrite':initial,'end_rewrite':end,'state_edges':end-initial,'rule_counts':dict(counts),
        'matched_complete_checkpoints':matched,'matched_choice_codes':len(choices),'passed':True,
        'actor_imported':False,'time_or_head_totals_recomputed':False,'elapsed_seconds':time.monotonic()-start}
    (HERE/'symbolic-recheck.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)


if __name__=='__main__':main()
