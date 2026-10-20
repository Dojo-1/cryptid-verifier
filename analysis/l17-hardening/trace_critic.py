"""Audit each frozen symbolic edge against the new declarative claims, without actor imports."""
from __future__ import annotations
import json
from pathlib import Path
from specification import equal_words,skip,first_bits,matching_prefix,trim


def edge_claim(row,claims):
    a=row['a_before'];w=[tuple(x) for x in row['tail_before']];name=row['rule']
    if name=='entry1':return claims.instantiate('E',{},skip(w,1))
    if name=='reset00':return claims.instantiate('Z',{'a':a},skip(w,2))
    if name=='pair11':return claims.instantiate('P',{'a':a},skip(w,2))
    if name=='countdown111':
        q=matching_prefix(w,'1')//3
        return claims.instantiate('Q',{'a':a,'q':q},skip(w,3*q))
    if name=='normalize01':
        q=matching_prefix(w,'01')//2
        return claims.instantiate('N',{'a':a,'q':q},skip(w,2*q))
    if name in ('core100','core111'):
        k=matching_prefix(w,'10')//2
        for c in (k,max(0,k-1)):
            if name=='core111' and c<1:continue
            terminal='100' if name=='core100' else '111'
            if first_bits(skip(w,2*c),3)!=terminal:continue
            claim=claims.instantiate('F100' if name=='core100' else 'F111',{'a':a,'c':c},skip(w,2*c+3))
            if equal_words([('01',a)]+w,claim['source']):return claim
    raise ValueError('No declarative parse for symbolic edge '+name)


def check_trace(path,claims):
    document=json.loads(Path(path).read_text())
    trace=document['trace'] if 'trace' in document else document['derived_next_frontier']['trace']
    total=shift=0;previous=[('01',6575648756),('1',1)];rows=[]
    for index,row in enumerate(trace['records']):
        claim=edge_claim(row,claims)
        before=[('01',row['a_before'])]+[tuple(x) for x in row['tail_before']]
        after=[('01',row['a_after'])]+[tuple(x) for x in row['tail_after']]
        assert equal_words(previous,before),(index,'broken chain')
        assert equal_words(before,claim['source']),(index,'source mismatch')
        assert equal_words(after,claim['target']),(index,'target mismatch')
        assert (row['raw_transitions'],row['shift'])==(claim['steps'],claim['shift']),(index,'time/head mismatch')
        total+=claim['steps'];shift+=claim['shift']
        assert (row['cumulative_transitions'],row['cumulative_shift'])==(total,shift),(index,'cumulative mismatch')
        previous=after;rows.append({'index':index,'claim':claim['rule'],'steps':claim['steps'],'shift':claim['shift']})
    assert (trace['steps'],trace['shift'])==(total,shift)
    return {'edges':len(rows),'total_steps':total,'total_shift':shift,'verified_edges':rows,
            'status':'Conditional arithmetic check against separately consumed declarative claims. No raw simulation at these times or new Lean verification.'}
