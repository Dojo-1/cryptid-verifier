"""Contextual tape identities and derived L17 endpoint formulas.

Universal interpretation rests on DERIVATION.md, not on finite tests or a Lean
build. Nothing here reads files, simulates, or writes output on import.
"""
from __future__ import annotations
from dataclasses import dataclass
from words import Word

MACHINE='1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'


@dataclass(frozen=True)
class Endpoint:
    a:int
    tail:Word
    steps:int
    shift:int
    rule:str

    def word(self):return self.tail.prepend(('01',self.a))


def core100(a,c,tail=Word()):
    if a<7 or c<0:raise ValueError('requires a>=7, c>=0')
    return Endpoint(0,tail.prepend(('1',2*a-12),('01',7),('1',2*c+3)),
                    4*a+4*c+50,-2,'core100')


def core111(a,c,tail=Word()):
    if a<5 or c<1:raise ValueError('requires a>=5, c>=1')
    return Endpoint(0,tail.prepend(('1',2*a-8),('01',c+6),('0',1)),
                    4*a+6*c+38,-2,'core111')


def core1100(a,c,tail=Word()):
    if a<7 or c<7:raise ValueError('requires a>=7, c>=7')
    return Endpoint(0,tail.prepend(('1',2*a-12),('01',7),('1',2*c-13),('01',7),('1',3)),
                    4*a+4*c+92,-2,'core1100')


def core1100_small(a,c,tail=Word()):
    if a<7 or c not in range(1,7):raise ValueError('requires a>=7, 1<=c<=6')
    if c==1:
        return Endpoint(0,tail.prepend(('1',2*a-2),('01',2),('1',6)),4*a+36,-2,'core1100-c1')
    if c==2:
        return Endpoint(0,tail.prepend(('1',2*a-10),('01',10)),4*a+110,-2,'core1100-c2')
    if c==3:
        return Endpoint(a+7,tail.prepend(('1',3)),6*a+75,-7,'core1100-c3')
    if c==4:
        return Endpoint(0,tail.prepend(('1',2*a-2),('01',1),('1',1),('01',5),('1',3)),4*a+70,-2,'core1100-c4')
    if c==5:
        return Endpoint(0,tail.prepend(('1',2*a-12),('01',14)),4*a+154,-2,'core1100-c5')
    return Endpoint(0,tail.prepend(('1',2*a-12),('01',6),('0',1),('01',7),('1',3)),4*a+116,-2,'core1100-c6')


def residue(a):
    if a>=7 and a%3==1:
        j=(a-7)//3
        return Endpoint(0,Word((('1',20*j+15),('01',6),('1',3))),
                        60*j*j+136*j+135,-14*j-13,'residue1')
    if a>=8 and a%3==2:
        j=(a-8)//3
        return Endpoint(0,Word((('1',20*j+4),('01',14))),
                        60*j*j+136*j+215,-14*j-13,'residue2')
    raise ValueError('requires a=3j+7 or a=3j+8, j>=0')


def rewrite(a,tail):
    """One guarded contextual rewrite, or an explicit unsupported case.

    C[a;w] is the whole configuration 0^infinity C> (01)^a w 0^infinity.
    Zero-step normalization is tape equality, not a machine transition.
    """
    if a<0:raise ValueError('nonnegative pair count required')
    pairs=tail.periodic_prefix_length('01')//2
    if pairs:
        return Endpoint(a+pairs,tail.drop(2*pairs),0,0,'normalize01')
    first=tail.prefix(3)
    if a==0 and first[0]=='1':return Endpoint(1,tail,2,-2,'entry1')
    if first[:2]=='00':
        return Endpoint(0,tail.drop(2).prepend(('1',2*a+4)),4*a+8,-2,'reset00')
    if first[:2]=='11' and a>=1:
        n=tail.periodic_prefix_length('1');q=n//3
        if q:
            return Endpoint(a+5*q,tail.drop(3*q),15*q*q+(6*a+6)*q,-7*q,'countdown111')
        return Endpoint(a+4,tail.drop(2).prepend(('0',1)),6*a+21,-7,'pair11')
    pairs=tail.periodic_prefix_length('10')//2
    remaining=tail.drop(2*pairs)
    if pairs and remaining.prefix(1)=='0':
        c=pairs-1
        if a<7:return {'unsupported':'core100 requires a>=7','a':a,'tail':tail.to_json()}
        return core100(a,c,tail.drop(2*c+3))
    prefix=remaining.prefix(3)
    if prefix=='100':
        if a<7:return {'unsupported':'core100 requires a>=7','a':a,'tail':tail.to_json()}
        return core100(a,pairs,tail.drop(2*pairs+3))
    if prefix=='111' and pairs>=1:
        if a<5:return {'unsupported':'core111 requires a>=5','a':a,'tail':tail.to_json()}
        return core111(a,pairs,tail.drop(2*pairs+3))
    return {'unsupported':'unhandled boundary prefix','a':a,'alternating10_pairs':pairs,
            'after_pairs':prefix,'tail':tail.to_json()}


def trajectory(a,tail,limit=100):
    records=[];time=shift=0
    for _ in range(limit):
        out=rewrite(a,tail)
        if isinstance(out,dict):return {'stop':out,'steps':time,'shift':shift,'records':records}
        time+=out.steps;shift+=out.shift
        records.append({'rule':out.rule,'a_before':a,'tail_before':tail.to_json(),
                        'a_after':out.a,'tail_after':out.tail.to_json(),
                        'raw_transitions':out.steps,'shift':out.shift,
                        'cumulative_transitions':time,'cumulative_shift':shift})
        a,tail=out.a,out.tail
    return {'stop':{'budget':'contextual rewrite count','limit':limit,'a':a,'tail':tail.to_json()},
            'steps':time,'shift':shift,'records':records}
