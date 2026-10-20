"""Known-answer, representation, frame and compiler controls."""
from __future__ import annotations
import random
from backend import transform_machine
from specification import equal_words,expand,skip,first_bits

HISTORICAL='0001011011010001010111100110001110000110111'


def known_answers(machine):
    rows=[]
    def add(name,m,q,h,t,cells,expected):
        rows.append({'name':name,'request':{'machine':m,'q':q,'head':h,'limit':t,'ones':cells,'trace':False},'expected':expected})
    def want(q,h,t,cells,halted=False):return {'q':q,'head':h,'steps':t,'ones':cells,'halted':halted}
    add('blank-zero',machine,0,0,0,[],want(0,0,0,[]))
    add('blank-two',machine,0,0,2,[],want(2,0,2,[0,1]))
    add('undefined-zero-budget',machine,5,0,0,[0],want(5,0,0,[0],True))
    add('undefined-positive-budget',machine,5,0,100,[0],want(5,0,0,[0],True))
    add('all-undefined','_'.join(['------']*6),3,-9,100,[-10,-9,2],want(3,-9,0,[-10,-9,2],True))
    add('right-write-one','_'.join(['1RA1RA']*6),2,7,16,[],want(0,23,16,list(range(7,23))))
    add('right-erase','_'.join(['0RA0RA']*6),4,0,4,[-3,-1,0,1,3,10],want(0,4,4,[-3,-1,10]))
    cells=[i for i,b in enumerate(HISTORICAL) if b=='1']
    add('historical-leading-zero',machine,2,0,0,cells,want(2,0,0,cells))
    return rows


def metamorphic(requests,results,seed):
    rng=random.Random(seed^0x9D3);rows=[]
    for i,(request,result) in enumerate(zip(requests[:64],results[:64])):
        for mode in ('translation','reflection','state-renaming'):
            req=dict(request);want={k:result[k] for k in ('q','head','steps','halted','ones')}
            if mode=='translation':
                delta=rng.choice((-999999,-17,17,999999));req['head']+=delta;req['ones']=[x+delta for x in req['ones']]
                want['head']+=delta;want['ones']=[x+delta for x in want['ones']]
            elif mode=='reflection':
                req['machine']=transform_machine(req['machine'],reflect=True)
                req['head']=-req['head'];req['ones']=sorted(-x for x in req['ones'])
                want['head']=-want['head'];want['ones']=sorted(-x for x in want['ones'])
            else:
                permutation=list(range(6));rng.shuffle(permutation)
                req['machine']=transform_machine(req['machine'],permutation)
                req['q']=permutation[req['q']];want['q']=permutation[want['q']]
            rows.append({'source_index':i,'mode':mode,'request':req,'expected':want})
    return rows


def representations(actor,seed,count=1024):
    rng=random.Random(seed^0xF17E);records=[]
    for index in range(count):
        pattern=''.join(rng.choice('01') for _ in range(rng.randint(1,8)));n=rng.randrange(65);cut=rng.randrange(n+1)
        extra=rng.randrange(17);original=pattern*n
        chunks=[(pattern,cut),(pattern,n-cut),('0',extra)]
        word=actor.Word(tuple(chunks));literal=original.rstrip('0')
        assert word.expand()==literal
        assert equal_words(word.parts,[(pattern,n)])
        assert word.equivalent(actor.Word.literal(original))
        for k in sorted(set((0,len(literal)//2,len(literal),len(literal)+1))):
            assert word.drop(k).expand()==literal[k:]
            assert equal_words(word.drop(k).parts,skip([(pattern,n)],k))
        for p in ('0','1','01','10','001'):
            expected=0
            while expected<len(literal) and literal[expected]==p[expected%len(p)]:expected+=1
            assert word.periodic_prefix_length(p)==expected
        assert word.prefix(17)==(literal+'0'*17)[:17]
        if literal:
            changed=('1' if literal[0]=='0' else '0')+literal[1:]
            assert not equal_words(word.parts,[(changed,1)])
        records.append({'pattern':pattern,'count':n,'split':cut,'exterior_zeros':extra})
    return records
