"""Check every l17_ctx rule against the literal machine on random small words with random context."""
import random,unittest
import l17_ctx as X
M='1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'
TR={}
for i,blk in enumerate(M.split('_')):
    for s in range(2):
        t=blk[3*s:3*s+3]
        TR[(i,s)]=None if t[2]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
def word(a,w): return [0,1]*a+[int(c) for u,n in w for c in u*n]
def first_hit(a,w,a2,w2,limit=10**6):
    tape={i:v for i,v in enumerate(word(a,w)) if v}; h=0; st=2
    goal=[i for i,v in enumerate(word(a2,w2)) if v]
    for n in range(1,limit):
        tr=TR[(st,tape.get(h,0))]
        if tr is None: return None
        v,d,st=tr
        if v: tape[h]=1
        else: tape.pop(h,None)
        h+=d
        if st==2 and (not tape or min(tape)>=h) and sorted(k-h for k in tape)==goal: return n
    return None
class Ctx(unittest.TestCase):
    def test_rules_raw(self):
        rng=random.Random(17); seen=set(); k=0
        while k<3000:
            a=rng.randrange(0,14)
            w=X.canon([(rng.choice(['1','0','01']),rng.randrange(1,9)) for _ in range(rng.randrange(1,6))])
            if k%5==0: a=rng.randrange(7,14); w=X.canon([('1',1),('01',rng.randrange(7,11)),('1',1),('0',2)]+w)
            r,a2,w2=X.step(a,w)
            if r.startswith('STOP') or r=='absorb': continue
            self.assertIsNotNone(first_hit(a,w,a2,w2),(r,a,w,a2,w2)); seen.add(r); k+=1
        self.assertEqual(seen,{'Z','EQ','Q','P','F111','F100','F1100'})
if __name__=='__main__':unittest.main()
