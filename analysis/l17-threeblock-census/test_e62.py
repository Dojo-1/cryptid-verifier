"""E62: bounded raw-machine audit for threePairDouble, not a proof."""
import random
import unittest
OPS=(((1,1,1),(0,1,4)),((1,-1,2),(0,1,0)),
     ((0,-1,3),(1,-1,1)),((1,-1,0),(1,-1,4)),
     ((0,-1,1),(0,-1,5)),((1,-1,3),None))
K="10"*7
GUARD="1111010101010101011010111"
WRITTEN="010101010101011111111111111111101010101010101010"
assert len(GUARD)==25 and len(WRITTEN)==48

def first_return(u,v,tail,origin,guard=GUARD):
    left="10"*(6+u)+"0"+"10"*(7+v)+"0"+"10"+"01"*2
    word=left+"0111"+guard+tail
    start=origin-len(left)
    tape={start+i for i,b in enumerate(word) if b=="1"}
    h=origin;q=2;lo=hi=None
    for steps in range(4000):
        if q==2 and (not tape or min(tape)>=h):
            return q,h,steps,{i-h for i in tape},(lo,hi)
        op=OPS[q][int(h in tape)]
        if op is None:return ("halt",steps)
        lo=h if lo is None else min(lo,h)
        hi=h if hi is None else max(hi,h)
        bit,d,q=op
        if bit:tape.add(h)
        else:tape.discard(h)
        h+=d
    raise AssertionError("finite cap")

class E62Tests(unittest.TestCase):
    def test_200_complete_endpoints(self):
        rng=random.Random(621625)
        count=0
        for term in ("00","100"):
            for j in range(100):
                u,v=((0,0),(1,0),(0,1),(1,1))[j%4] if j<4 else (rng.randrange(16),rng.randrange(16))
                R="".join(rng.choices("01",k=rng.randrange(50)))+"1"
                seed="1"*(6 if term=="00" else 4)
                origin=rng.randint(-2000,2000)
                out=first_return(u,v,seed+R,origin)
                leftlen=12+2*u+1+14+2*v+1+2+4
                want_head=origin-leftlen
                word="1"*(2*u+1)+K+"1"*(2*v)+WRITTEN+seed+R
                self.assertEqual(out[:3],(2,want_head,262+2*u+2*v))
                self.assertEqual(out[3],{i for i,b in enumerate(word) if b=="1"})
                self.assertGreaterEqual(out[4][0],want_head+1)
                self.assertLessEqual(out[4][1],origin+28)
                count+=1
        self.assertEqual(count,200)

    def test_guard_shortening_breaks_contextuality(self):
        prefix=GUARD[:24]
        a=first_return(0,0,"1"+"101001111",0,guard=prefix)
        b=first_return(0,0,"0"+"101001111",0,guard=prefix)
        self.assertNotEqual(a[:4],b[:4])
        self.assertNotEqual(b[:3],(2,-34,262))

if __name__=="__main__":unittest.main()
