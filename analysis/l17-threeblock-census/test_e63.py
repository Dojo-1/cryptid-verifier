"""E63: finite regression on triple-wide checkpoint and split contextual kernels.

The raw table is independently transcribed.  These finite tests do not
certify a universal theorem, nor blank-orbit nonhalting.
"""
import random
import unittest

OPS=(((1,1,1),(0,1,4)),((1,-1,2),(0,1,0)),
     ((0,-1,3),(1,-1,1)),((1,-1,0),(1,-1,4)),
     ((0,-1,1),(0,-1,5)),((1,-1,3),None))
FAMILIES=(
  (1,"1101010101010101101010101010101101010101010101111","010101010101010101101010101010101111110101010101010101010101010101",15,279,328,(-14,51),3,(90,180)),
  (2,"111101010101010101101010101010101101010101010101111","01010101010101111111111111101010101010101111110101010101010101010101010101",21,319,362,(-20,53),0,(110,220)),
)

def exact(start,n):
    q,h,T=start;T=set(T);visited=[]
    for _ in range(n):
        visited.append(h)
        op=OPS[q][int(h in T)]
        if op is None:raise AssertionError("halt before promised clock")
        bit,d,q=op
        if bit:T.add(h)
        else:T.discard(h)
        h+=d
    return q,h,frozenset(T), (min(visited),max(visited))

def scan(first,limit=2000):
    q,h,T=first;T=set(T);visited=[]
    for i in range(limit):
        if q==2 and not any(p<h for p in T):
            return q,h,i,frozenset(T),(min(visited),max(visited))
        visited.append(h)
        op=OPS[q][int(h in T)]
        if op is None:raise AssertionError("halt before section")
        bit,d,q=op
        if bit:T.add(h)
        else:T.discard(h)
        h+=d
    raise AssertionError("raw cap")

class TripleWideTests(unittest.TestCase):
    def test_400_full_C_endpoints(self):
        rng=random.Random(630715);count=0
        for outer,guard,written,nleft,kernel,clock,rd,middle,cuts in FAMILIES:
            for term in ("00","100"):
                for trial in range(100):
                    u,v=((0,0),(1,0),(0,1),(1,1))[trial] if trial<4 else (rng.randrange(18),rng.randrange(18))
                    R="".join(rng.choices("01",k=rng.randrange(45)))+"1"
                    suffix=("11" if term=="00" else "")+R
                    left="10"*(6+u)+"0"+"10"*(7+v)+"0"+"10"+"01"*2
                    right="0111"+guard+suffix
                    origin=rng.randrange(-1200,1200)
                    start=origin-len(left)
                    T={start+i for i,b in enumerate(left+right) if b=="1"}
                    q,h,t,Tfin,read=scan((2,origin,T))
                    want="1"*(2*u+1)+"10"*7+"1"*(2*(v+middle))+written+suffix
                    self.assertEqual((q,h,t),(2,start,clock+2*u+2*v))
                    self.assertEqual(Tfin,{start+i for i,b in enumerate(want) if b=="1"})
                    self.assertEqual(read,(origin-(33+2*u+2*v),origin+rd[1]))
                    count+=1
        self.assertEqual(count,400)

    def test_600_contextual_segments(self):
        rng=random.Random(639191); count=0
        for outer,guard,written,nleft,kernel,clock,rd,middle,cuts in FAMILIES:
            left=("10"*6+"0"+"10"*7+"0"+"10"+"01"*2)[-nleft:]
            source=left+"0111"+guard
            tape={i-nleft for i,b in enumerate(source) if b=="1"}
            states=[(2,0,frozenset(tape))]
            q,h=2,0
            for i in range(kernel):
                bit,d,nq=OPS[q][int(h in tape)]
                if bit:tape.add(h)
                else:tape.discard(h)
                h+=d;q=nq
                states.append((q,h,frozenset(tape)))
            Tcuts=(0,*cuts,kernel)
            def window(state):
                q,h,T=state
                return q,''.join('1' if i in T else '0' for i in range(h-1,-nleft-1,-1)),''.join('1' if i in T else '0' for i in range(h,len(source)-nleft))
            for trial in range(100):
                L="".join(rng.choices("01",k=rng.randrange(40)))
                R="".join(rng.choices("01",k=rng.randrange(40)))
                origin=rng.randrange(-500,500)
                for s,e in zip(Tcuts,Tcuts[1:]):
                    before=window(states[s]);after=window(states[e])
                    wb=L+before[1][::-1]+before[2]+R
                    wa=L+after[1][::-1]+after[2]+R
                    cells={origin+i for i,b in enumerate(wb) if b=="1"}
                    got=exact((before[0],origin+len(L)+len(before[1]),cells),e-s)
                    expected=(after[0],origin+len(L)+len(after[1]),frozenset(origin+i for i,b in enumerate(wa) if b=="1"))
                    self.assertEqual(got[:3],expected)
                    count+=1
        self.assertEqual(count,600)

    def test_right_guard_last_bit_is_read(self):
        for outer,guard,written,nleft,kernel,clock,rd,middle,cuts in FAMILIES:
            left=("10"*6+"0"+"10"*7+"0"+"10"+"01"*2)[-nleft:]
            def kernel_result(last):
                word=left+"0111"+guard[:-1]+last+"101011"
                tape={i for i,b in enumerate(word) if b=="1"}
                return exact((2,nleft,tape),kernel)[:3]
            self.assertNotEqual(kernel_result("0"),kernel_result("1"))

if __name__=="__main__":unittest.main()
