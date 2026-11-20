"""E61 adversarial finite phase-transport checks; no theorem claims.

The full raw transition table is transcribed here independently of the E60
expected-output functions. State 0=A, 1=B, 2=C, 3=D, 4=E, 5=F.
"""
import random
import unittest

OPS = (((1,1,1),(0,1,4)), ((1,-1,2),(0,1,0)),
       ((0,-1,3),(1,-1,1)), ((1,-1,0),(1,-1,4)),
       ((0,-1,1),(0,-1,5)), ((1,-1,3),None))

def source(family,m,u,v,R,origin=0):
    assert family in (1,3) and m>=0
    left='10'*(6+u)+'0'+'10'*(7+v)+'0'+'10'+'01'*2
    right='0111'+'1'*family+'10'*7+'11'+'01'+'10'*m+'111'+R
    w=left+right
    return (2,origin,frozenset(origin-len(left)+i for i,b in enumerate(w) if b=='1'))

def trace(start,limit=2400):
    q,h,cells=start
    tape=set(cells); states=[]; lo=hi=None
    for t in range(limit+1):
        states.append((q,h,frozenset(tape),lo,hi))
        if q==2 and all(i>=h for i in tape):break
        if t==limit:break
        op=OPS[q][int(h in tape)]
        if op is None:break
        lo=h if lo is None else min(lo,h)
        hi=h if hi is None else max(hi,h)
        bit,d,q=op
        if bit:tape.add(h)
        else:tape.discard(h)
        h+=d
    return states

def steps(start,n):
    q,h,cells=start; tape=set(cells)
    for _ in range(n):
        op=OPS[q][int(h in tape)]
        if op is None:raise AssertionError('undefined')
        bit,d,q=op
        if bit:tape.add(h)
        else:tape.discard(h)
        h+=d
    return (q,h,frozenset(tape))

def insertion(state,p):
    q,h,cells,*_=state
    return (q,h+(2 if h>=p else 0),
            frozenset([i+(2 if i>=p else 0) for i in cells]+[p]))

class PhaseDiamondTests(unittest.TestCase):
    def test_two_vs_eight_steps_arbitrary_exteriors(self):
        rng=random.Random(611705)
        for _ in range(240):
            L=''.join(rng.choices('01',k=rng.randrange(40)))
            R=''.join(rng.choices('01',k=rng.randrange(40)))
            x=rng.randrange(-500,500); origin=x+len(L)
            def initial(w):
                return (0,origin,frozenset(x+i for i,b in enumerate(L+w+R) if b=='1'))
            a=steps(initial('0111'),2)
            b=steps(initial('010111'),8)
            want_a={x+i for i,c in enumerate(L+'10'+'11'+R) if c=='1'}
            want_b={x+i for i,c in enumerate(L+'10'+'1110'+R) if c=='1'}
            self.assertEqual(a,(0,origin+2,frozenset(want_a)))
            self.assertEqual(b,(0,origin+2,frozenset(want_b)))

    def test_entire_trajectory_phase_transport_bounded(self):
        rng=random.Random(611706); cases=0
        for f in (1,3):
          for m in (1,2,3,4,5,8,12,20,50,100):
           for u,v in ((0,0),(1,0),(0,1),(2,4)):
            for R in ('1','00001010011',''.join(rng.choices('01',k=32))+'1'):
             origin=rng.randint(-500,500)
             a=trace(source(f,m,u,v,R,origin))
             b=trace(source(f,m+1,u,v,R,origin))
             self.assertEqual(len(b),len(a)+6)
             p_in=origin+22+f+2*m
             p_out=p_in+3
             sync=(88 if f==1 else 126)+2*m
             self.assertLess(sync,len(a))
             for t in range(sync-1):
                 self.assertEqual(insertion(a[t],p_in),b[t][:3],(f,m,u,v,t))
             a0,b0=a[sync],b[sync]
             self.assertEqual((a0[0],b0[0],a0[1],b0[1]),(0,0,a0[1],a0[1]))
             self.assertEqual(''.join('1' if a0[1]+i in a0[2] else '0' for i in range(2)),'11')
             self.assertEqual(''.join('1' if b0[1]+i in b0[2] else '0' for i in range(4)),'0111')
             for t in range(sync,len(a)):
                 self.assertEqual(insertion(a[t],p_out),b[t+6][:3],(f,m,u,v,t))
             self.assertLess(a[-1][4],p_out)
             self.assertLess(b[-1][4],p_out+2)
             self.assertEqual((a[-1][0],b[-1][0],a[-1][1],b[-1][1]),(2,2,a[-1][1],a[-1][1]))
             cases+=1
        self.assertEqual(cases,240)

if __name__=='__main__':unittest.main()
