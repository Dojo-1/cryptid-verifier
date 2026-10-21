"""Canonical guarded D/G transitions and an algebraic opposite stream.

No raw simulation, source-file access or work on import. Terminal or unsupported
states stop explicitly; no normalization boundary is inverted.
"""
from dataclasses import dataclass

@dataclass(frozen=True)
class State:
    mode:str
    N:int
    k:int
    m:int
    l:int
    s:int
    def __post_init__(self):
        if self.mode not in ('D','G') or any(type(x) is not int for x in (self.N,self.k,self.m,self.l,self.s)):
            raise ValueError('Canonical typed D/G state required')
        if self.N<2 or self.l<1 or self.s<0 or (self.mode=='D' and (self.k<1 or self.m<1)) or (self.mode=='G' and (self.k<0 or self.m!=0)):
            raise ValueError('Outside canonical internal interface')

def rank(x):return (x.s,x.l,3*x.k+(8*x.m+3 if x.mode=='D' else 0))

def forward(x):
    """Return(rule,target), or(reason,None) at every declared exit."""
    q,r=divmod(x.N,3);k,m,l,s=x.k,x.m,x.l,x.s
    if x.mode=='D':
        if r==0:return 'S-D0',None
        if r==2:
            if k==1:return 'S-D2k',None
            return 'D2',State('D',10*q+15,k-1,m,l,s)
        if m>=3:
            if m==3:return 'S-D1m0',None
            return 'D1',State('D',10*q-6,k+7,m-3,l,s)
        if m==2:return 'D12',State('G',10*q-6,k+6,0,l,s)
        if q<2:return 'J-low-a',None
        if k<5:return 'J-short-width',None
        if s<3:return 'J-short-terminal',None
        return 'D11join',State('D',10*q-10,7,2*k-9,l+7,s-3)
    if r==0:return 'S-G0',None
    if r==2:
        if k==0:return 'S-G2k',None
        return 'G2',State('G',10*q+15,k-1,0,l,s)
    if q<2:return 'G-low-a',None
    if l==1:return 'S-G1l0',None
    return 'G1',State('D',10*q-10,7,2*k+4,l-1,s)

def inverse(y):
    """Unique internal predecessor, or None. Exits to S/J are excluded."""
    n,k,m,l,s=y.N,y.k,y.m,y.l,y.s;r=n%10
    if r==4:
        q=(n+6)//10
        if q<1:return None
        if y.mode=='D' and k>=8:return 'D1',State('D',3*q+1,k-7,m+3,l,s)
        if y.mode=='G' and k>=7:return 'D12',State('D',3*q+1,k-6,2,l,s)
    if r==5:
        q=(n-15)//10
        if q>=0:return ('D2' if y.mode=='D' else 'G2'),State(y.mode,3*q+2,k+1,m,l,s)
    if y.mode=='D' and r==0 and n>=10 and k==7:
        q=(n+10)//10
        if m>=4 and m%2==0:return 'G1',State('G',3*q+1,(m-4)//2,0,l+1,s)
        if m%2==1 and l>=8:return 'D11join',State('D',3*q+1,(m+9)//2,1,l-7,s+3)
    return None

def push_entry(a,c):
    if type(a) is not int or type(c) is not int or a<7 or c<7:raise ValueError('F1100 guards')
    return State('D',2*a-12,7,2*c-13,7,3)

def trace(x,limit=2000):
    rows=[]
    for _ in range(limit):
        name,y=forward(x)
        if y is None:return rows,x,name
        assert rank(y)<rank(x)
        assert inverse(y)==(name,x)
        rows.append((name,x,y));x=y
    return rows,x,'row budget'

def finite_bound(x):
    """Coarse integer bound for internal rows before an explicit exit."""
    J=x.s//3;E=x.l-1+8*J
    return (E+1)*6**E*(rank(x)[2]+12)+E
