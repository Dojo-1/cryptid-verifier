"""Simplified (merged) rule systems from Appendix A of arXiv:2610.22603, plus Antihydra.
Each machine: step(state) -> state | 'HALT' | 'STUCK', start, dist(state) = L1 distance to the
halting pattern (or its predecessor relation where the halting state itself is uninformative)."""

def antihydra(s):
    a,b=s
    if b%2==0: return (a+2,3*(b//2)+2)
    if a==0: return 'HALT'
    return (a-1,3*(b//2)+3)
def d_antihydra(s): return s[0]                     # barrier: counter a must reach 0

def a1(s):
    a,b,c,d=s
    if c>0: return (a,b+1,c-1,d)
    if d==0: return (a+1,0,0,2*b+2)
    if a>=3: return (a-3,b+2,0,d-1)
    if a==2: return (0,0,b+1,d-1)
    if a==1: return (1,1,b+1,d-1) if b>0 else (0,0,0,d+2)
    if a==0:
        if d==1: return (0,0,2,5) if b==0 else (0,0,2,2*b+1)
        if d==b+2: return 'HALT'
        if d>=2 and b>=d-1: return (3*d-4,1,2,2*b-2*d+3)
        if d==b+3: return (3*b+2,0,0,6)
        if d==b+4: return (3*b+4,0,0,4)
        if d>=b+5: return (3*b+3,2,0,d-b-5)
    return 'STUCK'
def d_a1(s): a,b,c,d=s; return a+c+abs(d-b-2)

def a2(s):
    a,b,w=s
    if a==0 and b%2==1:
        k=(b-1)//2
        return (0,1,2*k+2*w+2) if w<=1 else (0,2*k+4,w-2)
    if a==0 and b%2==0:
        k=(b-2)//2
        if w==0: return 'HALT'
        if w<=3: return (k+1,1,2*w-1)
        return (k+1,5,w-4)
    if a>=1 and b%2==1:
        k=(b-1)//2
        return (a-1,1,2*k+2*w+3) if w<=1 else (a-1,2*k+5,w-2)
    return 'STUCK'
def d_a2(s): a,b,w=s; return a+(b%2)+w

def a3(s):
    a,c,f=s
    if (a,c) in ((2,4),(2,2)): return 'HALT'
    k,m=a//2,c//2
    if a>=4 and c>=4:
        if k<m: return (2,c-a+2,f+6*k-6)
        if m<k: return (a-c+2,2,f+6*m-6)
        return (2,2,f+6*k-6)
    if c==2 and k>=3: return (a-4,f+8,2) if f%2==0 else (a-4,f+7,5)
    if (a,c)==(4,2): return (f+4,6,5) if f%2==0 else (f+7,2,2)
    if a==2 and m>=4: return (c-6,f+10,5) if f%2==0 else (c-6,f+11,2)
    if (a,c)==(2,6): return (f+10,2,2) if f%2==0 else (f+7,6,5)
    return 'STUCK'
def d_a3(s): a,c,f=s; return abs(a-2)+min(abs(c-2),abs(c-4))

def a4(s):
    a,b=s
    if b>2*a+2: return (2*a+2,b-2*a-2)
    if b==1: return (2,2*a+2)
    if b==2: return 'HALT'
    if b%2==0 and a>=1 and 2<=b//2<=a+1: x=6*a+b+2; return (x//4,x%4+1)
    if b%2==1 and a>=1 and 1<=b//2<=a: x=6*a+b+5; return (x//4,x%4+1)
    return 'STUCK'
def d_a4(s):                                         # predecessor of halt: an expansion landing on b = 2
    a,b=s; return abs(b-2*a-4) if b>2*a+2 else None

def a5(s):
    a,z,w=s
    if a==0 and z%2==1:
        k=(z-1)//2
        if w>=2: return (0,2*k+4,w-2)
        return (0,2,2*k+2) if w==0 else (0,2,2*k+4)
    if a==0 and z%2==0:
        k=(z-2)//2
        if w>=4: return (k+1,5,w-4)
        if w==0: return 'HALT'
        return (k,3,2*w-1)
    if a>=1 and z%2==1:
        k=(z-1)//2
        if w>=2: return (a-1,2*k+5,w-2)
        if a==1: return (0,2,2*k+3+2*w)
        return (a-2,3,2*k+3+2*w)
    return 'STUCK'
def d_a5(s): a,z,w=s; return a+(z%2)+w

def a6(s):
    u,v,w=s
    if u==0:
        if w==0: return (0,0,2*v+12) if v%2==0 else (2,4,2*v+7)
        if w==1: return (2,4,2*v+9) if v%2==0 else (0,0,2*v+14)
        if w==2: return (2,v+4,1) if v%2==0 else (0,v+4,1)
        return (v+3,0,w-3)
    if w>=2: return (u-1,v+2,w-2)
    if w==0:
        if u==1: return (0,0,2*v+12)
        return (2,4,2*u+2*v+5) if u%2==0 else (0,0,2*u+2*v+10)
    if u==1: return 'HALT'
    if u==2: return (0,0,2*v+10)
    return (2,u,2*v+5) if u%2==0 else (0,u,2*v+5)
def d_a6(s): u,v,w=s; return abs(u-1)+abs(w-1)

def a7(s):
    a,k,c=s
    if k==0:
        m=a//2; o=a%2
        if c==0: return (3,0,a+2)
        if c%2==1: return (3+o,m+o,c)
        if c==2: return (o,1,2*m+2+2*o)
        return (3+o,m+1+o,c-2)
    if k==1:
        if c%2==0: return (a+3,c//2,0)
        if c==1: return 'HALT'
        if c==3: return (3,0,a+7)
        m=a//2; o=a%2
        if c==5: return (1-o,1,2*m+8)
        return (4-o,m+4,c-5)
    kk=k-2
    if c==0:
        m=a//2; o=a%2; return (3+o,m+1+o,2*kk+1)
    if c%2==1: return (a+6,kk,c)
    if c==2: return (a+3,1,2*kk+2)
    return (a+6,kk+1,c-2)
def d_a7(s): a,k,c=s; return abs(k-1)+abs(c-1)

def a8(s):
    a,b=s
    if b%2==0:
        k=(b-6)//2
        if a==0: return (k+1,9)
        a1_=a-1
        if k<=a1_+3: return (a1_-k+4,6*k+12)
        if k in (a1_+4,a1_+5): return 'HALT'
        return (k-a1_-5,6*a1_+39)
    k=(b-1)//2
    if k>a: return (k-a,6*a+6)
    if a in (k,k+1): return 'HALT'
    return (a-k-1,6*k+9)
def d_a8(s):
    a,b=s
    if b%2==0:
        k=(b-6)//2
        return min(abs(k-(a-1)-4),abs(k-(a-1)-5)) if a>=1 else None
    k=(b-1)//2; return min(abs(a-k),abs(a-k-1))

def a9(s):
    a,b,c=s
    if b==0 and c==0: return 'HALT'
    if b==0 and c==1: return (5,2,a//2+1) if a%2==0 else (2,0,a//2+3)
    if b==0: return (2,a//2+3,c-2) if a%2==0 else (5,a//2+3,c-2)
    if c==0: return (a+3,0,b-1)
    return (a+6,b-1,c-1)
def d_a9(s): a,b,c=s; return b+c

def a10(s):
    a,b,c=s
    if c==0:
        if a>=1: return (a-1,b,1)
        return {0:(1,0,1),1:(1,0,2),2:(1,0,6)}.get(b,(1,b-3,4))
    if b==0:
        if c<=2: return (1,0,2*a+2*c+1)
        if c==3: return 'HALT'
        if c<=6: return (1,a+1,2*(c-4)+2)
        return (1,a+3,c-6)
    if c<=2:
        if b==1: return (1,0,2*a+2*c+2)
        if b==2: return (1,2,2*a+2*c)
        return (1,b-3,2*a+2*c+4)
    return (a+2,b-1,c-2)
def d_a10(s): a,b,c=s; return b+abs(c-3)

def a11(s):
    a,b,c,d=s
    if c==0 and d==6: b,d=b+3,3
    if a>=2: return (a-2,b+3,c,d)
    if c>=2: return (a+b+4,3,c-2,d)
    if c==1 and d==6: return (a+b+4,0,3,3)
    if c==1:
        if b%2==1: return (a,0,(b-1)//2+3,6)
        if a==0: return 'HALT'
        return (6,0,3,3) if b==0 else (6,3,(b-2)//2,6)
    if b%2==0: return (a,0,b//2+3,3)
    if a==0: return 'HALT'
    return (6,3,(b-1)//2,3)
def d_a11(s):
    a,b,c,d=s
    if c==0 and d==6: b,d=b+3,3
    return a+min(c+(b%2==0),abs(c-1)+(b%2==1))+(d!=3)

MACHINES={
 "Antihydra":(antihydra,(0,4),d_antihydra,"barrier"),
 "A.1":(a1,(0,0,0,0),d_a1,"window"), "A.2":(a2,(0,1,1),d_a2,"window"),
 "A.3":(a3,(6,2,2),d_a3,"window"),   "A.4":(a4,(0,3),d_a4,"window"),
 "A.5":(a5,(0,2,2),d_a5,"window"),   "A.6":(a6,(0,0,0),d_a6,"window"),
 "A.7":(a7,(3,0,2),d_a7,"window"),   "A.8":(a8,(0,9),d_a8,"window"),
 "A.9":(a9,(5,2,0),d_a9,"window"),   "A.10":(a10,(1,0,2),d_a10,"window"),
 "A.11":(a11,(4,0,0,3),d_a11,"window"),
}
