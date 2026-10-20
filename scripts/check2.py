exec(open('a4.py').read().split('# 1)')[0])
s=(0,3); visits=[]; n=0
while n<3_000_000:
    r,k=step(*s)
    if k=='one': visits.append(s[0])
    s=r; n+=1
Hs=[2**(t+2)-4-t for t in range(0,3000)]
cands=[]
for M in range(2,400):
    V=set(v%M for v in visits); H=set(h%M for h in Hs)
    if not (V & H): cands.append((M,len(V)))
print("A.4: moduli M<400 where visited m mod M never meets a halting target mod M:", cands[:20])
# A.9: verify Gemini's Poincare compression and the a = 2 mod 3 invariant
def a9(s):
    a,b,c=s
    if b==0 and c==0: return 'HALT'
    if b==0 and c==1: return (5,2,a//2+1) if a%2==0 else (2,0,a//2+3)
    if b==0: return (2,a//2+3,c-2) if a%2==0 else (5,a//2+3,c-2)
    if c==0: return (a+3,0,b-1)
    return (a+6,b-1,c-1)
def to_section(s):
    while s!='HALT' and s[1]!=0: s=a9(s)
    return s
bad=0; amod=set()
for a in range(0,60):
    for c in range(2,60):
        k,p=a//2,a%2
        got=to_section(a9((a,0,c)))
        exp=(6*k+20+3*p,0,c-k-5) if c>=k+5 else (6*c-7+3*p,0,k-c+4)
        if got!=exp and not (got=='HALT'): bad+=1
print("A.9 compression mismatches (non-halting cases):",bad)
s=(5,2,0); n=0; ok=True; secs=0; minc=None
while n<200000:
    s=a9(s)
    if s=='HALT': print("A.9 halted"); break
    if s[0]%3!=2: ok=False
    n+=1
print("A.9 a = 2 mod 3 along the orbit (200k rule steps):",ok)
