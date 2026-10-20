from collections import Counter
# A.9 on its Poincare section S(a,c)=C(a,0,c), using the proved compressions
a,c=8,1   # C(5,2,0) -> C(8,0,1)
races=[]; n=0
while n<200000:
    k,p=a//2,a%2
    if c==0: print("HALT at section step",n); break
    if c==1:
        if p==1: a,c=2,k+3; n+=1; continue
        b0,c0=2,k+1; a0=5
    else:
        b0,c0=k+3,c-2; a0=2+3*p
    races.append((a,b0,c0,p,k))
    if b0<=c0: a,c=a0+6*b0,c0-b0
    else:
        if b0-c0==1: print("HALT (race b=c+1) at",n); break
        a,c=a0+6*c0+3,b0-c0-1
    if b0==c0: print("HALT (tie) at",n); break
    n+=1
    if a.bit_length()>4000: break
print("race starts:",len(races))
print("a mod 3 at section:",Counter(x[0]%3 for x in races))
print("(b mod 3, c mod 3):",sorted(Counter((x[1]%3,x[2]%3) for x in races).items()))
print("(b-c) mod 3:",Counter((x[1]-x[2])%3 for x in races)," mod 9:",sorted(Counter((x[1]-x[2])%9 for x in races).items()))
print("min |b-c| over races (excluding first 10):",min(abs(x[1]-x[2]) for x in races[10:]))
