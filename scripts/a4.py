# A.4 rules exactly as in the paper's Appendix A.4
def step(a,b):
    if b>2*a+2: return (2*a+2,b-2*a-2),'exp'
    if b==1: return (2,2*a+2),'one'
    if b==2: return 'HALT','halt'
    if b%2==0 and a>=1 and 2<=b//2<=a+1: x=6*a+b+2; return (x//4,x%4+1),'con'
    if b%2==1 and a>=1 and 1<=b//2<=a: x=6*a+(b-1)+6; return (x//4,x%4+1),'con'
    return None,'stuck'
# 1) which m make C(m,1) halt before returning to a contraction?
def from_one(m):
    s=(m,1); first=True
    while True:
        r,kind=step(*s)
        if kind=='halt': return True
        if kind=='con' or kind=='stuck': return False
        if kind=='one' and not first: return False   # cascade ended at b=1 again
        first=False; s=r
halting_m=[m for m in range(0,300) if from_one(m)]
print("m with C(m,1) -> ... -> Halt (direct cascade):", halting_m)
print("Gemini's claimed set:", [3*(2**s-1)-s for s in range(1,7)])
print("my formula 2^(s+2)-4-s :", [2**(s+2)-4-s for s in range(0,7)])
# 2) contraction outputs
outs=set()
for a in range(1,200):
    for b in range(3,2*a+3):
        r,kind=step(a,b)
        if kind=='con': outs.add(r[1])
print("b after contraction:", sorted(outs))
# 3) run the real orbit, record every visit to C(m,1)
s=(0,3); visits=[]; n=0; kinds={}
while n<3_000_000:
    r,kind=step(*s); kinds[kind]=kinds.get(kind,0)+1
    if kind=='halt': print("HALTED at",n); break
    if kind=='stuck': print("STUCK",s); break
    if kind=='one': visits.append(s[0])
    s=r; n+=1
print("steps",n,"kinds",kinds,"final a bits",s[0].bit_length())
print("number of C(m,1) visits:",len(visits),"first m's:",visits[:12])
H=set(2**(t+2)-4-t for t in range(0,400))
print("any visit in halting set?", any(v in H for v in visits))
import collections
for mod in (2,3,4,8,9,16):
    print(f"  m mod {mod} over visits:",dict(sorted(collections.Counter(v%mod for v in visits).items())))
print("  halting targets mod 3:",sorted(set(h%3 for h in list(H)[:200])), " mod 4:",sorted(set(h%4 for h in H)))
