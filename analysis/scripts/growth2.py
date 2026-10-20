import sys, math; sys.path.insert(0,'/tmp/zk/global')
from machines import MACHINES
N=3_000_000
print(f"{'machine':10s} {'status':12s} {'decisions':>9s} {'bits':>6s} {'bits/decision (late half)':>26s} {'regime':>11s}")
res={}
for name,(step,s0,dist,kind) in MACHINES.items():
    s=s0; prevd=None; dec=0; trace=[]; status='alive'
    for n in range(N):
        t=step(s)
        if t in('HALT','STUCK'): status=f'{t}@{n}'; break
        d=tuple(y-x for x,y in zip(s,t))
        if d!=prevd: dec+=1; trace.append((dec,max(t).bit_length()))
        prevd=d; s=t
        if max(s).bit_length()>4000: break
    half=trace[len(trace)//2:]
    rate=(half[-1][1]-half[0][1])/max(1,half[-1][0]-half[0][0])
    # polynomial check: bits vs log2(decisions)
    regime='geometric' if rate>0.02 else 'slow'
    res[name]=(rate,trace)
    print(f"{name:10s} {status:12s} {dec:9d} {trace[-1][1]:6d} {rate:26.4f} {regime:>11s}")
