import math, json, sys, collections
PHI=(1+5**0.5)/2; P=1/PHI          # P(walk +2/-1 ever hits -1 from 0) = 1/phi
def antihydra_stream(steps, tau=1000.0):
    a,b=0,4; ema=0.5; t=0
    while t<steps:
        odd=b&1
        if odd and a==0: yield dict(t=t,event="HALT"); return
        da = -1 if odd else 2
        a+=da; b=3*(b>>1)+(3 if odd else 2); t+=1
        ema+=(da-ema)/tau                     # adiabatic frame: slow drift estimate
        yield dict(t=t,bit=odd,a=a,
                   x=a-t/2,                    # co-moving coordinate (Haar drift 1/2 removed)
                   z=(a-t/2)/(1.5*math.sqrt(t)),  # normalized fluctuation (sd 1.5/step)
                   drift=ema,
                   risk=P**(a+1),              # Haar-model prob. of ever halting from here
                   blen=b.bit_length())
N=int(sys.argv[1]) if len(sys.argv)>1 else 100000
out=open('/tmp/zk/antihydra_stream.csv','w'); out.write("t,bit,a,x,z,drift,risk,b_bits\n")
mina=(10**9,0); maxrisk=0; blocks=collections.Counter(); buf=[]; zmin=(9,0); last=None
for r in antihydra_stream(N):
    if 'event' in r: print("HALT at",r['t']); break
    last=r
    if r['t']>10 and r['a']<mina[0]: mina=(r['a'],r['t'])
    if r['t']>100 and r['z']<zmin[0]: zmin=(r['z'],r['t'])
    buf.append(r['bit'])
    if len(buf)==8: blocks[tuple(buf)]+=1; buf=[]
    if r['t']%50==0 or r['t']<=200:
        out.write(f"{r['t']},{r['bit']},{r['a']},{r['x']:.1f},{r['z']:.4f},{r['drift']:.4f},{r['risk']:.3e},{r['blen']}\n")
out.close()
n=sum(blocks.values()); exp=n/256; chi=sum((c-exp)**2/exp for c in blocks.values())+exp*(256-len(blocks))
print(f"steps={last['t']} a={last['a']} co-moving x={last['x']:.1f} z={last['z']:.3f} drift(EMA)={last['drift']:.4f}")
print(f"min a after t>10: {mina}   min z after t>100: {zmin[0]:.3f} at t={zmin[1]}")
print(f"current halting risk (Haar model) = phi^-(a+1) = {last['risk']:.3e}")
print(f"8-bit block chi^2 = {chi:.1f} on 255 dof (Haar ~ 255±23)   b now has {last['blen']} bits")
