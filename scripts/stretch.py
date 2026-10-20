import math, time, sys
N=int(sys.argv[1]); a,b=0,4; t=0; run=0; best=0; recs=[]; worst=(1e9,0,0,0)
log_raw=None; L10=math.log10
def lsum(x,y): # log10(10^x+10^y)
    if x is None: return y
    m=max(x,y); return m+L10(1+10**(min(x,y)-m))
t0=time.time()
while t<N:
    k=b>>1; odd=b&1
    if odd and a==0: print("HALT",t); break
    # exact raw TM cost of this macro step (paper Sec 2.2), in log10 via bit length
    kb=k.bit_length(); lk=(kb-1)*L10(2)+L10((k>>max(kb-53,0))/(2**min(kb-1,52))) if k else 0
    cost_log = L10(3)+2*lk if k>10 else L10(2*a+3*k*k+12*k+11)
    log_raw=lsum(log_raw,cost_log)
    if odd:
        if run==0: a_start=a
        run+=1
        if run>best:
            best=run; recs.append((t,run,a_start,math.log2(t+1)))
        r=a_start/run
        if t>20 and r<worst[0]: worst=(r,t,run,a_start)
        a-=1; b=3*k+3
    else:
        run=0; a+=2; b=3*k+2
    t+=1
print(f"macro steps {t} in {time.time()-t0:.0f}s; a={a}; raw TM steps ~ 10^{log_raw:.1f}")
print("record odd runs (t, run length, counter at run start, log2 t):")
for r in recs: print("  ",r[0],r[1],r[2],f"{r[3]:.1f}")
print(f"tightest squeeze after t>20: counter/run = {worst[0]:.1f} at t={worst[1]} (run {worst[2]} vs counter {worst[3]})")
