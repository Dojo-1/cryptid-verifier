"""One-tail stepper (l17_orbit3) plus the Lean-proved push/collapse move (L17g.push_returns).

S(u+7, 1, 3j+8, 1) -> D(2u+2, 7, 2j+1) by F1100, then the D rows (D_r0/D_r1/D_r1z/D_r2/D_r2k) until a one-tail S.
Usage: python3 l17_orbit4.py SECONDS [gpt_json ...]; reports push events and checks GPT's recorded states.
"""
import sys,time,json; sys.set_int_max_str_digits(0)
import l17_orbit2 as orbit2
def D_collapse(N,k,z):
    rows=[]
    while True:
        q,r=divmod(N,3); rows.append(r); assert N>=2 and k>=1 and z>=1
        if r==0: return orbit2.canon(1+5*q+k,3*z,7,3),rows
        if r==1:
            if z==1: return orbit2.canon(0,10*q-6,k+14,3),rows
            N,k,z=10*q-6,k+7,z-1
        else:
            if k==1: return orbit2.canon(0,10*q+15+3*z,7,3),rows
            N,k=10*q+15,k-1
def step4(st):
    a,b,k,s=st
    if b==1 and k>=1 and s==1:
        if a>=9 and a%3==0 and k>=7: u=(a-9)//3; d=k-7; return ('RET',None,(10*u+18,2*d+1,7,3))
        if a>=7 and k>=8 and k%3==2:
            u=a-7; j=(k-8)//3; nst,rows=D_collapse(2*u+2,7,2*j+1); return ('PUSH',rows,nst)
        return ('STOP-PUSH',None,st)
    return orbit2.step(st)
if __name__=='__main__':
    limit=float(sys.argv[1]); gpt=[]
    for f in sys.argv[2:]:
        r=json.load(open(f)); gpt+=[int(e['a_before'],16) for e in r['events']]
    st=(30066981019881,27,0,0); n=0; ev=[]; t0=time.time()
    while time.time()-t0<limit:
        r,info,nst=step4(st)
        if r.startswith('STOP'):
            print("STOP at macro step",n,"b,k,s",st[1:],"a mod 3",st[0]%3,"a bits",st[0].bit_length()); break
        if r in('RET','PUSH'):
            ev.append((n,r,st[0].bit_length(),st[0]%3,st[2],info,st[0] in gpt)); print(*ev[-1],flush=True)
        st=nst; n+=1
    print("macro steps",n,"push events",len(ev),"matched GPT A values",sum(e[-1] for e in ev),"of",len(gpt),"final a bits",st[0].bit_length(),"elapsed",round(time.time()-t0))
