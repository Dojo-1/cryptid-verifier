import sys,time; sys.set_int_max_str_digits(0)
import l17_orbit2 as orbit2
def step3(st):
    a,b,k,s=st
    if b==1 and k>=1 and s==1:
        if a>=9 and a%3==0 and k>=7:
            u=(a-9)//3; d=k-7; return ('RET',None,(10*u+18,2*d+1,7,3))
        return ('STOP-RET',None,st)
    return orbit2.step(st)
st=(30066981019881,27,0,0); n=0; ev=[]; t0=time.time(); limit=float(sys.argv[1])
while time.time()-t0<limit:
    r,_,nst=step3(st)
    if r.startswith('STOP'):
        print("STOP at macro step",n,"state b,k,s",st[1:],"a mod 3",st[0]%3,"a bits",st[0].bit_length()); break
    if r=='RET': ev.append((n,st[0].bit_length(),st[2]))
    st=nst; n+=1
print("macro steps",n,"return events",len(ev),ev[:20],"final a bits",st[0].bit_length(),"elapsed",round(time.time()-t0))
