"""Write the declarative row transcription; not used by the actor."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
MACHINE='1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'
rules={}
def add(name,guards,source,target,steps,shift):
    rules[name]=dict(guards={k:[v,None] for k,v in guards.items()},source=source,target=target,steps=steps,shift=shift)
def D(N,k,m):return [('1',N),('01',k),('1',m),('01','l'),('1','s'),('v',1)]
def G(N,k):return [('1',N),('01',k),('0',1),('01','l'),('1','s'),('v',1)]
def S(a,b,k):return [('01',a),('1',b),('01',k),('1','s'),('v',1)]
g=dict(k=1,l=1,s=0)
add('M0',dict(N=2,**g),D('N','k',0),[('1','N'),('01','k+l'),('1','s'),('v',1)],0,0)
add('K0',dict(N=2,m=0,l=1,s=0),D('N',0,'m'),[('1','N+m'),('01','l'),('1','s'),('v',1)],0,0)
add('D0',dict(q=1,m=0,**g),D('3*q','k','m'),S('1+5*q+k','m','l'),'15*q*q+12*q+2','-7*q-2')
add('D1',dict(q=1,m=3,**g),D('3*q+1','k','m'),D('10*q-6','k+7','m-3'),'15*q*q+32*q+6*k+44','-7*q-4')
add('D12',dict(q=1,**g),D('3*q+1','k',2),G('10*q-6','k+6'),'15*q*q+32*q+6*k+44','-7*q-4')
add('D11',dict(q=1,**g),D('3*q+1','k',1),[('01','1+5*q'),('10','k'),('11',1),('01','l'),('1','s'),('v',1)],'15*q*q+12*q+2','-7*q-2')
add('D2',dict(q=0,m=0,**g),D('3*q+2','k','m'),D('10*q+15','k-1','m'),'15*q*q+62*q+57','-7*q-11')
add('G0',dict(q=1,k=0,l=1,s=0),G('3*q','k'),[('1','10*q+2*k+7'),('01','l-1'),('1','s'),('v',1)],'15*q*q+32*q+4*k+14','-7*q-4')
add('G1',dict(q=2,k=0,l=1,s=0),G('3*q+1','k'),[('1','10*q-10'),('01',7),('1','2*k+4'),('01','l-1'),('1','s'),('v',1)],'15*q*q+32*q+4*k+56','-7*q-4')
add('G2',dict(q=0,**g),G('3*q+2','k'),G('10*q+15','k-1'),'15*q*q+62*q+57','-7*q-11')
add('G2k',dict(q=0,l=1,s=0),G('3*q+2',0),[('1','10*q+14'),('01','l'),('1','s'),('v',1)],'15*q*q+62*q+57','-7*q-11')
add('JOIN',dict(a=7,c=5,l=1),[('01','a'),('10','c'),('11',1),('01','l'),('11',1),('v',1)],
    [('1','2*a-12'),('01',7),('1','2*c-9'),('01','l+6'),('0',1),('v',1)],'4*a+4*c+6*l+80',-2)
add('D11join',dict(q=2,k=5,l=1,s=3),D('3*q+1','k',1),[('1','10*q-10'),('01',7),('1','2*k-9'),('01','l+7'),('1','s-3'),('v',1)],'15*q*q+32*q+4*k+6*l+86','-7*q-4')
# The width39 guard fixes six successive residues; arithmetic uses affine pairs.
R=548;A=(729,R);N=(1458,2*R-12);k=7;m=65
T=[0,4*A[0],4*A[1]+248];H=[0,-2];itinerary=[]
for r in (1,1,1,2,2,0):
    assert N[0]%3==0 and N[1]%3==r
    q=(N[0]//3,(N[1]-r)//3);a,b=q;itinerary.append(dict(q_affine=q,k=k,m=m,r=r))
    lin={0:12,1:32,2:62}[r];constant={0:2,1:6*k+44,2:57}[r]
    T[0]+=15*a*a;T[1]+=30*a*b+lin*a;T[2]+=15*b*b+lin*b+constant
    H[0]-=7*a;H[1]-=7*b+{0:2,1:4,2:11}[r]
    if r==1:N=(10*a,10*b-6);k+=7;m-=3
    elif r==2:N=(10*a,10*b+15);k-=1
    else:B=(5*a,5*b+k+1)
assert m==56
steps=f'{T[0]}*t*t+{T[1]}*t+{T[2]}';shift=f'{H[0]}*t+({H[1]})'
add('RET39',dict(t=0),[('01','729*t+548'),('1',1),('01',39),('100',1),('v',1)],
 [('01',f'{B[0]}*t+{B[1]}'),('1',56),('01',7),('111',1),('v',1)],steps,shift)
def main():
    (HERE/'claims.json').write_text(json.dumps(dict(machine=MACHINE,provenance='Separate declarative transcription. Conditional analytic compositions, not new Lean theorems.',rules=rules),indent=2)+'\n')
    (HERE/'return39-polynomial.json').write_text(json.dumps(dict(R=R,q_rows=itinerary,a_out_affine=B,steps_coefficients=T,shift_affine=H,read_bound=[f'{H[0]}*t+({H[1]+1})','1458*t+1177']),indent=2)+'\n')
    print('Wrote',len(rules),'rules; RET39',B,T,H)

if __name__=='__main__':main()
