"""Declarative rows and read bounds; no actor, Word, or dispatcher imports."""
from gd_paths import HERE
from specification import Claims,integer

def window(name,p):
    if name in ('M0','K0'):return None
    if name=='JOIN':return -2,2*p['a']+2*p['c']+2*p['l']+3
    if name in ('RET39','RET729'):return -1998542*p['t']-1480698,1458*p['t']+2*p.get('c',39)+1099
    q=p['q'];k=p.get('k',0)
    if name in ('D0','D11'):return -7*q-1,3*q-2
    if name in ('D1','D12'):return -7*q-4,3*q+2*k+2
    if name in ('D2','G2','G2k'):return -7*q-11,3*q+2
    if name=='G0':return -7*q-4,3*q+2*k+1
    if name=='G1':return -7*q-4,3*q+2*k+2
    if name=='D11join':return -7*q-4,3*q+2*k+2*p['l']+3
    raise ValueError(name)

def single(claims,name,p,v=''):
    out=claims.instantiate(name,p,v);out['read_bound']=window(name,p);out['machine']=claims.machine
    return out

def ranked_exit(N,k,m):
    """Finite D reduction to S, G or J; NOT a universal return-to-S theorem."""
    if any(type(x) is not int for x in (N,k,m)) or N<2 or k<1 or m<0:raise ValueError('N>=2,k>=1,m>=0 integers required')
    rank=3*k+8*m;bound=rank//3+1;path=[]
    while True:
        if m==0:return dict(exit='S-m0',N=N,k=k,m=m,path=path,bound=bound)
        q,r=divmod(N,3);path.append(dict(N=hex(N),k=k,m=m,r=r))
        assert len(path)<=bound
        if r==0:return dict(exit='S-r0',a=1+5*q+k,b=m,l=7,s=3,path=path,bound=bound)
        if r==1 and m in (1,2):return dict(exit='J' if m==1 else 'G',N=N,k=k,m=m,path=path,bound=bound)
        if r==2 and k==1:return dict(exit='S-k0',N=10*q+15+m,l=7,s=3,path=path,bound=bound)
        previous=3*k+8*m
        if r==1:N,k,m=10*q-6,k+7,m-3
        else:N,k=10*q+15,k-1
        assert N>=2 and m>=0 and 3*k+8*m==previous-3
