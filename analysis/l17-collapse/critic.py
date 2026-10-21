"""Declarative collapse specifications; no orbit actor or word class imports."""
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/'l17-hardening'))
from specification import Claims,integer,equal_words


def window(name,p):
    if name=='C0':return -7*p['q']-1,3*p['q']-2
    if name=='C1':return -7*p['q']-4,3*p['q']+2*p['k']+2
    if name=='C2':return -7*p['q']-11,3*p['q']+2
    if name=='P0':return -14*p['h']-15,6*p['h']+4
    if name=='P1':return -14*p['h']-11,6*p['h']+19
    if name=='P2':return -14*p['h']-11,6*p['h']+2
    if name=='RES':return None if p['z']==0 else (-11*p['z'],2*p['k']+3*p['z']+2)
    if name=='LONG':return -199514*p['t']-183153,486*p['t']+2*p['e']+483
    raise ValueError(name)


def single(claims,name,p,v):
    out=claims.instantiate(name,p,v);out['read_bound']=window(name,p)
    return out


def ranked(claims,N,k,z,v):
    if type(N) is not int or type(k) is not int or type(z) is not int or N<2 or k<1 or z<1:
        raise ValueError('N>=2,k>=1,z>=1 integers required')
    initial={'N':N,'k':k,'z':z};bound=k+8*z;source=None;previous=None
    total=head=0;lo=hi=None;path=[]
    while True:
        q,r=divmod(N,3);name='C'+str(r);params={'q':q,'k':k,'z':z}
        item=single(claims,name,params,v)
        if source is None:source=item['source']
        else:assert equal_words(previous,item['source'])
        wlo,whi=item['read_bound'];lo=head+wlo if lo is None else min(lo,head+wlo);hi=head+whi if hi is None else max(hi,head+whi)
        total+=item['steps'];head+=item['shift'];previous=item['target']
        path.append({'r':r,'q':q,'k':k,'z':z,'steps':item['steps'],'shift':item['shift']})
        assert len(path)<=bound
        if r==0 or (r==1 and z==1) or (r==2 and k==1):break
        old=(z,k);old_rank=k+8*z
        # Read the reset counters from the consumed target schema.
        terms=claims.rules[name]['target'];N=integer(terms[0][1],params);k=integer(terms[1][1],params)
        if r==1:z-=1
        assert N>=2 and (z,k)<old
        assert k+8*z==old_rank-1
    return {'rule':'RANK','parameters':initial,'suffix':v,'source':source,'target':previous,
            'steps':total,'shift':head,'read_bound':[lo,hi],'path':path,'cycle_bound':bound}
