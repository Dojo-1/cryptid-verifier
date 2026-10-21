"""Compositions of the frozen contextual actor. New JOIN uses existing kernels."""
from gd_paths import HERE
from words import Word
import rules

def join(a,c,l,v=Word()):
    if any(type(x) is not int for x in (a,c,l)) or a<7 or c<5 or l<1:raise ValueError('JOIN requires a>=7,c>=5,l>=1')
    n=a+1
    # Entry, A sweep, K11, A sweep, K7, A sweep, A11,
    # D sweep, K22, C sweep, K43, final C sweep.
    time=sum((2,2*n,11,2*c,7,2*(l+2),3,4*(l+2),22,2*(c-4),43,2*(n-8)))
    return rules.Endpoint(0,v.prepend(('1',2*a-12),('01',7),('1',2*c-9),('01',l+6),('0',1)),time,-2,'JOIN')

def row(name,p,v=Word()):
    if name=='JOIN':return join(p['a'],p['c'],p['l'],v)
    if name in ('RET39','RET729'):
        t=p['t']
        if type(t) is not int or t<0:raise ValueError('t>=0 integer required')
        c=39 if name=='RET39' else p['c']
        if type(c) is not int or c<11:raise ValueError('c>=11 integer required')
        a=729*t+548;first=rules.core1100(a,c,v);ops=[first];N=2*a-12;k=7;m=2*c-13
        for want in (1,1,1,2,2,0):
            q,r=divmod(N,3);assert r==want
            ep=row('D'+str(r),dict(q=q,k=k,m=m,l=7,s=3),v);ops.append(ep)
            if r==1:N,k,m=10*q-6,k+7,m-3
            elif r==2:N,k=10*q+15,k-1
        return rules.Endpoint(ep.a,ep.tail,sum(x.steps for x in ops),sum(x.shift for x in ops),'RET39')
    if name in ('M0','K0'):
        N=p['N'];k=p.get('k',0);m=p.get('m',0)
        if any(type(x) is not int for x in (N,k,m,p['l'],p['s'])) or N<2 or min(k,m,p['s'])<0 or p['l']<1:raise ValueError('Identity guards')
        w=v.prepend(('1',N),('01',k),('1',m),('01',p['l']),('1',p['s']))
        return rules.Endpoint(0,w,0,0,name)
    q=p['q'];k=p.get('k',0);l=p['l'];s=p['s']
    if any(type(x) is not int for x in (q,k,l,s)) or q<0 or k<0 or l<1 or s<0:raise ValueError('Integer guards')
    isgap=name.startswith('G');r=int(name[1])
    if name in ('D0','D1','D12','D11') and (q<1 or k<1):raise ValueError('D q/k guard')
    if name=='D11join' and (q<2 or k<5 or s<3):raise ValueError('D11join guard')
    if name=='G0' and q<1:raise ValueError('G0 guard')
    if name=='G1' and q<2:raise ValueError('G1 guard')
    if name in ('D2','G2') and k<1:raise ValueError('k>=1 guard')
    m={'D12':2,'D11':1,'D11join':1}.get(name,p.get('m',0))
    if type(m) is not int or m<0 or (name=='D1' and m<3):raise ValueError('middle guard')
    N=3*q+r
    w=v.prepend(('1',N),('01',k),*( (('0',1),) if isgap else (('1',m),) ),('01',l),('1',s))
    e=rules.rewrite(0,w);assert e.rule=='entry1';ops=[e]
    if q:
        ep=rules.rewrite(e.a,e.tail);assert ep.rule=='countdown111'
    else:ep=rules.Endpoint(e.a,e.tail,0,0,'Q0')
    ops.append(ep)
    if name=='D11':pass
    elif name=='D11join':
        # E/Q leaves 1(01)^k1(01)^l1^s = (10)^k11(01)^l11 1^(s-2).
        ep=join(ep.a,k,l,v.prepend(('1',s-2)));ops.append(ep)
    elif r==0:
        if k:
            ep=rules.rewrite(ep.a,ep.tail);assert ep.rule=='normalize01';ops.append(ep)
        if isgap:
            ep=rules.rewrite(ep.a,ep.tail);assert ep.rule=='reset00';ops.append(ep)
    elif r==1:
        ep=rules.rewrite(ep.a,ep.tail);assert ep.rule==('core100' if isgap else 'core111');ops.append(ep)
    else:
        for want in ('pair11','reset00'):
            ep=rules.rewrite(ep.a,ep.tail);assert ep.rule==want;ops.append(ep)
    return rules.Endpoint(ep.a,ep.tail,sum(x.steps for x in ops),sum(x.shift for x in ops),name)
