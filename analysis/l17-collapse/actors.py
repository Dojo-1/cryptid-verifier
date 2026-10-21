"""Old rule compositions for comparison with the separate collapse critic."""
from search import Word
from extend import rules

T='01'*7+'111'


def cycle(N,k,m,v=Word()):
    if type(N) is not int or type(k) is not int or type(m) is not int or N<2 or k<1 or m<1:
        raise ValueError('Integer N>=2,k>=1,m>=1 required')
    q,r=divmod(N,3)
    if r==1 and m<3:raise ValueError('Outside the safe cycle guard; no 1101/short-middle extension')
    w=v.prepend(('1',N),('01',k),('1',m),(T,1))
    e=rules.rewrite(0,w);assert e.rule=='entry1';ops=[e]
    if q:
        c=rules.rewrite(e.a,e.tail);assert c.rule=='countdown111'
    else:c=rules.Endpoint(e.a,e.tail,0,0,'countdown0')
    ops.append(c)
    if r==0:
        last=rules.rewrite(c.a,c.tail);assert last.rule=='normalize01';ops.append(last)
    elif r==1:
        last=rules.rewrite(c.a,c.tail);assert last.rule=='core111';ops.append(last)
    else:
        p=rules.rewrite(c.a,c.tail);assert p.rule=='pair11';ops.append(p)
        last=rules.rewrite(p.a,p.tail);assert last.rule=='reset00';ops.append(last)
    return {'a':last.a,'tail':last.tail,'steps':sum(x.steps for x in ops),'shift':sum(x.shift for x in ops),'q':q,'r':r}


def immediate(name,h,d,v=Word()):
    if type(h) is not int or type(d) is not int or h<0 or d<0 or (name=='P1' and d==0):
        raise ValueError('Outside the declared immediate-cycle guard')
    N={'P0':6*h+6,'P1':6*h+4,'P2':6*h+2}[name]
    return cycle(N,7,2*d+1,v)


def ranked(N,k,z,v=Word()):
    if type(N) is not int or type(k) is not int or type(z) is not int or N<2 or k<1 or z<1:
        raise ValueError('N>=2,k>=1,z>=1 integer parameters required')
    bound=k+8*z;total=head=0;path=[]
    while True:
        out=cycle(N,k,3*z,v);r=out['r'];q=out['q'];total+=out['steps'];head+=out['shift']
        path.append(r);assert len(path)<=bound
        if r==0 or (r==1 and z==1) or (r==2 and k==1):break
        old=(z,k);old_rank=k+8*z
        if r==1:N,k,z=10*q-6,k+7,z-1
        else:N,k=10*q+15,k-1
        assert (z,k)<old
        assert k+8*z==old_rank-1
    return dict(out,steps=total,shift=head,path=path)


def resonance(k,z,v=Word()):
    if type(k) is not int or type(z) is not int or k<1 or z<0:raise ValueError('k>=1,z>=0 integers required')
    if z==0:return {'a':0,'tail':v.prepend(('1',4),('01',k+7),('1',3)),'steps':0,'shift':0}
    return ranked(4,k,z,v)


def long_return(t,e,v=Word()):
    if type(t) is not int or type(e) is not int or t<0 or e<0:raise ValueError('t,e>=0 integer parameters required')
    first=rules.core1100(243*t+230,e+10,v);N=486*t+448;k=7;m=2*e+7
    total=first.steps;head=first.shift;last=None
    for wanted in (1,2,2,1,0):
        last=cycle(N,k,m,v);assert last['r']==wanted
        total+=last['steps'];head+=last['shift'];q=last['q']
        if wanted==1:N,k,m=10*q-6,k+7,m-3
        elif wanted==2:N,k=10*q+15,k-1
    return dict(last,steps=total,shift=head)
