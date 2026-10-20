def orbit(extra=True, maxit=10**4):
    a,b,t=0,2,2; log=[]
    for it in range(maxit):
        if a==0 and b>=1: t+=2; a=1; continue
        if b>=3:
            q=b//3; t+=q*(6*a+21)+15*q*(q-1); a+=5*q; b%=3; continue
        if b==0: t+=4*a+8; a,b=0,2*a+4; log.append(('C(0,b)',b)); continue
        if b==2: t+=6*a+21; a,b=a+4,0; continue
        log.append(('C(a,1)',a,a%3,t))
        if extra and a%3==0 and a>=6:
            k=a//3; t+=60*k*k-204*k+244; a,b=10*k-12,3; continue
        return log,(a,t)
    return log,None
if __name__=='__main__':
    log,end=orbit(False); print([x[1] for x in log if x[0]=='C(0,b)'], log[-1])
    log,end=orbit(True,200); 
    for x in log: print(x)
    print(end)
