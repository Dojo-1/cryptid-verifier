"""Finite periodic words; counts stay exact even when the tape is enormous."""
from __future__ import annotations
from dataclasses import dataclass
from math import lcm


def primitive(word, count):
    for n in range(1,len(word)+1):
        if len(word)%n==0 and word[:n]*(len(word)//n)==word:
            return word[:n],count*(len(word)//n)
    raise AssertionError


@dataclass(frozen=True)
class Word:
    parts: tuple[tuple[str,int], ...] = ()

    def __post_init__(self):
        out=[]
        for word,count in self.parts:
            if not word or set(word)-{'0','1'} or not isinstance(count,int) or count<0:
                raise ValueError('binary words and nonnegative integer counts required')
            if not count:continue
            word,count=primitive(word,count)
            if out and out[-1][0]==word:out[-1]=(word,out[-1][1]+count)
            else:out.append((word,count))
        # Only the exterior zero suffix is implicit. Interior zeros are retained.
        while out:
            w,n=out[-1]
            if w[-1]=='1':break
            out.pop()
            if w=='0':continue
            if n>1:out.append((w,n-1))
            tail=w.rstrip('0')
            if tail:out.append((tail,1))
        object.__setattr__(self,'parts',tuple(out))

    @classmethod
    def literal(cls,s):
        return cls(tuple((c,1) for c in s))

    def size(self):return sum(len(w)*n for w,n in self.parts)

    def expand(self,limit=1000000):
        if self.size()>limit:raise ValueError('explicit expansion limit')
        return ''.join(w*n for w,n in self.parts)

    def prefix(self,n,pad=True):
        out=''
        for w,c in self.parts:
            take=min(n-len(out),len(w)*c)
            out+=(w*((take+len(w)-1)//len(w)))[:take]
            if len(out)==n:break
        return out+'0'*(n-len(out)) if pad else out

    def drop(self,n):
        if n<0:raise ValueError('nonnegative prefix length required')
        out=[]
        for w,c in self.parts:
            size=len(w)*c
            if n>=size:n-=size;continue
            if n:
                copies,offset=divmod(n,len(w))
                if offset:
                    out.append((w[offset:],1));copies+=1
                if c-copies:out.append((w,c-copies))
                n=0
            else:out.append((w,c))
        return Word(tuple(out))

    def prepend(self,*parts):return Word(tuple(parts)+self.parts)

    def periodic_prefix_length(self,pattern):
        """Longest explicit prefix matching pattern^infinity, without expansion."""
        total=0
        for w,n in self.parts:
            length=len(w)*n
            period=lcm(len(w),len(pattern))
            for i in range(min(length,period)):
                if w[i%len(w)]!=pattern[(total+i)%len(pattern)]:return total+i
            total+=length
        return total

    def equivalent(self,other):
        if self.size()!=other.size():return False
        i=j=oi=oj=0
        while i<len(self.parts):
            a,na=self.parts[i];b,nb=other.parts[j]
            span=min(len(a)*na-oi,len(b)*nb-oj)
            for k in range(min(span,lcm(len(a),len(b)))):
                if a[(oi+k)%len(a)]!=b[(oj+k)%len(b)]:return False
            oi+=span;oj+=span
            if oi==len(a)*na:i+=1;oi=0
            if oj==len(b)*nb:j+=1;oj=0
        return True

    def to_json(self):return [[w,n] for w,n in self.parts]
