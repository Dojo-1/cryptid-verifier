"""Exact finite-block TM evaluator with repeated-block sweeps.

The local evaluator is independent of the proposed counter rules. A sweep is
skipped only when one block returns the same control state at the opposite
boundary. This proves a repeatable, disjoint-block path by induction. Tests
compare complete states against a separate dense raw interpreter.
"""
from __future__ import annotations
from functools import lru_cache
from words import Word

TABLE='1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'.split('_')


def push(stack,value,count=1,keep_zero=False):
    if not count or (value==0 and not stack and not keep_zero):return
    if stack and stack[-1][0]==value:stack[-1]=(value,stack[-1][1]+count)
    else:stack.append((value,count))


def pop(stack):
    if not stack:return 0
    value,n=stack[-1]
    if n==1:stack.pop()
    else:stack[-1]=(value,n-1)
    return value


def encode(word,width):
    runs=[];pending=''
    for w,n in word.parts:
        remaining=len(w)*n;phase=0
        while pending and remaining:
            pending+=w[phase];phase=(phase+1)%len(w);remaining-=1
            if len(pending)==width:push(runs,int(pending,2),keep_zero=True);pending=''
        if not remaining:continue
        if width%len(w):
            # Short nonperiodic literals; keep the conversion exact.
            for i in range(remaining):
                pending+=w[(phase+i)%len(w)]
                if len(pending)==width:push(runs,int(pending,2),keep_zero=True);pending=''
            continue
        blocks,left=divmod(remaining,width)
        if blocks:
            pattern=''.join(w[(phase+i)%len(w)] for i in range(width))
            push(runs,int(pattern,2),blocks,keep_zero=True)
        pending+=''.join(w[(phase+i)%len(w)] for i in range(left))
    if pending:push(runs,int(pending.ljust(width,'0'),2),keep_zero=True)
    return runs


class BlockTM:
    def __init__(self,word,width=2,q=2,head=0):
        if width not in (2,6):raise ValueError('supported widths: 2 and 6')
        self.width=width;self.q=q;self.offset=0;self.index=0;self.origin=head
        self.left=[];runs=encode(word,width)
        self.current=runs[0][0] if runs else 0
        if runs:
            value,count=runs[0]
            runs=runs[1:] if count==1 else [(value,count-1)]+runs[1:]
        self.right=list(reversed(runs));self.steps=0;self.events=0;self.swept_blocks=0

    @property
    def head(self):return self.origin+self.index*self.width+self.offset

    @staticmethod
    @lru_cache(maxsize=None)
    def local(width,q,value,offset):
        path=[];seen={}
        while 0<=offset<width:
            key=q,value,offset
            if key in seen:return path,key,'loop',seen[key]
            seen[key]=len(path)
            bit=(value>>(width-1-offset))&1
            token=TABLE[q][3*bit:3*bit+3]
            if token=='---':return path,key,'halt',None
            path.append(key)
            mask=1<<(width-1-offset)
            value=(value|mask) if token[0]=='1' else (value&~mask)
            offset+=1 if token[1]=='R' else -1;q=ord(token[2])-65
        return path,(q,value,offset),'exit',None

    def run(self,budget,max_events=200000):
        if budget<self.steps:raise ValueError('budget precedes current state')
        while self.steps<budget and self.events<max_events:
            path,end,kind,loop=self.local(self.width,self.q,self.current,self.offset)
            cost=len(path);remaining=budget-self.steps;self.events+=1
            if remaining<cost:
                self.q,self.current,self.offset=path[remaining];self.steps=budget;break
            if kind=='loop':
                if remaining>=cost:
                    index=loop+(remaining-loop)%(cost-loop)
                    self.q,self.current,self.offset=path[index];self.steps=budget
                break
            if kind=='halt':
                self.q,self.current,self.offset=end;self.steps+=cost;break
            qout,value,offset=end
            direction=1 if offset==self.width else -1
            incoming=self.right if direction==1 else self.left
            outgoing=self.left if direction==1 else self.right
            count=1
            crossing=(self.offset==0 and direction==1) or (self.offset==self.width-1 and direction==-1)
            if crossing and qout==self.q:
                available=1+(incoming[-1][1] if incoming and incoming[-1][0]==self.current else 0)
                if self.current==0 and not incoming:available=remaining//cost
                count=min(available,remaining//cost)
            if count>1:
                eat=count-1
                if incoming:
                    old,n=incoming[-1]
                    assert old==self.current and eat<=n
                    if eat==n:incoming.pop()
                    else:incoming[-1]=(old,n-eat)
                else:assert self.current==0
                self.swept_blocks+=count
            push(outgoing,value,count)
            self.current=pop(incoming);self.q=qout
            self.index+=direction*count;self.offset=0 if direction==1 else self.width-1
            self.steps+=cost*count
        bit=(self.current>>(self.width-1-self.offset))&1
        halted=TABLE[self.q][3*bit:3*bit+3]=='---'
        return {'steps':self.steps,'events':self.events,'head':self.head,'q':self.q,
                'halted':halted,'complete':self.steps==budget or halted,
                'swept_blocks':self.swept_blocks}

    def tape(self):
        parts=[(format(v,f'0{self.width}b'),n) for v,n in self.left]
        parts.append((format(self.current,f'0{self.width}b'),1))
        parts.extend((format(v,f'0{self.width}b'),n) for v,n in reversed(self.right))
        word=Word(tuple(parts));origin=self.origin+(self.index-sum(n for v,n in self.left))*self.width
        zero=word.periodic_prefix_length('0')
        return origin+zero,word.drop(zero)

    def sparse(self,limit=1000000):
        origin,word=self.tape();bits=word.expand(limit)
        return {origin+i:int(bit) for i,bit in enumerate(bits) if bit=='1'}
