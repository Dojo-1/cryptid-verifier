"""Critic's declarative semantics. No actor/rules/words imports, no execution on import."""
from __future__ import annotations
import ast
import json
from math import gcd
from pathlib import Path


def integer(expression, parameters):
    if type(expression) is int:return expression
    def visit(node):
        if isinstance(node,ast.Constant) and type(node.value) is int:return node.value
        if isinstance(node,ast.Name) and type(parameters.get(node.id)) is int:return parameters[node.id]
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return -visit(node.operand)
        if isinstance(node,ast.BinOp):
            left,right=visit(node.left),visit(node.right)
            if isinstance(node.op,ast.Add):return left+right
            if isinstance(node.op,ast.Sub):return left-right
            if isinstance(node.op,ast.Mult):return left*right
        raise ValueError('Only integer constants, declared names, +, -, * are accepted')
    return visit(ast.parse(expression,mode='eval').body)


def materialize(terms,parameters,suffix):
    result=[]
    for pattern,count in terms:
        n=integer(count,parameters)
        if pattern=='v' and not isinstance(suffix,str):
            if n!=1:raise ValueError('Compressed suffix occurs exactly once')
            result.extend(suffix);continue
        pattern=suffix if pattern=='v' else pattern
        if n<0 or set(pattern)-{'0','1'}:raise ValueError('Invalid finite binary word')
        if pattern and n:result.append((pattern,n))
    return result


def trim(chunks):
    """Remove only the exterior zero suffix, retaining all interior bits."""
    chunks=[(w,n) for w,n in chunks if w and n]
    while chunks and chunks[-1][0].endswith('0'):
        word,count=chunks.pop()
        if not word.strip('0'):continue
        zeros=len(word)-len(word.rstrip('0'))
        if count>1:chunks.append((word,count-1))
        chunks.append((word[:-zeros],1))
    return [(w,n) for w,n in chunks if w and n]


def skip(chunks,count):
    if count<0:raise ValueError('Nonnegative skip required')
    result=[]
    for word,n in chunks:
        length=len(word)*n
        if count>=length:count-=length;continue
        if count:
            copies,offset=divmod(count,len(word))
            if offset:result.append((word[offset:],1));copies+=1
            if n>copies:result.append((word,n-copies))
            count=0
        else:result.append((word,n))
    return result


def first_bits(chunks,count):
    result=''
    for word,n in chunks:
        take=min(count-len(result),len(word)*n)
        result+=(word*((take+len(word)-1)//len(word)))[:take]
        if len(result)==count:break
    return result+'0'*(count-len(result))


def matching_prefix(chunks,pattern):
    total=0
    for word,n in chunks:
        size=len(word)*n
        bound=len(word)+len(pattern)-gcd(len(word),len(pattern))
        for k in range(min(size,bound)):
            if word[k%len(word)]!=pattern[(total+k)%len(pattern)]:return total+k
        total+=size
    return total


def expand(chunks,limit=100000):
    chunks=trim(chunks)
    if sum(len(w)*n for w,n in chunks)>limit:raise ValueError('Raw materialization limit exceeded')
    return ''.join(w*n for w,n in chunks)


def equal_words(left,right):
    """Exact comparison by periodic cursors and the Fine-Wilf period bound.

    Two p/q-periodic spans agreeing for p+q-gcd(p,q) positions agree over
    their overlap. Shorter overlaps are inspected in full. No probabilistic hash.
    """
    left,right=trim(left),trim(right)
    if sum(len(w)*n for w,n in left)!=sum(len(w)*n for w,n in right):return False
    if not left:return True
    li=ri=lo=ro=0
    while li<len(left):
        a,na=left[li];b,nb=right[ri]
        span=min(len(a)*na-lo,len(b)*nb-ro)
        bound=len(a)+len(b)-gcd(len(a),len(b))
        if any(a[(lo+k)%len(a)]!=b[(ro+k)%len(b)] for k in range(min(span,bound))):return False
        lo+=span;ro+=span
        if lo==len(a)*na:li+=1;lo=0
        if ro==len(b)*nb:ri+=1;ro=0
    return True


class Claims:
    def __init__(self,path):
        self.path=Path(path);self.document=json.loads(self.path.read_text())
        self.machine=self.document['machine'];self.rules=self.document['rules']

    def instantiate(self,rule,parameters=None,suffix=''):
        parameters={} if parameters is None else dict(parameters)
        if isinstance(suffix,str):
            if set(suffix)-{'0','1'}:raise ValueError('Binary suffix required')
        elif any(not w or set(w)-{'0','1'} or type(n) is not int or n<0 for w,n in suffix):
            raise ValueError('Invalid compressed suffix')
        claim=self.rules[rule]
        if set(parameters)!=set(claim['guards']):raise ValueError('Exactly the declared parameter names are required')
        for name,(lower,upper) in claim['guards'].items():
            value=parameters[name]
            if type(value) is not int or value<lower or (upper is not None and value>upper):raise ValueError('Parameter outside claim guard')
        steps=integer(claim['steps'],parameters)
        shift=integer(claim['shift'],parameters)
        return {'rule':rule,'parameters':parameters,'suffix':suffix,
                'source':materialize(claim['source'],parameters,suffix),
                'target':materialize(claim['target'],parameters,suffix),
                'steps':steps,'shift':shift}


def request(case,identifier,head=0):
    bits=expand(case['source'])
    return {'id':identifier,'machine':case['machine'],'q':2,'head':head,'limit':case['steps'],
            'ones':[head+i for i,b in enumerate(bits) if b=='1'],'trace':False}


def want(case,head=0):
    bits=expand(case['target'])
    return {'q':2,'head':head+case['shift'],'steps':case['steps'],'halted':False,
            'ones':[head+case['shift']+i for i,b in enumerate(bits) if b=='1']}


def agrees(actual,expected):
    return all(actual[key]==expected[key] for key in ('q','head','steps','halted','ones'))
