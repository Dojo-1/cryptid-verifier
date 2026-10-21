"""Generic exact linear solver over the consumed frozen row schemas.

No counter actor, inverse implementation, Word class or orbit engine imports.
"""
import ast,json,hashlib
from fractions import Fraction
from functools import lru_cache
from frame_paths import HERE

@lru_cache(None)
def linear(expr,names):
    if type(expr) is int:return (expr,)+(0,)*len(names)
    def visit(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return (n.value,)+(0,)*len(names)
        if isinstance(n,ast.Name):return (0,)+tuple(int(k==n.id) for k in names)
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return tuple(-x for x in visit(n.operand))
        if isinstance(n,ast.BinOp):
            a,b=visit(n.left),visit(n.right)
            if isinstance(n.op,ast.Add):return tuple(x+y for x,y in zip(a,b))
            if isinstance(n.op,ast.Sub):return tuple(x-y for x,y in zip(a,b))
            if isinstance(n.op,ast.Mult):
                if not any(a[1:]):return tuple(a[0]*x for x in b)
                if not any(b[1:]):return tuple(b[0]*x for x in a)
        raise ValueError('Non-affine expression')
    return visit(ast.parse(expr,mode='eval').body)

def solve(terms,values,names):
    matrix=[]
    for expr,value in zip(terms,values):
        a=linear(expr,names);matrix.append([Fraction(x) for x in a[1:]]+[Fraction(value-a[0])])
    row=0;pivots={}
    for col in range(len(names)):
        pivot=next((i for i in range(row,len(matrix)) if matrix[i][col]),None)
        if pivot is None:continue
        matrix[row],matrix[pivot]=matrix[pivot],matrix[row]
        scale=matrix[row][col];matrix[row]=[x/scale for x in matrix[row]]
        for i in range(len(matrix)):
            if i!=row and matrix[i][col]:
                scale=matrix[i][col];matrix[i]=[x-scale*y for x,y in zip(matrix[i],matrix[row])]
        pivots[col]=row;row+=1
    if any(not any(r[:-1]) and r[-1] for r in matrix):return None
    if len(pivots)!=len(names):raise ValueError('Underdetermined counter schema')
    result={name:matrix[pivots[i]][-1] for i,name in enumerate(names)}
    if any(x.denominator!=1 for x in result.values()):return None
    return {k:int(v) for k,v in result.items()}

def evaluate(expr,names,p):
    a=linear(expr,names);return a[0]+sum(a[i+1]*p[k] for i,k in enumerate(names))

def specs():
    path=HERE.parent/'l17-general-d/claims.json';data=json.loads(path.read_text());rules=data['rules'];out=[]
    for name,source_mode,target_mode,strengthen in (('D1','D','D',{'m':4}),('D2','D','D',{'k':2}),('D12','D','G',{}),('G1','G','D',{'l':2}),('G2','G','G',{}),('D11join','D','D',{})):
        rule=rules[name];guards={k:list(v) for k,v in rule['guards'].items()}
        for k,lo in strengthen.items():guards[k][0]=lo
        def vector(mode,terms):
            assert [x[0] for x in terms[:5]]==(['1','01','1','01','1'] if mode=='D' else ['1','01','0','01','1'])
            return [terms[0][1],terms[1][1],terms[2][1] if mode=='D' else 0,terms[3][1],terms[4][1]]
        out.append(dict(name=name,source_mode=source_mode,target_mode=target_mode,source=vector(source_mode,rule['source']),target=vector(target_mode,rule['target']),guards=guards))
    return out,hashlib.sha256(path.read_bytes()).hexdigest()

def candidates(mode,values,rows,reverse=True):
    output=[]
    for row in rows:
        side='target' if reverse else 'source';other='source' if reverse else 'target'
        if mode!=row[side+'_mode']:continue
        names=tuple(row['guards']);p=solve(row[side],values,names)
        if p is None:continue
        if any(p[k]<lo or (hi is not None and p[k]>hi) for k,(lo,hi) in row['guards'].items()):continue
        output.append((row['name'],row[other+'_mode'],tuple(evaluate(t,names,p) for t in row[other])))
    return output
