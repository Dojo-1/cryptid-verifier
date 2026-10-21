"""Explicit reversible display frames; logical neighbor moves stay explicit."""
from dataclasses import dataclass

@dataclass(frozen=True)
class Frame:
    name:str
    gaps:tuple=(1,)
    sign:int=1
    offsets:tuple=(0,)
    irregular:bool=False
    def __post_init__(self):
        if self.sign not in (-1,1) or not self.gaps or any(type(g) is not int or g<1 for g in self.gaps) or not self.offsets:raise ValueError('Invalid embedding')
    def offset(self,t):
        if type(t) is not int or t<0:raise ValueError('Nonnegative event clock')
        return (3*(t^(t>>1)).bit_count()-2*t.bit_count()) if self.irregular else self.offsets[t%len(self.offsets)]
    def place(self,x,t):
        if type(x) is not int:raise ValueError('Integer logical cell')
        q,r=divmod(x,len(self.gaps));z=q*sum(self.gaps)+sum(self.gaps[:r])
        return self.offset(t)+self.sign*z
    def unplace(self,y,t):
        z=self.sign*(y-self.offset(t));q,r=divmod(z,sum(self.gaps));prefix=0
        for j,g in enumerate(self.gaps):
            if prefix==r:return q*len(self.gaps)+j
            prefix+=g
        raise ValueError('Display filler is not a logical cell')
    def encode(self,state):
        t,q,h,ones=state
        return t,q,self.place(h,t),frozenset(self.place(x,t) for x in ones)
    def decode(self,view):
        t,q,h,ones=view
        return t,q,self.unplace(h,t),frozenset(self.unplace(x,t) for x in ones)

def table(machine):
    result=[]
    for row in machine.split('_'):
        out=[]
        for token in (row[:3],row[3:]):
            out.append(None if token=='---' else (int(token[0]),1 if token[1]=='R' else -1,ord(token[2])-65))
        result.append(out)
    return result

def mapped_step(frame,view,ops):
    """Execute on displayed cells. No call to the raw reference step."""
    t,q,head,ones=view;op=ops[q][int(head in ones)]
    if op is None:return view,False
    write,d,qq=op;cells=set(ones)
    if write:cells.add(head)
    else:cells.discard(head)
    logical_head=frame.unplace(head,t)
    # Remap the whole displayed tape when the observation frame moves.
    cells=frozenset(frame.place(frame.unplace(x,t),t+1) for x in cells)
    return (t+1,qq,frame.place(logical_head+d,t+1),cells),True

def variants():
    return [Frame('identity'),Frame('reflection',sign=-1),Frame('waggling',offsets=(0,5,-3,2,-1)),Frame('elongation-3',gaps=(3,)),Frame('unequal-spacing',gaps=(1,4,2,3)),Frame('waggling-stretch',gaps=(1,4,2,3),offsets=(0,5,-3,2,-1)),Frame('irregular',gaps=(2,1,3),irregular=True),Frame('opposite-irregular',gaps=(2,1,3),sign=-1,irregular=True)]

def angled(t,h,M=3,P=2):
    if type(M) is not int or type(P) is not int or M<=abs(P):raise ValueError('Need M>|P| for all logical unit head moves')
    return M*t+P*h

def adaptive_increment(frame,t,P=2):
    """A sufficient positive clock increment before adding P*display-head."""
    return 1+abs(P)*(max(frame.gaps)+abs(frame.offset(t+1)-frame.offset(t)))
