"""Independent dense raw-TM reference: no counter-rule or block acceleration."""
from __future__ import annotations

# Written directly from the six-row transition table; q A=0 through F=5.
OPS=(((1,1,1),(0,1,4)),((1,-1,2),(0,1,0)),
     ((0,-1,3),(1,-1,1)),((1,-1,0),(1,-1,4)),
     ((0,-1,1),(0,-1,5)),((1,-1,3),None))


def run(word,steps,q=2,head=0):
    if steps<0:raise ValueError('nonnegative step count required')
    pad=steps+2
    tape=bytearray(2*steps+len(word)+5)
    tape[pad:pad+len(word)]=bytes(int(b) for b in word)
    pos=pad;done=0;lo=pad;hi=pad+len(word)-1
    while done<steps:
        op=OPS[q][tape[pos]]
        if op is None:break
        value,move,q=op;tape[pos]=value;pos+=move;done+=1
        lo=min(lo,pos);hi=max(hi,pos)
    cells={i-pad+head:int(tape[i]) for i in range(lo,hi+1) if tape[i]}
    return {'q':q,'head':pos-pad+head,'steps':done,'halted':OPS[q][tape[pos]] is None,'tape':cells}
