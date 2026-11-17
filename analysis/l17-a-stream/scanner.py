"""Exact A-stream stack actor. The raw comparator does not import this file."""
def decode(right,cap=96):
    """Decode the unique finite stream, using the exterior zero tail if needed."""
    if set(right)-{'0','1'}:raise ValueError('binary word required')
    padded=right+'000';i=0;tokens=[]
    while True:
        if padded[i:i+2] in ('00','11'):return tokens,padded[i:i+2],i
        if padded[i:i+3]=='100':return tokens,'100',i
        if len(tokens)>=cap:raise ValueError('scanner token budget')
        if padded[i:i+2]=='01':tokens.append('01');i+=2
        elif padded[i:i+3]=='101':tokens.append('101');i+=3
        else:raise AssertionError('incomplete prefix code')

def compile_stack(runs,tokens):
    if len(runs)<1 or runs[-1]<2 or any(type(x) is not int or x<0 for x in runs):raise ValueError('invalid left run stack')
    out=list(runs);steps=shift=0
    for token in tokens:
        if token=='01':out[-1]+=1;steps+=2;shift+=2
        elif token=='101':
            if out[-1]<2:raise ValueError('A101 needs two10 pairs')
            out[-1]-=2;out.append(3);steps+=13;shift+=3
        else:raise ValueError('not an A scanning token')
    return out,steps,shift

def left_word(runs):return '0'.join('10'*n for n in runs)

def mixed_obstruction():
    before=[6,7,3];tokens=['01','101','01','101']
    return before,tokens,compile_stack(before,tokens)
