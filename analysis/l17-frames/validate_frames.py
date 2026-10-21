"""Frame metamorphisms against literal raw traces, including halting at time0."""
import json,random,subprocess,hashlib,time
from collections import Counter
from frame_paths import HERE,HARDENING
from reference import OPS
from tape_frames import variants,table,mapped_step,angled,adaptive_increment
from backend import execute,set_budget

MACHINE='1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'

def raw_step(x):
    t,q,h,ones=x;op=OPS[q][int(h in ones)]
    if op is None:return x,False
    value,d,qq=op;ones=set(ones)
    if value:ones.add(h)
    else:ones.discard(h)
    return (t+1,qq,h+d,frozenset(ones)),True

def inputs():
    rng=random.Random(21102026);out=[(0,0,0,frozenset()),(0,2,0,frozenset()),(0,5,0,frozenset({0})),(0,1,-3,frozenset({-4,-3,-1,2}))]
    for a in (37,46):
        word='01'*a+'10'*7+'1100';out.append((0,2,0,frozenset(i for i,b in enumerate(word) if b=='1')))
    while len(out)<32:out.append((0,rng.randrange(6),rng.randrange(-8,9),frozenset(i for i in range(-16,17) if rng.randrange(3)==0)))
    return out

def main():
    began=time.monotonic();ops=table(MACHINE);frames=variants();reqs=[];traces=[];checks=Counter();mutants=[]
    for identifier,x in enumerate(inputs()):
        initial=x;states=[x];reads=[]
        for _ in range(512):
            y,defined=raw_step(x)
            if not defined:break
            reads.append([x[1],x[2],int(x[2] in x[3])]);x=y;states.append(x)
        traces.append((states,reads));reqs.append(dict(id=identifier,machine=MACHINE,q=initial[1],head=initial[2],limit=512,trace=True,ones=sorted(initial[3])))
        for frame in frames:
            view=frame.encode(initial);clock=2*view[2]
            assert frame.decode(view)==initial
            for old,y in zip(states,states[1:]):
                oldview=view;view,defined=mapped_step(frame,view,ops)
                assert defined and frame.decode(view)==y
                assert view==frame.encode(y);checks['decoded_full_snapshots']+=1
                assert angled(y[0],y[2])>angled(old[0],old[2]);checks['logical_angled_clock']+=1
                increment=adaptive_increment(frame,old[0])+2*(view[2]-oldview[2]);assert increment>=1;clock+=increment
                checks['adaptive_display_clock']+=1
            # A halt does not advance the frame clock or rewrite a tape cell.
            if OPS[states[-1][1]][int(states[-1][2] in states[-1][3])] is None:
                same,defined=mapped_step(frame,view,ops);assert not defined and same==view;checks['halt_freezes_clock']+=1
        # An irregular observation schedule covers all intervals including the end.
        rng=random.Random(1000+identifier);points=[0]
        while points[-1]<len(states)-1:points.append(min(len(states)-1,points[-1]+rng.randrange(1,18)))
        recovered=[]
        for j,(a,b) in enumerate(zip(points,points[1:])):recovered.extend(states[a:b])
        if len(states)>1:recovered.append(states[-1]);assert recovered==states
        checks['irregular_interval_covers']+=1
    source=HARDENING/'raw_comparator.cpp';binary=HERE/'frame-comparator'
    subprocess.run(['g++','-std=c++17','-O2',str(source),'-o',str(binary)],check=True,capture_output=True)
    set_budget(2000000,HERE/'raw-budget.jsonl');actual,meta=execute(binary,reqs,HERE/'raw-traces.jsonl.gz')
    for out,(states,reads) in zip(actual,traces):
        t,q,h,ones=states[-1]
        assert (out['q'],out['head'],out['steps'],out['ones'])==(q,h,t,sorted(ones))
        assert out['halted']==(OPS[q][int(h in ones)] is None) and out['reads']==reads
    # Domain/coordinate mutations with explicit counterexamples.
    f={x.name:x for x in frames};x=(0,0,0,frozenset());y,_=raw_step(x)
    for name,wrong in (('stretch-unit-move',1),('reflection-forgot-direction',1)):
        frame=f['elongation-3' if name.startswith('stretch') else 'reflection'];assert wrong!=frame.encode(y)[2];mutants.append(dict(mutant=name,killed=True))
    frame=f['waggling'];good=frame.encode(y)
    assert frozenset({0})!=good[3];mutants.append(dict(mutant='waggling-forgot-tape-remap',killed=True))
    assert frame.decode((0,*good[1:]))!=y;mutants.append(dict(mutant='forgot-frame-phase',killed=True))
    try:f['elongation-3'].unplace(1,0)
    except ValueError:mutants.append(dict(mutant='filler-treated-as-cell',killed=True))
    else:raise AssertionError('Filler accepted')
    try:angled(0,0,1,1)
    except ValueError:mutants.append(dict(mutant='zero-causal-clock-increment',killed=True))
    else:raise AssertionError('Bad angle accepted')
    states=traces[0][0];bad=[]
    for a,b in zip(states,states[1:]):
        delta=3*(b[0]-a[0])+2*(frame.place(b[2],b[0])-frame.place(a[2],a[0]))
        if delta<=0:bad.append(delta)
    assert bad;mutants.append(dict(mutant='naive-physical-clock-under-waggling',killed=True,witness_increment=bad[0]))
    halted=frame.encode((0,5,0,frozenset({0})));assert mapped_step(frame,halted,ops)==(halted,False)
    mutants.append(dict(mutant='advance-clock-on-undefined-transition',killed=True))
    (HERE/'raw-requests.json').write_text(json.dumps(reqs,indent=2)+'\n')
    result=dict(passed=True,raw_cases=len(reqs),frame_variants=len(frames),checks=dict(checks),raw_reference_defined_transitions=sum(len(r) for _,r in traces),raw_metadata=meta,comparator_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),frame_mutations=mutants,total_frame_mutants=len(mutants),shared_authorship=True,elapsed_seconds=time.monotonic()-began)
    (HERE/'frames-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
