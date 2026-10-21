"""Compare generic affine-schema solving with the new forward/inverse actor."""
import json,random,hashlib,time
from dataclasses import asdict
from frame_paths import HERE
from counter_critic import specs,candidates
from counter_streams import State,forward,inverse,trace,push_entry

def values(x):return (x.N,x.k,x.m,x.l,x.s)
def pack(value):
    if value is None:return []
    name,x=value;return [(name,x.mode,values(x))]

def main():
    began=time.monotonic();rows,binding=specs();rng=random.Random(21102027);checks=0
    for i in range(2400):
        mode=rng.choice(('D','G'));N=rng.randrange(2,200) if i<2000 else (1<<rng.randrange(128,2048))+rng.randrange(10000)
        x=State(mode,N,rng.randrange(1 if mode=='D' else 0,25),rng.randrange(1,25) if mode=='D' else 0,rng.randrange(1,20),rng.randrange(10))
        name,y=forward(x)
        assert candidates(x.mode,values(x),rows,False)==pack((name,y) if y else None)
        assert candidates(x.mode,values(x),rows,True)==pack(inverse(x))
        if y is not None:assert candidates(y.mode,values(y),rows,True)==[(name,x.mode,values(x))]
        checks+=1
    source=HERE.parent/'l17-general-d/boundary.json';raw=source.read_bytes();boundary=json.loads(raw);A=int(boundary['a'],16)
    root=push_entry(A,39);chain,end,why=trace(root);x=end
    for name,expected_before,expected_after in reversed(chain):
        options=candidates(x.mode,values(x),rows,True);assert options==[(name,expected_before.mode,values(expected_before))]
        assert inverse(x)==(name,expected_before);x=expected_before
    assert x==root and not candidates(root.mode,values(root),rows,True)
    result=dict(passed=True,generic_schema_states=checks,huge_boundary_A_bits=A.bit_length(),huge_internal_rows=len(chain),huge_stop=why,huge_reverse_recovered_exact_push=True,boundary_source_sha256=hashlib.sha256(raw).hexdigest(),claims_sha256=binding,critic_uses_actor_for_candidates=False,critic_solver='Exact Fraction Gaussian elimination over the frozen claim expressions',elapsed_seconds=time.monotonic()-began)
    (HERE/'streams-recheck.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
