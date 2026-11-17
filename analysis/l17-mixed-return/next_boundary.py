"""Record the typed B exit when the stronger full-return buffer is absent."""
import json
from paths import HERE
from raw import replay
def main():
    # Use the source shape directly: the full C2_s2 row requires m>=6,
    # whereas this checkpoint deliberately supplies only three right ones.
    p,c,s,r,m=6,7,2,2,3;v='001101';src='10'*p+'0'+'10'*c+'0'+'10'*s+'0'+'10'*r+'1'*m+v;start=-2*p-2*c-2*s-2*r-2
    actual=replay(dict(q=2,head=0,limit=38,ones=[start+i for i,b in enumerate(src) if b=='1']))
    assert (actual['q'],actual['head'],actual['read_max'])==(1,4,3)
    out=dict(source=dict(p=p,c=c,s=s,r=r,m=m,v=v),checkpoint={k:actual[k] for k in ('q','head','steps','ones','read_min','read_max')},reason='The full C2_s2 table needs six leading ones. After three are consumed the next B read is arbitrary context; v has not been read.',scope='Generic source,not claimed blank-reachable. Uncovered by this guarded table,not claimed to be a nonreturning state.')
    (HERE/'next-boundary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
