"""Reproduce the exact generic mixed-width boundary and its bounded replay."""
import json
from paths import HERE
from scanner import mixed_obstruction,left_word
from raw import replay
from probe import run
def main():
    initial,tokens,(stack,t,d)=mixed_obstruction();left=left_word(initial);right=''.join(tokens)+'00'+'001101'
    source=left+right;r=replay(dict(q=0,head=0,limit=t+10,ones=[i-len(left) for i,b in enumerate(source) if b=='1']))
    window=''.join(str(int(r['head']+i in r['ones'])) for i in range(-5,1))
    assert (r['q'],r['head'],r['steps'],window)==(2,2,40,'001010')
    full=run(left,right)
    assert (full['reason'],full['steps'],full['head'])==('C-section',166,-34)
    out=dict(initial_runs=initial,tokens=tokens,scanned_runs=stack,scan_time=t,scan_shift=d,after_A00L={k:r[k] for k in ('q','head','steps','ones')},C_window=window,literal_C_section_return={k:full[k] for k in ('steps','head','word','reason')},scope='Generic mixed-token source,not a blank-reachable state. The homogeneous return rules do not cover its width2 runs. The166-step result is a finite literal check,not a general return rule.')
    (HERE/'mixed-boundary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='after_A00L'},indent=2))
if __name__=='__main__':main()
