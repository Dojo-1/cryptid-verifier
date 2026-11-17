"""Record the closed saved frontier and a precisely typed remaining exit."""
import json
from paths import HERE
from raw import replay


def main():
    prefix = '10'*6+'0'+'10'*7+'0'+'10'*2+'0'+'10'*2+'111'
    for filename, tail, steps, q, head in [('frontier.json', '001101', 108, 2, -36),
                                         ('joined-frontier.json', '1101001101', 166, 2, -36),
                                         ('next-boundary.json', '1101101001101', 52, 0, 8)]:
        source = prefix+tail
        actual = replay(dict(q=2, head=0, limit=steps, ones=[-36+i for i, b in enumerate(source) if b == '1']))
        assert (actual['q'], actual['head'], actual['steps']) == (q, head, steps)
        out = dict(source=dict(p=6, c=7, s=2, r=2, m=3, v=tail),
                   endpoint={k: actual[k] for k in ('q', 'head', 'steps', 'ones', 'read_min', 'read_max')},
                   scope='Generic guarded source, not asserted blank-reachable.',
                   status='C-section return' if q == 2 else 'Five-run A entry; scanner tokens can advance, but this table supplies no general return.',
                   remainder=None if q == 2 else 'Unbounded A scanning/return from widths[p,c,1,n-2,3]. Not claimed to be a first uncovered state of every existing calculus.')
        (HERE/filename).write_text(json.dumps(out, indent=2)+'\n')
        print(filename, q, head, steps)


if __name__ == '__main__':
    main()
