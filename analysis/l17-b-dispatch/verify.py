"""Critic: saved declarations and literal OPS, without the rule actor."""
import gzip
import json
from paths import HERE
from specification import integer, materialize, agrees
from raw import replay


def verify():
    rows = json.loads((HERE/'claims.json').read_text())['rules']
    kernels = json.loads((HERE/'kernels.json').read_text())
    cases = json.loads((HERE/'cases.json').read_text())
    with gzip.open(HERE/'raw-results.jsonl.gz', 'rt') as f:
        actual = [json.loads(x) for x in f]
    assert len(cases) == len(actual) and cases
    for c, r in zip(cases, actual):
        m = c['metadata']
        if 'rule' in m:
            row, p, v = rows[m['rule']], m['p'], m['v']
            assert set(p) == set(row['guards'])
            assert all(type(p[k]) is int and p[k] >= g[0] and (g[1] is None or p[k] <= g[1]) for k, g in row['guards'].items())
            for field in ('source', 'target'):
                assert c[field] == ''.join(w*n for w, n in materialize(row[field], p, v))
            for field, declaration in (('steps', 'steps'), ('head', 'shift'), ('start', 'source_start'), ('target_start', 'target_start')):
                assert c[field] == integer(row[declaration], p)
            assert c['q'] == row['source_q'] and c['qq'] == row['target_q']
            assert c['bounds'] == [integer(x, p) for x in row['read_bounds']]
        else:
            k = kernels[m['kernel']]
            assert c['source'] == m['pad']+k['input']+m['v']
            assert c['target'] == m['pad']+k['output']+m['v']
            assert c['q'] == k['q'] and c['qq'] == k['exit_q']
            assert c['steps'] == k['steps'] and c['head'] == k['exit_head']
            assert c['start'] == c['target_start'] == k['lo']-len(m['pad'])
        req = dict(q=c['q'], head=0, limit=c['steps'], ones=[c['start']+i for i, b in enumerate(c['source']) if b == '1'])
        expected = dict(q=c['qq'], head=c['head'], steps=c['steps'], halted=False,
                        ones=[c['target_start']+i for i, b in enumerate(c['target']) if b == '1'])
        py = replay(req)
        assert agrees(r, expected) and agrees(py, expected)
        if c['steps'] <= 1000:
            assert r['reads'] == py['reads']
        assert (r['read_min'], r['read_max']) == (py['read_min'], py['read_max'])
        assert c['bounds'][0] <= py['read_min'] <= py['read_max'] <= c['bounds'][1]
    return dict(passed=True, endpoints=len(cases), full_traces=sum(c['steps'] <= 1000 for c in cases),
                scope='Separate literal and declarative paths, same author.')


if __name__ == '__main__':
    result = verify()
    (HERE/'verification.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
