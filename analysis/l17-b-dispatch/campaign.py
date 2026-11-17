"""Seeded endpoint comparisons; run explicitly to regenerate evidence."""
import itertools
import json
import random
import subprocess
from paths import HERE, BASE
from claims import MACHINE, RULES, KERNELS
from specification import integer, materialize, agrees
from raw import replay
import backend


def render(terms, p, v):
    return ''.join(w*n for w, n in materialize(terms, p, v))


def case(name, p, v):
    row = RULES[name]
    return dict(label=name, source=render(row['source'], p, v),
                target=render(row['target'], p, v),
                start=integer(row['source_start'], p), target_start=integer(row['target_start'], p),
                q=row['source_q'], qq=row['target_q'], steps=integer(row['steps'], p),
                head=integer(row['shift'], p), bounds=[integer(x, p) for x in row['read_bounds']],
                metadata=dict(rule=name, p=p, v=v))


def request(c, i):
    return dict(id=i, machine=MACHINE, q=c['q'], head=0, limit=c['steps'],
                trace=c['steps'] <= 1000, ones=[c['start']+i for i, b in enumerate(c['source']) if b == '1'])


def want(c):
    return dict(q=c['qq'], head=c['head'], steps=c['steps'], halted=False,
                ones=[c['target_start']+i for i, b in enumerate(c['target']) if b == '1'])


def generate():
    rng = random.Random(17112028)
    out = []
    for name, row in RULES.items():
        base = {k: v[0] for k, v in row['guards'].items()}
        for delta in itertools.product(range(2), repeat=len(base)):
            p = {k: v+d for (k, v), d in zip(base.items(), delta)}
            for v in ('', '1', '001101'):
                out.append(case(name, p, v))
        for _ in range(12):
            p = {k: v+rng.randrange(128) for k, v in base.items()}
            v = ''.join(rng.choice('01') for _ in range(31))
            out.append(case(name, p, v))
    for name, (q, t, qq, h, lo, src, dst) in KERNELS.items():
        for _ in range(16):
            pad = ''.join(rng.choice('01') for _ in range(17))
            v = ''.join(rng.choice('01') for _ in range(17))
            out.append(dict(label='kernel:'+name, source=pad+src+v, target=pad+dst+v,
                            start=lo-len(pad), target_start=lo-len(pad),
                            q=q, qq=qq, steps=t, head=h, bounds=[lo, lo+len(src)-1],
                            metadata=dict(kernel=name, pad=pad, v=v)))
    assert len(out) <= 1200
    return out


def main():
    (HERE/'build').mkdir(exist_ok=True)
    binary = HERE/'build/raw-o2'
    subprocess.run(['g++', '-std=c++17', '-O2', str(BASE/'l17-hardening/raw_comparator.cpp'),
                    '-o', str(binary)], check=True)
    cases = generate()
    assert max(c['steps'] for c in cases) <= 200000
    ledger = HERE/'raw-budget.jsonl'
    spent = sum(json.loads(x)['executed_defined_transitions'] for x in ledger.read_text().splitlines()) if ledger.exists() else 0
    backend.set_budget(20000000-spent, ledger)
    got, meta = backend.execute(binary, [request(c, i) for i, c in enumerate(cases)], HERE/'raw-results.jsonl.gz')
    kernels = {}
    for name, (q, t, qq, h, lo, src, dst) in KERNELS.items():
        r = replay(dict(q=q, head=0, limit=t, ones=[lo+i for i, b in enumerate(src) if b == '1']))
        kernels[name] = dict(q=q, steps=t, exit_q=qq, exit_head=h, lo=lo,
                             input=src, output=dst, reads=r['reads'],
                             read_min=r['read_min'], read_max=r['read_max'])
    for i, (c, r) in enumerate(zip(cases, got)):
        py = replay(request(c, i))
        if not (agrees(r, want(c)) and agrees(py, want(c)) and (c['steps'] > 1000 or r['reads'] == py['reads'])
                and (r['read_min'], r['read_max']) == (py['read_min'], py['read_max'])
                and c['bounds'][0] <= r['read_min'] <= r['read_max'] <= c['bounds'][1]):
            (HERE/'failed-case.json').write_text(json.dumps(dict(case=c, actual=r, python=py), indent=2)+'\n')
            raise AssertionError(c['label'])
    (HERE/'claims.json').write_text(json.dumps(dict(machine=MACHINE, rules=RULES), indent=2)+'\n')
    (HERE/'kernels.json').write_text(json.dumps(kernels, indent=2)+'\n')
    (HERE/'cases.json').write_text(json.dumps(cases, separators=(',', ':'))+'\n')
    counts = {name: sum(c['label'] == name for c in cases) for name in sorted({c['label'] for c in cases})}
    result = dict(passed=True, cases=len(cases), full_trace_comparisons=sum(c['steps'] <= 1000 for c in cases),
                  by_kind=counts, maximum_steps=max(c['steps'] for c in cases), raw_metadata=meta,
                  scope='Same-author paths; compiler modes and raw implementations are controls, not external replication.')
    (HERE/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
