"""Whole-tape checks for the homogeneous11 returns and their outer sweeps.

The formulas are written independently of the Lean term. Literal Python
execution uses the frozen OPS table; C++ reads the machine's RLE string.
Importing this module performs no simulation, compilation or file writes.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.dont_write_bytecode = True
sys.path[:0] = [str(ROOT/'analysis/l17-hardening'), str(ROOT/'analysis/l17-stacked-section')]
from reference import OPS
import backend

MACHINE = '1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'
SEED = 17112029
CPP_BUDGET = 2_000_000


def full_case(parity, u, v, h, suffix):
    if type(parity) is not int or parity not in (0, 1) or any(type(n) is not int or n < 0 for n in (u, v, h)):
        raise ValueError('parity0/1 and natural counter parameters required')
    if not isinstance(suffix, str) or set(suffix)-{'0', '1'}:
        raise ValueError('binary suffix required')
    p, c = u+6, v+7
    j = 2*h+parity
    left = '10'*p+'0'+'10'*c+'0'+'10'*3
    start = -len(left)
    if parity == 0:
        target = '1'*(2*u+2)+'01'*7+'1'*(2*v+5)+'01'*(3*h+7)+'0'+suffix
        steps = 40*h+2*u+2*v+86
    else:
        target = '1'*(2*u+6)+'01'*(v+3*h+16)+'0'+suffix
        steps = 40*h+2*u+4*v+92
    return dict(kind='even' if parity == 0 else 'odd', q=0, qq=2,
                source=left+'101'*j+'11'+suffix, target=target,
                start=start, head=start, steps=steps,
                bounds=[start, 3*j+1], metadata=dict(u=u, v=v, h=h, suffix=suffix))


def helper_case(kind, n, pad, suffix):
    if kind not in ('middle', 'outer22') or type(n) is not int or n < 0:
        raise ValueError('known helper kind and natural sweep count required')
    if any(not isinstance(s, str) or set(s)-{'0', '1'} for s in (pad, suffix)):
        raise ValueError('binary exterior contexts required')
    if kind == 'middle':
        word = '0'+'10'*n+'1'
        out = '1'*(2*n+2)
        lo = -2*n-1
        head, steps, q = lo-1, 2*(n+1), 2
    else:
        word = '10'*(n+4)+'01010'
        out = '1'*(2*n+1)+'10'*6
        lo = -2*(n+4)
        head, steps, q = lo, 22+2*n, 3
    return dict(kind=kind, q=q, qq=2, source=pad+word+suffix,
                target=pad+out+suffix, start=lo-len(pad), head=head, steps=steps,
                bounds=[lo, lo+len(word)-1], metadata=dict(n=n, pad=pad, suffix=suffix))


def cases():
    rng = random.Random(SEED)
    out = [full_case(parity, u, v, h, suffix)
           for parity, u, v, h, suffix in itertools.product(
               range(2), range(4), range(4), range(9), ('', '1', '001101'))]
    for parity in range(2):
        for _ in range(32):
            out.append(full_case(parity, rng.randrange(64), rng.randrange(64), rng.randrange(128),
                                 ''.join(rng.choice('01') for _ in range(31))))
    for kind in ('middle', 'outer22'):
        for n in range(9):
            for _ in range(8):
                pad = ''.join(rng.choice('01') for _ in range(17))
                suffix = ''.join(rng.choice('01') for _ in range(17))
                out.append(helper_case(kind, n, pad, suffix))
    assert len(out) == 1072 and max(c['steps'] for c in out) <= 200000
    return out


def request(c, i, offset=0):
    return dict(id=i, machine=MACHINE, q=c['q'], head=offset, limit=c['steps'],
                trace=c['steps'] <= 1000,
                ones=[c['start']+i+offset for i, b in enumerate(c['source']) if b == '1'])


def expected(c, offset=0):
    return dict(q=c['qq'], head=c['head']+offset, steps=c['steps'], halted=False,
                ones=[c['start']+i+offset for i, b in enumerate(c['target']) if b == '1'])


def agrees(got, want):
    return all(got[k] == want[k] for k in ('q', 'head', 'steps', 'halted', 'ones'))


def literal(req):
    q, head, done = req['q'], req['head'], 0
    ones = set(req['ones'])
    reads = []
    lo = hi = None
    while done < req['limit']:
        b = int(head in ones)
        op = OPS[q][b]
        if op is None:
            break
        if req.get('trace', False):
            reads.append([q, head, b])
        lo = head if lo is None else min(lo, head)
        hi = head if hi is None else max(hi, head)
        value, move, q = op
        if value:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        done += 1
    return dict(q=q, head=head, steps=done, halted=OPS[q][int(head in ones)] is None,
                ones=sorted(ones), reads=reads, read_min=lo, read_max=hi)


def check(c, got, py, offset=0):
    assert agrees(got, expected(c, offset)), (c['kind'], c['metadata'], got, expected(c, offset))
    assert agrees(py, expected(c, offset))
    assert (got['read_min'], got['read_max']) == (py['read_min'], py['read_max'])
    assert c['bounds'][0]+offset <= got['read_min'] <= got['read_max'] <= c['bounds'][1]+offset
    if c['steps'] <= 1000:
        assert got['reads'] == py['reads']


def mutations(queue, actual):
    results = []
    def mutate(name, kind, field, change, predicate=lambda c: True):
        c, got = next((c, r) for c, r in zip(queue, actual) if c['kind'] == kind and predicate(c))
        bad = copy.deepcopy(c)
        bad[field] = change(c)
        killed = not agrees(got, expected(bad))
        assert killed, name
        results.append(dict(name=name, killed=killed, witness=c['metadata']))
    mutate('even_missing_D10_clock', 'even', 'steps', lambda c: c['steps']-4)
    mutate('odd_extra_D10_clock', 'odd', 'steps', lambda c: c['steps']+4)
    mutate('even_head_one_pair_short', 'even', 'head', lambda c: c['head']+2)
    mutate('odd_consumes_nonexistent_separator', 'odd', 'head', lambda c: c['head']-2)
    mutate('middle_forgets_separator_clock', 'middle', 'steps', lambda c: c['steps']-2)
    mutate('middle_forgets_separator_head', 'middle', 'head', lambda c: c['head']+2)
    mutate('outer22_uses_middle_clock', 'outer22', 'steps', lambda c: c['steps']+2)
    mutate('outer22_uses_middle_head', 'outer22', 'head', lambda c: c['head']-2)
    mutate('even_drops_internal_zero', 'even', 'target', lambda c: c['target'].replace('0', '', 1))
    mutate('odd_drops_zero_before_context', 'odd', 'target',
           lambda c: c['target'][:-len(c['metadata']['suffix'])-1]+c['metadata']['suffix'],
           lambda c: c['metadata']['suffix'] == '001101')
    c, got = next((c, r) for c, r in zip(queue, actual) if c['kind'] == 'even' and c['metadata']['h'] == 1)
    u, v, h = (c['metadata'][k] for k in ('u', 'v', 'h'))
    bad = copy.deepcopy(c)
    bad['target'] = '1'*(2*u+2)+'01'*7+'1'*(2*v+5)+'01'*(2*h+7)+'0'+c['metadata']['suffix']
    killed = not agrees(got, expected(bad))
    assert killed
    results.append(dict(name='even_period_two_instead_of_three', killed=killed, witness=c['metadata']))
    mutate('odd_remains_D', 'odd', 'qq', lambda c: 3)
    assert len(results) == 12
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cpp', type=Path, required=True, help='existing literal comparator')
    parser.add_argument('--no-save', action='store_true')
    args = parser.parse_args()
    queue = cases()
    ledger = None if args.no_save else HERE/'raw-budget.jsonl'
    spent = sum(json.loads(x)['executed_defined_transitions'] for x in ledger.read_text().splitlines()) if ledger and ledger.exists() else 0
    backend.set_budget(CPP_BUDGET-spent, ledger)
    raw_path = None if args.no_save else HERE/'raw.jsonl.gz'
    reqs = [request(c, i) for i, c in enumerate(queue)]
    actual, meta = backend.execute(args.cpp, reqs, raw_path)
    for c, req, got in zip(queue, reqs, actual):
        check(c, got, literal(req))
    controls = mutations(queue, actual)
    report = dict(passed=True, seed=SEED, cases=len(queue),
                  by_kind={k: sum(c['kind'] == k for c in queue) for k in ('even', 'odd', 'middle', 'outer22')},
                  full_traces=sum(c['steps'] <= 1000 for c in queue),
                  maximum_steps=max(c['steps'] for c in queue),
                  mutations=len(controls), mutation_controls=controls, raw=meta,
                  cases_sha256=hashlib.sha256(json.dumps(queue, sort_keys=True).encode()).hexdigest(),
                  source_sha256=hashlib.sha256((ROOT/'analysis/l17-hardening/raw_comparator.cpp').read_bytes()).hexdigest(),
                  scope='Bounded same-author cross-checks; the all-parameter proof is L17ab.lean.')
    if not args.no_save:
        (HERE/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('mutation_controls', 'raw')}, indent=2))


if __name__ == '__main__':
    main()
