"""Fresh full-tape replay for L17MixedBoundary; no simulation or file writes on import."""
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
sys.path[:0] = [str(ROOT/'analysis/l17-hardening'),
               str(ROOT/'analysis/l17-stacked-section')]
import backend
from reference import OPS

MACHINE = '1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'
SEED = 18112030
CPP_BUDGET = 2_000_000
TOKENS = '01'+'101'+'01'+'101'+'00'


def natural(*values):
    if any(type(n) is not int or n < 0 for n in values):
        raise ValueError('natural integer parameters required')


def binary(*values):
    if any(not isinstance(s, str) or set(s)-{'0', '1'} for s in values):
        raise ValueError('binary exterior tapes required')


def full_case(kind, u, v, suffix):
    natural(u, v)
    binary(suffix)
    p, c = u+4, v+1
    out = '1'*(2*u+2)+'01'*(v+13)+'11'+suffix
    if kind == 'original':
        source = '01'*(p+1)+'10'*c+'1101'+TOKENS+suffix
        start, target_start, head = 0, -2, -2
        steps, q, bounds = 4*u+6*v+178, 2, [-2, 2*(p+1)+2*c+15]
    elif kind == 'A':
        left = '10'*p+'0'+'10'*c+'0'+'10'*3
        source = left+TOKENS+suffix
        start = target_start = head = -len(left)
        steps, q, bounds = 2*u+4*v+138, 0, [start, 11]
    elif kind == 'C2':
        left = '10'*p+'0'+'10'*c+'0'+'10'*2+'0'+'10'*2
        source = left+'111111'+suffix
        start = target_start = head = -len(left)+1
        steps, q, bounds = 2*u+4*v+98, 2, [start, 6]
        out = '1'*(2*u+2)+'01'*(v+12)+'0'+suffix
    else:
        raise ValueError('known full return kind required')
    return dict(kind=kind, q=q, qq=2, source=source, target=out,
                start=start, target_start=target_start, head=head,
                steps=steps, bounds=bounds,
                metadata=dict(u=u, v=v, suffix=suffix))


def helper_case(kind, n, v, pad, suffix):
    natural(n, v)
    binary(pad, suffix)
    if kind == 'A01':
        word, out, lo, head, steps, q, qq = '01'*n, '10'*n, 0, 2*n, 2*n, 0, 0
        bounds = [0, 2*n-1] if n else [None, None]
    elif kind == 'BtoD':
        word, out = '01'*(n+1)+'111', '0'+'10'*(n+2)
        lo = head = -2*(n+1)
        steps, q, qq, bounds = 4*n+8, 1, 3, [lo, 2]
    elif kind == 'Dpair1':
        word = '0'+'10'*(v+1)+'0'+'10'+'0'+'10'*(n+1)
        out = '0'+'10'*(v+n+4)
        lo = head = -2*(v+1)-4
        steps, q, qq, bounds = 4*v+14, 3, 3, [lo, 2*(n+1)]
        # The separator preceding the v+1 run belongs to arbitrary left context.
        # Keep it explicit for the head target, without reading that exterior cell.
        bounds[0] = lo+1
    elif kind == 'A01101':
        word = '0'+'10'*(n+2)+'01101'
        out = '0'+'10'*(n+1)+'0'+'10'*3
        lo, head, steps, q, qq = -2*(n+2)-1, 5, 15, 0, 0
        bounds = [-4, 4]
    elif kind == 'scanner':
        word = '0'+'10'*3+TOKENS
        out = '0'+'10'*2+'0'+'10'*2+'1'*9
        lo, head, steps, q, qq, bounds = -7, 2, 40, 0, 2, [-7, 11]
    elif kind == 'entry1101':
        # Canonical blank-left source; pad is a harmless zero exterior only.
        if set(pad)-{'0'}:
            raise ValueError('1101 entry requires blank left tape')
        p, c = n+4, v+1
        word = '01'*(p+1)+'10'*c+'1101'
        out = '10'*p+'0'+'10'*c+'0'+'10'*3
        lo, head, steps, q, qq = 0, 2*(p+1)+2*c+4, 2*n+2*v+40, 2, 0
        bounds = [-2, head-1]
        return dict(kind=kind, q=q, qq=qq, source=pad+word+suffix,
                    target=pad+out+suffix, start=lo-len(pad),
                    target_start=-2-len(pad), head=head, steps=steps,
                    bounds=bounds, metadata=dict(n=n, v=v, pad=pad, suffix=suffix))
    else:
        raise ValueError('known helper kind required')
    return dict(kind=kind, q=q, qq=qq, source=pad+word+suffix,
                target=pad+out+suffix, start=lo-len(pad),
                target_start=lo-len(pad), head=head, steps=steps,
                bounds=bounds, metadata=dict(n=n, v=v, pad=pad, suffix=suffix))


def cases():
    rng = random.Random(SEED)
    queue = []
    for kind in ('original', 'A', 'C2'):
        for u, v, suffix in itertools.product(range(6), range(8), ('', '1', '001101')):
            queue.append(full_case(kind, u, v, suffix))
        for _ in range(32):
            queue.append(full_case(kind, rng.randrange(128), rng.randrange(128),
                                   ''.join(rng.choice('01') for _ in range(31))))
    for kind in ('A01', 'BtoD', 'Dpair1', 'A01101', 'scanner', 'entry1101'):
        for i in range(72):
            n, v = (i%8, i//8) if i < 64 else (rng.randrange(128), rng.randrange(128))
            pad = ''.join(rng.choice('01') for _ in range(17))
            if kind == 'entry1101':
                pad = '0'*17
            suffix = ''.join(rng.choice('01') for _ in range(17))
            queue.append(helper_case(kind, n, v, pad, suffix))
    assert len(queue) == 960 and max(c['steps'] for c in queue) <= 10000
    return queue


def request(c, i, offset=0):
    return dict(id=i, machine=MACHINE, q=c['q'], head=offset, limit=c['steps'],
                trace=c['steps'] <= 1000,
                ones=[c['start']+j+offset for j, b in enumerate(c['source']) if b == '1'])


def expected(c, offset=0):
    return dict(q=c['qq'], head=c['head']+offset, steps=c['steps'], halted=False,
                ones=[c['target_start']+j+offset for j, b in enumerate(c['target']) if b == '1'])


def agrees(got, want):
    return all(got[k] == want[k] for k in ('q', 'head', 'steps', 'halted', 'ones'))


def literal(req):
    q, head, done = req['q'], req['head'], 0
    ones, reads = set(req['ones']), []
    while done < req['limit']:
        b = int(head in ones)
        op = OPS[q][b]
        if op is None:
            break
        reads.append([q, head, b])
        value, move, q = op
        if value:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        done += 1
    return dict(q=q, head=head, steps=done, halted=OPS[q][int(head in ones)] is None,
                ones=sorted(ones), reads=reads,
                read_min=min((r[1] for r in reads), default=None),
                read_max=max((r[1] for r in reads), default=None))


def check(c, got, py, offset=0):
    assert agrees(got, expected(c, offset)), (c, got, expected(c, offset))
    assert agrees(py, expected(c, offset)), (c, py, expected(c, offset))
    if c['steps'] <= 1000:
        assert got['reads'] == py['reads']
    assert (got['read_min'], got['read_max']) == (py['read_min'], py['read_max'])
    if c['steps']:
        assert c['bounds'][0]+offset <= got['read_min'] <= got['read_max'] <= c['bounds'][1]+offset
    else:
        assert got['read_min'] is None and got['read_max'] is None


def mutations(queue, actual):
    results = []
    def plant(name, kind, field, transform):
        c, got = next((c, r) for c, r in zip(queue, actual) if c['kind'] == kind)
        bad = copy.deepcopy(c)
        bad[field] = transform(c)
        caught = not agrees(got, expected(bad))
        assert caught, name
        results.append(dict(name=name, caught=caught, witness=c['metadata']))
    for kind in ('original', 'A', 'C2'):
        plant(kind+'_clock_off_two', kind, 'steps', lambda c: c['steps']+2)
        plant(kind+'_head_off_pair', kind, 'head', lambda c: c['head']+2)
    plant('C2_left_zero_trim', 'C2', 'target', lambda c: c['target'].replace('0', '', 1))
    plant('A_scanner_skips_01', 'A', 'target', lambda c: c['target'][:-2])
    plant('B_wrong_exit_mode', 'BtoD', 'qq', lambda c: 2)
    plant('D_wrong_exit_mode', 'Dpair1', 'qq', lambda c: 2)
    plant('entry_wrong_clock', 'entry1101', 'steps', lambda c: c['steps']-2)
    plant('A01101_missing_gap', 'A01101', 'target', lambda c: c['target'].replace('0', '', 1))
    assert len(results) == 12
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cpp', required=True, type=Path)
    parser.add_argument('--no-save', action='store_true')
    args = parser.parse_args()
    queue = cases()
    ledger = None if args.no_save else HERE/'raw-budget.jsonl'
    spent = sum(json.loads(x)['executed_defined_transitions'] for x in ledger.read_text().splitlines()) if ledger and ledger.exists() else 0
    rejected = json.loads((HERE/'rejected-attempt.json').read_text())['conservative_transition_charge']
    backend.set_budget(CPP_BUDGET-spent-rejected, ledger)
    reqs = [request(c, i) for i, c in enumerate(queue)]
    actual, meta = backend.execute(args.cpp, reqs, None if args.no_save else HERE/'raw.jsonl.gz')
    for c, req, got in zip(queue, reqs, actual):
        check(c, got, literal(req))
    controls = mutations(queue, actual)
    report = dict(passed=True, seed=SEED, cases=len(queue),
                  full_traces=sum(c['steps'] <= 1000 for c in queue),
                  by_kind={k: sum(c['kind'] == k for c in queue) for k in sorted({c['kind'] for c in queue})},
                  maximum_steps=max(c['steps'] for c in queue), mutations=controls,
                  raw=meta, cases_sha256=hashlib.sha256(json.dumps(queue, sort_keys=True).encode()).hexdigest(),
                  scope='Bounded same-author checks; quantified validity is established by L17MixedBoundary.lean.')
    if not args.no_save:
        (HERE/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('raw', 'mutations')}, indent=2))


if __name__ == '__main__':
    main()
