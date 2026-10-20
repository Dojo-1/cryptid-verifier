"""Exact partial counter rules for L17, with an explicit unresolved frontier.

C(a,b) means state C, head at 0, word (01)^a 1^b immediately
to its right, and zeros everywhere else. Translation is recorded separately.
Sample checks are not universal proofs. See l17-reduction.md for the derivation.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import random
from tm import Config, parse

ROOT = Path(__file__).resolve().parent
MACHINE = '1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'
TABLE = parse(MACHINE)
PROBE_LIMIT = 200000


def make(a, b, q=2, head=0):
    if a < 0 or b < 0:
        raise ValueError('nonnegative counters required')
    word = '01'*a + '1'*b
    return Config({head+i:int(v) for i,v in enumerate(word) if v != '0'}, head, q)


def recognize(config):
    if config.q != 2 or (config.tape and min(config.tape) < config.head):
        return None
    end = max(config.tape, default=config.head-1)
    word = ''.join(str(config.tape.get(i,0)) for i in range(config.head, end+1))
    a = 0
    while word.startswith('01', 2*a):
        a += 1
    suffix = word[2*a:]
    if set(suffix) <= {'1'}:
        return a, len(suffix)
    return None


def partial_rule(a, b):
    """Return (a', b', steps, head shift, branch), or None at the frontier."""
    if a < 0 or b < 0:
        raise ValueError('nonnegative counters required')
    if b == 0:
        return 0, 2*a+4, 4*a+8, -2, 'empty_suffix'
    if a == 0:
        return 1, b, 2, -2, 'no_pairs'
    if b == 2:
        return a+4, 0, 6*a+21, -7, 'two_ones'
    if b >= 3:
        return a+5, b-3, 6*a+21, -7, 'countdown'
    return None  # a >= 1 and b == 1: no formula has been established.


def outer_rule(n):
    """Algebraic consequence of the partial rules, starting at C(0,n).

    This is a derived endpoint, not a newly simulated prefix. Its universal
    interpretation depends on the unformalized sweep derivation.
    """
    if n <= 0:
        raise ValueError('positive all-ones suffix required')
    k,r = divmod(n,3)
    if r == 0:
        return 0,10*k+6,15*k*k+32*k+14,-7*k-4,'return'
    if r == 2:
        return 0,10*k+14,15*k*k+62*k+57,-7*k-11,'return'
    return 5*k+1,1,15*k*k+12*k+2,-7*k-2,'frontier'


def derived_blank_frontier(max_outer=64):
    """Follow arithmetic endpoints to the first unsupported boundary.

    This analysis was added after the bounded experiment. No extra raw-TM
    horizon is run, and no measured prefix claim is attached to this result.
    """
    n,t,head = 2,2,0
    entries = [{'n':n,'derived_raw_time':t,'head':head}]
    for _ in range(max_outer):
        a,b,steps,shift,kind = outer_rule(n)
        t += steps;head += shift
        if kind == 'frontier':
            return {'status':'conditional arithmetic derivation; not raw simulation or Lean verification',
                    'entries':entries,'frontier':{'a':a,'b':b,'derived_raw_time':t,'head':head}}
        n = b
        entries.append({'n':n,'derived_raw_time':t,'head':head})
    return {'status':'conditional outer-iteration budget exhausted','entries':entries,'frontier':None}


def raw_probe(a, b, limit=PROBE_LIMIT):
    """First positive return to C(a,b), halt, or a fixed-budget timeout."""
    if limit < 0:
        raise ValueError('nonnegative probe limit required')
    config = make(a,b)
    for _ in range(limit):
        if not config.step(TABLE):
            return {'kind':'halt', 'steps':config.t, 'head_shift':config.head}
        result = recognize(config)
        if result is not None:
            return {'kind':'return', 'a':result[0], 'b':result[1],
                    'steps':config.t, 'head_shift':config.head}
    if TABLE[config.q][config.tape.get(config.head,0)] is None:
        return {'kind':'halt', 'steps':config.t, 'head_shift':config.head}
    return {'kind':'timeout','steps':limit,'state':chr(config.q+65),
            'head_shift':config.head,'nonzero_cells':len(config.tape)}


def check_rule(a, b):
    prediction = partial_rule(a,b)
    if prediction is None:
        raise ValueError('frontier has no rule')
    ap,bp,steps,shift,branch = prediction
    if steps > PROBE_LIMIT:
        raise ValueError('probe exceeds frozen budget')
    config = make(a,b)
    for _ in range(steps):
        if not config.step(TABLE):
            raise AssertionError(('unexpected halt',a,b,config.t))
    expected = make(ap,bp,head=shift)
    assert config.q == expected.q and config.head == expected.head and config.tape == expected.tape, (a,b)
    return branch


def blank_prefix(limit=PROBE_LIMIT):
    """Stop at an unsupported boundary or budget, whichever comes first."""
    config = Config()
    while recognize(config) is None:
        if config.t >= limit or not config.step(TABLE):
            raise AssertionError('blank entry not found within budget')
    entries = [{'a':recognize(config)[0], 'b':recognize(config)[1],
                'raw_time':config.t, 'head':config.head}]
    while True:
        a,b = recognize(config)
        rule = partial_rule(a,b)
        if rule is None:
            stop = 'unsupported_boundary'
            break
        if config.t + rule[2] > limit:
            stop = 'budget'
            break
        for _ in range(rule[2]):
            assert config.step(TABLE)
        assert recognize(config) == rule[:2]
        entries.append({'a':rule[0], 'b':rule[1], 'raw_time':config.t, 'head':config.head})
    return {'entries':entries, 'stop':stop, 'budget':limit,
            'next_rule_steps':rule[2] if rule is not None else None}


def main():
    counts = {}; checked = set()
    def check(a,b):
        if (a,b) in checked:
            return
        branch = check_rule(a,b)
        counts[branch] = counts.get(branch,0)+1
        checked.add((a,b))
    for a in range(65):
        for b in range(65):
            if partial_rule(a,b) is not None:
                check(a,b)
    rng = random.Random(20261020)
    for _ in range(256):
        a,b = rng.randrange(2049),rng.randrange(2049)
        if partial_rule(a,b) is not None:
            check(a,b)
    # Check every captured configuration already on this exact section, too.
    trace = next(json.loads(line) for line in (ROOT/'traces.jsonl').read_text().splitlines()
                 if json.loads(line)['id'] == 'L17')
    observed = []
    for snap in trace['snapshots']:
        if snap['q'] != 2 or snap['left']:
            continue
        config = Config({snap['head']+i:int(v) for i,v in enumerate(snap['right']) if v != '0'}, snap['head'], 2)
        ab = recognize(config)
        if ab is not None and partial_rule(*ab) is not None:
            check(*ab); observed.append({'a':ab[0], 'b':ab[1], 'raw_time':snap['t']})
    frontier = [{'a':a,'b':1,'result':raw_probe(a,1)} for a in range(1,65)]
    kinds = {kind:sum(r['result']['kind']==kind for r in frontier)
             for kind in ('return','halt','timeout')}
    cases = sorted(checked)
    output = {'machine':MACHINE,'section':'C(a,b) = 0^infty C> (01)^a 1^b 0^infty',
              'rule_status':'Derivation in l17-reduction.md plus finite raw checks; not Lean verified. Boundary b=1,a>=1 remains unsupported.',
              'probe_limit':PROBE_LIMIT,'checked_cases':len(cases),'branch_counts':counts,
              'checked_case_sha256':hashlib.sha256(json.dumps(cases,separators=(',',':')).encode()).hexdigest(),
              'observed_section_samples_checked':observed,'blank_prefix':blank_prefix(),
              'derived_blank_frontier':derived_blank_frontier(),
              'frontier_counts':kinds,'frontier':frontier,
              'new_certified_cryptids':0}
    (ROOT/'l17-probes.json').write_text(json.dumps(output,indent=2)+'\n')
    print('Rule checks',len(cases),counts,'frontier',kinds,flush=True)
    print('Blank prefix',output['blank_prefix'],flush=True)


if __name__ == '__main__':
    main()
