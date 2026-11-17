"""Twenty-four planted faults, applied to in-memory expectations only."""
import copy
import gzip
import json
from paths import HERE
from specification import agrees


def expected(c):
    return dict(q=c['qq'], head=c['head'], steps=c['steps'], halted=False,
                ones=[c['target_start']+i for i, b in enumerate(c['target']) if b == '1'])


def main():
    cases = json.loads((HERE/'cases.json').read_text())
    with gzip.open(HERE/'raw-results.jsonl.gz', 'rt') as f:
        actual = [json.loads(x) for x in f]
    out = []
    def pick(label):
        return next((c, r) for c, r in zip(cases, actual) if c['label'] == label)
    def mutate(label, field, change, name):
        c, r = pick(label)
        bad = copy.deepcopy(c)
        bad[field] = change(c)
        killed = not agrees(r, expected(bad))
        out.append(dict(name=name, killed=killed, witness=c['metadata']))
        assert killed, name
    for n in (5, 6, 7):
        mutate(f'B_1100_n{n}', 'steps', lambda c: c['steps']-2, f'short_{n}_wrong_clock')
        mutate(f'kernel:B1100_n{n}', 'head', lambda c: c['head']+1, f'short_{n}_read_exit_cell')
    for label in ('B_1101', 'C2_1101', 'C5_1101'):
        mutate(label, 'qq', lambda c: 2, label+'_claim_C_return')
    mutate('B_zero', 'head', lambda c: c['head']+1, 'B0_one_cell_short')
    mutate('B_111', 'steps', lambda c: c['steps']+1, 'B111_charge_nine_steps')
    mutate('B_1100_large', 'target', lambda c: c['target'][:-1]+('0' if c['target'][-1] == '1' else '1'), 'corrupt_suffix_context')
    mutate('C2_zero', 'steps', lambda c: c['steps']-38, 'omit_C2_entry')
    mutate('C5_zero', 'steps', lambda c: c['steps']-62, 'omit_C5_entry')
    mutate('C2_1101', 'head', lambda c: c['head']-4, 'forget_B1101_shift')
    mutate('B_1100_n6', 'target', lambda c: c['target'].replace('0011', '011', 1), 'drop_short_6_internal_zero')
    mutate('B_1100_n5', 'target', lambda c: c['target'][:-1], 'shorten_short_5_output')
    mutate('kernel:C2B', 'qq', lambda c: 2, 'forget_C2_B_mode')
    mutate('kernel:C5B', 'steps', lambda c: 42, 'omit_C5_B_bounce')
    c, r = pick('kernel:B1100_n6')
    killed = r['read_min'] < c['bounds'][0]+1
    out.append(dict(name='shrink_short_6_left_window', killed=killed, witness=c['metadata']))
    assert killed
    mutate('B_110100_n5', 'qq', lambda c: 0, 'miss_normalized_00_return')
    mutate('B_110100_n6', 'target', lambda c: c['target'].replace('0011', '011', 1), 'drop_joined_00_internal_zero')
    mutate('B_110100_large', 'steps', lambda c: c['steps']-10, 'omit_A00L_clock')
    mutate('C2_110100_n5', 'steps', lambda c: c['steps']-14, 'omit_B1101_before_00_join')
    assert len(out) == 24
    result = dict(passed=True, planted=len(out), killed=sum(x['killed'] for x in out), checks=out,
                  scope='Manual ACAF fault controls, same author; no on-disk mutation or completeness claim.')
    (HERE/'mutation-results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
