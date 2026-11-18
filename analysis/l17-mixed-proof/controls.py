"""Translated controls across three compiler modes under the registered cap."""
import json
import subprocess
from check_mixed import HERE, ROOT, CPP_BUDGET, cases, request, literal, check, backend


def main():
    queue = cases()
    selected = []
    for kind in ('original', 'A', 'C2', 'A01', 'A01101', 'BtoD', 'Dpair1', 'entry1101'):
        group = [c for c in queue if c['kind'] == kind]
        chosen = []
        for c in [group[0], max(group, key=lambda c: c['steps']), group[len(group)//2], *group]:
            if c not in chosen:
                chosen.append(c)
            if len(chosen) == 3:
                break
        selected.extend(chosen)
    assert len(selected) == 24
    ledger = HERE/'raw-budget.jsonl'
    spent = sum(json.loads(x)['executed_defined_transitions'] for x in ledger.read_text().splitlines())
    rejected = json.loads((HERE/'rejected-attempt.json').read_text())['conservative_transition_charge']
    backend.set_budget(CPP_BUDGET-spent-rejected, ledger)
    build = HERE/'build'
    build.mkdir(exist_ok=True)
    results = {}
    for name, flags in [('O2', ['-O2']), ('O0', ['-O0']),
                        ('UBSan', ['-O1', '-g', '-fsanitize=undefined', '-fno-sanitize-recover=all'])]:
        binary = build/('comparator-'+name)
        subprocess.run(['g++', '-std=c++17', *flags,
                        str(ROOT/'analysis/l17-hardening/raw_comparator.cpp'), '-o', str(binary)], check=True)
        offsets = [(-1 if i%2 else 1)*(i+71) for i in range(len(selected))]
        reqs = [request(c, i, off) for i, (c, off) in enumerate(zip(selected, offsets))]
        actual, meta = backend.execute(binary, reqs, HERE/('control-'+name+'.jsonl.gz'))
        for c, req, got, off in zip(selected, reqs, actual, offsets):
            check(c, got, literal(req), off)
        results[name] = meta
    report = dict(passed=True, translated_inputs_per_mode=len(selected), builds=results,
                  scope='Same-author compiler-mode and translation controls; not independent external replication.')
    (HERE/'controls.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
