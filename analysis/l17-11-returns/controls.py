"""Matched translated controls in three compiler modes, under the same cap."""
import json
import subprocess
from check_returns import HERE, ROOT, CPP_BUDGET, cases, request, literal, check, backend


def main():
    queue = cases()
    selected = []
    for kind in ('even', 'odd', 'middle', 'outer22'):
        group = [c for c in queue if c['kind'] == kind]
        candidates = [group[0], group[-1], max(group, key=lambda c: c['steps']), group[len(group)//2], *group]
        chosen = []
        for c in candidates:
            if c not in chosen:
                chosen.append(c)
            if len(chosen) == 4:
                break
        selected.extend(chosen)
    ledger = HERE/'raw-budget.jsonl'
    spent = sum(json.loads(x)['executed_defined_transitions'] for x in ledger.read_text().splitlines())
    backend.set_budget(CPP_BUDGET-spent, ledger)
    build = HERE/'build'
    build.mkdir(exist_ok=True)
    results = {}
    for name, flags in [('O2', ['-O2']), ('O0', ['-O0']), ('UBSan', ['-O1', '-g', '-fsanitize=undefined', '-fno-sanitize-recover=all'])]:
        binary = build/('comparator-'+name)
        subprocess.run(['g++', '-std=c++17', *flags,
                        str(ROOT/'analysis/l17-hardening/raw_comparator.cpp'), '-o', str(binary)], check=True)
        offsets = [(-1 if i % 2 else 1)*(i+37) for i in range(len(selected))]
        reqs = [request(c, i, offset) for i, (c, offset) in enumerate(zip(selected, offsets))]
        got, meta = backend.execute(binary, reqs, HERE/('control-'+name+'.jsonl.gz'))
        for c, req, r, offset in zip(selected, reqs, got, offsets):
            check(c, r, literal(req), offset)
        results[name] = meta
    report = dict(passed=True, translated_inputs_per_mode=len(selected), builds=results,
                  scope='Same compiler and authorship; modes and translations are controls, not external replication.')
    (HERE/'controls.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
