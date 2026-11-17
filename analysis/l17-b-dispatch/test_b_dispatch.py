import itertools
import json
import unittest
from paths import HERE
from claims import RULES, KERNELS, classify
from specification import Claims, integer, materialize, agrees
from raw import replay


class BDispatchTests(unittest.TestCase):
    def test_prefix_partition_exhaustive_finite_words(self):
        for n in range(12):
            for bits in itertools.product('01', repeat=n):
                word = ''.join(bits)
                d = classify(word)
                self.assertIn(d['terminal'], ('0', '111', '1100', '1101'))
                consumed = '10'*d['j']+d['terminal']
                self.assertEqual((word+'0'*4)[:len(consumed)], consumed)
                self.assertEqual(d['suffix'], word[d['consumed']:])
                for j in range(d['j']):
                    self.assertEqual((word+'00')[2*j:2*j+2], '10')

    def test_guard_corners_against_literal_machine(self):
        for name, row in RULES.items():
            p = {k: v[0] for k, v in row['guards'].items()}
            v = '001101'
            src = ''.join(w*n for w, n in materialize(row['source'], p, v))
            dst = ''.join(w*n for w, n in materialize(row['target'], p, v))
            start = integer(row['source_start'], p)
            got = replay(dict(q=row['source_q'], head=0, limit=integer(row['steps'], p),
                              ones=[start+i for i, b in enumerate(src) if b == '1']))
            expected = dict(q=row['target_q'], head=integer(row['shift'], p),
                            steps=integer(row['steps'], p), halted=False,
                            ones=[start+i for i, b in enumerate(dst) if b == '1'])
            self.assertTrue(agrees(got, expected), name)

    def test_saved_boundary_returns_in_108_steps(self):
        old = json.loads((HERE.parent/'l17-mixed-return/next-boundary.json').read_text())['source']
        self.assertEqual(old, dict(p=6, c=7, s=2, r=2, m=3, v='001101'))
        src = '10'*6+'0'+'10'*7+'0'+'10'*2+'0'+'10'*2+'111'+'001101'
        got = replay(dict(q=2, head=0, limit=108, ones=[-36+i for i, b in enumerate(src) if b == '1']))
        target = '11'+'01'*7+'1'*11+'010'+'1'*11+'01101'
        self.assertTrue(agrees(got, dict(q=2, head=-36, steps=108, halted=False,
                                      ones=[-36+i for i, b in enumerate(target) if b == '1'])))
        self.assertEqual(got['read_max'], 4)

    def test_1101_is_an_A_exit_not_a_section_return(self):
        row = RULES['C2_1101']
        p = dict(p=6, c=7, j=0)
        self.assertEqual((row['target_q'], integer(row['steps'], p), integer(row['shift'], p)), (0, 52, 8))
        self.assertEqual(integer(row['read_bounds'][1], p), 7)

    def test_short_1100_partition_and_join_to_large_rule(self):
        for n in range(5, 50):
            short = [k for k in (5, 6, 7) if k == n]
            self.assertEqual(len(short)+int(n >= 8), 1)
        self.assertEqual(RULES['B_1100_large']['guards']['n'][0], 8)

    def test_guards_reject_unsupported_sources(self):
        claims = Claims(HERE/'claims.json')
        for p in [dict(p=5, c=7, n=5), dict(p=6, c=6, n=5), dict(p=6, c=7, n=4)]:
            with self.assertRaises(ValueError):
                claims.instantiate('B_zero', p, '001101')
        with self.assertRaises(ValueError):
            claims.instantiate('B_1100_large', dict(p=6, c=7, n=7), '')

    def test_huge_exact_parameters_without_tape_expansion(self):
        for row in RULES.values():
            p = {k: 10**100+v[0] for k, v in row['guards'].items()}
            src = materialize(row['source'], p, '001101')
            dst = materialize(row['target'], p, '001101')
            self.assertEqual(sum(len(w)*n for w, n in src), sum(len(w)*n for w, n in dst))
            self.assertGreater(integer(row['steps'], p), 0)

    def test_local_kernel_contexts_are_not_read(self):
        for name, (q, t, qq, h, lo, src, dst) in KERNELS.items():
            for outside in ('0', '1'):
                word = outside+src+outside
                got = replay(dict(q=q, head=0, limit=t, ones=[lo-1+i for i, b in enumerate(word) if b == '1']))
                expected = outside+dst+outside
                self.assertTrue(agrees(got, dict(q=qq, head=h, steps=t, halted=False,
                                               ones=[lo-1+i for i, b in enumerate(expected) if b == '1'])), name)
                self.assertGreaterEqual(got['read_min'], lo)
                self.assertLessEqual(got['read_max'], lo+len(src)-1)

    def test_short_kernel_exit_cell_is_unread(self):
        for n in (5, 6, 7):
            row = KERNELS['B1100_n'+str(n)]
            self.assertEqual(row[3], row[4]-1)

    def test_fixed_1101_kernel_exits_at_context(self):
        row = KERNELS['B1101']
        self.assertEqual(row[3], row[4]+len(row[5]))

    def test_undefined_transition_has_zero_cost(self):
        got = replay(dict(q=5, head=0, limit=100, ones=[0]))
        self.assertTrue(got['halted'])
        self.assertEqual(got['steps'], 0)

    def test_confirmatory_budget_includes_failed_attempt(self):
        rows = [json.loads(x) for x in (HERE/'raw-budget.jsonl').read_text().splitlines()]
        self.assertTrue(any(r.get('charge_type') == 'conservative_upper_bound_failed_attempt' for r in rows))
        self.assertLessEqual(sum(r['executed_defined_transitions'] for r in rows), 20000000)

    def test_critic_replays_saved_results(self):
        from verify import verify
        self.assertEqual(verify()['endpoints'], 924)

    def test_mixed_gap_is_a_five_run_stack(self):
        for n in range(2, 40):
            left = '10'*6+'0'+'10'*7+'0'+'10'+'01'*(n-2)+'00'+'10'*3
            runs = '0'.join('10'*x for x in (6, 7, 1, n-2, 3))
            self.assertEqual(left, runs)

    def test_former_A_checkpoint_has_a_166_step_return(self):
        src = '10'*6+'0'+'10'*7+'0'+'10'*2+'0'+'10'*2+'111'+'1101001101'
        got = replay(dict(q=2, head=0, limit=166, ones=[-36+i for i, b in enumerate(src) if b == '1']))
        target = '11'+'01'*7+'1'*5+'01'*9+'0'+'1'*6+'1101'
        self.assertTrue(agrees(got, dict(q=2, head=-36, steps=166, halted=False,
                                      ones=[-36+i for i, b in enumerate(target) if b == '1'])))
        self.assertEqual(got['read_max'], 9)

    def test_reject_nonbinary_dispatch_input(self):
        for word in ('102', None, 1):
            with self.assertRaises(ValueError):
                classify(word)


if __name__ == '__main__':
    unittest.main()
