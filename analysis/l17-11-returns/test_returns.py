import unittest
from check_returns import cases, expected, request, literal, agrees, helper_case, full_case


class ReturnTests(unittest.TestCase):
    def test_every_guarded_endpoint_and_read_window(self):
        for i, c in enumerate(cases()):
            got = literal(request(c, i))
            self.assertTrue(agrees(got, expected(c)), (c['kind'], c['metadata']))
            self.assertLessEqual(c['bounds'][0], got['read_min'])
            self.assertLessEqual(got['read_max'], c['bounds'][1])

    def test_zero_repetition_clock_and_full_word(self):
        c = full_case(0, 0, 0, 0, '001101')
        self.assertEqual((c['steps'], c['head']), (86, -34))
        self.assertEqual(c['target'], '11'+'01'*7+'1'*5+'01'*7+'0001101')

    def test_one_repetition_clock_and_full_word(self):
        c = full_case(1, 0, 0, 0, '001101')
        self.assertEqual((c['steps'], c['head']), (92, -34))
        self.assertEqual(c['target'], '1'*6+'01'*16+'0001101')

    def test_middle_zero_pairs_still_consumes_separator(self):
        c = helper_case('middle', 0, '101', '001101')
        self.assertEqual((c['steps'], c['head']), (2, -2))
        got = literal(request(c, 0))
        self.assertEqual(got['read_min'], -1)

    def test_outer_zero_sweep_still_runs_k22(self):
        c = helper_case('outer22', 0, '101', '001101')
        self.assertEqual((c['steps'], c['head']), (22, -8))

    def test_absolute_translation(self):
        for kind in ('middle', 'outer22'):
            c = helper_case(kind, 8, '1101011', '001101')
            for offset in (-1000, -1, 37, 1000):
                self.assertTrue(agrees(literal(request(c, 0, offset)), expected(c, offset)))

    def test_context_only_begins_after_terminal(self):
        for parity in (0, 1):
            c = full_case(parity, 1, 2, 7, '1111111111')
            got = literal(request(c, 0))
            self.assertEqual(got['read_max'], 3*(14+parity)+1)

    def test_undefined_transition_counts_zero(self):
        got = literal(dict(q=5, head=0, ones=[0], limit=100, trace=True))
        self.assertEqual((got['steps'], got['halted']), (0, True))

    def test_old_D10_D6_order_has_wrong_phase(self):
        c = full_case(0, 0, 0, 1, '')
        req = request(c, 0)
        req['limit'] = 37
        corrected = literal(req)
        self.assertEqual((corrected['q'], corrected['head']), (3, 1))
        # The correction note presents this window head-nearest-first.
        word = lambda r: ''.join(str(int(x in r['ones'])) for x in range(r['head'], r['head']-6, -1))
        self.assertEqual(word(corrected), '010010')
        req['limit'] = 41
        wrong_phase = literal(req)
        self.assertEqual((wrong_phase['q'], wrong_phase['head']), (3, -1))
        self.assertEqual(word(wrong_phase), '001001')
        self.assertNotEqual(word(wrong_phase), '010010')

    def test_return_encoder_rejects_inputs_outside_theorem_domain(self):
        for p in (-1, 2, True):
            with self.assertRaises(ValueError):
                full_case(p, 0, 0, 0, '')
        for n in (-1, 1.5, True):
            with self.assertRaises(ValueError):
                full_case(0, n, 0, 0, '')
        with self.assertRaises(ValueError):
            full_case(0, 0, 0, 0, '102')

    def test_helper_encoder_rejects_unknown_mode_or_bad_sweep(self):
        for kind, n in [('typo', 1), ('middle', -1), ('outer22', True)]:
            with self.assertRaises(ValueError):
                helper_case(kind, n, '', '')
        with self.assertRaises(ValueError):
            helper_case('middle', 0, 'x', '')


if __name__ == '__main__':
    unittest.main()
