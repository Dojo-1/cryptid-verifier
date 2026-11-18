"""Guard, representation, framing and fault-control regression tests."""
import hashlib
import json
from pathlib import Path
import unittest
import check_mixed as m


class MixedProofTests(unittest.TestCase):
    def test_registered_campaign(self):
        q = m.cases()
        self.assertEqual(len(q), 960)
        report = json.loads((m.HERE/'report.json').read_text())
        digest = hashlib.sha256(json.dumps(q, sort_keys=True).encode()).hexdigest()
        self.assertEqual(digest, report['cases_sha256'])
        self.assertEqual(sum(c['steps'] <= 1000 for c in q), 950)

    def test_lower_guard_corner(self):
        for kind, steps in [('original', 178), ('A', 138), ('C2', 98)]:
            c = m.full_case(kind, 0, 0, '001101')
            self.assertEqual(c['steps'], steps)
            self.assertTrue(m.agrees(m.literal(m.request(c, 0)), m.expected(c)))

    def test_historical_222_step_boundary(self):
        c = m.full_case('original', 2, 6, '001101')
        self.assertEqual(c['steps'], 222)
        self.assertEqual(c['head'], -2)
        self.assertEqual(c['target'], '1'*6+'01'*19+'11'+'001101')
        self.assertTrue(m.agrees(m.literal(m.request(c, 0)), m.expected(c)))

    def test_negative_and_non_integer_parameters(self):
        for bad in (-1, True, 1.0, '1'):
            with self.assertRaises(ValueError):
                m.full_case('original', bad, 0, '')
            with self.assertRaises(ValueError):
                m.helper_case('Dpair1', 0, bad, '', '')

    def test_binary_contexts(self):
        for bad in ('012', 1, None):
            with self.assertRaises(ValueError):
                m.full_case('C2', 0, 0, bad)
            with self.assertRaises(ValueError):
                m.helper_case('A01101', 0, 0, bad, '')

    def test_unknown_kinds(self):
        with self.assertRaises(ValueError):
            m.full_case('homogeneous', 0, 0, '')
        with self.assertRaises(ValueError):
            m.helper_case('C3', 0, 0, '', '')

    def test_blank_left_entry_guard(self):
        with self.assertRaises(ValueError):
            m.helper_case('entry1101', 0, 0, '1', '')

    def test_zero_sweep(self):
        c = m.helper_case('A01', 0, 0, '101', '001101')
        got = m.literal(m.request(c, 0))
        self.assertEqual(got['steps'], 0)
        self.assertEqual(got['reads'], [])
        self.assertTrue(m.agrees(got, m.expected(c)))

    def test_Dpair_source_origin(self):
        c = m.helper_case('Dpair1', 0, 0, '101', '001101')
        self.assertEqual(c['head'], -6)
        got = m.literal(m.request(c, 0))
        self.assertTrue(m.agrees(got, m.expected(c)))
        bad = dict(c, start=c['start']-1)
        self.assertFalse(m.agrees(m.literal(m.request(bad, 0)), m.expected(bad)))

    def test_right_context_never_read(self):
        for kind in ('original', 'A', 'C2'):
            a = m.full_case(kind, 0, 0, '0'*37)
            b = m.full_case(kind, 0, 0, '1'*37)
            ra, rb = (m.literal(m.request(c, 0)) for c in (a, b))
            self.assertEqual(ra['reads'], rb['reads'])
            for c, r in ((a, ra), (b, rb)):
                self.assertTrue(m.agrees(r, m.expected(c)))

    def test_translated_complete_endpoint(self):
        c = m.full_case('original', 1, 2, '001101')
        for offset in (-73, 109):
            got = m.literal(m.request(c, 0, offset))
            self.assertTrue(m.agrees(got, m.expected(c, offset)))

    def test_mutation_controls(self):
        q = m.cases()
        controls = m.mutations(q, [m.literal(m.request(c, 0)) for c in q])
        self.assertEqual(len(controls), 12)
        self.assertTrue(all(c['caught'] for c in controls))


if __name__ == '__main__':
    unittest.main()
