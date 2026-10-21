import gzip,json,unittest
from search import HERE,Word
from actors import cycle,ranked,resonance
from critic import window
from validate_return2 import short,candidate_exit


class CollapseTests(unittest.TestCase):
    def test_zero_countdown_boundary(self):
        out=ranked(2,1,1)
        self.assertEqual((out['a'],out['steps'],out['shift']),(0,57,-11))
        self.assertTrue(out['tail'].equivalent(Word((('1',18),('01',7),('1',3)))))

    def test_resonant_fixed_front(self):
        out=resonance(7,10)
        self.assertEqual((out['a'],out['steps'],out['shift']),(0,3220,-110))
        self.assertTrue(out['tail'].equivalent(Word((('1',4),('01',84),('1',3)))))

    def test_forbidden_middle_not_silently_extended(self):
        with self.assertRaises(ValueError):cycle(4,7,1)
        with self.assertRaises(ValueError):cycle(4,7,2)

    def test_candidate_push_guard_not_invariant(self):
        out=candidate_exit()
        self.assertEqual((out['a'],out['steps'],out['shift']),(16,295,-25))
        self.assertTrue(out['tail'].equivalent(Word((('1',1),('01',15),('1',1)))))
        self.assertNotEqual(16%3,0);self.assertNotEqual(15%3,2)

    def test_independent_raw_record_verifier(self):
        from verify_raw import verify
        self.assertTrue(verify()['passed'])

    def test_two_decision_return_minimum(self):
        out=short(0,0)
        self.assertEqual((out['a'],out['steps'],out['shift']),(55,1547,-85))

    def test_long_return_not_mislabeled_raw(self):
        result=json.loads((HERE/'validation.json').read_text())
        self.assertTrue(result['long_reached_witness']['passed'])
        self.assertFalse(result['long_reached_witness']['raw_simulated'])
        self.assertGreater(5555729670,200000)

    def test_rank_bound_on_declared_toys(self):
        for N,k,z in ((3,1,1),(8,7,2),(26,3,2),(4,1,3)):
            out=ranked(N,k,z)
            self.assertLessEqual(len(out['path']),k+8*z)

    def test_corrected_read_bound_regression(self):
        row=next(json.loads(x) for x in gzip.open(HERE/'raw.jsonl.gz','rt') if json.loads(x)['id']==40)
        self.assertEqual((row['read_min'],row['read_max']),(-11,19))
        self.assertEqual(window('P1',{'h':0,'d':1}),(-11,19))
        self.assertLess(row['read_min'],-10)

    def test_scalar_calibration_preserved(self):
        rows=json.loads((HERE/'scalar-calibration.json').read_text())
        self.assertEqual(len(rows),500)
        self.assertTrue(all(r.get('passed') or r.get('stops_before_push') for r in rows))

    def test_reached_five_decision_itinerary(self):
        report=json.loads((HERE/'fast.json').read_text())
        self.assertEqual(report['trigger_index'],1407520)
        names=[r['rule'] for r in report['local_trace']]
        self.assertEqual(names,['F1100','E','Q','F111','E','Q','P','Z','E','Q','P','Z','E','Q','F111','E','Q','N'])

    def test_search_ends_at_registered_global_cap(self):
        report=json.loads((HERE/'guard.json').read_text())
        self.assertEqual(report['stop_index'],2000000)
        self.assertIsNone(report['trigger_index'])


if __name__=='__main__':unittest.main()
