from __future__ import annotations
import json,unittest
from extend import HERE,Word,shape,rewrite,claim_for
from nesting import U,T,nest
from discover import extended_state_edge,critical_check
from specification import Claims,equal_words
import rules


class StackTests(unittest.TestCase):
    def test_zero_depth_agrees_with_original_base(self):
        for a in (7,8,127):
            got=nest(a,0,Word.literal('001101'));old=rules.core100(a,0,Word.literal('001101'))
            self.assertTrue(equal_words(got['word'].parts,old.word().parts))
            self.assertEqual((got['steps'],got['shift']),(old.steps,old.shift))

    def test_single_push_agrees_with_F1100(self):
        for a in (7,8,127):
            got=nest(a,1);old=rules.core1100(a,8)
            self.assertTrue(equal_words(got['word'].parts,old.word().parts))
            self.assertEqual((got['steps'],got['shift']),(old.steps,old.shift))

    def test_guards_include_types(self):
        for a,n in ((6,0),(7,-1),(True,0),(7,True),(7.0,0),(7,0.0)):
            with self.assertRaises(ValueError):nest(a,n)

    def test_source_patterns_have_seventeen_cells(self):
        self.assertEqual(len(U),17);self.assertEqual(len(T),17)
        self.assertNotEqual(U,T)

    def test_shape_uses_bits_not_chunks(self):
        self.assertEqual(shape(Word((('1',1),('01',75),('0',1),('1',2))))['layers'],[[76,1]])
        self.assertEqual(shape(Word.literal('11'+T*3))['depth'],3)

    def test_gap_is_not_called_a_pure_tail(self):
        self.assertEqual(shape(Word((('1',2),('01',6),('0',1),('01',7),('1',3))))['kind'],'gap')

    def test_all_six_short_full_time_critic_branches(self):
        claims=Claims(HERE.parent/'l17-hardening'/'claims.json')
        for c in range(1,9):
            a=11;w=Word((('10',c),('1100',1),('001101',1)))
            out=rewrite(a,w);self.assertFalse(isinstance(out,dict))
            claim=claim_for(a,w,out,claims)
            self.assertTrue(equal_words(out.word().parts,claim['target']))
            self.assertEqual((out.steps,out.shift),(claim['steps'],claim['shift']))

    def test_linear_short_and_general_critic_branches(self):
        claims=Claims(HERE.parent/'l17-hardening'/'claims.json')
        for c in range(1,9):
            a=11;w=Word((('10',c),('1100',1),('001101',1)))
            critical_check(a,w,extended_state_edge(a,w),claims)

    def test_low_guard_stays_explicit(self):
        w=Word((('10',8),('1100',1)))
        self.assertIsInstance(rewrite(6,w),dict)
        self.assertIsNone(extended_state_edge(6,w))

    def test_raw_results_replay_from_specification(self):
        from verify_results import verify
        self.assertTrue(verify()['passed'])

    def test_case_ids_fit_literal_protocol(self):
        rows=json.loads((HERE/'nesting-cases.json').read_text())
        self.assertTrue(all(type(x['id']) is int and x['id']>=0 for x in rows))
        self.assertEqual(len({x['id'] for x in rows}),len(rows))

    def test_first_blank_push_has_checked_collapse(self):
        from verify_symbolic import verify_source_bindings
        self.assertTrue(verify_source_bindings())
        data=json.loads((HERE/'replay-compact.json').read_text());events=data['events']
        self.assertTrue(data['confirmed_state_only_discovery'])
        self.assertEqual(data['rule_counts']['core1100'],1)
        changes=[(int(x['index'],16),int(x['shape']['depth'],16)) for x in events if 'shape' in x]
        self.assertEqual(changes,[(226798,2),(226801,1)])


if __name__=='__main__':unittest.main()
