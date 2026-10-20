import unittest
from validate import composed,excursion_checks,Word,Claims,HERE,equal_words


class ReturnTests(unittest.TestCase):
    def test_guard_boundary(self):
        a,w,t,h=composed(0,0,Word())
        self.assertEqual((a,t,h),(18,242,-18))
        self.assertTrue(equal_words(w.parts,[('1',1),('01',7),('1',3)]))

    def test_contextual_suffix(self):
        for suffix in ('1','001101','0'*12+'1'):
            a,w,t,h=composed(2,4,Word.literal(suffix))
            c=Claims(HERE/'claims.json').instantiate('RETURN',{'u':2,'d':4},suffix)
            self.assertTrue(equal_words([('01',a)]+list(w.parts),c['target']))
            self.assertEqual((t,h),(c['steps'],c['shift']))

    def test_invalid_guards(self):
        for u,d in ((-1,0),(0,-1),(True,0),(0,True)):
            with self.assertRaises(ValueError):composed(u,d,Word())

    def test_all_recorded_excursions(self):
        self.assertEqual([r['target_index'] for r in excursion_checks()],[226801,344268,366712])

    def test_independent_raw_record_verification(self):
        from verify import verify
        self.assertTrue(verify()['passed'])


if __name__=='__main__':unittest.main()
