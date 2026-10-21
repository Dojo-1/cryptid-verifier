import unittest,json,random,subprocess,sys
from gd_paths import HERE
from gd_critic import Claims,single,ranked_exit
from specification import equal_words,materialize,trim
from gd_actor import row,Word,join

class GeneralDTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.claims=Claims(HERE/'claims.json')
    def test_m2_retains_the_interior_zero(self):
        c=single(self.claims,'D12',dict(q=2,k=1,l=7,s=3),'')
        wrong=[('1',14),('01',14),('111',1)]
        self.assertFalse(equal_words(c['target'],wrong))
        self.assertEqual(ranked_exit(7,1,2)['exit'],'G')
    def test_m1_has_a_real_join_boundary(self):
        self.assertEqual(ranked_exit(7,5,1)['exit'],'J')
        c=single(self.claims,'D11join',dict(q=2,k=5,l=7,s=3),'')
        self.assertTrue(equal_words(c['target'],[('1',10),('01',7),('1',1),('01',14)]))
        self.assertFalse(equal_words(c['target'],[('1',10),('01',7),('1',1),('01',7),('111',1)]))
    def test_gap_rows_change_the_right_width(self):
        c=single(self.claims,'G1',dict(q=2,k=0,l=7,s=3),'')
        self.assertTrue(equal_words(c['target'],[('1',10),('01',7),('1',4),('01',6),('111',1)]))
    def test_identity_at_large_zero_middle(self):
        p=dict(N=2**1024+4,k=2**256+7,l=7,s=3)
        c=single(self.claims,'M0',p,'00101');ep=row('M0',p,Word.literal('00101'))
        self.assertTrue(equal_words(c['source'],ep.word().parts));self.assertTrue(equal_words(c['source'],c['target']))
    def test_join_guard_boundaries(self):
        for a,c,l in ((6,5,7),(7,4,7),(7,5,0)):
            with self.assertRaises(ValueError):join(a,c,l)
            with self.assertRaises(ValueError):self.claims.instantiate('JOIN',dict(a=a,c=c,l=l))
    def test_short_middle_not_allowed_in_old_row(self):
        for m in (0,1,2):
            with self.assertRaises(ValueError):self.claims.instantiate('D1',dict(q=2,k=7,m=m,l=7,s=3))
    def test_low_join_guard_stays_explicit(self):
        with self.assertRaises(ValueError):row('D11join',dict(q=1,k=5,l=7,s=3))
        out=ranked_exit(4,5,1);self.assertEqual(out['exit'],'J')
    def test_rank_decreases_until_a_named_exit(self):
        rng=random.Random(21012026)
        for i in range(2000):
            N=rng.randrange(2,10**8);k=rng.randrange(1,50);m=rng.randrange(0,70)
            out=ranked_exit(N,k,m);self.assertLessEqual(len(out['path']),out['bound'])
            for before,after in zip(out['path'],out['path'][1:]):
                self.assertEqual(3*before['k']+8*before['m']-3,3*after['k']+8*after['m'])
    def test_boolean_is_not_a_counter(self):
        with self.assertRaises(ValueError):self.claims.instantiate('JOIN',dict(a=7,c=5,l=True))
    def test_join_fragmented_context(self):
        v=[('01',2**128),('0',1),('1',17)];p=dict(a=2**256+7,c=5,l=2**128+7)
        c=single(self.claims,'JOIN',p,v);ep=row('JOIN',p,Word(tuple(v)))
        self.assertTrue(equal_words(c['target'],ep.word().parts));self.assertEqual(c['steps'],ep.steps)
    def test_return_family_includes_the_zero_middle_boundary(self):
        family=Claims(HERE/'return-family-claims.json')
        for c in (11,12,39,75):
            p=dict(t=2,c=c);case=single(family,'RET729',p,'001101');ep=row('RET729',p,Word.literal('001101'))
            self.assertTrue(equal_words(case['target'],ep.word().parts));self.assertEqual(case['steps'],ep.steps)
    def test_exterior_zero_and_interior_zero_are_distinct(self):
        self.assertTrue(equal_words([('101',1),('0',10)],[('101',1)]))
        self.assertFalse(equal_words([('10',1),('01',1)],[('101',1)]))
    def test_no_import_writes(self):
        code="import sys,pathlib,importlib;sys.path.insert(0,sys.argv[1]);pathlib.Path.write_text=lambda *a,**k: (_ for _ in ()).throw(AssertionError('import write'));importlib.import_module(sys.argv[2])"
        for name in ('make_spec','gd_actor','gd_critic','recover_boundary','continue','gd_validate','gd_verify_raw','gd_mutate'):
            out=subprocess.run([sys.executable,'-c',code,str(HERE),name],capture_output=True,text=True)
            self.assertEqual(out.returncode,0,out.stderr)
    def test_replay_imports_no_actor(self):
        code="import sys;sys.path.insert(0,sys.argv[1]);import verify_continuation;assert not any(n in sys.modules for n in ('actors','rules','words','fast','discover'))"
        subprocess.run([sys.executable,'-c',code,str(HERE)],check=True,capture_output=True)
    def test_scientific_source_binding(self):
        import hashlib
        d=json.loads((HERE/'validation.json').read_text())
        self.assertEqual(d['claims_sha256'],hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest())
if __name__=='__main__':unittest.main()
