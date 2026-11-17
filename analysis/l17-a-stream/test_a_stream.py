import itertools,json,random,unittest
from paths import HERE
from scanner import decode,compile_stack,left_word,mixed_obstruction
from verify import literal_left
from specification import integer,materialize
from claims import RULES
from raw import replay

class StreamTests(unittest.TestCase):
    def test_decoder_exhaustive_finite_words(self):
        for n in range(10):
            for bits in itertools.product('01',repeat=n):
                word=''.join(bits);tokens,terminal,pos=decode(word)
                self.assertEqual(''.join(tokens),(word+'000')[:pos]);self.assertIn(terminal,('00','100','11'))
                self.assertEqual(terminal,(word+'000')[pos:pos+len(terminal)])
    def test_zero_and_exact_budget(self):
        self.assertEqual(decode('00',0),([], '00',0))
        tokens=['101']*96;self.assertEqual(decode(''.join(tokens)+'00')[0],tokens)
        with self.assertRaises(ValueError):decode('101'*97+'00')
    def test_mixed_actor_against_literal_rewriting(self):
        rng=random.Random(17112026)
        for _ in range(100):
            runs=[rng.randrange(10),rng.randrange(1,10),rng.randrange(3,10)];tokens=[rng.choice(('01','101')) for _ in range(rng.randrange(97))]
            stack,t,d=compile_stack(runs,tokens);literal,tt,dd=literal_left(runs,tokens)
            self.assertEqual((left_word(stack),t,d),(literal,tt,dd))
    def test_token_order_matters(self):
        self.assertNotEqual(compile_stack([6,7,3],['01','101'])[0],compile_stack([6,7,3],['101','01'])[0])
    def test_uniform_stack_normal_form(self):
        for j in range(30):
            stack,t,d=compile_stack([6,7,3],['101']*j)
            self.assertEqual(stack,[6,7]+[1]*j+[3] if j else [6,7,3]);self.assertEqual((t,d),(13*j,3*j))
    def test_general_stack_normal_form(self):
        z=[2,0,4,3];tokens=[]
        for i,n in enumerate(z):
            tokens+=['01']*n
            if i<len(z)-1:tokens.append('101')
        self.assertEqual(compile_stack([6,7,3],tokens)[0],[6,7,3,1,5,6])
    def test_width2_boundary_stays_explicit(self):
        initial,tokens,(stack,t,d)=mixed_obstruction();self.assertEqual(stack,[6,7,2,2,3]);self.assertEqual((t,d),(30,10))
        self.assertEqual(json.loads((HERE/'mixed-boundary.json').read_text())['C_window'],'001010')
    def test_symbolic_times_and_suffix_positions_at_huge_parameters(self):
        for name,row in RULES.items():
            p={k:max(v[0],10**80+7) for k,v in row['guards'].items()};v='001101'
            source=materialize(row['source'],p,v);target=materialize(row['target'],p,v)
            self.assertEqual(sum(len(w)*n for w,n in source),sum(len(w)*n for w,n in target))
            self.assertGreater(integer(row['steps'],p),0)
    def test_endpoints_small_guard_corners(self):
        for name,row in RULES.items():
            p={k:v[0] for k,v in row['guards'].items()};v='001101';source=''.join(w*n for w,n in materialize(row['source'],p,v));target=''.join(w*n for w,n in materialize(row['target'],p,v));start=integer(row['source_start'],p)
            r=replay(dict(q=0,head=0,ones=[start+i for i,b in enumerate(source) if b=='1'],limit=integer(row['steps'],p)))
            self.assertEqual(r['head'],start);self.assertEqual(r['ones'],[start+i for i,b in enumerate(target) if b=='1']);self.assertEqual(r['q'],2)
    def test_framed_periodic_kernels(self):
        rows=json.loads((HERE/'kernels.json').read_text())
        for name in ('A101','A100','C6','D6'):
            row=rows[name];self.assertGreaterEqual(row['read_min'],row['lo']);self.assertLessEqual(row['read_max'],row['hi'])
    def test_C6_induction(self):
        for h in range(21):
            source='010010'*h;target='111010'*h;lo=-len(source)+1
            r=replay(dict(q=2,head=0,ones=[lo+i for i,b in enumerate(source) if b=='1'],limit=6*h))
            self.assertEqual(r['head'],-6*h);self.assertEqual(r['ones'],[lo+i for i,b in enumerate(target) if b=='1']);self.assertEqual(r['q'],2)
    def test_D6_induction(self):
        for h in range(21):
            source='010010'*h;target='101010'*h;lo=-len(source)+1
            r=replay(dict(q=3,head=0,ones=[lo+i for i,b in enumerate(source) if b=='1'],limit=14*h))
            self.assertEqual(r['head'],-6*h);self.assertEqual(r['ones'],[lo+i for i,b in enumerate(target) if b=='1']);self.assertEqual(r['q'],3)
    def test_bad_tokens_and_guards(self):
        with self.assertRaises(ValueError):compile_stack([6,7,1],['101'])
        with self.assertRaises(ValueError):compile_stack([6,7,3],['10'])
        with self.assertRaises(ValueError):decode('1?')
    def test_halt_convention(self):
        r=replay(dict(q=5,head=0,ones=[0],limit=20));self.assertEqual(r['steps'],0);self.assertTrue(r['halted'])
    def test_transition_ledger(self):
        spent=sum(json.loads(s)['executed_defined_transitions'] for s in (HERE/'raw-budget.jsonl').read_text().splitlines());self.assertLessEqual(spent,20000000)

if __name__=='__main__':unittest.main()
