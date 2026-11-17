import json,unittest
from paths import HERE
from claims import RULES,TRANSFERS
from specification import Claims,integer,materialize
from raw import replay

class MixedReturnTests(unittest.TestCase):
    def test_partition_of_previous_widths(self):
        for r in range(2,6):
            for s in range(1,25):
                matches=[x for x in RULES.values() if x['r']==r and (s==x['s'] if type(x['s']) is int else s>=x['guards']['s'][0])]
                self.assertEqual(len(matches),1,(r,s))
    def test_every_guard_corner_literal(self):
        for name,row in {**RULES,**TRANSFERS}.items():
            p={k:v[0] for k,v in row['guards'].items()};v='001101';src=''.join(w*n for w,n in materialize(row['source'],p,v));dst=''.join(w*n for w,n in materialize(row['target'],p,v));start=integer(row['source_start'],p)
            got=replay(dict(q=row['source_q'],head=0,limit=integer(row['steps'],p),ones=[start+i for i,b in enumerate(src) if b=='1']))
            self.assertEqual(got['q'],row['target_q'],name);self.assertEqual(got['head'],integer(row['shift'],p),name);self.assertEqual(got['ones'],[start+i for i,b in enumerate(dst) if b=='1'],name);self.assertFalse(got['halted'])
    def test_huge_parameter_suffix_positions(self):
        for row in {**RULES,**TRANSFERS}.values():
            p={k:10**90+max(v[0],17) for k,v in row['guards'].items()};src=materialize(row['source'],p,'001101');dst=materialize(row['target'],p,'001101')
            self.assertEqual(sum(len(w)*n for w,n in src),sum(len(w)*n for w,n in dst));self.assertGreater(integer(row['steps'],p),0)
    def test_right_buffers_are_guards(self):
        claims=Claims(HERE/'claims.json')
        for name in ('C2_s1','C2_s4','C5_s2','C5_s5'):
            with self.assertRaises(ValueError):claims.instantiate(name,{'p':6,'c':7,'m':8},'0')
    def test_mixed_A_166_step_witness(self):
        p,c=6,7;left='10'*p+'0'+'10'*c+'0'+'10'*3;right='01'+'101'+'01'+'101'+'00'+'001101'
        src=left+right;start=-len(left);got=replay(dict(q=0,head=0,limit=166,ones=[start+i for i,b in enumerate(src) if b=='1']))
        target='1'*6+'01'*19+'11'+'001101';self.assertEqual(got['q'],2);self.assertEqual(got['head'],-34);self.assertEqual(got['ones'],[-34+i for i,b in enumerate(target) if b=='1'])
    def test_original_C_222_step_composition(self):
        src='01'*7+'10'*7+'1101'+'01'+'101'+'01'+'101'+'00'+'001101';got=replay(dict(q=2,head=0,limit=222,ones=[i for i,b in enumerate(src) if b=='1']))
        target='1'*6+'01'*19+'11'+'001101';self.assertEqual(got['head'],-2);self.assertEqual(got['q'],2);self.assertEqual(got['ones'],[-2+i for i,b in enumerate(target) if b=='1'])
    def test_named_lemma_lower_guard_corners(self):
        for p in (4,5):
            for c in (1,2):
                a=p+1;src='01'*a+'10'*c+'1101'+'01'+'101'+'01'+'101'+'00'+'001101';time=4*a+6*c+152
                got=replay(dict(q=2,head=0,limit=time,ones=[i for i,b in enumerate(src) if b=='1']));target='1'*(2*p-6)+'01'*(c+12)+'11'+'001101'
                self.assertEqual(got['q'],2);self.assertEqual(got['head'],-2);self.assertEqual(got['ones'],[-2+i for i,b in enumerate(target) if b=='1'])
    def test_width2_has_a_rightward_B_exit(self):
        row=json.loads((HERE/'kernels.json').read_text())['C2B'];self.assertEqual((row['exit_q'],row['exit_head'],row['steps']),(1,4,38))
    def test_width5_needs_two_previous_pairs_for_B_exit(self):
        row=json.loads((HERE/'kernels.json').read_text())['C5B'];self.assertEqual(row['lo'],-14);self.assertEqual(row['steps'],62);self.assertEqual(row['read_min'],-14)
    def test_frame_exit_cell_is_not_read(self):
        for name in ('C_large','C_pair1','C_pair4','D_large','D_pair2'):
            row=TRANSFERS[name];p={k:v[0] for k,v in row['guards'].items()};self.assertEqual(integer(row['shift'],p),integer(row['source_start'],p)-1)
    def test_empty_run_turn_counter_effect(self):
        row=TRANSFERS['D_zero_turn']
        for c in (1,2,7):
            for n in (1,2,13):
                p=dict(c=c,n=n);v='001101';src=''.join(w*k for w,k in materialize(row['source'],p,v));dst=''.join(w*k for w,k in materialize(row['target'],p,v));start=-2*c-1
                got=replay(dict(q=3,head=0,limit=6*n+25,ones=[start+i for i,b in enumerate(src) if b=='1']))
                self.assertEqual((got['q'],got['head']),(3,-3));self.assertEqual(got['ones'],[start+i for i,b in enumerate(dst) if b=='1'])
    def test_C4_zero_middle_is_retained(self):
        row=RULES['C4'];p=dict(p=6,c=7,s=1,m=3);target=''.join(w*n for w,n in materialize(row['target'],p,''));self.assertIn('0011',target)
    def test_more_unused_ones_do_not_change_time(self):
        for row in RULES.values():
            p={k:v[0] for k,v in row['guards'].items()};time=integer(row['steps'],p);p['m']+=10**100;self.assertEqual(integer(row['steps'],p),time)
    def test_local_unknown_read_stops_are_not_C_sections(self):
        rows=json.loads((HERE/'local-probes.json').read_text())
        self.assertTrue(all(r['reason']=='unknown-read' for r in rows));self.assertTrue(any(r['q']==0 for r in rows));self.assertTrue(any(r['q']==1 for r in rows))
    def test_halt_convention(self):
        self.assertEqual(replay(dict(q=5,head=0,limit=100,ones=[0]))['steps'],0)
    def test_budget(self):
        spent=sum(json.loads(x)['executed_defined_transitions'] for x in (HERE/'raw-budget.jsonl').read_text().splitlines());self.assertLessEqual(spent,20000000)

if __name__=='__main__':unittest.main()
