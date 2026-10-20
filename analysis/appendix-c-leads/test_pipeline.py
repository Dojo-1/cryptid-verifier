"""Differential and adversarial checks for the bounded discovery machinery."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import random
import subprocess
import tempfile
import unittest
from unittest.mock import patch
from analyze import compress, encode
from tm import Config, parse, serialize, relabel, canonical, certificate
from probe_l17 import TABLE, make, recognize, partial_rule, outer_rule, raw_probe, check_rule, blank_prefix

ROOT = Path(__file__).resolve().parent


def literal_best(s, max_block):
    best, copies, best_score = s[0],1,0
    for length in range(1,min(len(s),2*max_block)//2+1):
        word, n = s[:length],1
        while (n+1)*length <= len(s) and s[n*length:(n+1)*length] == word:
            n += 1
        score = n/length
        if n >= 2 and score > best_score:
            best,copies,best_score = word,n,score
    return best,copies


def literal_compress(s, max_block):
    """Direct Appendix D pseudocode; no primitive-word optimization."""
    out = []
    while s:
        word,n = literal_best(s,max_block)
        full = n*len(word)
        if n>=2 and full<len(s):
            nxt,c = literal_best(s[full:],max_block)
            full_coverage = full+c*len(nxt)
            short = full-len(word)
            nxt,c = literal_best(s[short:],max_block)
            if short+c*len(nxt)>full_coverage:
                n -= 1
        out.append((word,n));s=s[n*len(word):]
    return out


class ParserChecks(unittest.TestCase):
    def test_paper_boundary_example(self):
        self.assertEqual(compress('1111110101010',8),[('1',5),('10',4)])

    def test_literal_paper_oracle_and_round_trip(self):
        rng = random.Random(20261020)
        words = [''.join(bits) for n in range(10) for bits in itertools.product('01',repeat=n)]
        words += [''.join(rng.choice('01234') for _ in range(rng.randrange(1,300))) for _ in range(300)]
        words += [(rng.choice(['01','100','10110','001011'])*rng.randrange(2,40))+rng.choice(['','1','001']) for _ in range(200)]
        for width in (8,32):
            for word in words:
                result = compress(word,width)
                self.assertEqual(result,literal_compress(word,width))
                self.assertEqual(''.join(w*n for w,n in result),word)

    def test_sides_expand_with_head_preserved(self):
        snap = {'left':'101010101111','right':'0011101110111'}
        for width in (8,32):
            left,right = encode(snap,width)
            self.assertEqual(''.join(w*n for w,n in left),snap['left'])
            self.assertEqual(''.join(w*n for w,n in right),snap['right'])


class ConjugacyChecks(unittest.TestCase):
    def test_random_state_renaming_reflection_witness(self):
        rng = random.Random(1020)
        leads = json.loads((ROOT/'leads.json').read_text())
        for lead in leads:
            table = parse(lead['machine']); self.assertEqual(serialize(table),lead['machine'])
            for rooted in (True,False):
                for _ in range(4):
                    tail = list(range(1 if rooted else 0,len(table))); rng.shuffle(tail)
                    mapping = ([0] if rooted else [])+tail
                    reflected = rng.choice([True,False])
                    changed = relabel(table,mapping,reflected)
                    self.assertEqual(canonical(table,rooted)[0],canonical(changed,rooted)[0])
                    witness = certificate(table,changed,rooted)
                    self.assertIsNotNone(witness)
                    self.assertEqual(relabel(table,[ord(c)-65 for c in witness['state_map']],witness['reflected']),changed)

    def test_same_table_family_does_not_preserve_start(self):
        known = parse('1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA')
        lead = parse('1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---')
        self.assertIsNone(certificate(lead,known,True))
        witness = certificate(lead,known,False)
        self.assertFalse(witness['preserves_blank_start'])
        self.assertEqual(witness['source_start_maps_to'],'D')

    def test_single_transition_change_is_rejected(self):
        original = parse('1RB---_1LA0RB')
        changed = parse('0RB---_1LA0RB')
        self.assertIsNone(certificate(original,changed,False))


class ScannerChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.path = Path(cls.temp.name)
        cls.binary = cls.path/'scan'
        subprocess.run(['g++','-std=c++17','-O2','-Wall','-Wextra','-pedantic',str(ROOT/'scan.cpp'),'-o',str(cls.binary)],check=True)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def run_tables(self,tables,budget=600,cap=16,width=8192):
        inp,out = self.path/'input.txt',self.path/'output.jsonl'
        inp.write_text(''.join(f'T{i} {machine}\n' for i,machine in enumerate(tables)))
        subprocess.run([str(self.binary),str(inp),str(out),str(budget),'20261020',str(cap),str(width)],check=True,capture_output=True)
        return [json.loads(line) for line in out.read_text().splitlines()]

    def test_sparse_reference_at_every_saved_configuration(self):
        rng = random.Random(20261020)
        tables = [r['machine'] for r in json.loads((ROOT/'leads.json').read_text())]
        tables += ['---1RA','1RB1RB_---1LB','1RA---']
        for _ in range(100):
            n,m = rng.randrange(1,7),rng.randrange(2,6)
            table = tuple(tuple(None if rng.random()<.08 else
                                (rng.randrange(m),rng.choice((-1,1)),rng.randrange(n))
                                for _ in range(m)) for _ in range(n))
            tables.append(serialize(table))
        records = self.run_tables(tables)
        for machine,record in zip(tables,records):
            table = parse(machine); c = Config(); by_time = {s['t']:s for s in record['snapshots']}
            for t in range(601):
                if t in by_time:
                    s = by_time[t]
                    self.assertEqual((c.q,c.head),(s['q'],s['head']))
                    lo,hi = (min(c.tape),max(c.tape)) if c.tape else (s['lo'],s['hi'])
                    if c.tape:self.assertEqual((lo,hi),(s['lo'],s['hi']))
                    left = ''.join(str(c.tape.get(p,0)) for p in range(lo,c.head)) if c.tape else ''
                    right = ''.join(str(c.tape.get(p,0)) for p in range(c.head,hi+1)) if c.tape else ''
                    self.assertEqual((left,right),(s['left'],s['right']))
                if t == 600 or not c.step(table):break
            self.assertEqual((c.t,c.q,c.head),(record['steps'],record['final_state'],record['final_head']))
            self.assertEqual(table[c.q][c.tape.get(c.head,0)] is None,record['halted'])

    def test_zero_budget_and_full_support_filter(self):
        records = self.run_tables(['---1RA','1RA---'],budget=0)
        self.assertEqual([r['steps'] for r in records],[0,0])
        self.assertEqual([r['halted'] for r in records],[True,False])
        limited = self.run_tables(['1RA---'],budget=200,width=8)[0]
        self.assertGreater(limited['skipped_wide_events'],0)
        self.assertTrue(all(len(s['left'])+len(s['right'])<=8 for s in limited['snapshots']))

    def test_seeded_sampling_is_repeatable(self):
        machines = ['1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---']
        self.assertEqual(self.run_tables(machines,3000),self.run_tables(machines,3000))


class L17Checks(unittest.TestCase):
    def test_probe_detects_halt_at_exact_budget_endpoint(self):
        # C on 1 enters D on a blank; D has no defined transition.
        with patch('probe_l17.TABLE',parse('------_------_---1RD_------')):
            self.assertEqual(raw_probe(0,1,limit=1),{'kind':'halt','steps':1,'head_shift':1})
            self.assertEqual(raw_probe(0,1,limit=0)['kind'],'timeout')

    def test_section_recognizer_rejects_lost_tape(self):
        self.assertEqual(recognize(make(5,3)),(5,3))
        c = make(5,3);c.tape[-1] = 1
        self.assertIsNone(recognize(c))
        c = make(5,3);c.tape[30] = 1
        self.assertIsNone(recognize(c))

    def test_rule_guards_and_endpoints(self):
        for a in range(16):
            for b in range(16):
                if a>=1 and b==1:self.assertIsNone(partial_rule(a,b))
                else:check_rule(a,b)
        with self.assertRaises(ValueError):partial_rule(-1,2)

    def test_local_sweeps_never_read_outside_their_block(self):
        # Each checked fixed path induces a repeatable disjoint-block sweep.
        for word,output,q,head,steps,target_head in (
                ('01','10',0,0,2,2),
                ('10','10',3,1,4,-1),
                ('01','11',2,1,2,-1)):
            c=Config({i:int(v) for i,v in enumerate(word) if v!='0'},head,q)
            for _ in range(steps):
                self.assertIn(c.head,range(len(word)))
                self.assertTrue(c.step(TABLE))
            self.assertEqual((c.q,c.head),(q,target_head))
            self.assertEqual(''.join(str(c.tape.get(i,0)) for i in range(len(word))),output)

    def test_collapsed_outer_rules_against_raw_tape(self):
        for n in range(1,81):
            a,b,steps,shift,kind = outer_rule(n)
            self.assertLess(steps,200000)
            c = make(0,n)
            for _ in range(steps):
                self.assertTrue(c.step(TABLE))
            expected = make(a,b,head=shift)
            self.assertEqual((c.q,c.head,c.tape),(expected.q,expected.head,expected.tape))

    def test_blank_prefix_respects_budget_and_open_frontier(self):
        result = blank_prefix(1000)
        prefix = result['entries']
        self.assertEqual(prefix[0],{'a':0,'b':2,'raw_time':2,'head':0})
        self.assertEqual([(p['a'],p['b']) for p in prefix[:4]],[(0,2),(1,2),(5,0),(0,14)])
        end = prefix[-1]
        self.assertLessEqual(end['raw_time'],1000)
        if result['stop']=='unsupported_boundary':
            self.assertIsNone(partial_rule(end['a'],end['b']))
        else:
            self.assertGreater(end['raw_time']+result['next_rule_steps'],1000)


if __name__ == '__main__':
    unittest.main()
