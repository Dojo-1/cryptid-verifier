"""Necessary differential, contextual and boundary tests for the new derivation."""
from __future__ import annotations
import itertools
import random
import unittest
from block_sim import BlockTM
from reference import run
from rules import core100,core111,core1100,core1100_small,residue,rewrite,Endpoint,trajectory
from validate import check,kernels
from words import Word


class WordChecks(unittest.TestCase):
    def test_expansion_slicing_and_periodic_prefix_oracles(self):
        for n in range(9):
            for bits in itertools.product('01',repeat=n):
                s=''.join(bits);w=Word.literal(s);trim=s.rstrip('0')
                self.assertEqual(w.expand(),trim)
                for k in range(n+2):
                    self.assertEqual(w.drop(k).expand(),trim[k:])
                for pattern in ('0','1','01','10'):
                    expected=0
                    while expected<len(trim) and trim[expected]==pattern[expected%len(pattern)]:expected+=1
                    self.assertEqual(w.periodic_prefix_length(pattern),expected)

    def test_exact_huge_word_identity_and_negative_control(self):
        n=10**100;m=10**90;k=10**80
        x=Word((('1',n),('10',m),('1',k)))
        y=Word((('1',n+1),('01',m),('1',k-1)))
        self.assertTrue(x.equivalent(y))
        self.assertFalse(x.equivalent(Word((('1',n+2),('01',m),('1',k-2)))))
        with self.assertRaises(ValueError):x.expand(1000)


class RuleChecks(unittest.TestCase):
    def test_fixed_paths_read_only_their_declared_context(self):
        self.assertEqual(len(kernels()),8)

    def test_residue_guard_boundaries_and_raw_endpoints(self):
        for a in range(7,41):
            if a%3:
                check(Word((('01',a),('1',1))),residue(a))
            else:
                with self.assertRaises(ValueError):residue(a)
        for a in range(7):
            with self.assertRaises(ValueError):residue(a)

    def test_new_core_guards_and_arbitrary_right_context(self):
        suffix=Word.literal('0100110011011001')
        for a,c in ((7,0),(7,1),(8,2),(19,17)):
            source=Word((('01',a),('10',c),('100',1))+suffix.parts)
            check(source,core100(a,c,suffix))
        for a,c in ((5,1),(5,2),(6,7),(19,17)):
            source=Word((('01',a),('10',c),('111',1))+suffix.parts)
            check(source,core111(a,c,suffix))
        with self.assertRaises(ValueError):core100(6,0)
        with self.assertRaises(ValueError):core111(4,1)
        with self.assertRaises(ValueError):core111(5,0)

    def test_small_cases_stay_explicitly_unsupported(self):
        self.assertIsInstance(rewrite(1,Word.literal('1')),dict)
        self.assertIsInstance(rewrite(6,Word.literal('1001')),dict)
        self.assertIsInstance(rewrite(4,Word.literal('10111')),dict)
        self.assertIsInstance(rewrite(12,Word.literal('10110')),dict)

    def test_stack_producing_core_guards_and_context(self):
        suffix=Word.literal('0110010010110101')
        for a,c in ((7,7),(7,8),(8,7),(32,25)):
            check(Word((('01',a),('10',c),('1100',1))+suffix.parts),core1100(a,c,suffix))
        with self.assertRaises(ValueError):core1100(6,7)
        with self.assertRaises(ValueError):core1100(7,6)

    def test_one_tail_family_is_not_closed_counterexample(self):
        source=Word((('01',7),('1',1),('01',8),('1',1)))
        target=Endpoint(0,Word((('1',2),('01',7),('1',3),('01',7),('1',3))),152,-2,'two-tail-witness')
        check(source,target)

    def test_short_tail_fixed_windows_and_boundaries(self):
        from validate_small_tails import kernels as short_kernels
        self.assertEqual(len(short_kernels()),7)
        for c in range(1,7):
            for a in (7,8,19):
                check(Word((('01',a),('10',c),('11',1))),core1100_small(a,c))
        with self.assertRaises(ValueError):core1100_small(6,1)
        with self.assertRaises(ValueError):core1100_small(7,7)

    def test_derived_trajectory_respects_event_limit(self):
        result=trajectory(6575648756,Word.literal('1'),3)
        self.assertEqual(len(result['records']),3)
        self.assertIn('budget',result['stop'])


class BlockChecks(unittest.TestCase):
    def test_random_full_state_agreement(self):
        rng=random.Random(20261020)
        for width in (2,6):
            for _ in range(100):
                bits=''.join(rng.choice('01') for _ in range(rng.randrange(81)))
                q=rng.randrange(6);steps=rng.randrange(1001);shift=rng.randrange(-20,21)
                direct=run(bits,steps,q,shift)
                fast=BlockTM(Word.literal(bits),width,q,shift);out=fast.run(steps)
                self.assertEqual((out['steps'],out['q'],out['head'],out['halted'],fast.sparse()),
                                 (direct['steps'],direct['q'],direct['head'],direct['halted'],direct['tape']))

    def test_leading_zero_alignment_regression(self):
        bits='0001011011010001010111100110001110000110111'
        for width in (2,6):
            for steps in (0,1,17,386):
                direct=run(bits,steps)
                fast=BlockTM(Word.literal(bits),width);out=fast.run(steps)
                self.assertEqual((out['q'],out['head'],fast.sparse()),(direct['q'],direct['head'],direct['tape']))

    def test_halt_and_event_budget_are_not_nonhalting_claims(self):
        for width in (2,6):
            x=BlockTM(Word.literal('1'),width,q=5);out=x.run(100)
            self.assertEqual(out['steps'],0);self.assertTrue(out['halted'])
            x=BlockTM(Word((('01',1000),('1',1))),width)
            out=x.run(200000,max_events=1)
            self.assertFalse(out['complete']);self.assertFalse(out['halted'])

    def test_restart_partition_preserves_complete_state(self):
        for width in (2,6):
            word=Word((('01',80),('1',1)))
            once=BlockTM(word,width);once.run(20000)
            split=BlockTM(word,width)
            for t in (0,1,7,83,1000,20000):split.run(t)
            self.assertEqual((once.q,once.head,once.steps,once.sparse()),(split.q,split.head,split.steps,split.sparse()))


if __name__=='__main__':unittest.main()
