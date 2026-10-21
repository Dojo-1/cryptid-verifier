import unittest,random,subprocess,sys
from frame_paths import HERE
from counter_streams import State,forward,inverse,rank,push_entry,trace,finite_bound
from counter_critic import specs,candidates
from tape_frames import Frame,variants,table,mapped_step,angled,adaptive_increment
from validate_frames import raw_step,MACHINE

class FrameTests(unittest.TestCase):
    def test_negative_nonuniform_coordinates(self):
        f=Frame('periodic',(2,1,3))
        for x,y in ((-3,-6),(-2,-4),(-1,-3),(0,0),(1,2),(2,3),(3,6)):
            self.assertEqual(f.place(x,0),y);self.assertEqual(f.unplace(y,0),x)
    def test_fillers_are_outside_the_logical_tape(self):
        f=Frame('stretch',(3,))
        for y in (-2,-1,1,2):
            with self.assertRaises(ValueError):f.unplace(y,0)
    def test_exact_large_coordinate_roundtrip(self):
        for f in variants():
            for x in (-(1<<4096),-1,0,1<<4096):self.assertEqual(f.unplace(f.place(x,1234567),1234567),x)
    def test_frame_preserves_sparse_tape_and_clock(self):
        state=(19,2,-4,frozenset((-10,-4,8)))
        for f in variants():self.assertEqual(f.decode(f.encode(state)),state)
    def test_raw_machine_has_two_predecessors(self):
        # Both land on B at0 with ones at-1,+1. Restricted macro injectivity
        # must never be promoted to raw-machine reversibility.
        a=(0,0,-1,frozenset({1}));b=(0,2,1,frozenset({-1,1}))
        self.assertNotEqual(a,b);self.assertEqual(raw_step(a)[0],raw_step(b)[0])
    def test_undefined_halt_does_not_advance_frame(self):
        for f in variants():
            v=f.encode((0,5,0,frozenset({0})));self.assertEqual(mapped_step(f,v,table(MACHINE)),(v,False))
    def test_causal_angle_boundary(self):
        for M,P in ((1,1),(2,-2),(0,0)):
            with self.assertRaises(ValueError):angled(0,0,M,P)
        for d in (-1,1):self.assertGreater(angled(1,d)-angled(0,0),0)
    def test_adaptive_clock_at_digit_boundaries(self):
        f=Frame('irregular',(2,1,3),irregular=True)
        for p in range(1,128):
            t=(1<<p)-1
            for x in (-3,0,10):
                for d in (-1,1):self.assertGreaterEqual(adaptive_increment(f,t)+2*(f.place(x+d,t+1)-f.place(x,t)),1)
    def test_mode_offset_is_needed(self):
        x=State('D',7,1,2,7,3);_,y=forward(x)
        self.assertEqual(rank(x)[2]-rank(y)[2],1)
        self.assertLess(3*x.k+8*x.m,3*y.k)
    def test_join_and_gap_use_different_lex_levels(self):
        for x in (State('D',7,5,1,7,3),State('G',7,100,0,2,0)):
            _,y=forward(x);self.assertLess(rank(y),rank(x));self.assertGreater(rank(y)[2],rank(x)[2])
    def test_inverse_parity_tags(self):
        self.assertEqual(inverse(State('D',10,7,4,7,3))[0],'G1')
        self.assertEqual(inverse(State('D',10,7,1,14,0))[0],'D11join')
    def test_canonical_boundary_exclusions(self):
        for args in (('D',4,0,1,7,3),('D',4,7,0,7,3),('G',4,7,1,7,3),('G',4,7,0,0,3)):
            with self.assertRaises(ValueError):State(*args)
    def test_pushes_are_roots(self):
        for a,c in ((7,7),(8,9),(46,7),(10**100+7,10**20+7)):
            self.assertIsNone(inverse(push_entry(a,c)))
    def test_long_N4_path_returns_to_its_root(self):
        root=push_entry(8,80);chain,last,why=trace(root)
        self.assertEqual(len(chain),48);self.assertLessEqual(len(chain),finite_bound(root))
        x=last
        for _ in chain:x=inverse(x)[1]
        self.assertEqual(x,root)
    def test_named_uncovered_generic_pushes(self):
        self.assertEqual(trace(push_entry(37,7))[2],'J-short-width')
        self.assertEqual(trace(push_entry(46,7))[2],'J-short-terminal')
    def test_affine_obstruction_certificate(self):
        # 2*(7a-3b)+3*(2b-a)=11a. The left must be<0 and a>0.
        a,b=2*7+3*(-1),2*(-3)+3*2
        self.assertEqual((a,b),(11,0))
        # Mode-specific version:2*(7aD-3bD)+3*(aG-aD)+3*(2bD-aG).
        self.assertEqual((2*7-3,2*(-3)+3*2,3-3),(11,0,0))
    def test_generic_solver_is_separate(self):
        rows,_=specs();y=State('D',10,7,1,14,0)
        self.assertEqual(candidates('D',(10,7,1,14,0),rows),[('D11join','D',(7,5,1,7,3))])
    def test_imports_do_not_write(self):
        code="import sys,pathlib,importlib;sys.path.insert(0,sys.argv[1]);pathlib.Path.write_text=lambda *a,**k: (_ for _ in ()).throw(AssertionError('write on import'));importlib.import_module(sys.argv[2])"
        for name in ('counter_streams','counter_critic','tape_frames','validate_streams','verify_streams','validate_frames','mutations'):
            out=subprocess.run([sys.executable,'-c',code,str(HERE),name],capture_output=True,text=True);self.assertEqual(out.returncode,0,out.stderr)
if __name__=='__main__':unittest.main()
