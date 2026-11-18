import CryptidLink.L17ad
/-!
# L17: uniform mixed [p,c,2,2,3] return, exact all-width machine path

This file composes the three framed mixed-width transport kernels from
L17ad with the exact all-length D10 and C01 sweeps already proved in Lean.

Let p = u+4 (u : Nat) and let c : Nat be arbitrary. The initial
spatial left tape is (10)^p 0 (10)^c 0 (10)^3, followed by an A head
at 0, and right word 01·101·01·101·00·R. Exterior L and R are
arbitrary, not assumed blank. The exact return has 2u+4c+134 raw
defined steps (equivalently 2p+4c+126), ends in C at head coordinate
-(2p+2c+8), and leaves exterior L untouched.

The right result below is an *unnormalized* but complete physical word:
    1 (11)^u (10)^4 10 (10)^(c+7) 111 R.
The separate normalized claim
    1^(2p-6) (01)^(c+11) 0111 R
is a literal word identity still to be proved, not silently assumed.

Unlike a single finite trace, this theorem quantifies over all u,c
and over all exterior contexts. It does not assert any source is
blank-orbit reachable, and it does not establish a global mixed-width
return rule, stack boundedness, or halting/non-halting.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Guarded mixed-token A source with p=u+4 and arbitrary middle run
    length c. Left tape is head-nearest-first. -/
def mixed_width2_source (u c : ℕ) (L R : ListBlank (Fin 2)) :
    Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) L))))
    (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] R)

/-- Unnormalized complete right word; no internal zero is discarded. -/
def mixed_width2_result (u c : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank (Fin 2) :=
  ListBlank.append [1]
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
      (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0]
        (ListBlank.append [1, 0]
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 7))
            (ListBlank.append [1, 1, 1] R)))))

/-- All u,c and exterior L,R: 112-step A prelude; D10^c; 6-step D/C
    separator bridge; 16-step C outer kernel; C01^u. The complete
    framed C endpoint and exact total clock are preserved. -/
theorem mixed_width2_parametric_exact (u c : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (2 * u + 4 * c + 134)
      (mixed_width2_source u c L R)
      (Cfg.headRight C L (mixed_width2_result u c R)) := by
  let P : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) L
  let Dtail : ListBlank (Fin 2) := ListBlank.append [0] P
  let Aprefix : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ c) Dtail
  let Rbase : ListBlank (Fin 2) := ListBlank.append [1, 1, 1] R
  let R112 : ListBlank (Fin 2) :=
    ListBlank.append (([1, 0] : List (Fin 2)) ^ 8) Rbase
  let RafterD : ListBlank (Fin 2) :=
    ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 7)) Rbase
  let Inner : ListBlank (Fin 2) :=
    ListBlank.append [1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 3)) L)
  let Outer : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ u) L
  let Rout : ListBlank (Fin 2) :=
    ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append [1, 0] RafterD)

  have hleft : Dtail = ListBlank.append [0, 0] Inner := by
    change ListBlank.append [0]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) L) =
      ListBlank.append [0, 0]
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 3)) L))
    rw [show u + 4 = 1 + (u + 3) by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 1 (u + 3) L]
    rfl

  have hright :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ c) R112 =
      ListBlank.append [1, 0] RafterD := by
    change ListBlank.append (([1, 0] : List (Fin 2)) ^ c)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ 8) Rbase) =
      ListBlank.append [1, 0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 7)) Rbase)
    rw [← ListBlank.append_pow_add ([1, 0] : List (Fin 2)) c 8 Rbase,
      show c + 8 = 1 + (c + 7) by omega,
      ListBlank.append_pow_add ([1, 0] : List (Fin 2)) 1 (c + 7) Rbase]
    rfl

  have h12 : ReachesIn target (112 + 4 * c)
      (mixed_width2_source u c L R)
      (Cfg.headLeft D (ListBlank.append [0, 0] Inner)
        (ListBlank.append [1, 0] RafterD)) := by
    have h1 := mixed112_prelude_exact Aprefix R
    have h2 := d10_sweep_exact c Dtail R112
    have h12' := h1.trans h2
    rw [hleft, hright] at h12'
    exact h12'

  have h3 := mixed6_D_to_C_exact Inner RafterD
  have h123 := h12.trans h3

  have hphase :
      ListBlank.append [0, 1] Inner =
      ListBlank.append [0, 1, 1, 0, 1, 0, 1, 0, 1] Outer := by
    change ListBlank.append [0, 1]
      (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 3)) L)) =
      ListBlank.append [0, 1, 1, 0, 1, 0, 1, 0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) L)
    rw [show u + 3 = 3 + u by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 3 u L]
    rfl

  rw [hphase] at h123
  have h4 := mixed16_C_outer_exact Outer (ListBlank.append [1, 0] RafterD)
  have h1234 := h123.trans h4

  have hrotate :
      ListBlank.append [1] Outer =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
        (ListBlank.append [1] L) := rotLB u L
  rw [hrotate] at h1234

  have h5 := c01_sweep_exact u (ListBlank.append [1] L) Rout
  have h12345 := h1234.trans h5

  have hend :
      Cfg.headLeft C (ListBlank.append [1] L)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u) Rout) =
      Cfg.headRight C L (mixed_width2_result u c R) := by
    change Cfg.headLeft C (ListBlank.append [1] L)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u) Rout) =
      Cfg.headRight C L
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ u) Rout))
    exact Cfg.headLeft_cons C (1 : Fin 2) L
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u) Rout)

  rw [hend] at h12345
  set_option maxRecDepth 16384 in
    convert h12345 using 1 <;> (first | rfl | omega)

/-- For a blank exterior left tape, every guarded source returns
    to a genuinely blank-left C frame at its exact 2u+4c+134 clock. -/
theorem mixed_width2_blankleft_all_exact (u c : ℕ)
    (R : ListBlank (Fin 2)) :
    ReachesIn target (2 * u + 4 * c + 134)
      (mixed_width2_source u c default R)
      (Cfg.headRight C default (mixed_width2_result u c R)) :=
  mixed_width2_parametric_exact u c default R

end CryptidLink.L17

#print axioms CryptidLink.L17.mixed_width2_parametric_exact
#print axioms CryptidLink.L17.mixed_width2_blankleft_all_exact
