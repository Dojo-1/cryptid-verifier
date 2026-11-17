import CryptidLink.L17w
/-!
# L17: exact guarded blank-left returns through Cpop

After odd-00 or even-100 scanner/C6/Cpop, the left tape is a full
(10)^c run followed by the outer (10)^p run (in spatial orientation).
C01 exactly consumes c alternating pairs (2c defined transitions).
The outer K41/C01 kernel consumes p-6 further pairs (41+2(p-6)
defined transitions) and leaves an actual blank-left C head.

For p=u+6, c=v+7, the total exact clocks are
  odd 00:  32h+2u+2v+82 = 2p+2c+56+32h
  even100: 32h+2u+2v+78 = 2p+2c+52+32h

Both complete output words explicitly preserve the K41 remainder,
the 1010 Cpop output, the periodic 111010 blocks, and all exterior R
bits. The source is presented as a head-nearest-first word with two
adjacent zero separators. For c>=1 this is the same physical A-left
word (10)^p 0 (10)^c 0 (10)^3 in spatial left-to-right orientation.

No blank-tape reachability, universal mixed-stack return, or machine
non-halting is inferred.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Complete right tape of C after Cpop, C01^c and final K41+C01.
    S is an arbitrary unchanged right-side suffix after the initial 1010. -/
def cpop_bottom_result (u v : ℕ) (S : ListBlank (Fin 2)) :
    ListBlank (Fin 2) :=
  ListBlank.append [1]
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
      (ListBlank.append returnKtail
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 11))
          (ListBlank.append [1, 0, 1, 0] S))))

/-- Universal guarded bottom return: from C with left (10)^(v+7)
    followed by (10)^(u+6), and right word 1010S, the machine reaches
    a blank-left C head in exactly 2(v+7)+41+2u steps. -/
theorem cpop_bottom_blankleft_exact (u v : ℕ)
    (S : ListBlank (Fin 2)) :
    ReachesIn target (2 * (v + 7) + 41 + 2 * u)
      (Cfg.headLeft C
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))
        (ListBlank.append [1, 0, 1, 0] S))
      (Cfg.headRight C default (cpop_bottom_result u v S)) := by
  let Lp : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default
  let Rs : ListBlank (Fin 2) := ListBlank.append [1, 0, 1, 0] S
  let Rlast : ListBlank (Fin 2) :=
    ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 11)) Rs

  have h1 := c01_sweep_exact (v + 7) Lp Rs
  have hones :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 7)) Rs =
      ListBlank.append [1, 1, 1] Rlast := by
    change
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 7)) Rs =
      ListBlank.append [1, 1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 11)) Rs)
    rw [one_pow_two_mul (v + 7),
      show 2 * (v + 7) = 3 + (2 * v + 11) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2))
        3 (2 * v + 11) Rs]
    rfl

  rw [hones] at h1
  have h2 := k41_c01_last_exact u default Rlast
  have h12 := h1.trans h2

  have he :
      Cfg.headLeft C (ListBlank.append [1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append returnKtail Rlast)) =
      Cfg.headRight C default (cpop_bottom_result u v S) := by
    change
      Cfg.headLeft C (ListBlank.append [1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append returnKtail Rlast)) =
      Cfg.headRight C default
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
            (ListBlank.append returnKtail Rlast)))
    exact (Cfg.headRight_cons C (1 : Fin 2) default
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append returnKtail Rlast))).symm
  rw [he] at h12
  convert h12 using 1 <;> (first | rfl | omega)

/-- The entire physical A source after the last 10 run, with
    the double-zero Cpop guard and an odd number of 101 tokens. -/
def a00_odd_source (u v h : ℕ) (R : ListBlank (Fin 2)) :
    Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1]
      (ListBlank.append [0]
        (ListBlank.append [0]
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)))))
    (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 1))
      (ListBlank.append [0, 0] R))

/-- Complete right tape at the blank-left C endpoint of the odd-00 row. -/
def a00_odd_result (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank (Fin 2) :=
  cpop_bottom_result u v
    (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h)
      (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R))

/-- All h,u,v: full odd-00 A-to-C return, exact 2p+2c+56+32h steps,
    complete endpoint word, and genuinely blank left tape. -/
theorem a00_odd_blankleft_exact (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (32 * h + 2 * u + 2 * v + 82)
      (a00_odd_source u v h R)
      (Cfg.headRight C default (a00_odd_result u v h R)) := by
  let L : ListBlank (Fin 2) :=
    ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)
  let S : ListBlank (Fin 2) :=
    ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h)
      (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R)
  have h1 := a101_00_odd_cpop_exact h L R
  have h2 := cpop_bottom_blankleft_exact u v S
  convert h1.trans h2 using 1 <;>
    (first | rfl | omega | (simp only [a00_odd_source]; rfl))

/-- Even-100 A source with the same Cpop guard and outer run structure. -/
def a100_even_source (u v h : ℕ) (R : ListBlank (Fin 2)) :
    Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1]
      (ListBlank.append [0]
        (ListBlank.append [0]
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)))))
    (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h))
      (ListBlank.append [1, 0, 0] R))

def a100_even_result (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank (Fin 2) :=
  cpop_bottom_result u v
    (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h)
      (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R))

/-- All h,u,v: full even-100 A-to-C return, exact 2p+2c+52+32h steps,
    complete endpoint word, and genuinely blank left tape. -/
theorem a100_even_blankleft_exact (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (32 * h + 2 * u + 2 * v + 78)
      (a100_even_source u v h R)
      (Cfg.headRight C default (a100_even_result u v h R)) := by
  let L : ListBlank (Fin 2) :=
    ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)
  let S : ListBlank (Fin 2) :=
    ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h)
      (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R)
  have h1 := a101_100_even_cpop_exact h L R
  have h2 := cpop_bottom_blankleft_exact u v S
  convert h1.trans h2 using 1 <;>
    (first | rfl | omega | (simp only [a100_even_source]; rfl))

end CryptidLink.L17

#print axioms CryptidLink.L17.cpop_bottom_blankleft_exact
#print axioms CryptidLink.L17.a00_odd_blankleft_exact
#print axioms CryptidLink.L17.a100_even_blankleft_exact
