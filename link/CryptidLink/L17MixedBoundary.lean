import CryptidLink.L17ac
/-!
# L17: the saved mixed 01/101 boundary, with exact clocks

The four-run C2,s2 return and the scanner word 01·101·01·101 are
compositions of framed machine paths. The small middle runs remain
explicit; none of the homogeneous three-run guards is used to erase them.
All outside tape is symbolic. A blank-left conclusion is used only for
the final outer return, and no blank-orbit occurrence is asserted.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Any finite A01 scan, retaining both exterior tapes and its exact clock. -/
theorem a01_sweep_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (2 * n)
      (Cfg.headRight A L
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) R))
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) L) R) := by
  induction n generalizing L with
  | zero =>
    exact ReachesIn.zero _ _
  | succ n ih =>
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) n R]
    have h1 := a01_exact L
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) R)
    have h2 := ih (ListBlank.append [0, 1] L)
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) n L] at h2
    convert h1.trans h2 using 1
    omega

/-- B111 starter: eight transitions on [-1,2], arbitrary exterior L/R. -/
theorem b111_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 8
      (Cfg.headRight B (ListBlank.append [1] L)
        (ListBlank.append [1, 1, 1] R))
      (Cfg.headLeft D L (ListBlank.append [1, 0, 1, 0] R)) := by
  l17_exact_steps

/-- B over n+1 written 01 pairs and three ones returns in D mode.
    The zero under the final D head is kept explicitly. -/
theorem b_to_d_sweep_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (4 * n + 8)
      (Cfg.headRight B
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L)
        (ListBlank.append [1, 1, 1] R))
      (Cfg.headLeft D (ListBlank.append [0] L)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 2)) R)) := by
  have hs :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L =
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
          (ListBlank.append [0] L)) := by
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) n L,
      ← rotLB0 n L]
    rfl
  rw [hs]
  have h1 := b111_exact
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
      (ListBlank.append [0] L)) R
  have h2 := d10_sweep_exact n (ListBlank.append [0] L)
    (ListBlank.append [1, 0, 1, 0] R)
  have he :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append [1, 0, 1, 0] R) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 2)) R := by
    exact (ListBlank.append_pow_add ([1, 0] : List (Fin 2)) n 2 R).symm
  rw [he] at h2
  convert h1.trans h2 using 1
  omega

/-- The C2,s2 bounce uses six right ones. It ends in D, not at a C section.
    C2B (38) followed by B_to_D(5) (24); exterior tape is arbitrary. -/
theorem c2_s2_to_d_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 62
      (Cfg.headLeft C
        (ListBlank.append [0, 1, 0, 1, 0, 0, 1, 0, 1, 0] L)
        (ListBlank.append [1, 1, 1, 1, 1, 1] R))
      (Cfg.headLeft D (ListBlank.append [0, 0, 1, 0] L)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ 6) R)) := by
  have h1 := short_C2B_exact (ListBlank.append [0, 1, 0] L)
    (ListBlank.append [1, 1, 1] R)
  have h2 := b_to_d_sweep_exact 4 (ListBlank.append [0, 1, 0] L) R
  have hs :
      Cfg.headLeft C
        (ListBlank.append [0, 1, 0, 1, 0, 0, 1, 0, 1, 0] L)
        (ListBlank.append [1, 1, 1, 1, 1, 1] R) =
      Cfg.headRight C
        (ListBlank.append [1, 0, 1, 0, 0, 1]
          (ListBlank.append [0, 1, 0] L))
        (ListBlank.append [0, 1, 1, 1]
          (ListBlank.append [1, 1, 1] R)) := by
    exact Cfg.headLeft_cons C (0 : Fin 2) _ _
  rw [← hs] at h1
  exact h1.trans h2

/-- A single-pair D join followed by any c=v+1 D10 sweep.
    The right n+1 pairs and both exterior contexts remain explicit. -/
theorem d_pair1_sweep_exact (v n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (4 * v + 14)
      (Cfg.headLeft D
        (ListBlank.append [0, 0, 1, 0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1)) L))
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) R))
      (Cfg.headLeft D L
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + n + 4)) R)) := by
  let X := ListBlank.append [1]
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ v) L)
  let Y := ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 3)) R
  have hs :
      ListBlank.append [0, 0, 1, 0]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1)) L) =
      ListBlank.append [0, 0, 1, 0, 0] X := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) v L]
    rfl
  have hr :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) R =
      ListBlank.append [1, 0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R) :=
    ListBlank.append_pow_succ _ _ _
  rw [hs, hr]
  have h1 := j1k_headLeft_exact X
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R)
  have hright :
      ListBlank.append [0, 1, 0, 1, 0, 1, 0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R) =
      ListBlank.append [0] Y := by
    change ListBlank.append [0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R)) = _
    rw [← ListBlank.append_pow_add]
    dsimp [Y]
    rw [Nat.add_comm 3 n]
  have hleft : ListBlank.append [0] X =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1)) L := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) v L]
    rfl
  have he : Cfg.headRight D X (ListBlank.append [0] Y) =
      Cfg.headLeft D
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1)) L) Y :=
    (Cfg.headRight_cons D (0 : Fin 2) X Y).trans
      (congrArg (fun Z => Cfg.headLeft D Z Y) hleft)
  rw [hright, he] at h1
  have h2 := d10_sweep_exact (v + 1) L Y
  have hword :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 1)) Y =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + n + 4)) R := by
    dsimp [Y]
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun k : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ k) R) (by omega)
  rw [hword] at h2
  convert h1.trans h2 using 1
  omega

/-- The mixed scanner 01·101·01·101 followed by 00, in its full frame.
    Its two new width-two runs are retained at the C endpoint. -/
theorem mixed_scanner_0101_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 40
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0] L)
        (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] R))
      (Cfg.headLeft C
        (ListBlank.append [0, 1, 0, 1, 0, 0, 1, 0, 1, 0] L)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  set_option maxRecDepth 4096 in
    l17_exact_steps

/-- The four-run C2,s2 source: p=u+4,c=v+1, both small widths exactly two.
    The headLeft list includes the final zero currently under C. -/
def mixed_c2_source (u v : ℕ) (R : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C
    (ListBlank.append [0, 1, 0, 1, 0, 0, 1, 0, 1, 0]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1))
        (ListBlank.append [0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default))))
    (ListBlank.append [1, 1, 1, 1, 1, 1] R)

/-- C2,s2 has a complete return with p>=4,c>=1 and six buffered ones.
    Exact time 2p+4c+86; arbitrary right context R is preserved. -/
theorem mixed_c2_s2_blankleft_exact (u v : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (2 * u + 4 * v + 98)
      (mixed_c2_source u v R)
      (Cfg.headRight C default
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 12))
            (ListBlank.append [0] R)))) := by
  let Lp := ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default
  let L := ListBlank.append [0] Lp
  let Lc := ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1)) L
  let Rt := ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7)) R
  have h1 := c2_s2_to_d_exact Lc R
  have h2 := d_pair1_sweep_exact v 5 L R
  have h12 := h1.trans h2
  have hpairs :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 5 + 4)) R =
      ListBlank.append [1, 0, 1, 0] Rt := by
    change _ = ListBlank.append (([1, 0] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7)) R)
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun k : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ k) R) (by omega)
  rw [hpairs] at h12
  have h3 := k22_c01_last_exact u default Rt
  have h123 := h12.trans h3
  have hperiod :
      ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] Rt =
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 12))
          (ListBlank.append [0] R)) := by
    change ListBlank.append (([1, 0] : List (Fin 2)) ^ 6)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7)) R) = _
    rw [← ListBlank.append_pow_add,
      show 6 + (v + 7) = (v + 12) + 1 by omega,
      ← ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) (v + 12) R,
      rotLB (v + 12) (ListBlank.append [0] R)]
    rfl
  have hones (S : ListBlank (Fin 2)) :
      ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append [1] S)) =
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2)) S := by
    rw [one_pow_two_mul,
      show 2 * u + 2 = 1 + (2 * u + 1) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * u + 1),
      ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * u) 1]
    rfl
  have hword :
      ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] Rt)) =
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 12))
          (ListBlank.append [0] R)) := by
    rw [hperiod, hones]
  have he : Cfg.headLeft C (ListBlank.append [1] default)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] Rt)) =
      Cfg.headRight C default
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 12))
            (ListBlank.append [0] R))) :=
    (Cfg.headLeft_cons C (1 : Fin 2) default
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] Rt))).trans
      (congrArg (Cfg.headRight C default) hword)
  rw [he] at h123
  change ReachesIn target _ (mixed_c2_source u v R) _ at h123
  convert h123 using 1
  omega

/-- Source after the two outer runs and the final width-three A run. -/
def mixed_a_source (u v : ℕ) (R : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1))
        (ListBlank.append [0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default))))
    (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] R)

/-- Full target of the saved mixed scanner return, with canonical full word. -/
def mixed_a_result (u v : ℕ) (R : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 13))
      (ListBlank.append [1, 1] R))

/-- The mixed word 01·101·01·10100 returns to blank-left C, for p>=4,c>=1.
    Time 2p+4c+126. The 0111 join is a word identity, not an extra step. -/
theorem mixed_a_blankleft_exact (u v : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (2 * u + 4 * v + 138)
      (mixed_a_source u v R)
      (Cfg.headRight C default (mixed_a_result u v R)) := by
  let L := ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1))
    (ListBlank.append [0]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default))
  have h1 := mixed_scanner_0101_exact L R
  have h2 := mixed_c2_s2_blankleft_exact u v (ListBlank.append [1, 1, 1] R)
  have h12 := h1.trans h2
  have he :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 12))
          (ListBlank.append [0] (ListBlank.append [1, 1, 1] R))) =
      mixed_a_result u v R := by
    unfold mixed_a_result
    rw [← ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) (v + 12)
      (ListBlank.append [1, 1] R)]
    rfl
  rw [he] at h12
  change ReachesIn target _ (mixed_a_source u v R) _ at h12
  convert h12 using 1
  omega

/-- Two-step blank-left C entry, with the clock left implicit in entryC now explicit. -/
theorem entryC_exact (a : ℕ) (X : ListBlank (Fin 2)) :
    ReachesIn target 2
      (Ccal (a + 1) X)
      (Cfg.headRight A default
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2)) X)) := by
  change ReachesIn target 2
    (Cfg.headRight C default
      (ListBlank.append [0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) X)))
    (Cfg.headRight A default
      (ListBlank.append [0, 1, 0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) X)))
  l17_exact_steps

/-- The eleven-step K11 with arbitrary exterior contexts. -/
theorem k11_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 11
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1] L)
        (ListBlank.append [1, 0] R))
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0] L)
        (ListBlank.append [0] R)) := by
  l17_exact_steps

/-- A0 followed by B1101: exact split, including both zero gaps.
    The preceding run need only have n+2 pairs. -/
theorem a01101_split_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target 15
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 2))
          (ListBlank.append [0] L))
        (ListBlank.append [0, 1, 1, 0, 1] R))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 1))
            (ListBlank.append [0] L))) R) := by
  let X := ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 2))
    (ListBlank.append [0] L)
  let Y := ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L
  have h1 : ReachesIn target 1
      (Cfg.headRight A X (ListBlank.append [0, 1, 1, 0, 1] R))
      (Cfg.headRight B (ListBlank.append [1] X)
        (ListBlank.append [1, 1, 0, 1] R)) := by
    l17_exact_steps
  have hleft : ListBlank.append [1] X = ListBlank.append [1, 0, 1, 0] Y := by
    change ListBlank.append [1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 2))
        (ListBlank.append [0] L)) =
      ListBlank.append [1, 0, 1, 0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L)
    rw [rotLB (n + 2) (ListBlank.append [0] L)]
    change ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 2))
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1) L) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ 2)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L)
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add]
    exact congrArg (fun k : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ k) L) (by omega)
  rw [hleft] at h1
  have h2 := short_B1101_exact Y R
  have he : ListBlank.append [0, 1, 0, 1, 0, 1, 0, 0] Y =
      ListBlank.append [0, 1, 0, 1, 0, 1, 0]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 1))
          (ListBlank.append [0] L)) := by
    change ListBlank.append [0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append [0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L)) = _
    rw [rotLB0]
  rw [he] at h2
  exact h1.trans h2

/-- Exact original-C 1101 prelude into the A source with stack [p,c,3].
    p=u+4,c=v+1; clock 2a+2c+28 for a=p+1. The suffix is arbitrary. -/
theorem entry1101_exact (u v : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (2 * u + 2 * v + 40)
      (Ccal (u + 5)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 1))
          (ListBlank.append [1, 1, 0, 1] R)))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1))
            (ListBlank.append [0]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default))))
        R) := by
  let Lp := ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default
  let Z := ListBlank.append (([1, 0] : List (Fin 2)) ^ v)
    (ListBlank.append [1, 1, 0, 1] R)
  let X := ListBlank.append [1, 0] Z
  have h1 := entryC_exact (u + 4) X
  have h2 := a01_sweep_exact (u + 6) default X
  have hleft :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default =
      ListBlank.append [0, 1, 0, 1] Lp := by
    rw [show u + 6 = 2 + (u + 4) by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 (u + 4)]
    rfl
  rw [hleft] at h2
  have h3 := k11_exact Lp Z
  have hright : ListBlank.append [0] Z =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ v)
        (ListBlank.append [0, 1, 1, 0, 1] R) := by
    exact rotLB0 v (ListBlank.append [1, 1, 0, 1] R)
  rw [hright] at h3
  have h4 := a01_sweep_exact v (ListBlank.append [0, 1, 0, 1, 0] Lp)
    (ListBlank.append [0, 1, 1, 0, 1] R)
  have hjoin :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ v)
        (ListBlank.append [0, 1, 0, 1, 0] Lp) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
        (ListBlank.append [0] Lp) := by
    exact (ListBlank.append_pow_add ([0, 1] : List (Fin 2)) v 2
      (ListBlank.append [0] Lp)).symm
  rw [hjoin] at h4
  have h5 := a01101_split_exact v Lp R
  have hall := (((h1.trans h2).trans h3).trans h4).trans h5
  have hs : X = ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 1))
      (ListBlank.append [1, 1, 0, 1] R) := by
    exact (ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) v
      (ListBlank.append [1, 1, 0, 1] R)).symm
  rw [hs] at hall
  convert hall using 1
  omega

/-- The saved mixed boundary, now from its original blank-left C section.
    For a=u+5,c=v+1, time 4a+6c+152. No right-context bit is consumed. -/
theorem mixed_original_C_exact (u v : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (4 * u + 6 * v + 178)
      (Ccal (u + 5)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 1))
          (ListBlank.append
            [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] R)))
      (Cfg.headRight C default (mixed_a_result u v R)) := by
  have h1 := entry1101_exact u v
    (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] R)
  have h2 := mixed_a_blankleft_exact u v R
  convert h1.trans h2 using 1 <;> (first | rfl | omega)

end CryptidLink.L17

#print axioms CryptidLink.L17.a01_sweep_exact
#print axioms CryptidLink.L17.b111_exact
#print axioms CryptidLink.L17.b_to_d_sweep_exact
#print axioms CryptidLink.L17.c2_s2_to_d_exact
#print axioms CryptidLink.L17.d_pair1_sweep_exact
#print axioms CryptidLink.L17.mixed_scanner_0101_exact
#print axioms CryptidLink.L17.mixed_c2_s2_blankleft_exact
#print axioms CryptidLink.L17.mixed_a_blankleft_exact
#print axioms CryptidLink.L17.entryC_exact
#print axioms CryptidLink.L17.k11_exact
#print axioms CryptidLink.L17.a01101_split_exact
#print axioms CryptidLink.L17.entry1101_exact
#print axioms CryptidLink.L17.mixed_original_C_exact
