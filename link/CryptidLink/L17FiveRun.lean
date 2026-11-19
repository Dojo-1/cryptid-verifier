import CryptidLink.L17MixedBoundary

/-! Exact guarded returns for the B dispatcher at 0, 111, 1100, 110100 and homogeneous 1101 scanner continuations. -/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))
private abbrev I := ([1] : List (Fin 2))

private def base (u v : ℕ) : Bits :=
  push [0, 1, 0] (push (P ^ (v + 7)) (push [0] (push (P ^ (u + 6)) default)))

/-- Five spatial runs of widths [u+6,v+7,1,k+6,3], with a terminal 00. -/
def five_run00_source (u v k : ℕ) (R : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (push [0, 1, 0, 1, 0, 1, 0] (push (P ^ (k + 6)) (push [0] (base u v))))
    (push [0, 0] R)

/-- Wide five-run terminal return: the middle K41 transfer exposes the
width-one Cpop guard. The full residual tape is retained. -/
theorem five_run00_wide_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 2 * k + 112)
      (five_run00_source u v k R)
      (Cfg.headRight C default
        (cpop_bottom_result u v
          (push (I ^ (2 * k + 2)) (push returnKtail (push (I ^ 6) R))))) := by
  let Lp := push (P ^ (u + 6)) default
  let S := push returnKtail (push (I ^ 6) R)
  let T := push (I ^ (2 * k + 2)) S
  let L := push (Q ^ (v + 7)) Lp
  have hb : push [0] (base u v) = push [0] (push [0, 1, 0, 0] L) := by
    change push [0] (push [0, 1, 0] (push (P ^ (v + 7)) (push [0] Lp))) =
      push [0] (push [0, 1, 0, 0] L)
    have hr : L = push [1] (push (P ^ (v + 6)) (push [0] Lp)) := by
      change push (Q ^ (v + 7)) Lp = _
      rw [← ListBlank.append_pow_succ' Q (v + 6) Lp]
      exact (rotLB (v + 6) (push [0] Lp)).symm
    rw [hr, ListBlank.append_pow_succ P (v + 6)]
    rfl
  have h1 := a00l_exact (push (P ^ (k + 6)) (push [0] (base u v))) R
  have h2 := k41_c01_middle_exact k (push [0, 1, 0, 0] L) (push (I ^ 6) R)
  rw [← hb] at h2
  have h12 := h1.trans h2
  have ht : push (([1, 1] : List (Fin 2)) ^ (k + 1)) S = T := by
    change push (([1, 1] : List (Fin 2)) ^ (k + 1)) S = push (I ^ (2 * k + 2)) S
    rw [one_pow_two_mul, show 2 * (k + 1) = 2 * k + 2 by omega]
  change ReachesIn target _ _ (Cfg.headLeft C (push [0, 1, 0, 0] L)
    (push (([1, 1] : List (Fin 2)) ^ (k + 1)) S)) at h12
  rw [ht] at h12
  have h3 := cpop_headLeft_exact L T
  have h4 := cpop_bottom_blankleft_exact u v T
  have h := (h12.trans h3).trans h4
  change ReachesIn target _ (five_run00_source u v k R) _ at h
  convert h using 1
  omega

/-- The B dispatcher source preceding a 110100 terminal, with n=k+8. -/
def b110100_wide_source (u v k : ℕ) (R : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (push (Q ^ (k + 8)) (base u v))
    (push [1, 1, 0, 1, 0, 0] R)

/-- Original B source, including the 14-step normalization into five runs.
This adds a full C return for n>=8 with every exterior R preserved. -/
theorem b110100_wide_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 2 * k + 126)
      (b110100_wide_source u v k R)
      (Cfg.headRight C default
        (cpop_bottom_result u v
          (push (I ^ (2 * k + 2)) (push returnKtail (push (I ^ 6) R))))) := by
  let Y := push (Q ^ (k + 6)) (base u v)
  have h1 := short_B1101_exact Y (push [0, 0] R)
  have hs : push [1, 0, 1, 0] Y = push (Q ^ (k + 8)) (base u v) := by
    change push (Q ^ 2) (push (Q ^ (k + 6)) (base u v)) = _
    rw [← ListBlank.append_pow_add, show 2 + (k + 6) = k + 8 by omega]
  rw [hs] at h1
  have he : push [0, 1, 0, 1, 0, 1, 0, 0] Y =
      push [0, 1, 0, 1, 0, 1, 0] (push (P ^ (k + 6)) (push [0] (base u v))) := by
    change push [0, 1, 0, 1, 0, 1, 0] (push [0] (push (Q ^ (k + 6)) (base u v))) = _
    rw [rotLB0]
  rw [he] at h1
  change ReachesIn target 14 (b110100_wide_source u v k R)
    (five_run00_source u v k R) at h1
  have h := h1.trans (five_run00_wide_exact u v k R)
  convert h using 1
  omega


/-- B source at an arbitrary width n (the five-run return requires n ≥ 5). -/
def b110100_source (u v n : ℕ) (R : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (push (Q ^ n) (base u v)) (push [1, 1, 0, 1, 0, 0] R)

/-- Complete outer K41 output, preserving the suffix from the middle run. -/
def five_run_bottom_result (u : ℕ) (S : Bits) : Bits :=
  push [1] (push (([1, 1] : List (Fin 2)) ^ u) (push returnKtail S))

/-- Fixed prefix for width 5. Relative to B, all reads are in [-20,5].
The exit head is one cell farther left, with arbitrary exterior tapes. -/
private theorem b110100_prefix5 (L R : Bits) :
    ReachesIn target 79
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [1, 1, 0, 1, 0, 0] R))
      (Cfg.headRight C L (push [1] (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R))) := by
  set_option maxRecDepth 8192 in
    l17_exact_steps

/-- Complete short width-5 return for every p=u+6 and c=v+7. -/
theorem b110100_n5_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 128)
      (b110100_source u v 5 R)
      (Cfg.headRight C default
        (five_run_bottom_result u
          (push (I ^ (2 * v + 5)) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R)))) := by
  let Lp := push (P ^ (u + 6)) default
  let L := push (P ^ (v + 3)) (push [0] Lp)
  let S := push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R
  have h1 := b110100_prefix5 L R
  have hs : b110100_source u v 5 R =
      Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [1, 1, 0, 1, 0, 0] R) := by
    unfold b110100_source base
    rw [show v + 7 = 4 + (v + 3) by omega,
      ListBlank.append_pow_add P 4 (v + 3)]
    rfl
  rw [← hs] at h1
  have h2 := c01_middle_headRight_exact (v + 3) Lp S
  have h12 := h1.trans h2
  have ho : push (([1, 1] : List (Fin 2)) ^ (v + 3 + 1)) S =
      push [1, 1, 1] (push (I ^ (2 * v + 5)) S) := by
    rw [one_pow_two_mul, show 2 * (v + 3 + 1) = 3 + (2 * v + 5) by omega,
      ListBlank.append_pow_add I 3 (2 * v + 5)]
    rfl
  rw [ho] at h12
  have h := h12.trans (k41_c01_last_exact u default (push (I ^ (2 * v + 5)) S))
  have hframe : Cfg.headLeft C (push [1] default)
      (push (([1, 1] : List (Fin 2)) ^ u) (push returnKtail (push (I ^ (2 * v + 5)) S))) =
      Cfg.headRight C default (five_run_bottom_result u (push (I ^ (2 * v + 5)) S)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hframe] at h
  convert h using 1
  omega

/-- Fixed prefix for width 6. Relative to B, all reads are in [-26,5].
The exit head is one cell farther left, with arbitrary exterior tapes. -/
private theorem b110100_prefix6 (L R : Bits) :
    ReachesIn target 99
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [1, 1, 0, 1, 0, 0] R))
      (Cfg.headRight C L (push [1] (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R))) := by
  set_option maxRecDepth 8192 in
    l17_exact_steps

/-- Complete short width-6 return for every p=u+6 and c=v+7. -/
theorem b110100_n6_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 144)
      (b110100_source u v 6 R)
      (Cfg.headRight C default
        (five_run_bottom_result u
          (push (I ^ (2 * v + 1)) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R)))) := by
  let Lp := push (P ^ (u + 6)) default
  let L := push (P ^ (v + 1)) (push [0] Lp)
  let S := push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R
  have h1 := b110100_prefix6 L R
  have hs : b110100_source u v 6 R =
      Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [1, 1, 0, 1, 0, 0] R) := by
    unfold b110100_source base
    rw [show v + 7 = 6 + (v + 1) by omega,
      ListBlank.append_pow_add P 6 (v + 1)]
    rfl
  rw [← hs] at h1
  have h2 := c01_middle_headRight_exact (v + 1) Lp S
  have h12 := h1.trans h2
  have ho : push (([1, 1] : List (Fin 2)) ^ (v + 1 + 1)) S =
      push [1, 1, 1] (push (I ^ (2 * v + 1)) S) := by
    rw [one_pow_two_mul, show 2 * (v + 1 + 1) = 3 + (2 * v + 1) by omega,
      ListBlank.append_pow_add I 3 (2 * v + 1)]
    rfl
  rw [ho] at h12
  have h := h12.trans (k41_c01_last_exact u default (push (I ^ (2 * v + 1)) S))
  have hframe : Cfg.headLeft C (push [1] default)
      (push (([1, 1] : List (Fin 2)) ^ u) (push returnKtail (push (I ^ (2 * v + 1)) S))) =
      Cfg.headRight C default (five_run_bottom_result u (push (I ^ (2 * v + 1)) S)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hframe] at h
  convert h using 1
  omega

/-- Fixed prefix for width 7. Relative to B, all reads are in [-18,5].
The exit head is one cell farther left, with arbitrary exterior tapes. -/
private theorem b110100_prefix7 (L R : Bits) :
    ReachesIn target 69
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] L)
        (push [1, 1, 0, 1, 0, 0] R))
      (Cfg.headRight C L (push [1] (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R))) := by
  set_option maxRecDepth 8192 in
    l17_exact_steps

/-- Complete short width-7 return for every p=u+6 and c=v+7. -/
theorem b110100_n7_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 124)
      (b110100_source u v 7 R)
      (Cfg.headRight C default
        (five_run_bottom_result u
          (push (I ^ (2 * v + 11)) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R)))) := by
  let Lp := push (P ^ (u + 6)) default
  let L := push (P ^ (v + 6)) (push [0] Lp)
  let S := push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R
  have h1 := b110100_prefix7 L R
  have hs : b110100_source u v 7 R =
      Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] L)
        (push [1, 1, 0, 1, 0, 0] R) := by
    unfold b110100_source base
    rw [show v + 7 = 1 + (v + 6) by omega,
      ListBlank.append_pow_add P 1 (v + 6)]
    rfl
  rw [← hs] at h1
  have h2 := c01_middle_headRight_exact (v + 6) Lp S
  have h12 := h1.trans h2
  have ho : push (([1, 1] : List (Fin 2)) ^ (v + 6 + 1)) S =
      push [1, 1, 1] (push (I ^ (2 * v + 11)) S) := by
    rw [one_pow_two_mul, show 2 * (v + 6 + 1) = 3 + (2 * v + 11) by omega,
      ListBlank.append_pow_add I 3 (2 * v + 11)]
    rfl
  rw [ho] at h12
  have h := h12.trans (k41_c01_last_exact u default (push (I ^ (2 * v + 11)) S))
  have hframe : Cfg.headLeft C (push [1] default)
      (push (([1, 1] : List (Fin 2)) ^ u) (push returnKtail (push (I ^ (2 * v + 11)) S))) =
      Cfg.headRight C default (five_run_bottom_result u (push (I ^ (2 * v + 11)) S)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hframe] at h
  convert h using 1
  omega
/-- Exact transition count, indexed by k=n−5. -/
def b110100_clock (u v : ℕ) : ℕ → ℕ
  | 0 => 2 * u + 2 * v + 128
  | 1 => 2 * u + 2 * v + 144
  | 2 => 2 * u + 2 * v + 124
  | k + 3 => 2 * u + 2 * v + 2 * k + 126

/-- Complete right tape at the blank-left C return, indexed by k=n−5. -/
def b110100_result (u v : ℕ) (R : Bits) : ℕ → Bits
  | 0 => five_run_bottom_result u
          (push (I ^ (2 * v + 5)) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R))
  | 1 => five_run_bottom_result u
          (push (I ^ (2 * v + 1)) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R))
  | 2 => five_run_bottom_result u
          (push (I ^ (2 * v + 11)) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1] R))
  | k + 3 => cpop_bottom_result u v
      (push (I ^ (2 * k + 2)) (push returnKtail (push (I ^ 6) R)))

/-- Exhausts the guarded 110100 row: every n=k+5, p=u+6, c=v+7,
with arbitrary right suffix R. This is a configuration theorem. -/
theorem b110100_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (b110100_clock u v k)
      (b110100_source u v (k + 5) R)
      (Cfg.headRight C default (b110100_result u v R k)) := by
  match k with
  | 0 => exact b110100_n5_exact u v R
  | 1 => exact b110100_n6_exact u v R
  | 2 => exact b110100_n7_exact u v R
  | j + 3 => exact b110100_wide_exact u v j R

private theorem b10_exact (L R : Bits) :
    ReachesIn target 2
      (Cfg.headRight B L (push Q R))
      (Cfg.headRight B (push Q L) R) := by
  l17_exact_steps

/-- In B, each spatial 10 pair becomes 01 as the head moves right.
The written pair is 10 in head-nearest order on the left tape. -/
theorem b10_sweep_exact (j : ℕ) (L R : Bits) :
    ReachesIn target (2 * j)
      (Cfg.headRight B L (push (Q ^ j) R))
      (Cfg.headRight B (push (Q ^ j) L) R) := by
  induction j generalizing L with
  | zero => exact ReachesIn.zero _ _
  | succ j ih =>
    rw [ListBlank.append_pow_succ Q j R]
    have h1 := b10_exact L (push (Q ^ j) R)
    have h2 := ih (push Q L)
    rw [ListBlank.append_pow_succ' Q j L] at h2
    convert h1.trans h2 using 1
    omega

/-- B may scan j more pairs before the terminal; they increase the width
from k+5 to k+j+5. No bound on j or on the arbitrary suffix R is needed. -/
theorem b110100_after_sweep_exact (u v k j : ℕ) (R : Bits) :
    ReachesIn target (2 * j + b110100_clock u v (k + j))
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push (Q ^ j) (push [1, 1, 0, 1, 0, 0] R)))
      (Cfg.headRight C default (b110100_result u v R (k + j))) := by
  have hs := b10_sweep_exact j (push (Q ^ (k + 5)) (base u v))
    (push [1, 1, 0, 1, 0, 0] R)
  rw [← ListBlank.append_pow_add, show j + (k + 5) = k + j + 5 by omega] at hs
  exact hs.trans (b110100_exact u v (k + j) R)

/-- From the C2 entry (previous width 2), B starts with five pairs.
The theorem includes the 38-step entry, the full sweep and the return. -/
theorem c2_110100_after_sweep_exact (u v j : ℕ) (R : Bits) :
    ReachesIn target (38 + (2 * j + b110100_clock u v j))
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] (base u v))
        (push [0, 1, 1, 1] (push (Q ^ j) (push [1, 1, 0, 1, 0, 0] R))))
      (Cfg.headRight C default (b110100_result u v R j)) := by
  have hs := b110100_after_sweep_exact u v 0 j R
  rw [Nat.zero_add j] at hs
  exact (short_C2B_exact (base u v)
    (push (Q ^ j) (push [1, 1, 0, 1, 0, 0] R))).trans hs

/-- From the C5 entry (previous width 3), B starts with nine pairs.
The theorem includes the 62-step entry, the full sweep and the return. -/
theorem c5_110100_after_sweep_exact (u v j : ℕ) (R : Bits) :
    ReachesIn target (62 + (2 * j + b110100_clock u v (4 + j)))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] (base u v))
        (push [0, 1, 1, 1] (push (Q ^ j) (push [1, 1, 0, 1, 0, 0] R))))
      (Cfg.headRight C default (b110100_result u v R (4 + j))) := by
  exact (short_C5B_exact (base u v) (push (Q ^ j) (push [1, 1, 0, 1, 0, 0] R))).trans
    (b110100_after_sweep_exact u v 4 j R)


/-- B source at the 1100 terminal. -/
def b1100_source (u v n : ℕ) (R : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (push (Q ^ n) (base u v)) (push [1, 1, 0, 0] R)

private theorem b1100_finish (u m : ℕ) (S : Bits) :
    ReachesIn target (2 * (m + 2) + (41 + 2 * u))
      (Cfg.headRight C (push (P ^ (m + 1)) (push [0] (push (P ^ (u + 6)) default)))
        (push [1] S))
      (Cfg.headRight C default (five_run_bottom_result u (push (I ^ (2 * m + 1)) S))) := by
  let Lp := push (P ^ (u + 6)) default
  let T := push (I ^ (2 * m + 1)) S
  have h1 := c01_middle_headRight_exact (m + 1) Lp S
  have ho : push (([1, 1] : List (Fin 2)) ^ (m + 2)) S =
      push [1, 1, 1] T := by
    change _ = push [1, 1, 1] (push (I ^ (2 * m + 1)) S)
    rw [one_pow_two_mul, show 2 * (m + 2) = 3 + (2 * m + 1) by omega,
      ListBlank.append_pow_add I 3 (2 * m + 1)]
    rfl
  change ReachesIn target _ _ (Cfg.headLeft C Lp
    (push (([1, 1] : List (Fin 2)) ^ (m + 2)) S)) at h1
  rw [ho] at h1
  have h := h1.trans (k41_c01_last_exact u default T)
  have hf : Cfg.headLeft C (push [1] default)
      (push (([1, 1] : List (Fin 2)) ^ u) (push returnKtail T)) =
      Cfg.headRight C default (five_run_bottom_result u T) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hf] at h
  exact h

private abbrev b1100_tail5 : List (Fin 2) := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1]

/-- Exact width-5 return from the 1100 dispatcher. -/
theorem b1100_n5_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 124)
      (b1100_source u v 5 R)
      (Cfg.headRight C default
        (five_run_bottom_result u (push (I ^ (2 * (v + 2) + 1)) (push b1100_tail5 R)))) := by
  let L := push (P ^ ((v + 2) + 1)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := short_B1100_n5_exact (push [1] L) R
  have hs : b1100_source u v 5 R =
      Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [1, 1, 0, 0] R) := by
    unfold b1100_source base
    rw [show v + 7 = 4 + ((v + 2) + 1) by omega,
      ListBlank.append_pow_add P 4 ((v + 2) + 1)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push b1100_tail5 R) =
      Cfg.headRight C L (push [1] (push b1100_tail5 R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  change ReachesIn target _ _ (Cfg.headLeft C (push [1] L) (push b1100_tail5 R)) at h1
  rw [hf] at h1
  have h := h1.trans (b1100_finish u (v + 2) (push b1100_tail5 R))
  convert h using 1
  omega

private abbrev b1100_tail6 : List (Fin 2) := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1]

/-- Exact width-6 return from the 1100 dispatcher. -/
theorem b1100_n6_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 140)
      (b1100_source u v 6 R)
      (Cfg.headRight C default
        (five_run_bottom_result u (push (I ^ (2 * v + 1)) (push b1100_tail6 R)))) := by
  let L := push (P ^ (v + 1)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := short_B1100_n6_exact (push [1] L) R
  have hs : b1100_source u v 6 R =
      Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [1, 1, 0, 0] R) := by
    unfold b1100_source base
    rw [show v + 7 = 6 + (v + 1) by omega,
      ListBlank.append_pow_add P 6 (v + 1)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push b1100_tail6 R) =
      Cfg.headRight C L (push [1] (push b1100_tail6 R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  change ReachesIn target _ _ (Cfg.headLeft C (push [1] L) (push b1100_tail6 R)) at h1
  rw [hf] at h1
  have h := h1.trans (b1100_finish u v (push b1100_tail6 R))
  convert h using 1
  omega

private abbrev b1100_tail7 : List (Fin 2) := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1]

/-- Exact width-7 return from the 1100 dispatcher. -/
theorem b1100_n7_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 120)
      (b1100_source u v 7 R)
      (Cfg.headRight C default
        (five_run_bottom_result u (push (I ^ (2 * (v + 5) + 1)) (push b1100_tail7 R)))) := by
  let L := push (P ^ ((v + 5) + 1)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := short_B1100_n7_exact (push [1] L) R
  have hs : b1100_source u v 7 R =
      Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0] (push [1] L)) (push [1, 1, 0, 0] R) := by
    unfold b1100_source base
    rw [show v + 7 = 1 + ((v + 5) + 1) by omega,
      ListBlank.append_pow_add P 1 ((v + 5) + 1)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push b1100_tail7 R) =
      Cfg.headRight C L (push [1] (push b1100_tail7 R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  change ReachesIn target _ _ (Cfg.headLeft C (push [1] L) (push b1100_tail7 R)) at h1
  rw [hf] at h1
  have h := h1.trans (b1100_finish u (v + 5) (push b1100_tail7 R))
  convert h using 1
  omega

private abbrev b1100_wide_tail : List (Fin 2) :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1]

/-- B1 followed by the exact 60-step local turn. -/
private theorem b1100_wide_kernel (L R : Bits) :
    ReachesIn target 61
      (Cfg.headRight B
        (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [1, 1, 0, 0] R))
      (Cfg.headRight C L (push [1] (push b1100_wide_tail R))) := by
  set_option maxRecDepth 8192 in
    l17_exact_steps

/-- Exact wide return, with n=k+8. -/
theorem b1100_wide_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 2 * k + 122)
      (b1100_source u v (k + 8) R)
      (Cfg.headRight C default (cpop_bottom_result u v
        (push (I ^ (2 * k + 2)) (push b1100_wide_tail R)))) := by
  let Lp := push (P ^ (u + 6)) default
  let L := push (Q ^ (v + 7)) Lp
  let S := push b1100_wide_tail R
  let T := push (I ^ (2 * k + 2)) S
  have hh : base u v = push [0, 1, 0, 0] L := by
    change push [0, 1, 0] (push (P ^ (v + 7)) (push [0] Lp)) = _
    have hr : L = push [1] (push (P ^ (v + 6)) (push [0] Lp)) := by
      change push (Q ^ (v + 7)) Lp = _
      rw [← ListBlank.append_pow_succ' Q (v + 6) Lp]
      exact (rotLB (v + 6) (push [0] Lp)).symm
    rw [hr, ListBlank.append_pow_succ P (v + 6)]
    rfl
  have h1 := b1100_wide_kernel (push [0] (push (Q ^ k) (base u v))) R
  have hs : b1100_source u v (k + 8) R =
      Cfg.headRight B
        (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
          (push [0] (push (Q ^ k) (base u v))))
        (push [1, 1, 0, 0] R) := by
    unfold b1100_source
    rw [show k + 8 = 8 + k by omega, ListBlank.append_pow_add Q 8 k]
    rfl
  rw [← hs, rotLB0] at h1
  have h := h1.trans (c01_middle_headRight_exact k (base u v) S)
  have ht : push (([1, 1] : List (Fin 2)) ^ (k + 1)) S = T := by
    change _ = push (I ^ (2 * k + 2)) S
    rw [one_pow_two_mul, show 2 * (k + 1) = 2 * k + 2 by omega]
  rw [hh, ht] at h
  have hf := (h.trans (cpop_headLeft_exact L T)).trans
    (cpop_bottom_blankleft_exact u v T)
  convert hf using 1
  omega

/-- Exact terminal clock indexed by k=n−5. -/
def b1100_clock (u v : ℕ) : ℕ → ℕ
  | 0 => 2 * u + 2 * v + 124
  | 1 => 2 * u + 2 * v + 140
  | 2 => 2 * u + 2 * v + 120
  | k + 3 => 2 * u + 2 * v + 2 * k + 122

/-- Full right tape at the 1100 return, indexed by k=n−5. -/
def b1100_result (u v : ℕ) (R : Bits) : ℕ → Bits
  | 0 => five_run_bottom_result u (push (I ^ (2 * (v + 2) + 1)) (push b1100_tail5 R))
  | 1 => five_run_bottom_result u (push (I ^ (2 * v + 1)) (push b1100_tail6 R))
  | 2 => five_run_bottom_result u (push (I ^ (2 * (v + 5) + 1)) (push b1100_tail7 R))
  | k + 3 => cpop_bottom_result u v
      (push (I ^ (2 * k + 2)) (push b1100_wide_tail R))

/-- Exact 1100 return for all widths n≥5. -/
theorem b1100_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (b1100_clock u v k)
      (b1100_source u v (k + 5) R)
      (Cfg.headRight C default (b1100_result u v R k)) := by
  match k with
  | 0 => exact b1100_n5_exact u v R
  | 1 => exact b1100_n6_exact u v R
  | 2 => exact b1100_n7_exact u v R
  | j + 3 => exact b1100_wide_exact u v j R

/-- Include the B sweep and dispatch at the increased width. -/
theorem b1100_after_sweep_exact (u v k j : ℕ) (R : Bits) :
    ReachesIn target (2 * j + b1100_clock u v (k + j))
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push (Q ^ j) (push [1, 1, 0, 0] R)))
      (Cfg.headRight C default (b1100_result u v R (k + j))) := by
  have hs := b10_sweep_exact j (push (Q ^ (k + 5)) (base u v))
    (push [1, 1, 0, 0] R)
  rw [← ListBlank.append_pow_add, show j + (k + 5) = k + j + 5 by omega] at hs
  exact hs.trans (b1100_exact u v (k + j) R)

/-- Include the 38-step C2 entry, the B sweep, and the 1100 return. -/
theorem c2_1100_after_sweep_exact (u v j : ℕ) (R : Bits) :
    ReachesIn target (38 + (2 * j + b1100_clock u v j))
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] (base u v))
        (push [0, 1, 1, 1] (push (Q ^ j) (push [1, 1, 0, 0] R))))
      (Cfg.headRight C default (b1100_result u v R j)) := by
  have hs := b1100_after_sweep_exact u v 0 j R
  rw [Nat.zero_add j] at hs
  exact (short_C2B_exact (base u v)
    (push (Q ^ j) (push [1, 1, 0, 0] R))).trans hs

/-- Include the 62-step C5 entry, the B sweep, and the 1100 return. -/
theorem c5_1100_after_sweep_exact (u v j : ℕ) (R : Bits) :
    ReachesIn target (62 + (2 * j + b1100_clock u v (4 + j)))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] (base u v))
        (push [0, 1, 1, 1] (push (Q ^ j) (push [1, 1, 0, 0] R))))
      (Cfg.headRight C default (b1100_result u v R (4 + j))) := by
  exact (short_C5B_exact (base u v) (push (Q ^ j) (push [1, 1, 0, 0] R))).trans
    (b1100_after_sweep_exact u v 4 j R)

/-- The extra two input cells in 110100 cost exactly four transitions. -/
theorem b110100_clock_eq_b1100_add_four (u v k : ℕ) :
    b110100_clock u v k = b1100_clock u v k + 4 := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 => rfl

/-- Both terminals have the same output prefix, except that 110100
places two additional ones immediately before the unchanged suffix. -/
theorem b110100_result_eq_b1100_with_two (u v k : ℕ) (R : Bits) :
    b110100_result u v R k = b1100_result u v (push [1, 1] R) k := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 => rfl


/-- Exact B0 return from width n=k+5. -/
theorem b_zero_terminal_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 2 * k + 70)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push [0] R))
      (Cfg.headRight C default
        (cpop_bottom_result u v (push (I ^ (2 * k + 11)) R))) := by
  let Lp := push (P ^ (u + 6)) default
  let L := push (Q ^ (v + 7)) Lp
  let S := push (I ^ (2 * k + 11)) R
  have hb : base u v = push [0, 1, 0, 0] L := by
    change push [0, 1, 0] (push (P ^ (v + 7)) (push [0] Lp)) = _
    have hr : L = push [1] (push (P ^ (v + 6)) (push [0] Lp)) := by
      change push (Q ^ (v + 7)) Lp = _
      rw [← ListBlank.append_pow_succ' Q (v + 6) Lp]
      exact (rotLB (v + 6) (push [0] Lp)).symm
    rw [hr, ListBlank.append_pow_succ P (v + 6)]
    rfl
  have h0 (X : Bits) : ReachesIn target 1
      (Cfg.headRight B X (push [0] R))
      (Cfg.headLeft C X (push [1] R)) := by
    l17_exact_steps
  have h := (h0 (push (Q ^ (k + 5)) (base u v))).trans
    (c01_sweep_exact (k + 5) (base u v) (push [1] R))
  have ht : push (([1, 1] : List (Fin 2)) ^ (k + 5)) (push [1] R) = S := by
    change _ = push (I ^ (2 * k + 11)) R
    rw [one_pow_two_mul, ListBlank.append_pow_succ' I (2 * (k + 5)) R,
      show 2 * (k + 5) + 1 = 2 * k + 11 by omega]
  rw [ht] at h
  have hpop := cpop_headLeft_exact L S
  rw [← hb] at hpop
  have hf := (h.trans hpop).trans (cpop_bottom_blankleft_exact u v S)
  convert hf using 1
  omega

/-- Full right tape of the 111 return: a ones run, an alternating run and a final zero. -/
def b_triple_one_result (u v k : ℕ) (R : Bits) : Bits :=
  push (I ^ (2 * u + 6)) (push (P ^ (v + k + 18)) (push [0] R))

private theorem b111_to_outer (u v k : ℕ) (R : Bits) :
    ReachesIn target (4 * (k + 4) + 8 + (4 * (v + 6) + 14))
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push [1, 1, 1] R))
      (Cfg.headLeft D (push [0] (push (P ^ (u + 6)) default))
        (push [1, 0, 1, 0] (push (Q ^ (v + k + 13)) R))) := by
  let L := push [0] (push (P ^ (u + 6)) default)
  have h1 := b_to_d_sweep_exact (k + 4) (base u v) R
  have h2 := d_pair1_sweep_exact (v + 6) (k + 5) L R
  have h := h1.trans h2
  have hr : push (Q ^ (v + 6 + (k + 5) + 4)) R =
      push [1, 0, 1, 0] (push (Q ^ (v + k + 13)) R) := by
    change _ = push (Q ^ 2) (push (Q ^ (v + k + 13)) R)
    rw [← ListBlank.append_pow_add,
      show v + 6 + (k + 5) + 4 = 2 + (v + k + 13) by omega]
  rw [hr] at h
  exact h

private theorem b111_normalize (u v k : ℕ) (R : Bits) :
    push [1] (push (([1, 1] : List (Fin 2)) ^ (u + 2))
      (push (Q ^ 6) (push (Q ^ (v + k + 13)) R))) =
      b_triple_one_result u v k R := by
  have hq : push (Q ^ 6) (push (Q ^ (v + k + 13)) R) =
      push [1] (push (P ^ (v + k + 18)) (push [0] R)) := by
    rw [← ListBlank.append_pow_add, show 6 + (v + k + 13) = v + k + 18 + 1 by omega,
      rotLB (v + k + 18) (push [0] R)]
    exact (ListBlank.append_pow_succ' Q (v + k + 18) R).symm
  rw [hq, one_pow_two_mul]
  unfold b_triple_one_result
  rw [show 2 * u + 6 = 1 + (2 * (u + 2) + 1) by omega,
    ListBlank.append_pow_add I 1 (2 * (u + 2) + 1),
    ← ListBlank.append_pow_succ' I (2 * (u + 2))]
  rfl

private theorem b111_outer (u v k : ℕ) (R : Bits) :
    ReachesIn target (22 + 2 * (u + 2))
      (Cfg.headLeft D (push [0] (push (P ^ (u + 6)) default))
        (push [1, 0, 1, 0] (push (Q ^ (v + k + 13)) R)))
      (Cfg.headRight C default (b_triple_one_result u v k R)) := by
  let T := push (Q ^ (v + k + 13)) R
  let S := push (([1, 1] : List (Fin 2)) ^ (u + 2)) (push (Q ^ 6) T)
  have h : ReachesIn target (22 + 2 * (u + 2))
      (Cfg.headLeft D (push [0] (push (P ^ (u + 6)) default)) (push [1, 0, 1, 0] T))
      (Cfg.headLeft C (push [1] default) S) :=
    k22_c01_last_exact (u + 2) default T
  have he : Cfg.headLeft C (push [1] default) S =
      Cfg.headRight C default (b_triple_one_result u v k R) :=
    (Cfg.headLeft_cons C (1 : Fin 2) default S).trans
      (congrArg (Cfg.headRight C default) (b111_normalize u v k R))
  rw [he] at h
  exact h

/-- Exact B111 return from width n=k+5. -/
theorem b_triple_one_terminal_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 4 * v + 4 * k + 88)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push [1, 1, 1] R))
      (Cfg.headRight C default (b_triple_one_result u v k R)) := by
  have hc : 2 * u + 4 * v + 4 * k + 88 =
      (4 * (k + 4) + 8 + (4 * (v + 6) + 14)) + (22 + 2 * (u + 2)) := by omega
  rw [hc]
  exact (b111_to_outer u v k R).trans (b111_outer u v k R)

/-- Bare 1101 enters A in 14 steps, preserving the whole continuation.
The two zeros are written on the left tape, not assumed on the right. -/
theorem b1101_to_a_exact (u v k : ℕ) (S : Bits) :
    ReachesIn target 14
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push [1, 1, 0, 1] S))
      (Cfg.headRight A
        (push [0, 1, 0, 1, 0, 1, 0] (push (P ^ (k + 3)) (push [0] (base u v)))) S) := by
  let Y := push (Q ^ (k + 3)) (base u v)
  have h := short_B1101_exact Y S
  have hs : push [1, 0, 1, 0] Y = push (Q ^ (k + 5)) (base u v) := by
    change push (Q ^ 2) (push (Q ^ (k + 3)) (base u v)) = _
    rw [← ListBlank.append_pow_add, show 2 + (k + 3) = k + 5 by omega]
  have he : push [0, 1, 0, 1, 0, 1, 0, 0] Y =
      push [0, 1, 0, 1, 0, 1, 0] (push (P ^ (k + 3)) (push [0] (base u v))) := by
    change push [0, 1, 0, 1, 0, 1, 0] (push [0] (push (Q ^ (k + 3)) (base u v))) = _
    rw [rotLB0]
  rw [hs, he] at h
  exact h

private abbrev b1101100_residue (k : ℕ) (R : Bits) : Bits :=
  push (I ^ (2 * k + 6)) (push [1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1] R)

/-- The alternating sweep left after the local scanner's Cpop. -/
private theorem b1101_cpop_sweep (u v k : ℕ) (S : Bits) :
    ReachesIn target (2 * (k + 3))
      (Cfg.headLeft C (push (Q ^ (k + 3)) (base u v)) S)
      (Cfg.headLeft C (base u v) (push (I ^ (2 * k + 6)) S)) := by
  have h := c01_sweep_exact (k + 3) (base u v) S
  rw [one_pow_two_mul, show 2 * (k + 3) = 2 * k + 6 by omega] at h
  exact h

private theorem b1101100_finish (u v : ℕ) (S : Bits) :
    ReachesIn target (4 + (2 * (v + 7) + 41 + 2 * u))
      (Cfg.headLeft C (base u v) S)
      (Cfg.headRight C default (cpop_bottom_result u v S)) := by
  let Lp := push (P ^ (u + 6)) default
  let L := push (Q ^ (v + 7)) Lp
  have hb : base u v = push [0, 1, 0, 0] L := by
    change push [0, 1, 0] (push (P ^ (v + 7)) (push [0] Lp)) = _
    have hr : L = push [1] (push (P ^ (v + 6)) (push [0] Lp)) := by
      change push (Q ^ (v + 7)) Lp = _
      rw [← ListBlank.append_pow_succ' Q (v + 6) Lp]
      exact (rotLB (v + 6) (push [0] Lp)).symm
    rw [hr, ListBlank.append_pow_succ P (v + 6)]
    rfl
  rw [hb]
  exact (cpop_headLeft_exact L S).trans (cpop_bottom_blankleft_exact u v S)

private abbrev scanner101 := ([1, 0, 1] : List (Fin 2))
private abbrev scannerC6 := ([1, 1, 1, 0, 1, 0] : List (Fin 2))

/-- Any even number of 101 tokens followed by 100 returns via Cpop. -/
theorem b1101_even100_exact (u v k h : ℕ) (R : Bits) :
    ReachesIn target (32 * h + 2 * u + 2 * v + 2 * k + 102)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push [1, 1, 0, 1] (push (scanner101 ^ (2 * h)) (push [1, 0, 0] R))))
      (Cfg.headRight C default (cpop_bottom_result u v
        (push (I ^ (2 * k + 6))
          (push [1, 0, 1, 0] (push (scannerC6 ^ h) (push (I ^ 7) R)))))) := by
  let L := push (Q ^ (k + 3)) (base u v)
  let S := push [1, 0, 1, 0] (push (scannerC6 ^ h) (push (I ^ 7) R))
  have hh := b1101_to_a_exact u v k (push (scanner101 ^ (2 * h)) (push [1, 0, 0] R))
  rw [← rotLB0 (k + 3) (base u v)] at hh
  have h1 := a101_100_even_cpop_exact h L R
  have h2 := b1101_cpop_sweep u v k S
  have h3 := b1101100_finish u v (push (I ^ (2 * k + 6)) S)
  convert ((hh.trans h1).trans h2).trans h3 using 1 <;> (first | rfl | omega)

/-- Any odd number of 101 tokens followed by 00 returns via Cpop. -/
theorem b1101_odd00_exact (u v k h : ℕ) (R : Bits) :
    ReachesIn target (32 * h + 2 * u + 2 * v + 2 * k + 106)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push [1, 1, 0, 1] (push (scanner101 ^ (2 * h + 1)) (push [0, 0] R))))
      (Cfg.headRight C default (cpop_bottom_result u v
        (push (I ^ (2 * k + 6))
          (push [1, 0, 1, 0] (push (scannerC6 ^ h) (push (I ^ 9) R)))))) := by
  let L := push (Q ^ (k + 3)) (base u v)
  let S := push [1, 0, 1, 0] (push (scannerC6 ^ h) (push (I ^ 9) R))
  have hh := b1101_to_a_exact u v k (push (scanner101 ^ (2 * h + 1)) (push [0, 0] R))
  rw [← rotLB0 (k + 3) (base u v)] at hh
  have h1 := a101_00_odd_cpop_exact h L R
  have h2 := b1101_cpop_sweep u v k S
  have h3 := b1101100_finish u v (push (I ^ (2 * k + 6)) S)
  convert ((hh.trans h1).trans h2).trans h3 using 1 <;> (first | rfl | omega)

/-- Zero scanner tokens recovers the original 100 continuation. -/
theorem b1101100_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 2 * k + 102)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push [1, 1, 0, 1, 1, 0, 0] R))
      (Cfg.headRight C default (cpop_bottom_result u v (b1101100_residue k R))) := by
  have h := b1101_even100_exact u v k 0 R
  simp only [Nat.mul_zero, Nat.zero_add, list_pow_zero, ListBlank.append_append,
    List.nil_append, b1101100_residue] at h ⊢
  exact h

/-- Common return checkpoint. The three leading right ones belong to
the return path; S begins beyond its local read window. -/
def scannerCutSource (u v k : ℕ) (S : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C (push [0] (push (Q ^ (k + 3)) (base u v))) (push [1, 1, 1] S)

/-- Defined steps from the common checkpoint, indexed by k=n−5. -/
def scannerCutClock (u v : ℕ) : ℕ → ℕ
  | 0 => 2 * u + 2 * v + 104
  | 1 => 2 * u + 2 * v + 120
  | 2 => 2 * u + 2 * v + 100
  | j + 3 => 2 * u + 2 * v + 2 * j + 102

private abbrev scannerWrite5 := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))
private abbrev scannerWrite6 := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))
private abbrev scannerWrite7 := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

/-- The complete return word as a function of the unread checkpoint suffix. -/
def scannerCutResult (u v : ℕ) (S : Bits) : ℕ → Bits
  | 0 => five_run_bottom_result u (push (I ^ (2 * v + 5)) (push scannerWrite5 S))
  | 1 => five_run_bottom_result u (push (I ^ (2 * v + 1)) (push scannerWrite6 S))
  | 2 => five_run_bottom_result u (push (I ^ (2 * v + 11)) (push scannerWrite7 S))
  | j + 3 => cpop_bottom_result u v (push (I ^ (2 * j + 2)) (push returnKtail S))

private theorem scanner_cut_short_finish (u z : ℕ) (S : Bits) :
    ReachesIn target (2 * (z + 2) + (41 + 2 * u))
      (Cfg.headRight C (push (P ^ (z + 1)) (push [0] (push (P ^ (u + 6)) default)))
        (push [1] S))
      (Cfg.headRight C default (five_run_bottom_result u (push (I ^ (2 * z + 1)) S))) := by
  let Lp := push (P ^ (u + 6)) default
  let T := push (I ^ (2 * z + 1)) S
  have h1 := c01_middle_headRight_exact (z + 1) Lp S
  have hw : push (([1, 1] : List (Fin 2)) ^ (z + 1 + 1)) S = push [1, 1, 1] T := by
    rw [one_pow_two_mul, show 2 * (z + 1 + 1) = 3 + (2 * z + 1) by omega,
      ListBlank.append_pow_add I 3 (2 * z + 1)]
    rfl
  rw [hw] at h1
  have h := h1.trans (k41_c01_last_exact u default T)
  have he : Cfg.headLeft C (push [1] default)
      (push (([1, 1] : List (Fin 2)) ^ u) (push returnKtail T)) =
      Cfg.headRight C default (five_run_bottom_result u T) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [he] at h
  exact h

/-- Width 5: 55 steps reading [-16,3] relative to the checkpoint. -/
private theorem scanner_cut_kernel5 (L S : Bits) :
    ReachesIn target 55
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1] S))
      (Cfg.headRight C L (push [1] (push scannerWrite5 S))) := by
  have h : ReachesIn target 55
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1] S))
      (Cfg.headLeft C (push [1] L) (push scannerWrite5 S)) := by
    set_option maxRecDepth 8192 in
      l17_exact_steps
  have hf : Cfg.headLeft C (push [1] L) (push scannerWrite5 S) =
      Cfg.headRight C L (push [1] (push scannerWrite5 S)) :=
    Cfg.headLeft_cons C (1 : Fin 2) L (push scannerWrite5 S)
  rw [hf] at h
  exact h

private theorem scanner_cut_width5 (u v : ℕ) (S : Bits) :
    ReachesIn target (scannerCutClock u v 0) (scannerCutSource u v 0 S)
      (Cfg.headRight C default (scannerCutResult u v S 0)) := by
  let L := push (P ^ (v + 3)) (push [0] (push (P ^ (u + 6)) default))
  have hs : scannerCutSource u v 0 S =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1] S) := by
    unfold scannerCutSource
    have hf : Cfg.headLeft C (push [0] (push (Q ^ (0 + 3)) (base u v))) (push [1, 1, 1] S) =
        Cfg.headRight C (push (Q ^ (0 + 3)) (base u v)) (push [0, 1, 1, 1] S) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 4 + (v + 3) by omega, ListBlank.append_pow_add P 4 (v + 3)]
    rfl
  have h := scanner_cut_kernel5 L S
  rw [← hs] at h
  have hh := scanner_cut_short_finish u (v + 2) (push scannerWrite5 S)
  have ht : 2 * (v + 2) + 1 = 2 * v + 5 := by omega
  rw [ht] at hh
  have he : scannerCutClock u v 0 = 55 + (2 * (v + 2 + 2) + (41 + 2 * u)) := by
    simp only [scannerCutClock]
    omega
  rw [he]
  exact h.trans hh

/-- Width 6: 75 steps reading [-22,3] relative to the checkpoint. -/
private theorem scanner_cut_kernel6 (L S : Bits) :
    ReachesIn target 75
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1] S))
      (Cfg.headRight C L (push [1] (push scannerWrite6 S))) := by
  have h : ReachesIn target 75
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1] S))
      (Cfg.headLeft C (push [1] L) (push scannerWrite6 S)) := by
    set_option maxRecDepth 8192 in
      l17_exact_steps
  have hf : Cfg.headLeft C (push [1] L) (push scannerWrite6 S) =
      Cfg.headRight C L (push [1] (push scannerWrite6 S)) :=
    Cfg.headLeft_cons C (1 : Fin 2) L (push scannerWrite6 S)
  rw [hf] at h
  exact h

private theorem scanner_cut_width6 (u v : ℕ) (S : Bits) :
    ReachesIn target (scannerCutClock u v 1) (scannerCutSource u v 1 S)
      (Cfg.headRight C default (scannerCutResult u v S 1)) := by
  let L := push (P ^ (v + 1)) (push [0] (push (P ^ (u + 6)) default))
  have hs : scannerCutSource u v 1 S =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1] S) := by
    unfold scannerCutSource
    have hf : Cfg.headLeft C (push [0] (push (Q ^ (1 + 3)) (base u v))) (push [1, 1, 1] S) =
        Cfg.headRight C (push (Q ^ (1 + 3)) (base u v)) (push [0, 1, 1, 1] S) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 6 + (v + 1) by omega, ListBlank.append_pow_add P 6 (v + 1)]
    rfl
  have h := scanner_cut_kernel6 L S
  rw [← hs] at h
  have hh := scanner_cut_short_finish u (v + 0) (push scannerWrite6 S)
  have ht : 2 * (v + 0) + 1 = 2 * v + 1 := by omega
  rw [ht] at hh
  have he : scannerCutClock u v 1 = 75 + (2 * (v + 0 + 2) + (41 + 2 * u)) := by
    simp only [scannerCutClock]
    omega
  rw [he]
  exact h.trans hh

/-- Width 7: 45 steps reading [-14,3] relative to the checkpoint. -/
private theorem scanner_cut_kernel7 (L S : Bits) :
    ReachesIn target 45
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0] (push [1] L)) (push [0, 1, 1, 1] S))
      (Cfg.headRight C L (push [1] (push scannerWrite7 S))) := by
  have h : ReachesIn target 45
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0] (push [1] L)) (push [0, 1, 1, 1] S))
      (Cfg.headLeft C (push [1] L) (push scannerWrite7 S)) := by
    set_option maxRecDepth 8192 in
      l17_exact_steps
  have hf : Cfg.headLeft C (push [1] L) (push scannerWrite7 S) =
      Cfg.headRight C L (push [1] (push scannerWrite7 S)) :=
    Cfg.headLeft_cons C (1 : Fin 2) L (push scannerWrite7 S)
  rw [hf] at h
  exact h

private theorem scanner_cut_width7 (u v : ℕ) (S : Bits) :
    ReachesIn target (scannerCutClock u v 2) (scannerCutSource u v 2 S)
      (Cfg.headRight C default (scannerCutResult u v S 2)) := by
  let L := push (P ^ (v + 6)) (push [0] (push (P ^ (u + 6)) default))
  have hs : scannerCutSource u v 2 S =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0] (push [1] L)) (push [0, 1, 1, 1] S) := by
    unfold scannerCutSource
    have hf : Cfg.headLeft C (push [0] (push (Q ^ (2 + 3)) (base u v))) (push [1, 1, 1] S) =
        Cfg.headRight C (push (Q ^ (2 + 3)) (base u v)) (push [0, 1, 1, 1] S) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 1 + (v + 6) by omega, ListBlank.append_pow_add P 1 (v + 6)]
    rfl
  have h := scanner_cut_kernel7 L S
  rw [← hs] at h
  have hh := scanner_cut_short_finish u (v + 5) (push scannerWrite7 S)
  have ht : 2 * (v + 5) + 1 = 2 * v + 11 := by omega
  rw [ht] at hh
  have he : scannerCutClock u v 2 = 45 + (2 * (v + 5 + 2) + (41 + 2 * u)) := by
    simp only [scannerCutClock]
    omega
  rw [he]
  exact h.trans hh

private theorem scanner_cut_wide (u v j : ℕ) (S : Bits) :
    ReachesIn target (scannerCutClock u v (j + 3)) (scannerCutSource u v (j + 3) S)
      (Cfg.headRight C default (scannerCutResult u v S (j + 3))) := by
  have h1 := k41_c01_middle_exact j (base u v) S
  rw [← rotLB0] at h1
  have he : 2 * (j + 1) = 2 * j + 2 := by omega
  rw [one_pow_two_mul, he] at h1
  have h2 := b1101100_finish u v (push (I ^ (2 * j + 2)) (push returnKtail S))
  have ht : scannerCutClock u v (j + 3) =
      (41 + 2 * (j + 1)) + (4 + (2 * (v + 7) + 41 + 2 * u)) := by
    simp only [scannerCutClock]
    omega
  rw [ht]
  exact h1.trans h2

/-- The complete checkpoint return for every guarded width n=k+5. -/
theorem scanner_cut_return_exact (u v k : ℕ) (S : Bits) :
    ReachesIn target (scannerCutClock u v k) (scannerCutSource u v k S)
      (Cfg.headRight C default (scannerCutResult u v S k)) := by
  match k with
  | 0 => exact scanner_cut_width5 u v S
  | 1 => exact scanner_cut_width6 u v S
  | 2 => exact scanner_cut_width7 u v S
  | j + 3 => exact scanner_cut_wide u v j S

/-- The original 110100 route takes 24 steps to enter this checkpoint. -/
theorem scanner_cut_clock_eq (u v k : ℕ) :
    24 + scannerCutClock u v k = b110100_clock u v k := by
  match k with
  | 0 => simp only [scannerCutClock, b110100_clock]; omega
  | 1 => simp only [scannerCutClock, b110100_clock]; omega
  | 2 => simp only [scannerCutClock, b110100_clock]; omega
  | j + 3 => simp only [scannerCutClock, b110100_clock]; omega

/-- The old endpoint is recovered by feeding six extra ones into the cut suffix. -/
theorem scanner_cut_result_eq (u v k : ℕ) (R : Bits) :
    scannerCutResult u v (push (I ^ 6) R) k = b110100_result u v R k := by
  match k with
  | 0 => simp only [scannerCutResult, b110100_result, ListBlank.append_append] <;> rfl
  | 1 => simp only [scannerCutResult, b110100_result, ListBlank.append_append] <;> rfl
  | 2 => simp only [scannerCutResult, b110100_result, ListBlank.append_append] <;> rfl
  | j + 3 => rfl

private abbrev scannerCutSuffix (h e : ℕ) (R : Bits) : Bits :=
  push [0, 1, 0] (push (scannerC6 ^ h) (push (I ^ e) R))

/-- The odd100 scanner and the shared checkpoint give a complete return. -/
theorem b1101_odd100_exact (u v k h : ℕ) (R : Bits) :
    ReachesIn target ((14 + (32 * h + 38)) + scannerCutClock u v k)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push [1, 1, 0, 1] (push (scanner101 ^ (2 * h + 1)) (push [1, 0, 0] R))))
      (Cfg.headRight C default (scannerCutResult u v (scannerCutSuffix h 7 R) k)) := by
  let L := push [0] (push (Q ^ (k + 3)) (base u v))
  have h1 := b1101_to_a_exact u v k (push (scanner101 ^ (2 * h + 1)) (push [1, 0, 0] R))
  rw [← rotLB0 (k + 3) (base u v)] at h1
  have h2 := a101_100_odd_c6_exact h L R
  rw [ListBlank.append_pow_succ] at h2
  have h3 := scanner_cut_return_exact u v k (scannerCutSuffix h 7 R)
  convert (h1.trans h2).trans h3 using 1 <;> (first | rfl | omega)

/-- The positive even00 scanner and the shared checkpoint give a complete return. -/
theorem b1101_positive_even00_exact (u v k h : ℕ) (R : Bits) :
    ReachesIn target ((14 + (32 * h + 42)) + scannerCutClock u v k)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push [1, 1, 0, 1] (push (scanner101 ^ (2 * h + 2)) (push [0, 0] R))))
      (Cfg.headRight C default (scannerCutResult u v (scannerCutSuffix h 9 R) k)) := by
  let L := push [0] (push (Q ^ (k + 3)) (base u v))
  have h1 := b1101_to_a_exact u v k (push (scanner101 ^ (2 * h + 2)) (push [0, 0] R))
  rw [← rotLB0 (k + 3) (base u v)] at h1
  have h2 := a101_00_even_c6_exact h L R
  rw [ListBlank.append_pow_succ] at h2
  have h3 := scanner_cut_return_exact u v k (scannerCutSuffix h 9 R)
  convert (h1.trans h2).trans h3 using 1 <;> (first | rfl | omega)

/-- Terminal words for which this dispatcher proves a full C return. -/
inductive BReturnTerminal where
  | zero | tripleOne | oneOneZeroZero | oneOneZeroOneZeroZero | oneOneZeroOneOneZeroZero
  | scannerEven100 (h : ℕ) | scannerOdd00 (h : ℕ)
  | scannerOdd100 (h : ℕ) | scannerPositiveEven00 (h : ℕ)

def BReturnTerminal.word : BReturnTerminal → List (Fin 2)
  | .zero => [0]
  | .tripleOne => [1, 1, 1]
  | .oneOneZeroZero => [1, 1, 0, 0]
  | .oneOneZeroOneZeroZero => [1, 1, 0, 1, 0, 0]
  | .oneOneZeroOneOneZeroZero => [1, 1, 0, 1, 1, 0, 0]
  | .scannerEven100 h => [1, 1, 0, 1] ++ (scanner101 ^ (2 * h) ++ [1, 0, 0])
  | .scannerOdd00 h => [1, 1, 0, 1] ++ (scanner101 ^ (2 * h + 1) ++ [0, 0])

  | .scannerOdd100 h => [1, 1, 0, 1] ++ (scanner101 ^ (2 * h + 1) ++ [1, 0, 0])
  | .scannerPositiveEven00 h => [1, 1, 0, 1] ++ (scanner101 ^ (2 * h + 2) ++ [0, 0])

def BReturnTerminal.clock (t : BReturnTerminal) (u v k : ℕ) : ℕ :=
  match t with
  | .zero => 2 * u + 2 * v + 2 * k + 70
  | .tripleOne => 2 * u + 4 * v + 4 * k + 88
  | .oneOneZeroZero => b1100_clock u v k
  | .oneOneZeroOneZeroZero => b110100_clock u v k
  | .oneOneZeroOneOneZeroZero => 2 * u + 2 * v + 2 * k + 102
  | .scannerEven100 h => 32 * h + 2 * u + 2 * v + 2 * k + 102
  | .scannerOdd00 h => 32 * h + 2 * u + 2 * v + 2 * k + 106

  | .scannerOdd100 h => (14 + (32 * h + 38)) + scannerCutClock u v k
  | .scannerPositiveEven00 h => (14 + (32 * h + 42)) + scannerCutClock u v k

def BReturnTerminal.result (t : BReturnTerminal) (u v k : ℕ) (R : Bits) : Bits :=
  match t with
  | .zero => cpop_bottom_result u v (push (I ^ (2 * k + 11)) R)
  | .tripleOne => b_triple_one_result u v k R
  | .oneOneZeroZero => b1100_result u v R k
  | .oneOneZeroOneZeroZero => b110100_result u v R k
  | .oneOneZeroOneOneZeroZero => cpop_bottom_result u v (b1101100_residue k R)

  | .scannerEven100 h => cpop_bottom_result u v
      (push (I ^ (2 * k + 6))
        (push [1, 0, 1, 0] (push (scannerC6 ^ h) (push (I ^ 7) R))))
  | .scannerOdd00 h => cpop_bottom_result u v
      (push (I ^ (2 * k + 6))
        (push [1, 0, 1, 0] (push (scannerC6 ^ h) (push (I ^ 9) R))))

  | .scannerOdd100 h => scannerCutResult u v (scannerCutSuffix h 7 R) k
  | .scannerPositiveEven00 h => scannerCutResult u v (scannerCutSuffix h 9 R) k

/-- Exact return at any of the verified terminal families. -/
theorem b_return_terminal_exact (t : BReturnTerminal) (u v k : ℕ) (R : Bits) :
    ReachesIn target (t.clock u v k)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push t.word R))
      (Cfg.headRight C default (t.result u v k R)) := by
  cases t
  · exact b_zero_terminal_exact u v k R
  · exact b_triple_one_terminal_exact u v k R
  · exact b1100_exact u v k R
  · exact b110100_exact u v k R
  · exact b1101100_exact u v k R
  · rename_i h
    simpa only [BReturnTerminal.word, BReturnTerminal.clock, BReturnTerminal.result,
      ListBlank.append_append] using b1101_even100_exact u v k h R
  · rename_i h
    simpa only [BReturnTerminal.word, BReturnTerminal.clock, BReturnTerminal.result,
      ListBlank.append_append] using b1101_odd00_exact u v k h R

  · rename_i h
    simpa only [BReturnTerminal.word, BReturnTerminal.clock, BReturnTerminal.result,
      ListBlank.append_append] using b1101_odd100_exact u v k h R
  · rename_i h
    simpa only [BReturnTerminal.word, BReturnTerminal.clock, BReturnTerminal.result,
      ListBlank.append_append] using b1101_positive_even00_exact u v k h R

/-- Scan j alternating pairs in B and dispatch at the resulting width. -/
theorem b_return_after_sweep_exact (t : BReturnTerminal) (u v k j : ℕ) (R : Bits) :
    ReachesIn target (2 * j + t.clock u v (k + j))
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push (Q ^ j) (push t.word R)))
      (Cfg.headRight C default (t.result u v (k + j) R)) := by
  have hs := b10_sweep_exact j (push (Q ^ (k + 5)) (base u v)) (push t.word R)
  rw [← ListBlank.append_pow_add, show j + (k + 5) = k + j + 5 by omega] at hs
  exact hs.trans (b_return_terminal_exact t u v (k + j) R)

/-- Any verified terminal return, including the 38-step C2 handoff. -/
theorem c2_b_return_exact (t : BReturnTerminal) (u v j : ℕ) (R : Bits) :
    ReachesIn target (38 + (2 * j + t.clock u v j))
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] (base u v))
        (push [0, 1, 1, 1] (push (Q ^ j) (push t.word R))))
      (Cfg.headRight C default (t.result u v j R)) := by
  have hs := b_return_after_sweep_exact t u v 0 j R
  rw [Nat.zero_add j] at hs
  exact (short_C2B_exact (base u v) (push (Q ^ j) (push t.word R))).trans hs

/-- Any verified terminal return, including the 62-step C5 handoff. -/
theorem c5_b_return_exact (t : BReturnTerminal) (u v j : ℕ) (R : Bits) :
    ReachesIn target (62 + (2 * j + t.clock u v (4 + j)))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] (base u v))
        (push [0, 1, 1, 1] (push (Q ^ j) (push t.word R))))
      (Cfg.headRight C default (t.result u v (4 + j) R)) := by
  exact (short_C5B_exact (base u v) (push (Q ^ j) (push t.word R))).trans
    (b_return_after_sweep_exact t u v 4 j R)

end CryptidLink.L17

#print axioms CryptidLink.L17.five_run00_wide_exact
#print axioms CryptidLink.L17.b110100_wide_exact
#print axioms CryptidLink.L17.b110100_n5_exact
#print axioms CryptidLink.L17.b110100_n6_exact
#print axioms CryptidLink.L17.b110100_n7_exact
#print axioms CryptidLink.L17.b110100_exact
#print axioms CryptidLink.L17.b10_sweep_exact
#print axioms CryptidLink.L17.b110100_after_sweep_exact
#print axioms CryptidLink.L17.c2_110100_after_sweep_exact
#print axioms CryptidLink.L17.c5_110100_after_sweep_exact
#print axioms CryptidLink.L17.b1100_n5_exact
#print axioms CryptidLink.L17.b1100_n6_exact
#print axioms CryptidLink.L17.b1100_n7_exact
#print axioms CryptidLink.L17.b1100_wide_exact
#print axioms CryptidLink.L17.b1100_exact
#print axioms CryptidLink.L17.b1100_after_sweep_exact
#print axioms CryptidLink.L17.c2_1100_after_sweep_exact
#print axioms CryptidLink.L17.c5_1100_after_sweep_exact
#print axioms CryptidLink.L17.b110100_clock_eq_b1100_add_four
#print axioms CryptidLink.L17.b110100_result_eq_b1100_with_two
#print axioms CryptidLink.L17.b_zero_terminal_exact
#print axioms CryptidLink.L17.b_triple_one_terminal_exact
#print axioms CryptidLink.L17.b_return_terminal_exact
#print axioms CryptidLink.L17.b_return_after_sweep_exact
#print axioms CryptidLink.L17.c2_b_return_exact
#print axioms CryptidLink.L17.c5_b_return_exact
#print axioms CryptidLink.L17.b1101_to_a_exact
#print axioms CryptidLink.L17.b1101100_exact

#print axioms CryptidLink.L17.b1101_even100_exact
#print axioms CryptidLink.L17.b1101_odd00_exact

#print axioms CryptidLink.L17.scanner_cut_return_exact
#print axioms CryptidLink.L17.b1101_odd100_exact
#print axioms CryptidLink.L17.b1101_positive_even00_exact

#print axioms CryptidLink.L17.scanner_cut_clock_eq
#print axioms CryptidLink.L17.scanner_cut_result_eq
