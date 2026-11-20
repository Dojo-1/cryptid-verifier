import CryptidLink.L17Interleaved

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

/-- Scanner families for which an initial block of 01 pairs can be
returned through the shared C checkpoint. -/
inductive PrefixedScanner where
  | zero00
  | odd100 (h : ℕ)
  | positiveEven00 (h : ℕ)
  | wideEven100 (h : ℕ)
  | wideOdd00 (h : ℕ)

def PrefixedScanner.prefixLen : PrefixedScanner → ℕ → ℕ
  | .wideEven100 _, j | .wideOdd00 _, j => j + 5
  | _, j => j

def PrefixedScanner.repeatCount : PrefixedScanner → ℕ
  | .zero00 => 0
  | .odd100 h | .wideOdd00 h => 2 * h + 1
  | .positiveEven00 h => 2 * h + 2
  | .wideEven100 h => 2 * h

def PrefixedScanner.terminator : PrefixedScanner → List (Fin 2)
  | .odd100 _ | .wideEven100 _ => [1, 0, 0]
  | _ => [0, 0]

def PrefixedScanner.word (t : PrefixedScanner) (j : ℕ) : List (Fin 2) :=
  [1, 1, 0, 1] ++ (P ^ (t.prefixLen j) ++ (scanner101 ^ t.repeatCount ++ t.terminator))

def PrefixedScanner.clockToCut (t : PrefixedScanner) (j : ℕ) : ℕ :=
  4 * j + match t with
    | .zero00 => 24
    | .odd100 h => 32 * h + 52
    | .positiveEven00 h => 32 * h + 56
    | .wideEven100 h => 32 * h + 86
    | .wideOdd00 h => 32 * h + 90

private def scannerGuardTail (h e : ℕ) (R : Bits) : Bits :=
  match h with
  | 0 => push (I ^ e) R
  | l + 1 => scannerCutSuffix l (e + 3) R

private def scannerWideSuffix (j : ℕ) (S : Bits) : Bits :=
  match j with
  | 0 => push (0 :: Q ^ 6) S
  | l + 1 => push (I ^ (2 * l + 1)) (push returnKtail S)

def PrefixedScanner.cutSuffix (t : PrefixedScanner) (j : ℕ) (R : Bits) : Bits :=
  match t with
  | .zero00 => push (I ^ (2 * j)) (push (I ^ 6) R)
  | .odd100 h => push (I ^ (2 * j)) (scannerCutSuffix h 7 R)
  | .positiveEven00 h => push (I ^ (2 * j)) (scannerCutSuffix h 9 R)
  | .wideEven100 h => scannerWideSuffix j (scannerGuardTail h 4 R)
  | .wideOdd00 h => scannerWideSuffix j (scannerGuardTail h 6 R)

private abbrev prefixA := ([0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

private theorem prefix_a_transport (j : ℕ) (L : Bits) :
    push (P ^ j) (push prefixA L) = push prefixA (push (Q ^ j) L) := by
  change push (P ^ j) (push (P ^ 3) (push [0] L)) =
    push (P ^ 3) (push [0] (push (Q ^ j) L))
  rw [rotLB0 j L, ← ListBlank.append_pow_add, ← ListBlank.append_pow_add, Nat.add_comm j 3]

private theorem b1101_prefix_to_a_context (L : Bits) (j : ℕ) (S : Bits) :
    ReachesIn target (14 + 2 * j)
      (Cfg.headRight B (push (Q ^ 2) L) (push [1, 1, 0, 1] (push (P ^ j) S)))
      (Cfg.headRight A (push prefixA (push (Q ^ j) (push [0] L))) S) := by
  have h1 := short_B1101_exact L (push (P ^ j) S)
  have h2 := a01_sweep_exact j (push prefixA (push [0] L)) S
  rw [prefix_a_transport] at h2
  exact h1.trans h2

private theorem b1101_prefix_to_a (u v k j : ℕ) (S : Bits) :
    ReachesIn target (14 + 2 * j)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push [1, 1, 0, 1] (push (P ^ j) S)))
      (Cfg.headRight A (push prefixA (push (Q ^ j) (push [0] (push (Q ^ (k + 3)) (base u v))))) S) := by
  have h := b1101_prefix_to_a_context (push (Q ^ (k + 3)) (base u v)) j S
  rw [← ListBlank.append_pow_add, show 2 + (k + 3) = k + 5 by omega] at h
  exact h

private theorem prefix_c_sweep (j : ℕ) (L S : Bits) :
    ReachesIn target (2 * j)
      (Cfg.headLeft C (push (Q ^ j) L) (push [1, 1, 1] S))
      (Cfg.headLeft C L (push [1, 1, 1] (push (I ^ (2 * j)) S))) := by
  have h := c01_sweep_exact j L (push [1, 1, 1] S)
  rw [one_pow_two_mul] at h
  have he : push (I ^ (2 * j)) (push [1, 1, 1] S) =
      push [1, 1, 1] (push (I ^ (2 * j)) S) := by
    change push (I ^ (2 * j)) (push (I ^ 3) S) = push (I ^ 3) (push (I ^ (2 * j)) S)
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add, Nat.add_comm (2 * j) 3]
  rw [he] at h
  exact h

private theorem prefix_wide_c_sweep (j : ℕ) (L S : Bits) :
    ReachesIn target (41 + 2 * (j + 1))
      (Cfg.headLeft C (push [0, 1, 0] (push (Q ^ (j + 5)) L)) (push [1, 1, 1] S))
      (Cfg.headLeft C L (push [1, 1, 1] (scannerWideSuffix j S))) := by
  have h := k41_c01_middle_exact j L S
  have hl : push [0, 1, 0] (push (Q ^ (j + 5)) L) =
      push (P ^ (j + 6)) (push [0] L) := by
    change push P (push [0] (push (Q ^ (j + 5)) L)) = _
    rw [rotLB0]
    change push (P ^ 1) (push (P ^ (j + 5)) (push [0] L)) = _
    rw [← ListBlank.append_pow_add, show 1 + (j + 5) = j + 6 by omega]
  have hr : push (([1, 1] : List (Fin 2)) ^ (j + 1)) (push returnKtail S) =
      push [1, 1, 1] (scannerWideSuffix j S) := by
    rw [one_pow_two_mul]
    cases j with
    | zero =>
      simp only [scannerWideSuffix, ListBlank.append_append]
      rfl
    | succ j =>
      rw [show 2 * (j + 1 + 1) = 3 + (2 * j + 1) by omega, ListBlank.append_pow_add]
      rfl
  rw [← hl] at h
  change ReachesIn target _ _ (Cfg.headLeft C L
    (push (([1, 1] : List (Fin 2)) ^ (j + 1)) (push returnKtail S))) at h
  rw [hr] at h
  exact h

/-- Transfer one pair left of A into its right guard. Read window [-1,1]. -/
private theorem pair_a_transfer (L R : Bits) :
    ReachesIn target 4
      (Cfg.headRight A (push [0, 1] L) (push [1, 1, 1] R))
      (Cfg.headRight A L (push [1, 1, 1, 0, 1] R)) := by
  set_option maxRecDepth 8192 in
    set_option maxHeartbeats 3000000 in
      l17_exact_steps

private theorem pair_a_sweep (p : ℕ) (L R : Bits) :
    ReachesIn target (4 * p)
      (Cfg.headRight A (push (P ^ p) L) (push [1, 1, 1] R))
      (Cfg.headRight A L (push [1, 1, 1] (push (P ^ p) R))) := by
  induction p generalizing R with
  | zero => simpa only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil] using
      ReachesIn.zero target (Cfg.headRight A L (push [1, 1, 1] R))
  | succ p ih =>
    have h := pair_a_transfer (push (P ^ p) L) R
    change ReachesIn target 4 (Cfg.headRight A (push P (push (P ^ p) L)) (push [1, 1, 1] R))
      (Cfg.headRight A (push (P ^ p) L) (push [1, 1, 1] (push P R))) at h
    have hh := h.trans (ih (push P R))
    rw [← ListBlank.append_pow_succ P p L, ListBlank.append_pow_comm P p R,
      ← ListBlank.append_pow_succ P p R, show 4 + 4 * p = 4 * (p + 1) by omega] at hh
    exact hh

/-- Expose the middle pair run. Read window [-7,3]. -/
private theorem short_two_entry (L R : Bits) :
    ReachesIn target 30
      (Cfg.headLeft C (push [0, 1, 0, 1, 0, 1, 0, 0, 1] L) (push [1, 1, 1] R))
      (Cfg.headRight A L (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  l17_exact_steps

/-- Restore C after the middle sweep. Read window [-9,1]. -/
private theorem short_two_exit (L R : Bits) :
    ReachesIn target 18
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 0, 1, 0] L) (push [1, 1] R))
      (Cfg.headLeft C L (push [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] R)) := by
  l17_exact_steps

private def shortTwoResidue (j : ℕ) (R : Bits) : Bits :=
  push [0, 1, 1, 0, 1, 0, 1, 0, 1]
    (push (P ^ j) (push [0, 1, 0, 1, 0, 1, 0, 1, 0] R))

/-- An interleaving with a variable middle run, in head-nearest-first order
X Q² X Q^j X Q X, restoring the same 111 guard. -/
private theorem short_two_exact (j : ℕ) (L R : Bits) :
    ReachesIn target (48 + 4 * j)
      (Cfg.headLeft C (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0]
        (push (Q ^ j) (push [0, 1, 0, 1, 0, 0, 1, 0] L))) (push [1, 1, 1] R))
      (Cfg.headLeft C L (push [1, 1, 1] (shortTwoResidue j R))) := by
  let X := push [0, 1, 0, 1, 0, 0, 1, 0] L
  let W := push [0, 1, 0, 1, 0, 1, 0, 1, 0] R
  have h1 := short_two_entry (push [0] (push (Q ^ j) X)) R
  have h2 := pair_a_sweep j (push [0] X) W
  rw [← rotLB0 j X] at h2
  have h3 := short_two_exit L (push [1] (push (P ^ j) W))
  convert (h1.trans h2).trans h3 using 1 <;> (first | rfl | omega)

/-- Blocks listed in C processing order, nearest the head first.
The input scanner reads the blocks in the opposite order. -/
inductive ReturnBlock where
  | pair | double | bridge | wide (extra : ℕ) | shortTwo (middle : ℕ)

/-- Scanner tokens in forward (A scan) order for a single C block. -/
def ReturnBlock.tokens : ReturnBlock → List ScannerToken
  | .pair => [.a01]
  | .double => [.a101, .a101]
  | .bridge => [.a101, .a01, .a01, .a01, .a101]
  | .wide j => List.replicate (j + 5) .a01 ++ [.a101]
  | .shortTwo j => [.a101, .a01, .a101] ++
      (List.replicate j .a01 ++ [.a101, .a01, .a01, .a101])

def ReturnBlock.clock : ReturnBlock → ℕ
  | .pair => 2
  | .double => 6
  | .bridge => 34
  | .wide j => 41 + 2 * (j + 1)
  | .shortTwo j => 48 + 4 * j

/-- The output after the three leading ones needed by the next block. -/
def ReturnBlock.output (R : Bits) : ReturnBlock → Bits
  | .pair => push [1, 1] R
  | .double => push [0, 1, 0] (push [1, 1, 1] R)
  | .bridge => push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R
  | .wide j => scannerWideSuffix j R
  | .shortTwo j => shortTwoResidue j R

def returnBlockTokens : List ReturnBlock → List ScannerToken
  | [] => []
  | b :: bs => returnBlockTokens bs ++ b.tokens

def returnBlockClock : List ReturnBlock → ℕ
  | [] => 0
  | b :: bs => b.clock + returnBlockClock bs

def returnBlockOutput (R : Bits) : List ReturnBlock → Bits
  | [] => R
  | b :: bs => returnBlockOutput (b.output R) bs

private theorem scanner_deposit_append (L : Bits) (s t : List ScannerToken) :
    scannerDeposit L (s ++ t) = scannerDeposit (scannerDeposit L s) t := by
  induction s generalizing L with
  | nil => rfl
  | cons a s ih => exact ih (push a.deposit L)

private theorem scanner_deposit_pairs (L : Bits) (n : ℕ) :
    scannerDeposit L (List.replicate n .a01) = push (Q ^ n) L := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change scannerDeposit (push Q L) (List.replicate n .a01) = _
    rw [ih, ListBlank.append_pow_comm, ListBlank.append_pow_succ]

/-- A genuinely interleaved block: no cells of L or R are read. -/
private theorem return_bridge_exact (L R : Bits) :
    ReachesIn target 34
      (Cfg.headLeft C (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0] L) (push [1, 1, 1] R))
      (Cfg.headLeft C L (push [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  l17_exact_steps

private theorem return_block_exact (b : ReturnBlock) (L R : Bits) :
    ReachesIn target b.clock
      (Cfg.headLeft C (scannerDeposit L b.tokens) (push [1, 1, 1] R))
      (Cfg.headLeft C L (push [1, 1, 1] (b.output R))) := by
  cases b with
  | pair => exact prefix_c_sweep 1 L R
  | double => exact c6_sweep_exact 1 L (push [1, 1, 1] R)
  | bridge => exact return_bridge_exact L R
  | wide j =>
    simp only [ReturnBlock.tokens, scanner_deposit_append, scanner_deposit_pairs, scannerDeposit,
      ScannerToken.deposit, ReturnBlock.clock, ReturnBlock.output]
    exact prefix_wide_c_sweep j L R
  | shortTwo j =>
    simp only [ReturnBlock.tokens, scanner_deposit_append, scanner_deposit_pairs, scannerDeposit,
      ScannerToken.deposit, ReturnBlock.clock, ReturnBlock.output]
    exact short_two_exact j L R

/-- Every finite concatenation of return blocks is consumed. Each block
restores the very same three-one guard for the following block. -/
theorem return_blocks_exact (bs : List ReturnBlock) (L R : Bits) :
    ReachesIn target (returnBlockClock bs)
      (Cfg.headLeft C (scannerDeposit L (returnBlockTokens bs)) (push [1, 1, 1] R))
      (Cfg.headLeft C L (push [1, 1, 1] (returnBlockOutput R bs))) := by
  induction bs generalizing R with
  | nil => exact ReachesIn.zero _ _
  | cons b bs ih =>
    simp only [returnBlockTokens, scanner_deposit_append, returnBlockClock, returnBlockOutput]
    exact (return_block_exact b (scannerDeposit L (returnBlockTokens bs)) R).trans (ih (b.output R))

/-- Both scanner stops supply the three-one guard. The 100 stop also
deposits one extra 101 token, which must participate in the block grammar. -/
inductive ReturnTerm where
  | zero | hundred

def ReturnTerm.word : ReturnTerm → List (Fin 2)
  | .zero => [0, 0]
  | .hundred => [1, 0, 0]

def ReturnTerm.extra : ReturnTerm → List ScannerToken
  | .zero => []
  | .hundred => [.a101]

def ReturnTerm.clock : ReturnTerm → ℕ
  | .zero => 10
  | .hundred => 19

def ReturnTerm.residue (R : Bits) : ReturnTerm → Bits
  | .zero => push (I ^ 6) R
  | .hundred => push (I ^ 4) R

private theorem b_scanner_term_exact (term : ReturnTerm) (ts : List ScannerToken) (L R : Bits) :
    ReachesIn target (14 + (scannerSteps ts + term.clock))
      (Cfg.headRight B (push (Q ^ 2) L)
        (push [1, 1, 0, 1] (push (scannerInput ts) (push term.word R))))
      (Cfg.headLeft C (scannerDeposit (push [0] L) (ts ++ term.extra))
        (push [1, 1, 1] (term.residue R))) := by
  cases term with
  | zero =>
    rw [ReturnTerm.extra, List.append_nil]
    exact b_mixed_scan_00_exact ts L R
  | hundred =>
    rw [ReturnTerm.extra, scanner_deposit_append]
    exact b_mixed_scan_100_exact ts L R

/-- Complete B-to-C return whenever the reversed scanner deposits admit
the block grammar. The result retains the whole right tape and exact clock. -/
theorem b_return_blocks_exact (term : ReturnTerm) (ts : List ScannerToken)
    (bs : List ReturnBlock) (u v k : ℕ) (R : Bits)
    (hg : ts ++ term.extra = returnBlockTokens bs) :
    ReachesIn target
      ((14 + (scannerSteps ts + term.clock)) + returnBlockClock bs + scannerCutClock u v k)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push [1, 1, 0, 1] (push (scannerInput ts) (push term.word R))))
      (Cfg.headRight C default
        (scannerCutResult u v (returnBlockOutput (term.residue R) bs) k)) := by
  let L := push (Q ^ (k + 3)) (base u v)
  let S := returnBlockOutput (term.residue R) bs
  have ha := b_scanner_term_exact term ts L R
  rw [hg, ← ListBlank.append_pow_add, show 2 + (k + 3) = k + 5 by omega] at ha
  have hb := return_blocks_exact bs (push [0] L) (term.residue R)
  exact (ha.trans hb).trans (scanner_cut_return_exact u v k S)

private theorem scanner_input_append (s t : List ScannerToken) :
    scannerInput (s ++ t) = scannerInput s ++ scannerInput t := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.cons_append, scannerInput, ih, List.append_assoc]

private theorem scanner_steps_append (s t : List ScannerToken) :
    scannerSteps (s ++ t) = scannerSteps s + scannerSteps t := by
  induction s with
  | nil => simp only [List.nil_append, scannerSteps, Nat.zero_add]
  | cons a s ih => simp only [List.cons_append, scannerSteps, ih, Nat.add_assoc]

/-- The mixed handoff adds five virtual pairs at the start of the A scan.
A block parse of those deposits gives a complete exact return at n=k+6. -/
theorem mixed_return_blocks_exact (term : ReturnTerm) (ts : List ScannerToken)
    (bs : List ReturnBlock) (u v k : ℕ) (R : Bits)
    (hg : (List.replicate 5 .a01 ++ ts) ++ term.extra = returnBlockTokens bs) :
    ReachesIn target
      (136 + (scannerSteps ts + term.clock + returnBlockClock bs + scannerCutClock u v k))
      (Cfg.headRight B (push (Q ^ (k + 6)) (base u v))
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] (push (scannerInput ts) (push term.word R))))
      (Cfg.headRight C default
        (scannerCutResult u v (returnBlockOutput (term.residue R) bs) k)) := by
  let five : List ScannerToken := List.replicate 5 .a01
  let L := push (Q ^ (k + 3)) (base u v)
  let W := push (scannerInput ts) (push term.word R)
  let Y := Cfg.headRight C default (scannerCutResult u v (returnBlockOutput (term.residue R) bs) k)
  let N := scannerSteps ts + term.clock + returnBlockClock bs + scannerCutClock u v k
  have ha := b_return_blocks_exact term (five ++ ts) bs u v k R hg
  rw [scanner_steps_append, scanner_input_append, ← ListBlank.append_append] at ha
  have ht := mixed_suffix_transport L W Y N
  have he2 : push [1, 0, 1, 0] L = push (Q ^ (k + 5)) (base u v) := by
    change push (Q ^ 2) (push (Q ^ (k + 3)) (base u v)) = _
    rw [← ListBlank.append_pow_add, show 2 + (k + 3) = k + 5 by omega]
  have he3 : push [1, 0, 1, 0, 1, 0] L = push (Q ^ (k + 6)) (base u v) := by
    change push (Q ^ 3) (push (Q ^ (k + 3)) (base u v)) = _
    rw [← ListBlank.append_pow_add, show 3 + (k + 3) = k + 6 by omega]
  rw [he2, he3] at ht
  apply ht.mpr
  have htime : (14 + (scannerSteps five + scannerSteps ts + term.clock)) +
      returnBlockClock bs + scannerCutClock u v k = 24 + N := by
    change (14 + (10 + scannerSteps ts + term.clock)) +
      returnBlockClock bs + scannerCutClock u v k = 24 + N
    dsimp only [N]
    omega
  rw [htime] at ha
  exact ha

private theorem scanner_guard_split (h e : ℕ) (R : Bits) :
    push (scannerC6 ^ h) (push (I ^ (e + 3)) R) =
      push [1, 1, 1] (scannerGuardTail h e R) := by
  cases h with
  | zero =>
    rw [list_pow_zero, ListBlank.append_nil, show e + 3 = 3 + e by omega,
      ListBlank.append_pow_add]
    rfl
  | succ h =>
    rw [ListBlank.append_pow_succ]
    simp only [scannerGuardTail, ListBlank.append_append]
    rfl

/-- The scanner checkpoint and clock do not depend on the exterior left tape. -/
private theorem b1101_prefixed_to_cut_context (t : PrefixedScanner) (X : Bits) (j : ℕ) (R : Bits) :
    ReachesIn target (t.clockToCut j)
      (Cfg.headRight B (push (Q ^ 2) X) (push (t.word j) R))
      (Cfg.headLeft C (push [0] X) (push [1, 1, 1] (t.cutSuffix j R))) := by
  let L := push [0] X
  have h1 := b1101_prefix_to_a_context X (t.prefixLen j)
    (push (scanner101 ^ t.repeatCount) (push t.terminator R))
  cases t
  · simp only [PrefixedScanner.prefixLen, PrefixedScanner.repeatCount,
      PrefixedScanner.terminator, list_pow_zero, ListBlank.append_nil] at h1
    have h2 := a00l_exact (push (Q ^ j) L) R
    have h3 := prefix_c_sweep j L (push (I ^ 6) R)
    have hc : PrefixedScanner.clockToCut .zero00 j = (14 + 2 * j + 10) + 2 * j := by
      simp only [PrefixedScanner.clockToCut]; omega
    rw [hc]
    have hh := (h1.trans h2).trans h3
    simp only [PrefixedScanner.word, PrefixedScanner.prefixLen, PrefixedScanner.repeatCount,
      PrefixedScanner.terminator, list_pow_zero, List.nil_append,
      PrefixedScanner.cutSuffix, ListBlank.append_append] at hh ⊢
    exact hh
  · rename_i h
    have h2 := a101_100_odd_c6_exact h (push (Q ^ j) L) R
    rw [ListBlank.append_pow_succ] at h2
    have h3 := prefix_c_sweep j L (scannerCutSuffix h 7 R)
    have hh := (h1.trans h2).trans h3
    simp (config := { failIfUnchanged := false }) only [PrefixedScanner.word,
      PrefixedScanner.prefixLen, PrefixedScanner.repeatCount, PrefixedScanner.terminator,
      PrefixedScanner.cutSuffix, ListBlank.append_append] at hh ⊢
    convert hh using 1 <;> (first | rfl | (simp only [PrefixedScanner.clockToCut]; omega))
  · rename_i h
    have h2 := a101_00_even_c6_exact h (push (Q ^ j) L) R
    rw [ListBlank.append_pow_succ] at h2
    have h3 := prefix_c_sweep j L (scannerCutSuffix h 9 R)
    have hh := (h1.trans h2).trans h3
    simp (config := { failIfUnchanged := false }) only [PrefixedScanner.word,
      PrefixedScanner.prefixLen, PrefixedScanner.repeatCount, PrefixedScanner.terminator,
      PrefixedScanner.cutSuffix, ListBlank.append_append] at hh ⊢
    convert hh using 1 <;> (first | rfl | (simp only [PrefixedScanner.clockToCut]; omega))
  · rename_i h
    let Lw := push (Q ^ (j + 5)) L
    have ht := a101_100_terminal_exact (2 * h) Lw R
    rw [c6_phase_even] at ht
    have hc := c6_sweep_exact h (push [0, 1, 0] Lw) (push (I ^ (4 + 3)) R)
    have htc := ht.trans hc
    rw [scanner_guard_split h 4 R] at htc
    have hw := prefix_wide_c_sweep j L (scannerGuardTail h 4 R)
    have h12 := h1.trans htc
    simp only [PrefixedScanner.word, PrefixedScanner.prefixLen, PrefixedScanner.repeatCount,
      PrefixedScanner.terminator, ListBlank.append_append] at h12 ⊢
    have hh := h12.trans hw
    convert hh using 1 <;> (first | rfl | (simp only [PrefixedScanner.clockToCut]; omega))
  · rename_i h
    let Lw := push (Q ^ (j + 5)) L
    have ht := a101_00_positive_terminal_exact (2 * h) Lw R
    rw [c6_phase_even] at ht
    have hc := c6_sweep_exact h (push [0, 1, 0] Lw) (push (I ^ (6 + 3)) R)
    have htc := ht.trans hc
    rw [scanner_guard_split h 6 R] at htc
    have hw := prefix_wide_c_sweep j L (scannerGuardTail h 6 R)
    have h12 := h1.trans htc
    simp only [PrefixedScanner.word, PrefixedScanner.prefixLen, PrefixedScanner.repeatCount,
      PrefixedScanner.terminator, ListBlank.append_append] at h12 ⊢
    have hh := h12.trans hw
    convert hh using 1 <;> (first | rfl | (simp only [PrefixedScanner.clockToCut]; omega))

/-- The contextual checkpoint lemma at every guarded width n=k+5. -/
theorem b1101_prefixed_to_cut (t : PrefixedScanner) (u v k j : ℕ) (R : Bits) :
    ReachesIn target (t.clockToCut j)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push (t.word j) R))
      (scannerCutSource u v k (t.cutSuffix j R)) := by
  have h := b1101_prefixed_to_cut_context t (push (Q ^ (k + 3)) (base u v)) j R
  rw [← ListBlank.append_pow_add, show 2 + (k + 3) = k + 5 by omega] at h
  exact h

/-- Exact blank-left C return for the prefixed scanner dispatcher. -/
theorem b1101_prefixed_return_exact (t : PrefixedScanner) (u v k j : ℕ) (R : Bits) :
    ReachesIn target (t.clockToCut j + scannerCutClock u v k)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push (t.word j) R))
      (Cfg.headRight C default (scannerCutResult u v (t.cutSuffix j R) k)) :=
  (b1101_prefixed_to_cut t u v k j R).trans
    (scanner_cut_return_exact u v k (t.cutSuffix j R))

/-- Full return for the mixed 00 word at every width n=k+5. -/
theorem mixed_101_01_00_return_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (110 + 2 * u + 2 * v + 2 * k)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v))
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0] R))
      (Cfg.headRight C default (cpop_bottom_result u v
        (push (I ^ (2 * k + 6)) (push [1, 0, 1, 0] (push (I ^ 11) R))))) := by
  let S := push [1, 0, 1, 0] (push (I ^ 11) R)
  have h1 := mixed_101_01_00_frame_exact (push (Q ^ (k + 3)) (base u v)) R
  have he : push [1, 0, 1, 0] (push (Q ^ (k + 3)) (base u v)) =
      push (Q ^ (k + 5)) (base u v) := by
    change push (Q ^ 2) (push (Q ^ (k + 3)) (base u v)) = _
    rw [← ListBlank.append_pow_add, show 2 + (k + 3) = k + 5 by omega]
  rw [he] at h1
  have h2 := b1101_cpop_sweep u v k S
  have h3 := b1101100_finish u v (push (I ^ (2 * k + 6)) S)
  convert (h1.trans h2).trans h3 using 1 <;> omega

/-- The right word consumed after the mixed handoff, excluding the handoff
itself and the five pairs already represented within the new A frame. -/
def PrefixedScanner.resumeWord (t : PrefixedScanner) (j : ℕ) : List (Fin 2) :=
  P ^ j ++ (scanner101 ^ t.repeatCount ++ t.terminator)

/-- Index giving j+5 pairs in the equivalent two-block entry. -/
def PrefixedScanner.resumeIndex : PrefixedScanner → ℕ → ℕ
  | .wideEven100 _, j | .wideOdd00 _, j => j
  | _, j => j + 5

private theorem PrefixedScanner.resume_word_eq (t : PrefixedScanner) (j : ℕ) :
    t.word (t.resumeIndex j) = [1, 1, 0, 1] ++ (P ^ 5 ++ t.resumeWord j) := by
  have hn : t.prefixLen (t.resumeIndex j) = 5 + j := by
    cases t <;> simp only [PrefixedScanner.prefixLen, PrefixedScanner.resumeIndex] <;> omega
  rw [PrefixedScanner.word, hn, list_pow_add]
  simp only [PrefixedScanner.resumeWord, List.append_assoc]

/-- An exact full mixed return at width n=k+6. Rescanning the two-block
continuation gives the same output tape as a width n−1 entry with five more
01 pairs, and adds exactly 112 steps to that entry's clock. -/
theorem mixed_resumed_return_exact (t : PrefixedScanner) (u v k j : ℕ) (R : Bits) :
    ReachesIn target (112 + (t.clockToCut (t.resumeIndex j) + scannerCutClock u v k))
      (Cfg.headRight B (push (Q ^ (k + 6)) (base u v))
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] (push (t.resumeWord j) R)))
      (Cfg.headRight C default (scannerCutResult u v (t.cutSuffix (t.resumeIndex j) R) k)) := by
  let L := push (Q ^ (k + 3)) (base u v)
  let W := push (t.resumeWord j) R
  let Y := Cfg.headRight C default (scannerCutResult u v (t.cutSuffix (t.resumeIndex j) R) k)
  let N := t.clockToCut (t.resumeIndex j) + scannerCutClock u v k
  have hN : 24 ≤ N := by
    dsimp only [N]
    cases t <;> simp only [PrefixedScanner.resumeIndex, PrefixedScanner.clockToCut] <;> omega
  have h := b1101_prefixed_return_exact t u v k (t.resumeIndex j) R
  rw [PrefixedScanner.resume_word_eq, ← ListBlank.append_append, ← ListBlank.append_append] at h
  have htime : 24 + (N - 24) = N := by omega
  have hL2 : push [1, 0, 1, 0] L = push (Q ^ (k + 5)) (base u v) := by
    change push (Q ^ 2) (push (Q ^ (k + 3)) (base u v)) = _
    rw [← ListBlank.append_pow_add, show 2 + (k + 3) = k + 5 by omega]
  have hL3 : push [1, 0, 1, 0, 1, 0] L = push (Q ^ (k + 6)) (base u v) := by
    change push (Q ^ 3) (push (Q ^ (k + 3)) (base u v)) = _
    rw [← ListBlank.append_pow_add, show 3 + (k + 3) = k + 6 by omega]
  have ht := mixed_suffix_transport L W Y (N - 24)
  rw [hL2, hL3, htime] at ht
  change ReachesIn target (112 + N)
    (Cfg.headRight B (push (Q ^ (k + 6)) (base u v)) (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] W)) Y
  rw [show 112 + N = 136 + (N - 24) by omega]
  exact ht.mpr h

/-- Fixed width-four checkpoint kernel. Read window [-14,4]. -/
private theorem width4_zero (L R : Bits) :
    ReachesIn target 63
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1, 0] R))
      (Cfg.headRight A L (push [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  set_option maxRecDepth 8192 in
    set_option maxHeartbeats 3000000 in
      l17_exact_steps

/-- Fixed width-four checkpoint kernel. Read window [-16,9]. -/
private theorem width4_ones (L R : Bits) :
    ReachesIn target 145
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 1, 1] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 8192 in
    set_option maxHeartbeats 3000000 in
      l17_exact_steps

/-- Fixed width-four checkpoint kernel. Read window [-14,21]. -/
private theorem width4_onep (L R : Bits) :
    ReachesIn target 139
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] R))
      (Cfg.headRight A L (push [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 8192 in
    set_option maxHeartbeats 3000000 in
      l17_exact_steps

/-- Fixed width-four checkpoint kernel. Read window [-14,19]. -/
private theorem width4_onec (L R : Bits) :
    ReachesIn target 133
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  set_option maxRecDepth 8192 in
    set_option maxHeartbeats 3000000 in
      l17_exact_steps

/-- Fixed width-four checkpoint kernel. Read window [-16,23]. -/
private theorem width4_threep (L R : Bits) :
    ReachesIn target 187
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 8192 in
    set_option maxHeartbeats 3000000 in
      l17_exact_steps

/-- Fixed width-four checkpoint kernel. Read window [-20,21]. -/
private theorem width4_threec (L R : Bits) :
    ReachesIn target 173
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  set_option maxRecDepth 8192 in
    set_option maxHeartbeats 3000000 in
      l17_exact_steps

/-- Fixed width-four checkpoint kernel. Read window [-8,1]. -/
private theorem width4_a_finish (L R : Bits) :
    ReachesIn target 25
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 8192 in
    set_option maxHeartbeats 3000000 in
      l17_exact_steps

/-- The reduced width-four C checkpoint. Unlike the wide checkpoint, it
reads a finite prefix of the scanner's output suffix. -/
def widthFourCutSource (u v : ℕ) (S : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (push (Q ^ 2) (base u v)) (push [0, 1, 1, 1] S)

private theorem width4_left_frame (u v d p : ℕ) (h : v + 7 = d + p) :
    push (Q ^ 2) (base u v) =
      push ([1, 0, 1, 0, 0, 1, 0] ++ P ^ d)
        (push (P ^ p) (push [0] (push (P ^ (u + 6)) default))) := by
  unfold base
  rw [h, ListBlank.append_pow_add P d p]
  simp only [ListBlank.append_append, List.append_assoc]
  rfl

private theorem width4_c_finish (u p : ℕ) (R : Bits) :
    ReachesIn target (2 * (p + 1) + (41 + 2 * u))
      (Cfg.headRight C (push (P ^ p) (push [0] (push (P ^ (u + 6)) default)))
        (push [1, 1] R))
      (Cfg.headRight C default (five_run_bottom_result u (push (I ^ (2 * p)) R))) := by
  have h := c01_middle_headRight_exact p (push (P ^ (u + 6)) default) (push [1] R)
  have hs : push (([1, 1] : List (Fin 2)) ^ (p + 1)) (push [1] R) =
      push [1, 1, 1] (push (I ^ (2 * p)) R) := by
    rw [one_pow_two_mul, show 2 * (p + 1) = 3 + 2 * p - 1 by omega]
    change push (I ^ (3 + 2 * p - 1)) (push (I ^ 1) R) = _
    rw [← ListBlank.append_pow_add, show 3 + 2 * p - 1 + 1 = 3 + 2 * p by omega,
      ListBlank.append_pow_add I 3 (2 * p)]
    rfl
  rw [hs] at h
  have h2 := k41_c01_last_exact u default (push (I ^ (2 * p)) R)
  have he : Cfg.headLeft C (push [1] default)
      (push (([1, 1] : List (Fin 2)) ^ u) (push returnKtail (push (I ^ (2 * p)) R))) =
      Cfg.headRight C default (five_run_bottom_result u (push (I ^ (2 * p)) R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [he] at h2
  exact h.trans h2

private theorem width4_a_unwind (u p : ℕ) (R : Bits) :
    ReachesIn target (4 * p + 29 + 2 * u)
      (Cfg.headRight A (push (P ^ p) (push [0] (push (P ^ (u + 6)) default)))
        (push [1, 1, 1] R))
      (Cfg.headRight C default
        (push (I ^ (2 * u + 6)) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] (push (P ^ p) R)))) := by
  let W := push (P ^ p) R
  let L : Bits := push (P ^ (u + 2)) default
  have h1 := pair_a_sweep p (push [0] (push (P ^ (u + 6)) default)) R
  have h2 := width4_a_finish L (push [1] W)
  have hL : push [0, 0, 1, 0, 1, 0, 1, 0, 1] L = push [0] (push (P ^ (u + 6)) default) := by
    change push [0] (push (P ^ 4) (push (P ^ (u + 2)) default)) = _
    rw [← ListBlank.append_pow_add, show 4 + (u + 2) = u + 6 by omega]
  rw [hL] at h2
  let T := push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] W)
  have he : Cfg.headRight C L (push [1] T) =
      Cfg.headLeft C (push (Q ^ (u + 2)) (push [1] default)) T := by
    calc
      _ = Cfg.headLeft C (push [1] L) T := Cfg.headRight_cons C (1 : Fin 2) L T
      _ = _ := by unfold L; rw [rotLB]
  change ReachesIn target 25 _ (Cfg.headRight C L (push [1] T)) at h2
  rw [he] at h2
  have h3 := c01_sweep_exact (u + 2) (push [1] default) T
  rw [one_pow_two_mul] at h3
  have hE : Cfg.headLeft C (push [1] default) (push (I ^ (2 * (u + 2))) T) =
      Cfg.headRight C default (push [1] (push (I ^ (2 * (u + 2))) T)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hE] at h3
  have hR : push [1] (push (I ^ (2 * (u + 2))) T) =
      push (I ^ (2 * u + 6)) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] W) := by
    change push (I ^ 1) (push (I ^ (2 * (u + 2))) (push (I ^ 1)
      (push [0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] W)))) = _
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add,
      show 1 + 2 * (u + 2) + 1 = 2 * u + 6 by omega]
    rfl
  rw [hR] at h3
  convert (h1.trans h2).trans h3 using 1 <;> omega

/-- Two wide strips at the width-four checkpoint. Read window [-14,36]. -/
private theorem width4_one_two_wide (L R : Bits) :
    ReachesIn target 209
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 5000000 in
      l17_exact_steps

/-- Two wide strips at the width-four checkpoint. Read window [-20,38]. -/
private theorem width4_three_two_wide (L R : Bits) :
    ReachesIn target 249
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 5000000 in
      l17_exact_steps

/-- Reduced-width guards for the scanner and composed return blocks. -/
inductive WidthFourGuard where
  | zero | ones | onePlain | oneC6 | threePlain | threeC6 | oneTwoWide | threeTwoWide
  deriving DecidableEq

def WidthFourGuard.word : WidthFourGuard → List (Fin 2)
  | .zero => [0]
  | .ones => [1, 1, 1, 1, 1, 1]
  | .onePlain => [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]
  | .oneC6 => [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0]
  | .threePlain => [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]
  | .threeC6 => [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0]
  | .oneTwoWide => [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]
  | .threeTwoWide => [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]

def WidthFourGuard.clock (u v : ℕ) : WidthFourGuard → ℕ
  | .zero => 104 + 2 * u + 4 * v
  | .ones => 192 + 2 * u + 2 * v
  | .onePlain => 180 + 2 * u + 4 * v
  | .oneC6 => 182 + 2 * u + 2 * v
  | .threePlain => 234 + 2 * u + 2 * v
  | .threeC6 => 216 + 2 * u + 2 * v
  | .oneTwoWide => 258 + 2 * u + 2 * v
  | .threeTwoWide => 292 + 2 * u + 2 * v

def WidthFourGuard.written : WidthFourGuard → List (Fin 2)
  | .zero => [0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | .ones => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  | .onePlain => [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  | .oneC6 => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | .threePlain => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  | .threeC6 => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | .oneTwoWide => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  | .threeTwoWide => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- Exact right half tape after the reduced-width return. -/
def WidthFourGuard.result (u v : ℕ) (R : Bits) (g : WidthFourGuard) : Bits :=
  match g with
  | .zero | .onePlain => push (I ^ (2 * u + 6))
      (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] (push (P ^ (v + 3)) (push g.written R)))
  | .ones | .threePlain => five_run_bottom_result u (push (I ^ (2 * (v + 2))) (push g.written R))
  | .oneC6 => five_run_bottom_result u (push (I ^ (2 * (v + 3))) (push g.written R))
  | .threeC6 => five_run_bottom_result u (push (I ^ (2 * v)) (push g.written R))
  | .oneTwoWide => five_run_bottom_result u (push (I ^ (2 * (v + 3))) (push g.written R))
  | .threeTwoWide => five_run_bottom_result u (push (I ^ (2 * v)) (push g.written R))

/-- Reduced width-four exact C return for each of the required guards. -/
theorem width_four_cut_return_exact (g : WidthFourGuard) (u v : ℕ) (R : Bits) :
    ReachesIn target (WidthFourGuard.clock u v g)
      (widthFourCutSource u v (push g.word R))
      (Cfg.headRight C default (WidthFourGuard.result u v R g)) := by
  cases g
  · unfold widthFourCutSource
    rw [width4_left_frame u v 4 (v + 3) (by omega)]
    let L := push (P ^ (v + 3)) (push [0] (push (P ^ (u + 6)) default))
    have h := (width4_zero L R).trans (width4_a_unwind u (v + 3) (push (WidthFourGuard.written .zero) R))
    convert h using 1 <;> (first | rfl | (simp only [WidthFourGuard.clock]; omega))
  · unfold widthFourCutSource
    rw [width4_left_frame u v 5 (v + 2) (by omega)]
    let L := push (P ^ (v + 2)) (push [0] (push (P ^ (u + 6)) default))
    have h := (width4_ones L R).trans (width4_c_finish u (v + 2) (push (WidthFourGuard.written .ones) R))
    convert h using 1 <;> (first | rfl | (simp only [WidthFourGuard.clock]; omega))
  · unfold widthFourCutSource
    rw [width4_left_frame u v 4 (v + 3) (by omega)]
    let L := push (P ^ (v + 3)) (push [0] (push (P ^ (u + 6)) default))
    have h := (width4_onep L R).trans (width4_a_unwind u (v + 3) (push (WidthFourGuard.written .onePlain) R))
    convert h using 1 <;> (first | rfl | (simp only [WidthFourGuard.clock]; omega))
  · unfold widthFourCutSource
    rw [width4_left_frame u v 4 (v + 3) (by omega)]
    let L := push (P ^ (v + 3)) (push [0] (push (P ^ (u + 6)) default))
    have h := (width4_onec L R).trans (width4_c_finish u (v + 3) (push (WidthFourGuard.written .oneC6) R))
    convert h using 1 <;> (first | rfl | (simp only [WidthFourGuard.clock]; omega))
  · unfold widthFourCutSource
    rw [width4_left_frame u v 5 (v + 2) (by omega)]
    let L := push (P ^ (v + 2)) (push [0] (push (P ^ (u + 6)) default))
    have h := (width4_threep L R).trans (width4_c_finish u (v + 2) (push (WidthFourGuard.written .threePlain) R))
    convert h using 1 <;> (first | rfl | (simp only [WidthFourGuard.clock]; omega))
  · unfold widthFourCutSource
    rw [width4_left_frame u v 7 v (by omega)]
    let L := push (P ^ v) (push [0] (push (P ^ (u + 6)) default))
    have h := (width4_threec L R).trans (width4_c_finish u v (push (WidthFourGuard.written .threeC6) R))
    convert h using 1 <;> (first | rfl | (simp only [WidthFourGuard.clock]; omega))
  · unfold widthFourCutSource
    rw [width4_left_frame u v 4 (v + 3) (by omega)]
    let L := push (P ^ (v + 3)) (push [0] (push (P ^ (u + 6)) default))
    have h := (width4_one_two_wide L R).trans
      (width4_c_finish u (v + 3) (push (WidthFourGuard.written .oneTwoWide) R))
    convert h using 1 <;> (first | rfl | (simp only [WidthFourGuard.clock]; omega))
  · unfold widthFourCutSource
    rw [width4_left_frame u v 7 v (by omega)]
    let L := push (P ^ v) (push [0] (push (P ^ (u + 6)) default))
    have h := (width4_three_two_wide L R).trans
      (width4_c_finish u v (push (WidthFourGuard.written .threeTwoWide) R))
    convert h using 1 <;> (first | rfl | (simp only [WidthFourGuard.clock]; omega))

/-- Only the first three pair counts need special treatment in the wide scanner families. -/
private def wideWidthFourGuard : ℕ → ℕ → WidthFourGuard
  | 0, _ => .zero
  | 1, 0 => .onePlain
  | 1, _ + 1 => .oneC6
  | 2, 0 => .threePlain
  | 2, _ + 1 => .threeC6
  | _ + 3, _ => .ones

/-- Guard selected by the resumed scanner at width five. -/
def PrefixedScanner.narrowGuard : PrefixedScanner → ℕ → WidthFourGuard
  | .wideEven100 h, j | .wideOdd00 h, j => wideWidthFourGuard j h
  | _, _ => .ones

private theorem width4_wide_guard (j h e : ℕ) (R : Bits) :
    ∃ S : Bits, scannerWideSuffix j (scannerGuardTail h (3 + e) R) =
      push (wideWidthFourGuard j h).word S := by
  match j with
  | 0 =>
    exact ⟨push (Q ^ 6) (scannerGuardTail h (3 + e) R), rfl⟩
  | 1 =>
    cases h with
    | zero =>
      refine ⟨push (I ^ e) R, ?_⟩
      simp only [scannerWideSuffix, scannerGuardTail, ListBlank.append_pow_add I 3 e]
      rfl
    | succ h =>
      exact ⟨push [1, 0] (push (scannerC6 ^ h) (push (I ^ ((3 + e) + 3)) R)), rfl⟩
  | 2 =>
    cases h with
    | zero =>
      refine ⟨push (I ^ e) R, ?_⟩
      simp only [scannerWideSuffix, scannerGuardTail, ListBlank.append_pow_add I 3 e]
      rfl
    | succ h =>
      exact ⟨push [1, 0] (push (scannerC6 ^ h) (push (I ^ ((3 + e) + 3)) R)), rfl⟩
  | 3 =>
    exact ⟨push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
      (scannerGuardTail h (3 + e) R), rfl⟩
  | j + 4 =>
    let W := push returnKtail (scannerGuardTail h (3 + e) R)
    refine ⟨push (I ^ (2 * j + 1)) W, ?_⟩
    change push (I ^ (2 * (j + 3) + 1)) W = push (I ^ 6) (push (I ^ (2 * j + 1)) W)
    rw [← ListBlank.append_pow_add, show 2 * (j + 3) + 1 = 6 + (2 * j + 1) by omega]

private theorem width4_ordinary_guard (j : ℕ) (R : Bits) :
    ∃ S : Bits, push (I ^ (2 * (j + 5))) R = push WidthFourGuard.ones.word S := by
  refine ⟨push (I ^ (2 * j + 4)) R, ?_⟩
  change push (I ^ (2 * (j + 5))) R = push (I ^ 6) (push (I ^ (2 * j + 4)) R)
  rw [← ListBlank.append_pow_add, show 2 * (j + 5) = 6 + (2 * j + 4) by omega]

/-- Every output of the reduced-width scanner has the selected guard. The
rest of the tape begins immediately after the corresponding read window. -/
theorem mixed_narrow_guard_complete (t : PrefixedScanner) (j : ℕ) (R : Bits) :
    ∃ S : Bits, t.cutSuffix (t.resumeIndex j) R = push (t.narrowGuard j).word S := by
  cases t with
  | zero00 => exact width4_ordinary_guard j (push (I ^ 6) R)
  | odd100 h => exact width4_ordinary_guard j (scannerCutSuffix h 7 R)
  | positiveEven00 h => exact width4_ordinary_guard j (scannerCutSuffix h 9 R)
  | wideEven100 h => exact width4_wide_guard j h 1 R
  | wideOdd00 h => exact width4_wide_guard j h 3 R

/-- Exact width-five mixed return. The scanner can read either terminator;
the selected reduced-width path accounts for the extra suffix reads. -/
theorem mixed_narrow_return_exact (t : PrefixedScanner) (u v j : ℕ) (R : Bits) :
    ∃ S : Bits, t.cutSuffix (t.resumeIndex j) R = push (t.narrowGuard j).word S ∧
      ReachesIn target
        (112 + (t.clockToCut (t.resumeIndex j) + WidthFourGuard.clock u v (t.narrowGuard j)))
        (Cfg.headRight B (push (Q ^ 5) (base u v))
          (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] (push (t.resumeWord j) R)))
        (Cfg.headRight C default (WidthFourGuard.result u v S (t.narrowGuard j))) := by
  obtain ⟨S, hs⟩ := mixed_narrow_guard_complete t j R
  refine ⟨S, hs, ?_⟩
  let X := push (Q ^ 2) (base u v)
  let W := push (t.resumeWord j) R
  let g := t.narrowGuard j
  let Y := Cfg.headRight C default (WidthFourGuard.result u v S g)
  let N := t.clockToCut (t.resumeIndex j) + WidthFourGuard.clock u v g
  have hN : 24 ≤ N := by
    dsimp only [N]
    cases t <;> simp only [PrefixedScanner.resumeIndex, PrefixedScanner.clockToCut] <;> omega
  have h := b1101_prefixed_to_cut_context t X (t.resumeIndex j) R
  have hC : Cfg.headLeft C (push [0] X) (push [1, 1, 1] (push g.word S)) =
      widthFourCutSource u v (push g.word S) :=
    Cfg.headLeft_cons C (0 : Fin 2) X _
  rw [PrefixedScanner.resume_word_eq, ← ListBlank.append_append, ← ListBlank.append_append,
    hs, hC] at h
  have hh := h.trans (width_four_cut_return_exact g u v S)
  have ht := mixed_suffix_transport X W Y (N - 24)
  have he : push [1, 0, 1, 0, 1, 0] X = push (Q ^ 5) (base u v) := by
    change push (Q ^ 3) (push (Q ^ 2) (base u v)) = _
    rw [← ListBlank.append_pow_add]
  rw [he, show 24 + (N - 24) = N by omega] at ht
  change ReachesIn target (112 + N)
    (Cfg.headRight B (push (Q ^ 5) (base u v)) (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] W)) Y
  rw [show 112 + N = 136 + (N - 24) by omega]
  exact ht.mpr hh

/-- At mixed width five, a parse of the actual scan leaves the five virtual
pairs to be swept last. They supply ten ones and force the existing six-one
checkpoint, without assuming any prefix on the output of the parsed blocks. -/
theorem mixed_narrow_return_blocks_exact (term : ReturnTerm) (ts : List ScannerToken)
    (bs : List ReturnBlock) (u v : ℕ) (R : Bits)
    (hg : ts ++ term.extra = returnBlockTokens bs) :
    ReachesIn target
      (136 + (scannerSteps ts + term.clock + returnBlockClock bs + 10 +
        WidthFourGuard.clock u v .ones))
      (Cfg.headRight B (push (Q ^ 5) (base u v))
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] (push (scannerInput ts) (push term.word R))))
      (Cfg.headRight C default
        (WidthFourGuard.result u v (push (I ^ 4) (returnBlockOutput (term.residue R) bs)) .ones)) := by
  let five : List ScannerToken := List.replicate 5 .a01
  let X := push (Q ^ 2) (base u v)
  let W := push (scannerInput ts) (push term.word R)
  let S := returnBlockOutput (term.residue R) bs
  let Y := Cfg.headRight C default (WidthFourGuard.result u v (push (I ^ 4) S) .ones)
  let N := scannerSteps ts + term.clock + returnBlockClock bs + 10 + WidthFourGuard.clock u v .ones
  have ha := b_scanner_term_exact term (five ++ ts) X R
  rw [List.append_assoc, hg, scanner_deposit_append, scanner_deposit_pairs,
    scanner_steps_append, scanner_input_append, ← ListBlank.append_append] at ha
  have hb := return_blocks_exact bs (push (Q ^ 5) (push [0] X)) (term.residue R)
  have hc := prefix_c_sweep 5 (push [0] X) S
  have he : Cfg.headLeft C (push [0] X) (push [1, 1, 1] (push (I ^ (2 * 5)) S)) =
      widthFourCutSource u v (push WidthFourGuard.ones.word (push (I ^ 4) S)) :=
    Cfg.headLeft_cons C (0 : Fin 2) X _
  rw [he] at hc
  have hd := width_four_cut_return_exact .ones u v (push (I ^ 4) S)
  have hh := ((ha.trans hb).trans hc).trans hd
  have ht := mixed_suffix_transport X W Y N
  have he3 : push [1, 0, 1, 0, 1, 0] X = push (Q ^ 5) (base u v) := by
    change push (Q ^ 3) (push (Q ^ 2) (base u v)) = _
    rw [← ListBlank.append_pow_add]
  rw [he3] at ht
  apply ht.mpr
  have htime : (14 + (scannerSteps five + scannerSteps ts + term.clock)) +
      returnBlockClock bs + 2 * 5 + WidthFourGuard.clock u v .ones = 24 + N := by
    change (14 + (10 + scannerSteps ts + term.clock)) +
      returnBlockClock bs + 2 * 5 + WidthFourGuard.clock u v .ones = 24 + N
    dsimp only [N]
    omega
  rw [htime] at hh
  exact hh

/-- Complete mixed width-five return whenever the block output selects
a certified checkpoint guard, including parses that absorb virtual pairs. -/
theorem mixed_narrow_guarded_blocks_exact (term : ReturnTerm) (ts : List ScannerToken)
    (bs : List ReturnBlock) (g : WidthFourGuard) (u v : ℕ) (R S : Bits)
    (hg : (List.replicate 5 .a01 ++ ts) ++ term.extra = returnBlockTokens bs)
    (hs : returnBlockOutput (term.residue R) bs = push g.word S) :
    ReachesIn target
      (136 + (scannerSteps ts + term.clock + returnBlockClock bs + WidthFourGuard.clock u v g))
      (Cfg.headRight B (push (Q ^ 5) (base u v))
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] (push (scannerInput ts) (push term.word R))))
      (Cfg.headRight C default (WidthFourGuard.result u v S g)) := by
  let five : List ScannerToken := List.replicate 5 .a01
  let X := push (Q ^ 2) (base u v)
  let W := push (scannerInput ts) (push term.word R)
  let Y := Cfg.headRight C default (WidthFourGuard.result u v S g)
  let N := scannerSteps ts + term.clock + returnBlockClock bs + WidthFourGuard.clock u v g
  have ha := b_scanner_term_exact term (five ++ ts) X R
  rw [hg, scanner_steps_append, scanner_input_append, ← ListBlank.append_append] at ha
  have hb := return_blocks_exact bs (push [0] X) (term.residue R)
  have he : Cfg.headLeft C (push [0] X) (push [1, 1, 1] (push g.word S)) =
      widthFourCutSource u v (push g.word S) :=
    Cfg.headLeft_cons C (0 : Fin 2) X _
  rw [hs, he] at hb
  have hh := (ha.trans hb).trans (width_four_cut_return_exact g u v S)
  have ht := mixed_suffix_transport X W Y N
  have he3 : push [1, 0, 1, 0, 1, 0] X = push (Q ^ 5) (base u v) := by
    change push (Q ^ 3) (push (Q ^ 2) (base u v)) = _
    rw [← ListBlank.append_pow_add]
  rw [he3] at ht
  apply ht.mpr
  have htime : (14 + (scannerSteps five + scannerSteps ts + term.clock)) +
      returnBlockClock bs + WidthFourGuard.clock u v g = 24 + N := by
    change (14 + (10 + scannerSteps ts + term.clock)) +
      returnBlockClock bs + WidthFourGuard.clock u v g = 24 + N
    dsimp only [N]
    omega
  rw [htime] at hh
  exact hh

/-- The two-wide-block family with one or three ones before the first
strip and one before the second. Both stops provide at least three seed
ones; the rest of the seed stays in the right output. -/
theorem mixed_two_wide_return_exact (outerThree : Bool) (term : ReturnTerm)
    (ts : List ScannerToken) (u v : ℕ) (R : Bits)
    (hg : (List.replicate 5 .a01 ++ ts) ++ term.extra =
      returnBlockTokens [.wide 1, .wide (if outerThree then 2 else 1)]) :
    let g := if outerThree then WidthFourGuard.threeTwoWide else WidthFourGuard.oneTwoWide
    let bs := [ReturnBlock.wide 1, .wide (if outerThree then 2 else 1)]
    let S := push (I ^ (match term with | .zero => 3 | .hundred => 1)) R
    ReachesIn target
      (136 + (scannerSteps ts + term.clock + returnBlockClock bs + WidthFourGuard.clock u v g))
      (Cfg.headRight B (push (Q ^ 5) (base u v))
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] (push (scannerInput ts) (push term.word R))))
      (Cfg.headRight C default (WidthFourGuard.result u v S g)) := by
  cases outerThree <;> cases term
  · exact mixed_narrow_guarded_blocks_exact .zero ts [.wide 1, .wide 1] .oneTwoWide u v R _ hg rfl
  · exact mixed_narrow_guarded_blocks_exact .hundred ts [.wide 1, .wide 1] .oneTwoWide u v R _ hg rfl
  · exact mixed_narrow_guarded_blocks_exact .zero ts [.wide 1, .wide 2] .threeTwoWide u v R _ hg rfl
  · exact mixed_narrow_guarded_blocks_exact .hundred ts [.wide 1, .wide 2] .threeTwoWide u v R _ hg rfl

/-- The resumed family covers every two-block continuation, with either
terminator and no guard on the number of new pairs or repeats. -/
theorem mixed_resumed_scanner_complete (j r : ℕ) (terminates00 : Bool) :
    ∃ t : PrefixedScanner, t.resumeWord j =
      P ^ j ++ (scanner101 ^ r ++ if terminates00 then [0, 0] else [1, 0, 0]) := by
  cases terminates00
  · by_cases he : r % 2 = 0
    · obtain ⟨h, rfl⟩ : ∃ h : ℕ, r = 2 * h := ⟨r / 2, by omega⟩
      exact ⟨.wideEven100 h, rfl⟩
    · obtain ⟨h, rfl⟩ : ∃ h : ℕ, r = 2 * h + 1 := ⟨r / 2, by omega⟩
      exact ⟨.odd100 h, rfl⟩
  · by_cases hz : r = 0
    · subst r
      exact ⟨.zero00, rfl⟩
    · by_cases he : r % 2 = 0
      · obtain ⟨h, rfl⟩ : ∃ h : ℕ, r = 2 * h + 2 := ⟨(r - 2) / 2, by omega⟩
        exact ⟨.positiveEven00 h, rfl⟩
      · obtain ⟨h, rfl⟩ : ∃ h : ℕ, r = 2 * h + 1 := ⟨r / 2, by omega⟩
        exact ⟨.wideOdd00 h, rfl⟩

/-- Short prefixes whose complementary-parity C6 frames have a full return. -/
inductive ShortScannerPrefix where
  | two | three

def ShortScannerPrefix.pairs : ShortScannerPrefix → ℕ
  | .two => 2
  | .three => 3

private abbrev shortThreeWrite := ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

def ShortScannerPrefix.returnClock (m : ShortScannerPrefix) (u v k : ℕ) : ℕ :=
  match m with
  | .two => 105 + 4 * k + 4 * v + 2 * u
  | .three => 97 + 2 * k + 2 * v + 2 * u

def ShortScannerPrefix.result (m : ShortScannerPrefix) (u v k : ℕ) (S : Bits) : Bits :=
  match m with
  | .two => b_triple_one_result u v (k + 2) S
  | .three => cpop_bottom_result u v (push (I ^ (2 * k + 6)) (push shortThreeWrite S))

private def shortFrame (m : ℕ) (u v k : ℕ) (S : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C (push [0, 1, 0] (push (Q ^ m) (push [0] (push (Q ^ (k + 3)) (base u v)))))
    (push [1, 1, 1] S)

/-- For two pairs, the local return reads [-6,3] and exits D at -7. -/
private theorem prefix_two_kernel (L S : Bits) :
    ReachesIn target 29
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 1] S))
      (Cfg.headLeft D L (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] S)) := by
  l17_exact_steps

/-- For three pairs, the local return reads [-9,3] and exits C at -10. -/
private theorem prefix_three_kernel (L S : Bits) :
    ReachesIn target 32
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 0] L) (push [0, 1, 1, 1] S))
      (Cfg.headLeft C L (push shortThreeWrite S)) := by
  l17_exact_steps

private theorem prefix_two_frame_return (u v k : ℕ) (S : Bits) :
    ReachesIn target (ShortScannerPrefix.two.returnClock u v k)
      (shortFrame 2 u v k S) (Cfg.headRight C default (ShortScannerPrefix.two.result u v k S)) := by
  let L := push [0] (push (Q ^ (k + 3)) (base u v))
  let O := push [0] (push (P ^ (u + 6)) default)
  have h1 := prefix_two_kernel L S
  have hf : shortFrame 2 u v k S =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 1] S) :=
    Cfg.headLeft_cons C (0 : Fin 2) _ _
  rw [← hf] at h1
  change ReachesIn target 29 (shortFrame 2 u v k S)
    (Cfg.headLeft D L (push (Q ^ 5) S)) at h1
  have h2 := d10_sweep_exact (k + 3) (push [0] (base u v)) (push (Q ^ 5) S)
  rw [← rotLB0, ← ListBlank.append_pow_add] at h2
  have h3 := d_pair1_sweep_exact (v + 6) (k + 7) O S
  have h12 := h1.trans h2
  have h123 := h12.trans h3
  have h4 := b111_outer u v (k + 2) S
  have he : push (Q ^ (v + 6 + (k + 7) + 4)) S =
      push [1, 0, 1, 0] (push (Q ^ (v + (k + 2) + 13)) S) := by
    change _ = push (Q ^ 2) (push (Q ^ (v + (k + 2) + 13)) S)
    rw [← ListBlank.append_pow_add, show v + 6 + (k + 7) + 4 = 2 + (v + (k + 2) + 13) by omega]
  rw [he] at h123
  have ht : ShortScannerPrefix.two.returnClock u v k =
      29 + 4 * (k + 3) + (4 * (v + 6) + 14) + (22 + 2 * (u + 2)) := by
    simp only [ShortScannerPrefix.returnClock]; omega
  rw [ht]
  exact h123.trans h4

private theorem prefix_three_frame_return (u v k : ℕ) (S : Bits) :
    ReachesIn target (ShortScannerPrefix.three.returnClock u v k)
      (shortFrame 3 u v k S) (Cfg.headRight C default (ShortScannerPrefix.three.result u v k S)) := by
  let L := push (Q ^ (k + 3)) (base u v)
  have h1 := prefix_three_kernel L S
  have hf : shortFrame 3 u v k S =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 0] L) (push [0, 1, 1, 1] S) :=
    Cfg.headLeft_cons C (0 : Fin 2) _ _
  rw [← hf] at h1
  have h2 := b1101_cpop_sweep u v k (push shortThreeWrite S)
  have h3 := b1101100_finish u v (push (I ^ (2 * k + 6)) (push shortThreeWrite S))
  have ht : ShortScannerPrefix.three.returnClock u v k =
      32 + 2 * (k + 3) + (4 + (2 * (v + 7) + 41 + 2 * u)) := by
    simp only [ShortScannerPrefix.returnClock]; omega
  rw [ht]
  exact (h1.trans h2).trans h3

private theorem short_frame_return (m : ShortScannerPrefix) (u v k : ℕ) (S : Bits) :
    ReachesIn target (m.returnClock u v k) (shortFrame m.pairs u v k S)
      (Cfg.headRight C default (m.result u v k S)) := by
  cases m
  · exact prefix_two_frame_return u v k S
  · exact prefix_three_frame_return u v k S

private abbrev shortRepeats (odd00 : Bool) (h : ℕ) := 2 * h + if odd00 then 1 else 0
private abbrev shortTerm (odd00 : Bool) : List (Fin 2) := if odd00 then [0, 0] else [1, 0, 0]
private abbrev shortTail (odd00 : Bool) (h : ℕ) (R : Bits) :=
  scannerGuardTail h (if odd00 then 6 else 4) R

private def shortScannerWord (j : ℕ) (odd00 : Bool) (h : ℕ) : List (Fin 2) :=
  [1, 1, 0, 1] ++ (P ^ j ++ (scanner101 ^ (shortRepeats odd00 h) ++ shortTerm odd00))

private def shortScannerEntryClock (j : ℕ) (odd00 : Bool) (h : ℕ) : ℕ :=
  (14 + 2 * j) + (32 * h + if odd00 then 23 else 19)

private theorem short_to_frame (j : ℕ) (odd00 : Bool) (u v k h : ℕ) (R : Bits) :
    ReachesIn target (shortScannerEntryClock j odd00 h)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push (shortScannerWord j odd00 h) R))
      (shortFrame j u v k (shortTail odd00 h R)) := by
  let L := push (Q ^ j) (push [0] (push (Q ^ (k + 3)) (base u v)))
  cases odd00
  · have h1 := b1101_prefix_to_a u v k j (push (scanner101 ^ (2 * h)) (push [1, 0, 0] R))
    have ht := a101_100_terminal_exact (2 * h) L R
    rw [c6_phase_even] at ht
    have hs := c6_sweep_exact h (push [0, 1, 0] L) (push (I ^ (4 + 3)) R)
    have hts := ht.trans hs
    rw [scanner_guard_split h 4 R] at hts
    have hh := h1.trans hts
    have hc : shortScannerEntryClock j false h = (14 + 2 * j) + (13 * (2 * h) + 19 + 6 * h) := by
      change (14 + 2 * j) + (32 * h + 19) = _
      omega
    rw [hc]
    simp (config := { failIfUnchanged := false }) only [shortScannerWord, shortRepeats,
      shortTerm, shortFrame, shortTail, L, Bool.false_eq_true, ite_false, Nat.add_zero,
      ListBlank.append_append, List.append_assoc] at hh ⊢
    exact hh
  · have h1 := b1101_prefix_to_a u v k j (push (scanner101 ^ (2 * h + 1)) (push [0, 0] R))
    have ht := a101_00_positive_terminal_exact (2 * h) L R
    rw [c6_phase_even] at ht
    have hs := c6_sweep_exact h (push [0, 1, 0] L) (push (I ^ (6 + 3)) R)
    have hts := ht.trans hs
    rw [scanner_guard_split h 6 R] at hts
    have hh := h1.trans hts
    have hc : shortScannerEntryClock j true h = (14 + 2 * j) + (13 * (2 * h + 1) + 10 + 6 * h) := by
      change (14 + 2 * j) + (32 * h + 23) = _
      omega
    rw [hc]
    simp (config := { failIfUnchanged := false }) only [shortScannerWord, shortRepeats,
      shortTerm, shortFrame, shortTail, L, ite_true, ListBlank.append_append, List.append_assoc] at hh ⊢
    exact hh

def ShortScannerPrefix.word (m : ShortScannerPrefix) (odd00 : Bool) (h : ℕ) : List (Fin 2) :=
  shortScannerWord m.pairs odd00 h

def ShortScannerPrefix.entryClock (m : ShortScannerPrefix) (odd00 : Bool) (h : ℕ) : ℕ :=
  shortScannerEntryClock m.pairs odd00 h

/-- Exact return for the two missing parities at prefix lengths two and three. -/
theorem b1101_short_prefixed_return_exact (m : ShortScannerPrefix) (odd00 : Bool) (u v k h : ℕ) (R : Bits) :
    ReachesIn target (m.entryClock odd00 h + m.returnClock u v k)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push (m.word odd00 h) R))
      (Cfg.headRight C default (m.result u v k (shortTail odd00 h R))) :=
  (short_to_frame m.pairs odd00 u v k h R).trans
    (short_frame_return m u v k (shortTail odd00 h R))

/-! The one- and four-pair returns need two right guards: six ones
when the C6 run is empty, and three ones followed by zero otherwise. -/

private def edgeFrame (m k u v : ℕ) (G : List (Fin 2)) (R : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C (push [0, 1, 0] (push (Q ^ m) (push [0] (push (Q ^ (k + 3)) (base u v)))))
    (push G R)

private abbrev edge_one_positive_write := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem edge_one_positive_kernel (L R : Bits) :
    ReachesIn target 194
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 1, 0] R))
      (Cfg.headLeft C L (push edge_one_positive_write R)) := by
  l17_exact_steps

theorem edge_one_positive_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 241) (edgeFrame 1 0 u v [1, 1, 1, 0] R)
      (Cfg.headRight C default (five_run_bottom_result u
        (push (I ^ (2 * v + 3)) (push edge_one_positive_write R)))) := by
  let L := push (P ^ (v + 2)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := edge_one_positive_kernel (push [1] L) R
  have hs : edgeFrame 1 0 u v [1, 1, 1, 0] R =
      Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1, 0] R) := by
    unfold edgeFrame
    have hf : Cfg.headLeft C
        (push [0, 1, 0] (push (Q ^ 1) (push [0] (push (Q ^ (0 + 3)) (base u v)))))
        (push [1, 1, 1, 0] R) =
        Cfg.headRight C (push [1, 0] (push (Q ^ 1) (push [0] (push (Q ^ (0 + 3)) (base u v)))))
          (push [0, 1, 1, 1, 0] R) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 5 + (v + 2) by omega, ListBlank.append_pow_add P 5 (v + 2)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push edge_one_positive_write R) =
      Cfg.headRight C L (push [1] (push edge_one_positive_write R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hf] at h1
  have h2 := scanner_cut_short_finish u (v + 1) (push edge_one_positive_write R)
  have ht : 2 * (v + 1) + 1 = 2 * v + 3 := by omega
  rw [ht] at h2
  convert h1.trans h2 using 1 <;> omega

private abbrev edge_one_empty_write := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem edge_one_empty_kernel (L R : Bits) :
    ReachesIn target 118
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 1, 1, 1, 1] R))
      (Cfg.headLeft C L (push edge_one_empty_write R)) := by
  l17_exact_steps

theorem edge_one_empty_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 163) (edgeFrame 1 0 u v [1, 1, 1, 1, 1, 1] R)
      (Cfg.headRight C default (five_run_bottom_result u
        (push (I ^ (2 * v + 1)) (push edge_one_empty_write R)))) := by
  let L := push (P ^ (v + 1)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := edge_one_empty_kernel (push [1] L) R
  have hs : edgeFrame 1 0 u v [1, 1, 1, 1, 1, 1] R =
      Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1, 1, 1, 1] R) := by
    unfold edgeFrame
    have hf : Cfg.headLeft C
        (push [0, 1, 0] (push (Q ^ 1) (push [0] (push (Q ^ (0 + 3)) (base u v)))))
        (push [1, 1, 1, 1, 1, 1] R) =
        Cfg.headRight C (push [1, 0] (push (Q ^ 1) (push [0] (push (Q ^ (0 + 3)) (base u v)))))
          (push [0, 1, 1, 1, 1, 1, 1] R) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 6 + (v + 1) by omega, ListBlank.append_pow_add P 6 (v + 1)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push edge_one_empty_write R) =
      Cfg.headRight C L (push [1] (push edge_one_empty_write R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hf] at h1
  have h2 := scanner_cut_short_finish u (v + 0) (push edge_one_empty_write R)
  have ht : 2 * (v + 0) + 1 = 2 * v + 1 := by omega
  rw [ht] at h2
  convert h1.trans h2 using 1 <;> omega

private abbrev edge_four_positive0_write := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Fin 2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem edge_four_positive0_kernel (L R : Bits) :
    ReachesIn target 128
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 1, 0] R))
      (Cfg.headLeft C L (push edge_four_positive0_write R)) := by
  l17_exact_steps

theorem edge_four_positive0_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 173) (edgeFrame 4 0 u v [1, 1, 1, 0] R)
      (Cfg.headRight C default (five_run_bottom_result u
        (push (I ^ (2 * v + 1)) (push edge_four_positive0_write R)))) := by
  let L := push (P ^ (v + 1)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := edge_four_positive0_kernel (push [1] L) R
  have hs : edgeFrame 4 0 u v [1, 1, 1, 0] R =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1, 0] R) := by
    unfold edgeFrame
    have hf : Cfg.headLeft C
        (push [0, 1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (0 + 3)) (base u v)))))
        (push [1, 1, 1, 0] R) =
        Cfg.headRight C (push [1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (0 + 3)) (base u v)))))
          (push [0, 1, 1, 1, 0] R) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 6 + (v + 1) by omega, ListBlank.append_pow_add P 6 (v + 1)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push edge_four_positive0_write R) =
      Cfg.headRight C L (push [1] (push edge_four_positive0_write R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hf] at h1
  have h2 := scanner_cut_short_finish u (v + 0) (push edge_four_positive0_write R)
  have ht : 2 * (v + 0) + 1 = 2 * v + 1 := by omega
  rw [ht] at h2
  convert h1.trans h2 using 1 <;> omega

private abbrev edge_four_positive1_write := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Fin 2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem edge_four_positive1_kernel (L R : Bits) :
    ReachesIn target 226
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 1, 0] R))
      (Cfg.headLeft C L (push edge_four_positive1_write R)) := by
  l17_exact_steps

theorem edge_four_positive1_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 273) (edgeFrame 4 1 u v [1, 1, 1, 0] R)
      (Cfg.headRight C default (five_run_bottom_result u
        (push (I ^ (2 * v + 3)) (push edge_four_positive1_write R)))) := by
  let L := push (P ^ (v + 2)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := edge_four_positive1_kernel (push [1] L) R
  have hs : edgeFrame 4 1 u v [1, 1, 1, 0] R =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1, 0] R) := by
    unfold edgeFrame
    have hf : Cfg.headLeft C
        (push [0, 1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (1 + 3)) (base u v)))))
        (push [1, 1, 1, 0] R) =
        Cfg.headRight C (push [1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (1 + 3)) (base u v)))))
          (push [0, 1, 1, 1, 0] R) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 5 + (v + 2) by omega, ListBlank.append_pow_add P 5 (v + 2)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push edge_four_positive1_write R) =
      Cfg.headRight C L (push [1] (push edge_four_positive1_write R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hf] at h1
  have h2 := scanner_cut_short_finish u (v + 1) (push edge_four_positive1_write R)
  have ht : 2 * (v + 1) + 1 = 2 * v + 3 := by omega
  rw [ht] at h2
  convert h1.trans h2 using 1 <;> omega

private abbrev edge_four_empty0_write := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem edge_four_empty0_kernel (L R : Bits) :
    ReachesIn target 138
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 1, 1, 1, 1] R))
      (Cfg.headLeft C L (push edge_four_empty0_write R)) := by
  l17_exact_steps

theorem edge_four_empty0_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 187) (edgeFrame 4 0 u v [1, 1, 1, 1, 1, 1] R)
      (Cfg.headRight C default (five_run_bottom_result u
        (push (I ^ (2 * v + 5)) (push edge_four_empty0_write R)))) := by
  let L := push (P ^ (v + 3)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := edge_four_empty0_kernel (push [1] L) R
  have hs : edgeFrame 4 0 u v [1, 1, 1, 1, 1, 1] R =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1, 1, 1, 1] R) := by
    unfold edgeFrame
    have hf : Cfg.headLeft C
        (push [0, 1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (0 + 3)) (base u v)))))
        (push [1, 1, 1, 1, 1, 1] R) =
        Cfg.headRight C (push [1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (0 + 3)) (base u v)))))
          (push [0, 1, 1, 1, 1, 1, 1] R) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 4 + (v + 3) by omega, ListBlank.append_pow_add P 4 (v + 3)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push edge_four_empty0_write R) =
      Cfg.headRight C L (push [1] (push edge_four_empty0_write R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hf] at h1
  have h2 := scanner_cut_short_finish u (v + 2) (push edge_four_empty0_write R)
  have ht : 2 * (v + 2) + 1 = 2 * v + 5 := by omega
  rw [ht] at h2
  convert h1.trans h2 using 1 <;> omega

private abbrev edge_four_empty1_write := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem edge_four_empty1_kernel (L R : Bits) :
    ReachesIn target 158
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 1, 1, 1, 1] R))
      (Cfg.headLeft C L (push edge_four_empty1_write R)) := by
  l17_exact_steps

theorem edge_four_empty1_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 203) (edgeFrame 4 1 u v [1, 1, 1, 1, 1, 1] R)
      (Cfg.headRight C default (five_run_bottom_result u
        (push (I ^ (2 * v + 1)) (push edge_four_empty1_write R)))) := by
  let L := push (P ^ (v + 1)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := edge_four_empty1_kernel (push [1] L) R
  have hs : edgeFrame 4 1 u v [1, 1, 1, 1, 1, 1] R =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] L)) (push [0, 1, 1, 1, 1, 1, 1] R) := by
    unfold edgeFrame
    have hf : Cfg.headLeft C
        (push [0, 1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (1 + 3)) (base u v)))))
        (push [1, 1, 1, 1, 1, 1] R) =
        Cfg.headRight C (push [1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (1 + 3)) (base u v)))))
          (push [0, 1, 1, 1, 1, 1, 1] R) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 6 + (v + 1) by omega, ListBlank.append_pow_add P 6 (v + 1)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push edge_four_empty1_write R) =
      Cfg.headRight C L (push [1] (push edge_four_empty1_write R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hf] at h1
  have h2 := scanner_cut_short_finish u (v + 0) (push edge_four_empty1_write R)
  have ht : 2 * (v + 0) + 1 = 2 * v + 1 := by omega
  rw [ht] at h2
  convert h1.trans h2 using 1 <;> omega

private abbrev edge_four_empty2_write := ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem edge_four_empty2_kernel (L R : Bits) :
    ReachesIn target 128
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0] L) (push [0, 1, 1, 1, 1, 1, 1] R))
      (Cfg.headLeft C L (push edge_four_empty2_write R)) := by
  l17_exact_steps

theorem edge_four_empty2_exact (u v : ℕ) (R : Bits) :
    ReachesIn target (2 * u + 2 * v + 183) (edgeFrame 4 2 u v [1, 1, 1, 1, 1, 1] R)
      (Cfg.headRight C default (five_run_bottom_result u
        (push (I ^ (2 * v + 11)) (push edge_four_empty2_write R)))) := by
  let L := push (P ^ (v + 6)) (push [0] (push (P ^ (u + 6)) default))
  have h1 := edge_four_empty2_kernel (push [1] L) R
  have hs : edgeFrame 4 2 u v [1, 1, 1, 1, 1, 1] R =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0] (push [1] L)) (push [0, 1, 1, 1, 1, 1, 1] R) := by
    unfold edgeFrame
    have hf : Cfg.headLeft C
        (push [0, 1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (2 + 3)) (base u v)))))
        (push [1, 1, 1, 1, 1, 1] R) =
        Cfg.headRight C (push [1, 0] (push (Q ^ 4) (push [0] (push (Q ^ (2 + 3)) (base u v)))))
          (push [0, 1, 1, 1, 1, 1, 1] R) :=
      Cfg.headLeft_cons C (0 : Fin 2) _ _
    rw [hf]
    unfold base L
    rw [show v + 7 = 1 + (v + 6) by omega, ListBlank.append_pow_add P 1 (v + 6)]
    rfl
  rw [← hs] at h1
  have hf : Cfg.headLeft C (push [1] L) (push edge_four_empty2_write R) =
      Cfg.headRight C L (push [1] (push edge_four_empty2_write R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) _ _
  rw [hf] at h1
  have h2 := scanner_cut_short_finish u (v + 5) (push edge_four_empty2_write R)
  have ht : 2 * (v + 5) + 1 = 2 * v + 11 := by omega
  rw [ht] at h2
  convert h1.trans h2 using 1 <;> omega

private theorem edge_one_positive_wide_kernel (L R : Bits) :
    ReachesIn target 45
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 0] R))
      (Cfg.headRight C (push [0, 1, 0] L) (push (I ^ 8) R)) := by
  change ReachesIn target 45 _ (Cfg.headRight C (push [0, 1, 0] L) (push [1, 1, 1, 1, 1, 1, 1, 1] R))
  l17_exact_steps

private theorem edge_one_empty_wide_kernel (L R : Bits) :
    ReachesIn target 84
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0] L)
        (push [0, 1, 1, 1, 1, 1, 1] R))
      (Cfg.headLeft C L (push (Q ^ 10) R)) := by
  set_option maxRecDepth 8192 in
    l17_exact_steps

theorem edge_one_positive_wide_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (49 + scannerCutClock u v k) (edgeFrame 1 (k + 1) u v [1, 1, 1, 0] R)
      (Cfg.headRight C default (scannerCutResult u v (push (I ^ 8) R) k)) := by
  let L := push (P ^ (k + 3)) (push [0] (base u v))
  have hf : edgeFrame 1 (k + 1) u v [1, 1, 1, 0] R =
      Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 0] R) := by
    unfold edgeFrame
    have he : push [0] (push (Q ^ (k + 1 + 3)) (base u v)) = push [0, 1] L := by
      rw [rotLB0, show k + 1 + 3 = 1 + (k + 3) by omega, ListBlank.append_pow_add]
      rfl
    rw [he]
    exact Cfg.headLeft_cons C (0 : Fin 2) _ _
  have h1 := edge_one_positive_wide_kernel L R
  rw [← hf] at h1
  have he : Cfg.headRight C (push [0, 1, 0] L) (push (I ^ 8) R) =
      Cfg.headLeft C (push (Q ^ 2) L) (push (I ^ 7) R) :=
    Cfg.headRight_cons C (1 : Fin 2) _ _
  rw [he] at h1
  have h2 := c01_sweep_exact 2 L (push (I ^ 7) R)
  have hc : Cfg.headLeft C L (push (([1, 1] : List (Fin 2)) ^ 2) (push (I ^ 7) R)) =
      scannerCutSource u v k (push (I ^ 8) R) := by
    change Cfg.headLeft C (push (P ^ (k + 3)) (push [0] (base u v))) _ = _
    rw [← rotLB0]
    rfl
  rw [hc] at h2
  exact (h1.trans h2).trans (scanner_cut_return_exact u v k (push (I ^ 8) R))

theorem edge_one_empty_wide_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (143 + 2 * u + 2 * v + 2 * k) (edgeFrame 1 (k + 1) u v [1, 1, 1, 1, 1, 1] R)
      (Cfg.headRight C default (cpop_bottom_result u v (push (I ^ (2*k)) (push (Q ^ 10) R)))) := by
  let L := push (Q ^ k) (base u v)
  have h1 := edge_one_empty_wide_kernel L R
  have hf : edgeFrame 1 (k + 1) u v [1, 1, 1, 1, 1, 1] R =
      Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0] L)
        (push [0, 1, 1, 1, 1, 1, 1] R) := by
    unfold edgeFrame
    rw [show k + 1 + 3 = 4 + k by omega, ListBlank.append_pow_add]
    exact Cfg.headLeft_cons C (0 : Fin 2) _ _
  rw [← hf] at h1
  have h2 := c01_sweep_exact k (base u v) (push (Q ^ 10) R)
  rw [one_pow_two_mul] at h2
  have h3 := b1101100_finish u v (push (I ^ (2*k)) (push (Q ^ 10) R))
  convert (h1.trans h2).trans h3 using 1 <;> omega

private theorem edge_four_kernel (L R : Bits) :
    ReachesIn target 44
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0] L) (push [0, 1, 1, 1] R))
      (Cfg.headLeft B L (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  l17_exact_steps

private theorem edge_four_to_b (u v k : ℕ) (S : Bits) :
    ReachesIn target 62 (edgeFrame 4 k u v [1, 1, 1] S)
      (Cfg.headRight B (push (Q ^ 9) (push (P ^ (k + 1)) (push [0] (base u v)))) S) := by
  let L := push (P ^ (k + 1)) (push [0] (base u v))
  have hf : edgeFrame 4 k u v [1, 1, 1] S =
      Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0] (push [1] L))
        (push [0, 1, 1, 1] S) := by
    unfold edgeFrame
    rw [show k + 3 = 2 + (k + 1) by omega, ListBlank.append_pow_add]
    have hr : push [0] (push (Q ^ 2) (push (Q ^ (k + 1)) (base u v))) =
        push [0, 1, 0, 1] L := by
      change push [0, 1, 0, 1] (push [0] (push (Q ^ (k + 1)) (base u v))) = _
      rw [rotLB0 (k + 1)]
    rw [hr]
    exact Cfg.headLeft_cons C (0 : Fin 2) _ _
  have h1 := edge_four_kernel (push [1] L) S
  rw [← hf] at h1
  have he : Cfg.headLeft B (push [1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] S) =
      Cfg.headRight B L (push (Q ^ 9) S) :=
    Cfg.headLeft_cons B (1 : Fin 2) _ _
  rw [he] at h1
  exact h1.trans (b10_sweep_exact 9 L S)

theorem edge_four_positive_wide_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (81 + scannerCutClock u v k) (edgeFrame 4 (k + 2) u v [1, 1, 1, 0] R)
      (Cfg.headRight C default (scannerCutResult u v (push (I ^ 16) R) k)) := by
  let L := push (P ^ (k + 3)) (push [0] (base u v))
  have h1 := edge_four_to_b u v (k + 2) (push [0] R)
  have h0 : ReachesIn target 1 (Cfg.headRight B (push (Q ^ 9) L) (push [0] R))
      (Cfg.headLeft C (push (Q ^ 9) L) (push [1] R)) := by
    l17_exact_steps
  have h2 := c01_sweep_exact 9 L (push [1] R)
  have hc : Cfg.headLeft C L (push (([1, 1] : List (Fin 2)) ^ 9) (push [1] R)) =
      scannerCutSource u v k (push (I ^ 16) R) := by
    change Cfg.headLeft C (push (P ^ (k + 3)) (push [0] (base u v))) _ = _
    rw [← rotLB0]
    rfl
  rw [hc] at h2
  exact ((h1.trans h0).trans h2).trans (scanner_cut_return_exact u v k (push (I ^ 16) R))

theorem edge_four_empty_wide_exact (u v k : ℕ) (R : Bits) :
    ReachesIn target (185 + 2 * u + 2 * v + 2 * k)
      (edgeFrame 4 (k + 3) u v [1, 1, 1, 1, 1, 1] R)
      (Cfg.headRight C default (cpop_bottom_result u v
        (push (I ^ (2*k + 2)) (push (Q ^ 14) R)))) := by
  let L := push (P ^ (k + 4)) (push [0] (base u v))
  have h1 := edge_four_to_b u v (k + 3) (push [1, 1, 1] R)
  have h2 := b_to_d_sweep_exact 8 L R
  have h3 := k22_c01_last_exact k (push [0] (base u v)) (push (Q ^ 8) R)
  have h123 := (h1.trans h2).trans h3
  have h4 := c01_sweep_exact 1 (base u v) (push (([1, 1] : List (Fin 2)) ^ k) (push (Q ^ 14) R))
  have h1234 := h123.trans h4
  rw [one_pow_two_mul 1, one_pow_two_mul k] at h1234
  have he : push (I ^ (2 * 1)) (push (I ^ (2*k)) (push (Q ^ 14) R)) =
      push (I ^ (2*k + 2)) (push (Q ^ 14) R) := by
    change push (I ^ 2) (push (I ^ (2*k)) (push (Q ^ 14) R)) = _
    rw [← ListBlank.append_pow_add, Nat.add_comm 2 (2*k)]
  rw [he] at h1234
  have h5 := b1101100_finish u v (push (I ^ (2*k + 2)) (push (Q ^ 14) R))
  convert h1234.trans h5 using 1 <;> (first | rfl | omega)

/-- The two short prefixes that must inspect beyond the first three guard ones. -/
inductive EdgeScannerPrefix where
  | one | four

def EdgeScannerPrefix.pairs : EdgeScannerPrefix → ℕ
  | .one => 1
  | .four => 4

private def edgeGuard (h : ℕ) : List (Fin 2) :=
  match h with
  | 0 => [1, 1, 1, 1, 1, 1]
  | _ + 1 => [1, 1, 1, 0]

private def edgeTail (odd00 : Bool) (h : ℕ) (R : Bits) : Bits :=
  match h with
  | 0 => push (I ^ (if odd00 then 3 else 1)) R
  | l + 1 => push [1, 0] (push (scannerC6 ^ l) (push (I ^ (if odd00 then 9 else 7)) R))

def EdgeScannerPrefix.returnClock (u v : ℕ) : EdgeScannerPrefix → ℕ → ℕ → ℕ
  | .one, 0, 0 => 2 * u + 2 * v + 163
  | .one, 0, k + 1 => 143 + 2 * u + 2 * v + 2 * k
  | .one, _ + 1, 0 => 2 * u + 2 * v + 241
  | .one, _ + 1, k + 1 => 49 + scannerCutClock u v k
  | .four, 0, 0 => 2 * u + 2 * v + 187
  | .four, 0, 1 => 2 * u + 2 * v + 203
  | .four, 0, 2 => 2 * u + 2 * v + 183
  | .four, 0, k + 3 => 185 + 2 * u + 2 * v + 2 * k
  | .four, _ + 1, 0 => 2 * u + 2 * v + 173
  | .four, _ + 1, 1 => 2 * u + 2 * v + 273
  | .four, _ + 1, k + 2 => 81 + scannerCutClock u v k

def EdgeScannerPrefix.result (u v : ℕ) (R : Bits) : EdgeScannerPrefix → ℕ → ℕ → Bits
  | .one, 0, 0 => five_run_bottom_result u (push (I ^ (2 * v + 1)) (push edge_one_empty_write R))
  | .one, 0, k + 1 => cpop_bottom_result u v (push (I ^ (2*k)) (push (Q ^ 10) R))
  | .one, _ + 1, 0 => five_run_bottom_result u (push (I ^ (2 * v + 3)) (push edge_one_positive_write R))
  | .one, _ + 1, k + 1 => scannerCutResult u v (push (I ^ 8) R) k
  | .four, 0, 0 => five_run_bottom_result u (push (I ^ (2 * v + 5)) (push edge_four_empty0_write R))
  | .four, 0, 1 => five_run_bottom_result u (push (I ^ (2 * v + 1)) (push edge_four_empty1_write R))
  | .four, 0, 2 => five_run_bottom_result u (push (I ^ (2 * v + 11)) (push edge_four_empty2_write R))
  | .four, 0, k + 3 => cpop_bottom_result u v (push (I ^ (2*k + 2)) (push (Q ^ 14) R))
  | .four, _ + 1, 0 => five_run_bottom_result u (push (I ^ (2 * v + 1)) (push edge_four_positive0_write R))
  | .four, _ + 1, 1 => five_run_bottom_result u (push (I ^ (2 * v + 3)) (push edge_four_positive1_write R))
  | .four, _ + 1, k + 2 => scannerCutResult u v (push (I ^ 16) R) k

private theorem edge_frame_return (m : EdgeScannerPrefix) (u v k h : ℕ) (R : Bits) :
    ReachesIn target (EdgeScannerPrefix.returnClock u v m h k)
      (edgeFrame m.pairs k u v (edgeGuard h) R)
      (Cfg.headRight C default (EdgeScannerPrefix.result u v R m h k)) := by
  match m, h, k with
  | .one, 0, 0 => exact edge_one_empty_exact u v R
  | .one, 0, k + 1 => exact edge_one_empty_wide_exact u v k R
  | .one, _ + 1, 0 => exact edge_one_positive_exact u v R
  | .one, _ + 1, k + 1 => exact edge_one_positive_wide_exact u v k R
  | .four, 0, 0 => exact edge_four_empty0_exact u v R
  | .four, 0, 1 => exact edge_four_empty1_exact u v R
  | .four, 0, 2 => exact edge_four_empty2_exact u v R
  | .four, 0, k + 3 => exact edge_four_empty_wide_exact u v k R
  | .four, _ + 1, 0 => exact edge_four_positive0_exact u v R
  | .four, _ + 1, 1 => exact edge_four_positive1_exact u v R
  | .four, _ + 1, k + 2 => exact edge_four_positive_wide_exact u v k R

private theorem shortFrame_to_edge (m k u v : ℕ) (odd00 : Bool) (h : ℕ) (R : Bits) :
    shortFrame m u v k (shortTail odd00 h R) =
      edgeFrame m k u v (edgeGuard h) (edgeTail odd00 h R) := by
  cases h <;> cases odd00 <;> rfl

/-- Exact scanner return for one or four prepended pairs, in both
parities that needed additional short-prefix cases. -/
theorem b1101_edge_prefixed_return_exact (m : EdgeScannerPrefix) (odd00 : Bool) (u v k h : ℕ) (R : Bits) :
    ReachesIn target (shortScannerEntryClock m.pairs odd00 h + EdgeScannerPrefix.returnClock u v m h k)
      (Cfg.headRight B (push (Q ^ (k + 5)) (base u v)) (push (shortScannerWord m.pairs odd00 h) R))
      (Cfg.headRight C default (EdgeScannerPrefix.result u v (edgeTail odd00 h R) m h k)) := by
  have ht := short_to_frame m.pairs odd00 u v k h R
  rw [shortFrame_to_edge] at ht
  exact ht.trans (edge_frame_return m u v k h (edgeTail odd00 h R))

/-- Terminal words for which this dispatcher proves a full C return. -/
inductive BReturnTerminal where
  | zero | tripleOne | oneOneZeroZero | oneOneZeroOneZeroZero | oneOneZeroOneOneZeroZero
  | scannerEven100 (h : ℕ) | scannerOdd00 (h : ℕ)
  | scannerOdd100 (h : ℕ) | scannerPositiveEven00 (h : ℕ)
  | prefixedScanner (t : PrefixedScanner) (j : ℕ)
  | shortPrefixedScanner (m : ShortScannerPrefix) (odd00 : Bool) (h : ℕ)
  | edgePrefixedScanner (m : EdgeScannerPrefix) (odd00 : Bool) (h : ℕ)

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
  | .prefixedScanner t j => t.word j
  | .shortPrefixedScanner m odd00 h => m.word odd00 h
  | .edgePrefixedScanner m odd00 h => shortScannerWord m.pairs odd00 h

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
  | .prefixedScanner t j => t.clockToCut j + scannerCutClock u v k
  | .shortPrefixedScanner m odd00 h => m.entryClock odd00 h + m.returnClock u v k
  | .edgePrefixedScanner m odd00 h => shortScannerEntryClock m.pairs odd00 h + EdgeScannerPrefix.returnClock u v m h k

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
  | .prefixedScanner t j => scannerCutResult u v (t.cutSuffix j R) k
  | .shortPrefixedScanner m odd00 h => m.result u v k (shortTail odd00 h R)
  | .edgePrefixedScanner m odd00 h => EdgeScannerPrefix.result u v (edgeTail odd00 h R) m h k

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
  · rename_i s j
    exact b1101_prefixed_return_exact s u v k j R
  · rename_i m odd00 h
    exact b1101_short_prefixed_return_exact m odd00 u v k h R
  · rename_i m odd00 h
    exact b1101_edge_prefixed_return_exact m odd00 u v k h R

private def complementaryScanner (odd00 : Bool) (h : ℕ) : ℕ → BReturnTerminal
  | 0 => if odd00 then .scannerOdd00 h else .scannerEven100 h
  | 1 => .edgePrefixedScanner .one odd00 h
  | 2 => .shortPrefixedScanner .two odd00 h
  | 3 => .shortPrefixedScanner .three odd00 h
  | 4 => .edgePrefixedScanner .four odd00 h
  | j + 5 => .prefixedScanner (if odd00 then .wideOdd00 h else .wideEven100 h) j

private theorem complementaryScanner_word (odd00 : Bool) (h j : ℕ) :
    (complementaryScanner odd00 h j).word = shortScannerWord j odd00 h := by
  match j with
  | 0 => cases odd00 <;> rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | j + 5 => cases odd00 <;> rfl

/-- Every two-block scanner word is covered, for either terminator and
arbitrary prefix and repeat counts. Its selected terminal has the exact
return theorem `b_return_terminal_exact`. -/
theorem scanner_dispatch_complete (j r : ℕ) (terminates00 : Bool) :
    ∃ t : BReturnTerminal, t.word =
      [1, 1, 0, 1] ++ (P ^ j ++ (scanner101 ^ r ++ shortTerm terminates00)) := by
  cases terminates00
  · by_cases he : r % 2 = 0
    · obtain ⟨h, rfl⟩ : ∃ h : ℕ, r = 2 * h := ⟨r / 2, by omega⟩
      exact ⟨complementaryScanner false h j, complementaryScanner_word false h j⟩
    · obtain ⟨h, rfl⟩ : ∃ h : ℕ, r = 2 * h + 1 := ⟨r / 2, by omega⟩
      exact ⟨.prefixedScanner (.odd100 h) j, rfl⟩
  · by_cases hz : r = 0
    · subst r
      refine ⟨.prefixedScanner .zero00 j, ?_⟩
      rfl
    · by_cases he : r % 2 = 0
      · obtain ⟨h, rfl⟩ : ∃ h : ℕ, r = 2 * h + 2 := ⟨(r - 2) / 2, by omega⟩
        exact ⟨.prefixedScanner (.positiveEven00 h) j, rfl⟩
      · obtain ⟨h, rfl⟩ : ∃ h : ℕ, r = 2 * h + 1 := ⟨r / 2, by omega⟩
        exact ⟨complementaryScanner true h j, complementaryScanner_word true h j⟩

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

#print axioms CryptidLink.L17.b1101_prefixed_to_cut
#print axioms CryptidLink.L17.b1101_prefixed_return_exact

#print axioms CryptidLink.L17.b1101_short_prefixed_return_exact

#print axioms CryptidLink.L17.b1101_edge_prefixed_return_exact

#print axioms CryptidLink.L17.scanner_dispatch_complete

#print axioms CryptidLink.L17.mixed_101_01_00_return_exact
#print axioms CryptidLink.L17.mixed_resumed_return_exact
#print axioms CryptidLink.L17.mixed_resumed_scanner_complete
#print axioms CryptidLink.L17.width_four_cut_return_exact
#print axioms CryptidLink.L17.mixed_narrow_guard_complete
#print axioms CryptidLink.L17.mixed_narrow_return_exact
#print axioms CryptidLink.L17.return_blocks_exact
#print axioms CryptidLink.L17.b_return_blocks_exact
#print axioms CryptidLink.L17.mixed_return_blocks_exact
#print axioms CryptidLink.L17.mixed_narrow_return_blocks_exact
#print axioms CryptidLink.L17.mixed_narrow_guarded_blocks_exact
#print axioms CryptidLink.L17.mixed_two_wide_return_exact
