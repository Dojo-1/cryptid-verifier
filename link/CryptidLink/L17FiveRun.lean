import CryptidLink.L17MixedBoundary

/-! Exact returns for the 110100 branch of the B dispatcher. -/

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
  exact (short_C2B_exact (base u v) (push (Q ^ j) (push [1, 1, 0, 1, 0, 0] R))).trans
    (b110100_after_sweep_exact u v 0 j R)

/-- From the C5 entry (previous width 3), B starts with nine pairs.
The theorem includes the 62-step entry, the full sweep and the return. -/
theorem c5_110100_after_sweep_exact (u v j : ℕ) (R : Bits) :
    ReachesIn target (62 + (2 * j + b110100_clock u v (4 + j)))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] (base u v))
        (push [0, 1, 1, 1] (push (Q ^ j) (push [1, 1, 0, 1, 0, 0] R))))
      (Cfg.headRight C default (b110100_result u v R (4 + j))) := by
  exact (short_C5B_exact (base u v) (push (Q ^ j) (push [1, 1, 0, 1, 0, 0] R))).trans
    (b110100_after_sweep_exact u v 4 j R)

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
