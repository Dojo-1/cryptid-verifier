import CryptidLink.L17MixedBoundary

/-! Exact return for the wide 110100 branch of the B dispatcher. -/

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

end CryptidLink.L17

#print axioms CryptidLink.L17.five_run00_wide_exact
#print axioms CryptidLink.L17.b110100_wide_exact
