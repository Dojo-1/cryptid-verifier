import CryptidLink.L17b
/-!
# L17: GPT's contextual lemmas F100, F111 and Z/P, and the orbit to C(30066981019881, 27)

𝒞(a; X) := 0^∞ C> (01)^a X, with X an arbitrary right context. Lemmas (derivation by GPT,
`analysis/l17-stacked-section/DERIVATION.md`; proved here against the raw machine):

* `zT`:   𝒞(a; 00 w)               ⊢⁺ 𝒞(0; 1^(2a+4) w)
* `pzT`:  𝒞(a+1; 11 (01)^(m+1) X)  ⊢⁺ 𝒞(0; 1^(2a+15) (01)^m X)
* `F100`: 𝒞(u+7; (10)^(c+1) 0 v)   ⊢⁺ 𝒞(0; 1^(2u+2) (01)^7 1^(2c+3) v)
* `F111`: 𝒞(u+5; (10)^(d+1) 111 v) ⊢⁺ 𝒞(0; 1^(2u+2) (01)^(d+7) 0 v)

The fixed kernels K11, K43, K22 are proved by direct execution with symbolic outside context, so the
context is untouched by construction. `blank_reaches_boundary3`: from the blank tape the machine reaches
C(30066981019881, 27), back in the plain two-counter section.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- 𝒞(a; X) = 0^∞ C> (01)^a X. -/
def Ccal (a : ℕ) (X : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) X)

theorem entryC (a : ℕ) (X : ListBlank (Fin 2)) :
    ReachesPlus target (Ccal (a + 1) X)
      (Cfg.headRight A default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2)) X)) :=
  entryT a 0 X

theorem rotLB0 (n : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append [0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) s) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ n) (ListBlank.append [0] s) := by
  rw [ListBlank.append_append, ListBlank.append_append, rot_list]

/-! ## Fixed kernels (direct execution, symbolic context) -/

theorem segABT (L w : ListBlank (Fin 2)) :
    ReachesPlus target (Cfg.headRight A L (ListBlank.append [0, 0] w))
      (Cfg.headLeft C (ListBlank.append [1] L) (ListBlank.append [1] w)) := by
  bb_steps

theorem K11 (L Z : ListBlank (Fin 2)) :
    ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 1, 0, 1] L) (ListBlank.append [1, 0] Z))
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0] L) (ListBlank.append [0] Z)) := by
  bb_steps

theorem K43 (L R : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (ListBlank.append [1, 1] R))
      (Cfg.headLeft C (ListBlank.append [1] L)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] R)) := by
  bb_steps

theorem K22 (L R : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft D (ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (ListBlank.append [1, 0, 1, 0] R))
      (Cfg.headLeft C (ListBlank.append [1] L)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  bb_steps

/-! ## Z and P with context -/

/-- **Z:** 𝒞(a; 00 w) ⊢⁺ 𝒞(0; 1^(2a+4) w). -/
theorem zT (a : ℕ) (w : ListBlank (Fin 2)) :
    ReachesPlus target (Ccal a (ListBlank.append [0, 0] w))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 4)) w)) := by
  have h1 : ReachesPlus target (Ccal a (ListBlank.append [0, 0] w))
      (Cfg.headRight A default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
        (ListBlank.append [0, 0] w))) := by
    rcases a with _ | a
    · show ReachesPlus target (Cfg.headRight C default (ListBlank.append [0, 0] w))
        (Cfg.headRight A default (ListBlank.append [0, 1] (ListBlank.append [0, 0] w)))
      bb_steps
    · exact entryC a _
  have h2 := sweepA (a + 1) default (ListBlank.append [0, 0] w)
  have h3 := segABT (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default) w
  rw [rotLB] at h3
  have h4 := sweepC (a + 1) (ListBlank.append [1] default) (ListBlank.append [1] w)
  rw [hconv] at h4
  have e : ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [1] w)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 4)) w) := by
    rw [one_pow_two_mul, show 2 * a + 4 = (1 + 2 * (a + 1)) + 1 by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) (1 + 2 * (a + 1)) 1,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * (a + 1))]
    all_goals rfl
  rw [e] at h4
  exact ((h1.trans_star h2).trans h3).trans_star h4

/-- **P then Z:** 𝒞(a+1; 11 (01)^(m+1) X) ⊢⁺ 𝒞(0; 1^(2a+15) (01)^m X). -/
theorem pzT (a m : ℕ) (X : ListBlank (Fin 2)) :
    ReachesPlus target
      (Ccal (a + 1) (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1)) X)))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 15))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) X))) := by
  have h1 : ReachesPlus target
      (Ccal (a + 1) (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1)) X)))
      (Ccal (a + 5) (ListBlank.append [0, 0] (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) X)))) :=
    branch_ge2T a 0 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1)) X)
  have h2 := zT (a + 5) (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) X))
  rw [ListBlank.append_pow_succ', show 2 * (a + 5) + 4 + 1 = 2 * a + 15 by omega] at h2
  exact h1.trans h2

/-! ## F100 and F111 -/

/-- **F100:** 𝒞(u+7; (10)^(c+1) 0 v) ⊢⁺ 𝒞(0; 1^(2u+2) (01)^7 1^(2c+3) v). -/
theorem F100 (u c : ℕ) (v : ListBlank (Fin 2)) :
    ReachesPlus target
      (Ccal (u + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 1)) (ListBlank.append [0] v)))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * c + 3)) v)))) := by
  have hX : ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 1)) (ListBlank.append [0] v) =
      ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ c) (ListBlank.append [0] v)) :=
    ListBlank.append_pow_succ _ _ _
  have h1 := entryC (u + 6)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 1)) (ListBlank.append [0] v))
  have h2 := sweepA (u + 8) default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 1)) (ListBlank.append [0] v))
  have hs : ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 8)) default =
      ListBlank.append [0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default) := by
    rw [show u + 8 = 2 + (u + 6) by omega, ListBlank.append_pow_add]; rfl
  rw [hs, hX] at h2
  rw [hX] at h1
  have h3 := K11 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ c) (ListBlank.append [0] v))
  rw [rotLB0] at h3
  have h4 := sweepA c (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))
    (ListBlank.append [0] (ListBlank.append [0] v))
  have h5 := segABT (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
    (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))) v
  have hl5 : ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 2))
        (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)) := by
    rw [rotLB c, show c + 2 = c + 1 + 1 from rfl, ← ListBlank.append_pow_succ' _ (c + 1),
      ← ListBlank.append_pow_succ' _ c, show u + 6 = 6 + u by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 6 u]
    all_goals rfl
  rw [hl5] at h5
  have h6 := sweepC (c + 2) (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)) (ListBlank.append [1] v)
  have hr6 : ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 2)) (ListBlank.append [1] v) =
      ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1)) (ListBlank.append [1] v)) :=
    ListBlank.append_pow_succ _ _ _
  rw [hr6] at h6
  have h7 := K43 (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1)) (ListBlank.append [1] v))
  rw [rotLB u default] at h7
  have h8 := sweepC u (ListBlank.append [1] default)
    (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1)) (ListBlank.append [1] v)))
  rw [hconv] at h8
  have e : ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1)) (ListBlank.append [1] v)))) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * c + 3)) v))) := by
    rw [one_pow_two_mul u, one_pow_two_mul (c + 1), show 2 * u + 2 = (1 + 2 * u) + 1 by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) (1 + 2 * u) 1,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * u),
      show 2 * c + 3 = 2 * (c + 1) + 1 by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (c + 1)) 1]
    all_goals rfl
  rw [e] at h8
  exact (((((((h1.trans_star h2).trans h3).trans_star h4).trans h5).trans_star h6).trans h7).trans_star h8)

/-- **F111:** 𝒞(u+5; (10)^(d+1) 111 v) ⊢⁺ 𝒞(0; 1^(2u+2) (01)^(d+7) 0 v). -/
theorem F111 (u d : ℕ) (v : ListBlank (Fin 2)) :
    ReachesPlus target
      (Ccal (u + 5) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 1, 1] v)))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [0] v)))) := by
  have hX : ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 1, 1] v) =
      ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ d) (ListBlank.append [1, 1, 1] v)) :=
    ListBlank.append_pow_succ _ _ _
  have h1 := entryC (u + 4)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 1, 1] v))
  have h2 := sweepA (u + 6) default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 1, 1] v))
  have hs : ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default =
      ListBlank.append [0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default) := by
    rw [show u + 6 = 2 + (u + 4) by omega, ListBlank.append_pow_add]; rfl
  rw [hs, hX] at h2
  rw [hX] at h1
  have h3 := K11 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ d) (ListBlank.append [1, 1, 1] v))
  rw [rotLB0] at h3
  have hr3 : ListBlank.append (([0, 1] : List (Fin 2)) ^ d) (ListBlank.append [0] (ListBlank.append [1, 1, 1] v)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 1] v) :=
    ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) d (ListBlank.append [1, 1] v)
  rw [hr3] at h3
  have h4 := sweepA (d + 1) (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default))
    (ListBlank.append [1, 1] v)
  have h5 := segAEF (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
    (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default))) v
  have hl5 : ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 3))
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default)) := by
    rw [show d + 3 = d + 1 + 1 + 1 from rfl, ← ListBlank.append_pow_succ' _ (d + 1 + 1),
      ← ListBlank.append_pow_succ' _ (d + 1)]
    all_goals rfl
  rw [hl5] at h4 h5
  have h6 := sweepD (d + 3) (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default))
    (ListBlank.append [1, 0] v)
  have hl6 : ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 4)) default) =
      ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default) := by
    rw [show u + 4 = 4 + u by omega, ListBlank.append_pow_add]; rfl
  have hr6 : ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 3)) (ListBlank.append [1, 0] v) =
      ListBlank.append [1, 0, 1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 0] v)) := by
    rw [show d + 3 = 2 + (d + 1) by omega, ListBlank.append_pow_add]; rfl
  rw [hl6] at h4 h5 h6
  rw [hr6] at h6
  have h7 := K22 (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 0] v))
  rw [rotLB u default] at h7
  have h8 := sweepC u (ListBlank.append [1] default)
    (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 0] v)))
  rw [hconv] at h8
  have e : ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 0] v)))) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [0] v))) := by
    rw [ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) (d + 1) v,
      show d + 7 = 5 + (d + 2) by omega, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 5 (d + 2),
      ← rotLB0 (d + 2) v, one_pow_two_mul u, show 2 * u + 2 = (1 + 2 * u) + 1 by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) (1 + 2 * u) 1,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * u)]
    all_goals rfl
  rw [e] at h8
  exact (((((((h1.trans_star h2).trans h3).trans_star h4).trans h5).trans_star h6).trans h7).trans_star h8)

/-! ## Wrappers with explicit numbers, and the orbit -/

theorem stepR1 (a n c : ℕ) (ha : a = c + 7) (hn : n = 2 * c + 2) :
    ReachesPlus target (cfgC a 1) (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ n) tailT)) := by
  subst ha; subst hn; exact R1 c

/-- Entry then countdown: 𝒞(0; 1^n X) ⊢⁺ C(a, r)·X when n = 3q + r ≥ 1 and a = 1 + 5q. -/
theorem stepEC (n q r a : ℕ) (X : ListBlank (Fin 2)) (hn : n = 3 * q + r) (h1 : 1 ≤ n) (ha : a = 1 + 5 * q) :
    ReachesPlus target (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ n) X)) (cfgCt a r X) := by
  subst ha
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have h1 := branch_a0T n X
  have h2 := countdownT X q 1 le_rfl r
  rw [← hn] at h2
  exact h1.trans_star h2

theorem stepF111 (a n u : ℕ) (ha : a = u + 5) (hn : n = 2 * u + 2) :
    ReachesPlus target (cfgCt a 1 tailT)
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ n)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 14) default))) := by
  subst ha; subst hn
  have h := F111 u 6 (ListBlank.append [1] default)
  have e : ListBlank.append (([0, 1] : List (Fin 2)) ^ (6 + 7)) (ListBlank.append [0] (ListBlank.append [1] default)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 14) default :=
    ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) 13 default
  rw [e] at h
  exact h

theorem stepPZ (a n m : ℕ) (X : ListBlank (Fin 2)) (ha : 1 ≤ a) (hn : n = 2 * a + 13) :
    ReachesPlus target (cfgCt a 2 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1)) X))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ n) (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) X))) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [show n = 2 * a + 15 by omega]
  exact pzT a m X

theorem stepF100c12 (a n u : ℕ) (ha : a = u + 7) (hn : n = 2 * u + 2) :
    ReachesPlus target (cfgCt a 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 12) default))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ n)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ 27) default)))) := by
  subst ha; subst hn
  have h := F100 u 12 default
  have e : ListBlank.append (([1] : List (Fin 2)) ^ 1) (ListBlank.append (([0, 1] : List (Fin 2)) ^ 12) default) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (12 + 1)) (ListBlank.append [0] default) := by
    rw [list_pow_one, rotLB 12 default, ← ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) 12]
    congr 1
    show ListBlank.cons 1 default = ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 0 default))
    simp only [ListBlank.cons_zero_default]
  have e2 : cfgCt (u + 7) 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 12) default) =
      Ccal (u + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (12 + 1)) (ListBlank.append [0] default)) := by
    unfold cfgCt Ccal; rw [e]
  rw [e2]
  exact h

theorem stepEnd (a b : ℕ) (hb : b = a + 5) :
    cfgCt a 0 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 5) (ListBlank.append (([1] : List (Fin 2)) ^ 27) default)) =
      cfgC b 27 := by
  subst hb
  unfold cfgCt cfgC
  rw [list_pow_zero, ListBlank.append_nil, ← ListBlank.append_pow_add]

/-- **L17, machine level.** From the blank tape the machine reaches C(30066981019881, 27): it passes the
    a ≡ 2 (mod 3) boundary C(6575648756, 1) and returns to the plain two-counter section. -/
theorem blank_reaches_boundary3 : ReachesPlus target (init []) (cfgC 30066981019881 27) := by
  have h := blank_reaches_boundary2
    |>.trans (stepR1 6575648756 13151297500 6575648749 (by norm_num) (by norm_num))
    |>.trans (stepEC 13151297500 4383765833 1 21918829166 tailT (by norm_num) (by norm_num) (by norm_num))
    |>.trans (stepF111 21918829166 43837658324 21918829161 (by norm_num) (by norm_num))
    |>.trans (stepEC 43837658324 14612552774 2 73062763871 _ (by norm_num) (by norm_num) (by norm_num))
    |>.trans (stepPZ 73062763871 146125527755 13 default (by norm_num) (by norm_num))
    |>.trans (stepEC 146125527755 48708509251 2 243542546256 _ (by norm_num) (by norm_num) (by norm_num))
    |>.trans (stepPZ 243542546256 487085092525 12 default (by norm_num) (by norm_num))
    |>.trans (stepEC 487085092525 162361697508 1 811808487541 _ (by norm_num) (by norm_num) (by norm_num))
    |>.trans (stepF100c12 811808487541 1623616975070 811808487534 (by norm_num) (by norm_num))
    |>.trans (stepEC 1623616975070 541205658356 2 2706028291781 _ (by norm_num) (by norm_num) (by norm_num))
    |>.trans (stepPZ 2706028291781 5412056583575 6 _ (by norm_num) (by norm_num))
    |>.trans (stepEC 5412056583575 1804018861191 2 9020094305956 _ (by norm_num) (by norm_num) (by norm_num))
    |>.trans (stepPZ 9020094305956 18040188611925 5 _ (by norm_num) (by norm_num))
    |>.trans (stepEC 18040188611925 6013396203975 0 30066981019876 _ (by norm_num) (by norm_num) (by norm_num))
  rw [stepEnd 30066981019876 30066981019881 (by norm_num)] at h
  exact h

end CryptidLink.L17

#print axioms CryptidLink.L17.F100
#print axioms CryptidLink.L17.F111
#print axioms CryptidLink.L17.pzT
#print axioms CryptidLink.L17.blank_reaches_boundary3
