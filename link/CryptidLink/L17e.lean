import CryptidLink.L17c
/-!
# L17: stack-producing rules (GPT's derivation, `analysis/l17-stack/NESTING.md`)

With T = (01)^7 1^3 and U = (01)^8 1 (both 17 cells):

* `F1100`: 𝒞(u+7; (10)^(d+7) 1100 v) ⊢⁺ 𝒞(0; 1^(2u+2) (01)^7 1^(2d+1) T v). This is the rule the blank
  orbit uses at its first two-layer event, C(A,1)·(01)^76 1 (d = 69).
* `nestA`: (10)^8 A> 1 U^n 00 ⊢⁺ C> 11 T^(n+1), by induction on n, with arbitrary context on both sides.
* `nest`:  𝒞(u+7; 1 U^n 00 v) ⊢⁺ 𝒞(0; 1^(2u+2) T^(n+1) v), a uniform layer push.

New fixed kernels K7 and K41, and K60 with right context, run on symbolic context.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- T = (01)^7 1^3. -/
abbrev Tl : List (Fin 2) := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1]
/-- U = (01)^8 1. -/
abbrev Ul : List (Fin 2) := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]

/-! ## Kernels -/

theorem K60T (L R : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) L) (ListBlank.append [1, 0, 0] R))
      (Cfg.headLeft C (ListBlank.append [1] L) (ListBlank.append [1] (ListBlank.append Tl R))) := by
  show ReachesPlus target
    (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
      (ListBlank.append [1, 0, 0] R))
    (Cfg.headLeft C (ListBlank.append [1] L)
      (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1] R))
  bb_steps

theorem K7 (L R : ListBlank (Fin 2)) :
    ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 1, 0, 1] L) (ListBlank.append [1, 0, 1] R))
      (Cfg.headRight A (ListBlank.append [0] L) (ListBlank.append [0, 1, 0, 1, 0, 1] R)) := by
  bb_steps

theorem K41 (L R : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft C (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ 3) (ListBlank.append [1] R)))
      (Cfg.headLeft C (ListBlank.append [1] L) (ListBlank.append [1] (ListBlank.append Tl R))) := by
  show ReachesPlus target
    (Cfg.headLeft C (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
      (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R))
    (Cfg.headLeft C (ListBlank.append [1] L)
      (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1] R))
  bb_steps

/-! ## The A-section nesting induction -/

/-- **A-section nesting:** (10)^8 A> 1 U^n 00 ⊢⁺ C> 11 T^(n+1), outside context arbitrary on both sides. -/
theorem nestA (n : ℕ) : ∀ L R : ListBlank (Fin 2),
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) L)
        (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] R))))
      (Cfg.headLeft C (ListBlank.append [1] L) (ListBlank.append [1] (ListBlank.append (Tl ^ (n + 1)) R))) := by
  induction n with
  | zero =>
    intro L R
    show ReachesPlus target
      (Cfg.headRight A (ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) L) (ListBlank.append [1, 0, 0] R))
      (Cfg.headLeft C (ListBlank.append [1] L) (ListBlank.append [1] (ListBlank.append Tl R)))
    exact K60T L R
  | succ n ih =>
    intro L R
    have h1 := K7 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
        (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] R))))
    have h2 := sweepA 10 (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L))
      (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] R)))
    have h3 := ih (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L)) R
    have h4 := sweepC 3 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L)
      (ListBlank.append [1] (ListBlank.append (Tl ^ (n + 1)) R))
    have h5 := K41 L (ListBlank.append (Tl ^ (n + 1)) R)
    have e0 : ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) L =
        ListBlank.append [0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L) :=
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 6 L
    have e1 : ListBlank.append [1] (ListBlank.append (Ul ^ (n + 1)) (ListBlank.append [0, 0] R)) =
        ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] R)))) := by
      rw [ListBlank.append_pow_succ Ul n]
      all_goals rfl
    have e2 : ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] R)))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ 10)
          (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] R))) :=
      (ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 3 7 _).symm
    have e3 : ListBlank.append (([0, 1] : List (Fin 2)) ^ 10)
          (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L)) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ 8)
          (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L)) :=
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 8 2 _
    have e4 : ListBlank.append [1] (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L)) =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ 3) (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6) L) := rfl
    have e7 : ListBlank.append [1] (ListBlank.append Tl (ListBlank.append (Tl ^ (n + 1)) R)) =
        ListBlank.append [1] (ListBlank.append (Tl ^ (n + 1 + 1)) R) := by
      rw [ListBlank.append_pow_succ Tl (n + 1)]
    rw [e0, e1]
    rw [e2] at h1
    rw [e3] at h2
    rw [e4] at h3
    rw [e7] at h5
    exact (((h1.trans_star h2).trans h3).trans_star h4).trans h5

/-- **Uniform layer push:** 𝒞(u+7; 1 U^n 00 v) ⊢⁺ 𝒞(0; 1^(2u+2) T^(n+1) v). -/
theorem nest (u n : ℕ) (v : ListBlank (Fin 2)) :
    ReachesPlus target
      (Ccal (u + 7) (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] v))))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2)) (ListBlank.append (Tl ^ (n + 1)) v))) := by
  have h1 := entryC (u + 6) (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] v)))
  have h2 := sweepA (u + 8) default (ListBlank.append [1] (ListBlank.append (Ul ^ n) (ListBlank.append [0, 0] v)))
  have hs : ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 8)) default =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default) := by
    rw [show u + 8 = 8 + u by omega, ListBlank.append_pow_add]
  rw [hs] at h2
  have h3 := nestA n (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default) v
  rw [rotLB u default] at h3
  have h4 := sweepC u (ListBlank.append [1] default) (ListBlank.append [1] (ListBlank.append (Tl ^ (n + 1)) v))
  rw [hconv] at h4
  have e : ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1] (ListBlank.append (Tl ^ (n + 1)) v))) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2)) (ListBlank.append (Tl ^ (n + 1)) v)) := by
    rw [one_pow_two_mul u, show 2 * u + 2 = (1 + 2 * u) + 1 by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) (1 + 2 * u) 1,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * u)]
    all_goals rfl
  rw [e] at h4
  exact ((h1.trans_star h2).trans h3).trans_star h4

/-! ## F1100 -/

/-- **F1100:** 𝒞(u+7; (10)^(d+7) 1100 v) ⊢⁺ 𝒞(0; 1^(2u+2) (01)^7 1^(2d+1) T v). -/
theorem F1100 (u d : ℕ) (v : ListBlank (Fin 2)) :
    ReachesPlus target
      (Ccal (u + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [1, 1, 0, 0] v)))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * d + 1)) (ListBlank.append Tl v))))) := by
  have hX : ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [1, 1, 0, 0] v) =
      ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 6)) (ListBlank.append [1, 1, 0, 0] v)) :=
    ListBlank.append_pow_succ _ _ _
  have h1 := entryC (u + 6) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [1, 1, 0, 0] v))
  have h2 := sweepA (u + 8) default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [1, 1, 0, 0] v))
  have hs : ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 8)) default =
      ListBlank.append [0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default) := by
    rw [show u + 8 = 2 + (u + 6) by omega, ListBlank.append_pow_add]; rfl
  rw [hs, hX] at h2
  rw [hX] at h1
  have h3 := K11 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 6)) (ListBlank.append [1, 1, 0, 0] v))
  rw [rotLB0] at h3
  -- (01)^(d+6) 0 1100 v = (01)^(d+7) 100 v
  have hr3 : ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 6)) (ListBlank.append [0] (ListBlank.append [1, 1, 0, 0] v)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [1, 0, 0] v) :=
    ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) (d + 6) (ListBlank.append [1, 0, 0] v)
  rw [hr3] at h3
  have h4 := sweepA (d + 7) (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))
    (ListBlank.append [1, 0, 0] v)
  -- (01)^(d+7) (01)(01) 0 = (01)^8 (01)^(d+1) 0
  have hl4 : ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7))
        (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 8)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
          (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))) := by
    rw [← ListBlank.append_pow_add, show 8 + (d + 1) = d + 7 + 1 + 1 by omega,
      ← ListBlank.append_pow_succ' _ (d + 7 + 1), ← ListBlank.append_pow_succ' _ (d + 7)]
    all_goals rfl
  rw [hl4] at h4
  have h5 := K60T (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
      (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))) v
  -- 1 (01)^(d+1) 0 (01)^(u+6) = (10)^(d+1) 10 (01)^6 (01)^u
  have hl5 : ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)) := by
    rw [rotLB (d + 1), show u + 6 = 6 + u by omega, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 6 u]
    all_goals rfl
  rw [hl5] at h5
  have h6 := sweepC (d + 1) (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)) (ListBlank.append [1] (ListBlank.append Tl v))
  have hr6 : ListBlank.append (([1, 1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1] (ListBlank.append Tl v)) =
      ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1] (ListBlank.append Tl v))) :=
    ListBlank.append_pow_succ _ _ _
  rw [hr6] at h6
  have h7 := K43 (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1] (ListBlank.append Tl v)))
  rw [rotLB u default] at h7
  have h8 := sweepC u (ListBlank.append [1] default)
    (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1] (ListBlank.append Tl v))))
  rw [hconv] at h8
  have e : ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1] (ListBlank.append Tl v))))) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * d + 1)) (ListBlank.append Tl v)))) := by
    rw [one_pow_two_mul u, one_pow_two_mul d, show 2 * u + 2 = (1 + 2 * u) + 1 by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) (1 + 2 * u) 1,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * u),
      ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * d) 1]
    all_goals rfl
  rw [e] at h8
  exact (((((((h1.trans_star h2).trans h3).trans_star h4).trans h5).trans_star h6).trans h7).trans_star h8)

/-! ## Explicit two- and three-layer witnesses -/

/-- C(7,1)·(01)^8 1 ⊢⁺ C(0,2)·T·T. -/
theorem stack_two :
    ReachesPlus target (cfgCt 7 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) (ListBlank.append [1] default)))
      (cfgCt 0 2 (ListBlank.append Tl (ListBlank.append Tl default))) := by
  have h := F1100 0 1 default
  have e : cfgCt 7 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) (ListBlank.append [1] default)) =
      Ccal (0 + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (1 + 7)) (ListBlank.append [1, 1, 0, 0] default)) := by
    unfold cfgCt Ccal
    show _ = Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
      (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
        (ListBlank.cons 0 (ListBlank.cons 0 default))))
    simp only [ListBlank.cons_zero_default]
    rfl
  rw [e]
  exact h

/-- C(7,1)·U^2 ⊢⁺ C(0,2)·T^3. -/
theorem stack_three :
    ReachesPlus target (cfgCt 7 1 (ListBlank.append (Ul ^ 2) default))
      (cfgCt 0 2 (ListBlank.append (Tl ^ 3) default)) := by
  have h := nest 0 2 default
  have e : cfgCt 7 1 (ListBlank.append (Ul ^ 2) default) =
      Ccal (0 + 7) (ListBlank.append [1] (ListBlank.append (Ul ^ 2) (ListBlank.append [0, 0] default))) := by
    unfold cfgCt Ccal
    show _ = Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
      (ListBlank.append [1] (ListBlank.append (Ul ^ 2) (ListBlank.cons 0 (ListBlank.cons 0 default)))))
    simp only [ListBlank.cons_zero_default]
    rfl
  rw [e]
  exact h

end CryptidLink.L17

#print axioms CryptidLink.L17.nest
#print axioms CryptidLink.L17.F1100
#print axioms CryptidLink.L17.stack_two
#print axioms CryptidLink.L17.stack_three
