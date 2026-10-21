import CryptidLink.L17g
/-!
# L17: general D and G rows, and the RET729 return (GPT, `analysis/l17-general-d/`)

With an arbitrary right context V:

    D(N, k, m; V) = 𝒞(0; 1^N (01)^k 1^m V),     G(N, k; V) = 𝒞(0; 1^N (01)^k 0 V).

Each row is entry/countdown (`stepEC`) followed by F111, F100, P/Z (`stepPZ`), P (`branch_ge2T`) or Z (`zT`),
and then tape equalities. No new kernel is involved. `RET729` instantiates six rows after F1100:

    S(729t+548, 1, g+11, 1) ⊢⁺ S(10⁶t+740902, 2g, 7, 3).
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- D(N, k, m; V) = 𝒞(0; 1^N (01)^k 1^m V). -/
def Dg (N k m : ℕ) (V : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ N)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append (([1] : List (Fin 2)) ^ m) V)))

/-- G(N, k; V) = 𝒞(0; 1^N (01)^k 0 V). -/
def Gg (N k : ℕ) (V : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ N)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0] V)))

/-! ## D rows -/

/-- D0: N = 3q, q ≥ 1: absorb the k pairs. -/
theorem Dg0 (q k m : ℕ) (V : ListBlank (Fin 2)) (hq : 1 ≤ q) :
    ReachesPlus target (Dg (3 * q) k m V) (Ccal (1 + 5 * q + k) (ListBlank.append (([1] : List (Fin 2)) ^ m) V)) := by
  have h := stepEC (3 * q) q 0 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append (([1] : List (Fin 2)) ^ m) V))
    (by omega) (by omega) rfl
  have e : cfgCt (1 + 5 * q) 0 (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ m) V)) =
      Ccal (1 + 5 * q + k) (ListBlank.append (([1] : List (Fin 2)) ^ m) V) := by
    unfold cfgCt Ccal
    rw [list_pow_zero, ListBlank.append_nil, ← ListBlank.append_pow_add]
  rw [e] at h
  exact h

/-- D1: N = 3p+4, m ≥ 3: F111, to D(10p+4, k+7, m−3). -/
theorem Dg1 (p k m : ℕ) (V : ListBlank (Fin 2)) (hk : 1 ≤ k) :
    ReachesPlus target (Dg (3 * p + 4) k (m + 3) V) (Dg (10 * p + 4) (k + 7) m V) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have h1 := stepEC (3 * p + 4) (p + 1) 1 (1 + 5 * (p + 1))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append (([1] : List (Fin 2)) ^ (m + 3)) V))
    (by omega) (by omega) rfl
  have es : cfgCt (1 + 5 * (p + 1)) 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ (m + 3)) V)) =
      Ccal (5 * p + 1 + 5) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) V))) := by
    unfold cfgCt Ccal
    rw [show 1 + 5 * (p + 1) = 5 * p + 1 + 5 by omega, list_pow_one, rotLB (d + 1),
      show m + 3 = 2 + (m + 1) by omega, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (m + 1)]
    all_goals rfl
  rw [es] at h1
  have h2 := F111 (5 * p + 1) d (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) V)
  have et : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (5 * p + 1) + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) V)))) =
      Dg (10 * p + 4) (d + 1 + 7) m V := by
    unfold Dg
    rw [show 2 * (5 * p + 1) + 2 = 10 * p + 4 by omega, show d + 1 + 7 = d + 7 + 1 from rfl,
      ← ListBlank.append_pow_succ' _ (d + 7), ListBlank.append_pow_succ ([1] : List (Fin 2)) m]
    all_goals rfl
  rw [et] at h2
  exact h1.trans h2

/-- D12: N = 3p+4, m = 2: F111 leaves the interior zero, giving G(10p+4, k+6). -/
theorem Dg12 (p k : ℕ) (V : ListBlank (Fin 2)) (hk : 1 ≤ k) :
    ReachesPlus target (Dg (3 * p + 4) k 2 V) (Gg (10 * p + 4) (k + 6) V) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have h1 := stepEC (3 * p + 4) (p + 1) 1 (1 + 5 * (p + 1))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append (([1] : List (Fin 2)) ^ 2) V))
    (by omega) (by omega) rfl
  have es : cfgCt (1 + 5 * (p + 1)) 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2) V)) =
      Ccal (5 * p + 1 + 5) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [1, 1, 1] V)) := by
    unfold cfgCt Ccal
    rw [show 1 + 5 * (p + 1) = 5 * p + 1 + 5 by omega, list_pow_one, rotLB (d + 1)]
    all_goals rfl
  rw [es] at h1
  have h2 := F111 (5 * p + 1) d V
  have et : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (5 * p + 1) + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [0] V))) =
      Gg (10 * p + 4) (d + 1 + 6) V := by
    unfold Gg
    rw [show 2 * (5 * p + 1) + 2 = 10 * p + 4 by omega, show d + 1 + 6 = d + 7 from rfl]
  rw [et] at h2
  exact h1.trans h2

/-- D2: N = 3q+2, k ≥ 2: P then Z, to D(10q+15, k−1, m). -/
theorem Dg2 (q k m : ℕ) (V : ListBlank (Fin 2)) :
    ReachesPlus target (Dg (3 * q + 2) (k + 2) m V) (Dg (10 * q + 15) (k + 1) m V) := by
  have h1 := stepEC (3 * q + 2) q 2 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2)) (ListBlank.append (([1] : List (Fin 2)) ^ m) V))
    (by omega) (by omega) rfl
  have h2 := stepPZ (1 + 5 * q) (10 * q + 15) (k + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ m) V) (by omega) (by omega)
  exact h1.trans h2

/-- D2, k = 1: the ones join. -/
theorem Dg2k (q m : ℕ) (V : ListBlank (Fin 2)) :
    ReachesPlus target (Dg (3 * q + 2) 1 m V) (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (10 * q + 15 + m)) V)) := by
  have h1 := stepEC (3 * q + 2) q 2 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (0 + 1)) (ListBlank.append (([1] : List (Fin 2)) ^ m) V))
    (by omega) (by omega) rfl
  have h2 := stepPZ (1 + 5 * q) (10 * q + 15) 0
    (ListBlank.append (([1] : List (Fin 2)) ^ m) V) (by omega) (by omega)
  have e : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (10 * q + 15))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) (ListBlank.append (([1] : List (Fin 2)) ^ m) V))) =
      Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (10 * q + 15 + m)) V) := by
    simp only [list_pow_zero, ListBlank.append_nil]
    rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) (10 * q + 15) m]
  rw [e] at h2
  exact h1.trans h2

/-! ## G rows (the terminal starts with a pair: V = (01)^(l+1) W) -/

/-- G0: N = 3q: absorb, then Z on the interior zero; the terminal loses one pair. -/
theorem Gg0 (q k l : ℕ) (W : ListBlank (Fin 2)) (hq : 1 ≤ q) :
    ReachesPlus target (Gg (3 * q) k (ListBlank.append (([0, 1] : List (Fin 2)) ^ (l + 1)) W))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (1 + 5 * q + k) + 4 + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ l) W))) := by
  have h1 := stepEC (3 * q) q 0 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
      (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (l + 1)) W)))
    (by omega) (by omega) rfl
  have e1 : cfgCt (1 + 5 * q) 0 (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (l + 1)) W))) =
      Ccal (1 + 5 * q + k) (ListBlank.append [0, 0]
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ l) W))) := by
    unfold cfgCt Ccal
    rw [list_pow_zero, ListBlank.append_nil, ← ListBlank.append_pow_add, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) l]
    all_goals rfl
  rw [e1] at h1
  have h2 := zT (1 + 5 * q + k) (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ l) W))
  rw [ListBlank.append_pow_succ' ([1] : List (Fin 2)) (2 * (1 + 5 * q + k) + 4)] at h2
  exact h1.trans h2

/-- G1: N = 3p+7: F100, to D(10p+10, 7, 2k+4) with one pair fewer in the terminal. -/
theorem Gg1 (p k l : ℕ) (W : ListBlank (Fin 2)) :
    ReachesPlus target (Gg (3 * p + 7) k (ListBlank.append (([0, 1] : List (Fin 2)) ^ (l + 1)) W))
      (Dg (10 * p + 10) 7 (2 * k + 4) (ListBlank.append (([0, 1] : List (Fin 2)) ^ l) W)) := by
  have h1 := stepEC (3 * p + 7) (p + 2) 1 (1 + 5 * (p + 2))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
      (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (l + 1)) W)))
    (by omega) (by omega) rfl
  have es : cfgCt (1 + 5 * (p + 2)) 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (l + 1)) W))) =
      Ccal (5 * p + 4 + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [0] (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ l) W)))) := by
    unfold cfgCt Ccal
    rw [show 1 + 5 * (p + 2) = 5 * p + 4 + 7 by omega, list_pow_one, rotLB k,
      ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) l, ← ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) k]
    all_goals rfl
  rw [es] at h1
  have h2 := F100 (5 * p + 4) k (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ l) W))
  have et : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (5 * p + 4) + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7) (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 3))
          (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ l) W))))) =
      Dg (10 * p + 10) 7 (2 * k + 4) (ListBlank.append (([0, 1] : List (Fin 2)) ^ l) W) := by
    unfold Dg
    rw [show 2 * (5 * p + 4) + 2 = 10 * p + 10 by omega, show 2 * k + 4 = 2 * k + 3 + 1 from rfl,
      ListBlank.append_pow_succ' ([1] : List (Fin 2)) (2 * k + 3)]
  rw [et] at h2
  exact h1.trans h2

/-- G2: N = 3q+2, k ≥ 1: P then Z, to G(10q+15, k−1). -/
theorem Gg2 (q k : ℕ) (V : ListBlank (Fin 2)) :
    ReachesPlus target (Gg (3 * q + 2) (k + 1) V) (Gg (10 * q + 15) k V) := by
  have h1 := stepEC (3 * q + 2) q 2 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [0] V))
    (by omega) (by omega) rfl
  have h2 := stepPZ (1 + 5 * q) (10 * q + 15) k (ListBlank.append [0] V) (by omega) (by omega)
  exact h1.trans h2

/-- G2, k = 0: P then Z on the interior zero. -/
theorem Gg2k (q : ℕ) (V : ListBlank (Fin 2)) :
    ReachesPlus target (Gg (3 * q + 2) 0 V) (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (10 * q + 14)) V)) := by
  have h1 := stepEC (3 * q + 2) q 2 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) (ListBlank.append [0] V))
    (by omega) (by omega) rfl
  rw [show 1 + 5 * q = 5 * q + 1 by omega] at h1
  have h2 := branch_ge2T (5 * q) 0 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) (ListBlank.append [0] V))
  have e2 : Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (5 * q + 5))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) (ListBlank.append [0] V))))) =
      Ccal (5 * q + 5) (ListBlank.append [0, 0] V) := by
    unfold Ccal
    simp only [list_pow_zero, ListBlank.append_nil]
    rfl
  rw [e2] at h2
  have h3 := zT (5 * q + 5) V
  rw [show 2 * (5 * q + 5) + 4 = 10 * q + 14 by omega] at h3
  exact (h1.trans h2).trans h3

/-! ## Wrappers with explicit numbers -/

theorem LDg0 (N k m a' q : ℕ) (V : ListBlank (Fin 2)) (hN : N = 3 * q) (hq : 1 ≤ q) (ha : a' = 1 + 5 * q + k) :
    ReachesPlus target (Dg N k m V) (Ccal a' (ListBlank.append (([1] : List (Fin 2)) ^ m) V)) := by
  subst hN; subst ha; exact Dg0 q k m V hq

theorem LDg1 (N k m N' k' m' p : ℕ) (V : ListBlank (Fin 2)) (hN : N = 3 * p + 4) (hk : 1 ≤ k) (hm : m = m' + 3)
    (hN' : N' = 10 * p + 4) (hk' : k' = k + 7) : ReachesPlus target (Dg N k m V) (Dg N' k' m' V) := by
  subst hN; subst hm; subst hN'; subst hk'; exact Dg1 p k m' V hk

theorem LDg2 (N k m N' k' q : ℕ) (V : ListBlank (Fin 2)) (hN : N = 3 * q + 2) (hk : k = k' + 1) (hk' : 1 ≤ k')
    (hN' : N' = 10 * q + 15) : ReachesPlus target (Dg N k m V) (Dg N' k' m V) := by
  obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
  subst hN; subst hk; subst hN'; exact Dg2 q j m V

/-! ## RET729 -/

/-- **RET729:** S(729t+548, 1, g+11, 1) ⊢⁺ S(10⁶t+740902, 2g, 7, 3).
F1100, then D1, D1, D1, D2, D2, D0 (GPT's itinerary; the width-39 push is t = (A−548)/729, g = 28). -/
theorem RET729 (t g : ℕ) :
    ReachesPlus target (S (729 * t + 548) 1 (g + 11) 1) (S (1000000 * t + 740902) (2 * g) 7 3) := by
  have h0 := F1100 (729 * t + 541) (g + 4) default
  have es : S (729 * t + 548) 1 (g + 11) 1 =
      Ccal (729 * t + 541 + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (g + 4 + 7))
        (ListBlank.append [1, 1, 0, 0] default)) := by
    unfold S W cfgCt Ccal
    rw [show 729 * t + 541 + 7 = 729 * t + 548 by omega, show g + 4 + 7 = g + 11 by omega,
      list_pow_one, rotLB (g + 11)]
    show _ = Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (729 * t + 548))
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (g + 11))
        (ListBlank.append [1, 1] (ListBlank.cons 0 (ListBlank.cons 0 default)))))
    simp only [ListBlank.cons_zero_default]
    all_goals rfl
  rw [es]
  have e0 : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (729 * t + 541) + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (g + 4) + 1)) (ListBlank.append Tl default)))) =
      Dg (1458 * t + 1084) 7 (2 * g + 9) (ListBlank.append Tl default) := by
    unfold Dg
    rw [show 2 * (729 * t + 541) + 2 = 1458 * t + 1084 by omega, show 2 * (g + 4) + 1 = 2 * g + 9 by omega]
  rw [e0] at h0
  have h1 : ReachesPlus target (Dg (1458 * t + 1084) 7 (2 * g + 9) (ListBlank.append Tl default))
      (Dg (4860 * t + 3604) 14 (2 * g + 6) (ListBlank.append Tl default)) :=
    LDg1 _ _ _ _ _ _ (486 * t + 360) _ (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 : ReachesPlus target (Dg (4860 * t + 3604) 14 (2 * g + 6) (ListBlank.append Tl default))
      (Dg (16200 * t + 12004) 21 (2 * g + 3) (ListBlank.append Tl default)) :=
    LDg1 _ _ _ _ _ _ (1620 * t + 1200) _ (by omega) (by omega) (by omega) (by omega) (by omega)
  have h3 : ReachesPlus target (Dg (16200 * t + 12004) 21 (2 * g + 3) (ListBlank.append Tl default))
      (Dg (54000 * t + 40004) 28 (2 * g) (ListBlank.append Tl default)) :=
    LDg1 _ _ _ _ _ _ (5400 * t + 4000) _ (by omega) (by omega) (by omega) (by omega) (by omega)
  have h4 : ReachesPlus target (Dg (54000 * t + 40004) 28 (2 * g) (ListBlank.append Tl default))
      (Dg (180000 * t + 133355) 27 (2 * g) (ListBlank.append Tl default)) :=
    LDg2 _ _ _ _ _ (18000 * t + 13334) _ (by omega) (by omega) (by omega) (by omega)
  have h5 : ReachesPlus target (Dg (180000 * t + 133355) 27 (2 * g) (ListBlank.append Tl default))
      (Dg (600000 * t + 444525) 26 (2 * g) (ListBlank.append Tl default)) :=
    LDg2 _ _ _ _ _ (60000 * t + 44451) _ (by omega) (by omega) (by omega) (by omega)
  have h6 : ReachesPlus target (Dg (600000 * t + 444525) 26 (2 * g) (ListBlank.append Tl default))
      (Ccal (1000000 * t + 740902) (ListBlank.append (([1] : List (Fin 2)) ^ (2 * g)) (ListBlank.append Tl default))) :=
    LDg0 _ _ _ _ (200000 * t + 148175) _ (by omega) (by omega) (by omega)
  have e6 : Ccal (1000000 * t + 740902)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * g)) (ListBlank.append Tl default)) =
      S (1000000 * t + 740902) (2 * g) 7 3 := rfl
  rw [e6] at h6
  exact (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6

end CryptidLink.L17

#print axioms CryptidLink.L17.Gg0
#print axioms CryptidLink.L17.Gg1
#print axioms CryptidLink.L17.Gg2k
#print axioms CryptidLink.L17.Dg12
#print axioms CryptidLink.L17.RET729
