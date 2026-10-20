import Mathlib
import AntihydraOuroboros.Escape
/-
  Antihydra's orbit as one real number.

  With pₖ the parity of bₖ (b₀ = 4) and qₖ = 4 − pₖ ∈ {3, 4}, set
      ξ = 4 + Σₖ qₖ · (2/3)ᵏ / 3.
  Main theorem: bₙ = ⌊ξ · (3/2)ⁿ⌋ − 3 for every n. Hence Antihydra's parities are the
  parities of ⌊ξ · (3/2)ⁿ⌋ + 1, and (with `antihydra_survives_iff`) its halting question is
  a question about the integer parts of ξ·(3/2)ⁿ — the setting of Mahler's 3/2 problem.
-/

open Finset

namespace CryptidReal

/-- Weight qₖ = 4 − (bₖ mod 2) ∈ {3, 4}. -/
noncomputable def q (k : ℕ) : ℝ := ((4 - iterT k 4 % 2 : ℕ) : ℝ)

lemma q_ge (k : ℕ) : 3 ≤ q k := by
  have : 3 ≤ 4 - iterT k 4 % 2 := by omega
  unfold q; exact_mod_cast this

lemma q_le (k : ℕ) : q k ≤ 4 := by
  have : 4 - iterT k 4 % 2 ≤ 4 := by omega
  unfold q; exact_mod_cast this

lemma q_even (k : ℕ) (h : iterT k 4 % 2 = 0) : q k = 4 := by
  unfold q; rw [h]; norm_num

lemma q_odd (k : ℕ) (h : iterT k 4 % 2 = 1) : q k = 3 := by
  unfold q; rw [h]; norm_num

/-- Terms of ξ − 4. -/
noncomputable def t (k : ℕ) : ℝ := q k * (2 / 3 : ℝ) ^ k / 3

lemma t_nonneg (k : ℕ) : 0 ≤ t k := by
  unfold t; have := q_ge k; positivity

lemma t_le (k : ℕ) : t k ≤ 4 / 3 * (2 / 3 : ℝ) ^ k := by
  unfold t; have := q_le k; have hr : 0 ≤ (2 / 3 : ℝ) ^ k := by positivity
  nlinarith

lemma geom_summable : Summable (fun k : ℕ => (2 / 3 : ℝ) ^ k) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma t_summable : Summable t :=
  Summable.of_nonneg_of_le t_nonneg t_le (geom_summable.mul_left (4 / 3))

/-- The real number attached to Antihydra's orbit. -/
noncomputable def ξ : ℝ := 4 + ∑' k, t k

/-- Sₙ / 3ⁿ is the partial sum of the series. -/
lemma S_div (n : ℕ) : (S n 4 : ℝ) / 3 ^ n = ∑ k ∈ range n, t k := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    have hS : (S (n + 1) 4 : ℝ) = 3 * (S n 4 : ℝ) + 2 ^ n * q n := by
      simp only [S, q]; push_cast; ring
    rw [hS]; unfold t; rw [div_pow]; field_simp <;> ring_nf

/-- bₙ = (3/2)ⁿ · (4 + Σ_{k<n} tₖ), from `real_bridge`. -/
lemma b_eq (n : ℕ) : (iterT n 4 : ℝ) = (3 / 2 : ℝ) ^ n * (4 + ∑ k ∈ range n, t k) := by
  have h := real_bridge n 4
  have hR : (2 : ℝ) ^ n * (iterT n 4 : ℝ) = 3 ^ n * 4 + (S n 4 : ℝ) := by exact_mod_cast h
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have h3 : (3 : ℝ) ^ n ≠ 0 := by positivity
  rw [← S_div, div_pow]
  have hb : (iterT n 4 : ℝ) = (3 ^ n * 4 + (S n 4 : ℝ)) / 2 ^ n := by
    rw [eq_div_iff h2]; linarith
  rw [hb]; field_simp <;> ring_nf

/-- The tail Rₙ = ξ·(3/2)ⁿ − bₙ. -/
noncomputable def R (n : ℕ) : ℝ := ∑' j, q (n + j) * (2 / 3 : ℝ) ^ j / 3

lemma tail (n : ℕ) : ξ * (3 / 2 : ℝ) ^ n - iterT n 4 = R n := by
  have hsplit : ∑ k ∈ range n, t k + ∑' j, t (j + n) = ∑' k, t k :=
    t_summable.sum_add_tsum_nat_add n
  rw [b_eq, ξ, ← hsplit]
  have hmul : (3 / 2 : ℝ) ^ n * ∑' j, t (j + n) = R n := by
    rw [← tsum_mul_left]; unfold R
    congr 1; funext j; unfold t
    rw [Nat.add_comm j n, pow_add, div_pow, div_pow, div_pow]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    have h3 : (3 : ℝ) ^ n ≠ 0 := by positivity
    field_simp <;> ring_nf
  rw [← hmul]; ring

lemma w_summable : Summable (fun j : ℕ => (2 / 3 : ℝ) ^ j / 3) := geom_summable.div_const 3

lemma w_tsum : ∑' j : ℕ, (2 / 3 : ℝ) ^ j / 3 = 1 := by
  rw [tsum_div_const, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

lemma g_summable (n : ℕ) : Summable (fun j : ℕ => q (n + j) * (2 / 3 : ℝ) ^ j / 3) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (geom_summable.mul_left (4 / 3))
  · have := q_ge (n + j); positivity
  · have := q_le (n + j); have hr : 0 ≤ (2 / 3 : ℝ) ^ j := (by positivity)
    nlinarith

/-- 3 < Rₙ: some later parity is even (`exists_even_after`). -/
lemma R_gt (n : ℕ) : 3 < R n := by
  obtain ⟨j, -, hj⟩ := exists_even_after (iterT n 4)
  rw [iterT_add] at hj
  have h3 : ∑' i : ℕ, 3 * ((2 / 3 : ℝ) ^ i / 3) = 3 := by rw [tsum_mul_left, w_tsum]; ring
  rw [← h3]; unfold R
  refine Summable.tsum_lt_tsum (i := j) (fun i => ?_) ?_ (w_summable.mul_left 3) (g_summable n)
  · have := q_ge (n + i); have hr : 0 ≤ (2 / 3 : ℝ) ^ i := (by positivity)
    nlinarith
  · rw [q_even _ hj]; have hr : 0 < (2 / 3 : ℝ) ^ j := (by positivity)
    nlinarith

/-- Rₙ < 4: some later parity is odd (`exists_odd_after`). -/
lemma R_lt (n : ℕ) : R n < 4 := by
  obtain ⟨j, -, hj⟩ := exists_odd_after (iterT n 4)
  rw [iterT_add] at hj
  have h4 : ∑' i : ℕ, 4 * ((2 / 3 : ℝ) ^ i / 3) = 4 := by rw [tsum_mul_left, w_tsum]; ring
  rw [← h4]; unfold R
  refine Summable.tsum_lt_tsum (i := j) (fun i => ?_) ?_ (g_summable n) (w_summable.mul_left 4)
  · have := q_le (n + i); have hr : 0 ≤ (2 / 3 : ℝ) ^ i := (by positivity)
    nlinarith
  · rw [q_odd _ hj]; have hr : 0 < (2 / 3 : ℝ) ^ j := (by positivity)
    nlinarith

/-- **Main theorem.** Antihydra's b-orbit is bₙ = ⌊ξ · (3/2)ⁿ⌋ − 3. -/
theorem antihydra_floor (n : ℕ) : (iterT n 4 : ℤ) = ⌊ξ * (3 / 2 : ℝ) ^ n⌋ - 3 := by
  have ht := tail n
  have h1 := R_gt n
  have h2 := R_lt n
  have hfl : ⌊ξ * (3 / 2 : ℝ) ^ n⌋ = (iterT n 4 : ℤ) + 3 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  omega

/-- Antihydra's parities are those of ⌊ξ · (3/2)ⁿ⌋ − 3. -/
theorem antihydra_parity (n : ℕ) : ((iterT n 4 % 2 : ℕ) : ℤ) = (⌊ξ * (3 / 2 : ℝ) ^ n⌋ - 3) % 2 := by
  rw [← antihydra_floor]; omega

/-- 7 < ξ < 8 (the n = 0 case: ⌊ξ⌋ = 7). -/
theorem ξ_floor : ⌊ξ⌋ = 7 := by
  have := antihydra_floor 0
  simp [iterT] at this; omega

end CryptidReal

#print axioms CryptidReal.antihydra_floor
#print axioms CryptidReal.antihydra_parity
#print axioms CryptidReal.ξ_floor
