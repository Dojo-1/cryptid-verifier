import AntihydraOuroboros.Basic
/-
  No positive integer stays on a constant parity stream forever: within b + 4 steps of
  any b the T-orbit shows both an even and an odd value. (2-adically: b ≠ −3 and b ≠ −4.)
  These are the strictness facts behind ⌊ξ·(3/2)ⁿ⌋ in `CryptidReal`.
-/

theorem iterT_add (j : Nat) : ∀ n b, iterT j (iterT n b) = iterT (n + j) b := by
  intro n
  induction n with
  | zero => intro b; simp [iterT]
  | succ n ih =>
    intro b
    show iterT j (iterT n (T b)) = iterT (n + 1 + j) b
    rw [ih, show n + 1 + j = (n + j) + 1 by omega]; rfl

theorem pv_of_all (v : Bool) (m : Nat) : ∀ b, (∀ j, j < m → (iterT j b % 2 == 1) = v) →
    pv m b = List.replicate m v := by
  induction m with
  | zero => intro b _; rfl
  | succ m ih =>
    intro b h
    show (b % 2 == 1) :: pv m (T b) = v :: List.replicate m v
    have h0 : (b % 2 == 1) = v := h 0 (by omega)
    have hr : pv m (T b) = List.replicate m v := ih (T b) (fun j hj => h (j + 1) (by omega))
    rw [h0, hr]

theorem exists_even_after (b : Nat) : ∃ j, j < b + 4 ∧ iterT j b % 2 = 0 := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ j, j < b + 4 → (iterT j b % 2 == 1) = true := by
    intro j hj
    have : iterT j b % 2 ≠ 0 := fun h0 => hno ⟨j, hj, h0⟩
    have : iterT j b % 2 = 1 := by omega
    simp [this]
  have h1 := pv_of_all true (b + 4) b hall
  have h2 := pv_ones (b + 4) 2 (by decide)
  have hm := pv_inj (b + 4) b _ (h1.trans h2.symm)
  have hlt : b + 4 < 2 ^ (b + 4) := Nat.lt_two_pow_self
  have e : (2 ^ (b + 4) * 2 - 3) % 2 ^ (b + 4) = 2 ^ (b + 4) - 3 := by
    have : 2 ^ (b + 4) * 2 - 3 = (2 ^ (b + 4) - 3) + 2 ^ (b + 4) * 1 := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [e, Nat.mod_eq_of_lt (by omega)] at hm
  omega

theorem exists_odd_after (b : Nat) : ∃ j, j < b + 4 ∧ iterT j b % 2 = 1 := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ j, j < b + 4 → (iterT j b % 2 == 1) = false := by
    intro j hj
    have : iterT j b % 2 ≠ 1 := fun h1 => hno ⟨j, hj, h1⟩
    have : iterT j b % 2 = 0 := by omega
    simp [this]
  have h1 := pv_of_all false (b + 4) b hall
  have h2 := pv_zeros (b + 4) 2 (by decide)
  have hm := pv_inj (b + 4) b _ (h1.trans h2.symm)
  have hlt : b + 4 < 2 ^ (b + 4) := Nat.lt_two_pow_self
  have e : (2 ^ (b + 4) * 2 - 4) % 2 ^ (b + 4) = 2 ^ (b + 4) - 4 := by
    have : 2 ^ (b + 4) * 2 - 4 = (2 ^ (b + 4) - 4) + 2 ^ (b + 4) * 1 := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [e, Nat.mod_eq_of_lt (by omega)] at hm
  omega

/-- S is bounded: 3·(3ⁿ − 2ⁿ) ≤ Sₙ ≤ 4·(3ⁿ − 2ⁿ). -/
theorem S_bounds (b : Nat) : ∀ n, 3 * 2 ^ n + S n b ≥ 3 * 3 ^ n ∧ S n b + 4 * 2 ^ n ≤ 4 * 3 ^ n := by
  intro n
  induction n with
  | zero => simp [S]
  | succ n ih =>
    have hp : iterT n b % 2 ≤ 1 := by omega
    simp only [S, Nat.pow_succ]
    have e : 2 ^ n * (4 - iterT n b % 2) ≥ 2 ^ n * 3 := Nat.mul_le_mul_left _ (by omega)
    have f : 2 ^ n * (4 - iterT n b % 2) ≤ 2 ^ n * 4 := Nat.mul_le_mul_left _ (by omega)
    constructor <;> omega

#print axioms exists_even_after
#print axioms exists_odd_after
#print axioms S_bounds
