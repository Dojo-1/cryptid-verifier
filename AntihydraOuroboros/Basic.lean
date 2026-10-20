/-
  Antihydra: the ouroboros (2-adic) reformulation, machine-checked.
  Core Lean 4 only (no Mathlib). Builds on the acceleration of
  Dos Santos et al., arXiv:2610.22603, Sec. 2.2:

    A(a, 2k)   → A(a+2, 3k+2)
    A(0, 2k+1) → halt
    A(a+1, 2k+1) → A(a, 3k+3)

  Results:
  1. `T_shift`   : T (b + 2q) = T b + 3q        (the 2-adic "ouroboros" lemma)
  2. `pv_mod`    : the first k parities depend only on b mod 2^k
  3. `pv_inj`    : … and determine b mod 2^k   (Terras-type bijection)
  4. `run_eq`    : n macro-steps of Antihydra = the b-tape evolving autonomously
                   under T, plus a ±walk (+2 / −1) driven by the parity vector;
                   the machine halts iff that walk would go below 0.
-/

/-- The b-tape map. Even b = 2k ↦ 3k+2, odd b = 2k+1 ↦ 3k+3. -/
def T (b : Nat) : Nat := if b % 2 = 0 then 3 * (b / 2) + 2 else 3 * (b / 2) + 3

/-- Shifting b by an even amount 2q shifts T b by 3q. -/
theorem T_shift (b q : Nat) : T (b + 2 * q) = T b + 3 * q := by
  unfold T
  have h1 : (b + 2 * q) % 2 = b % 2 := by omega
  have h2 : (b + 2 * q) / 2 = b / 2 + q := by omega
  rw [h1, h2]
  split <;> omega

/-- Parity vector: the first k parities of the b-trajectory (true = odd). -/
def pv : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, b => (b % 2 == 1) :: pv k (T b)

theorem pv_length (k b : Nat) : (pv k b).length = k := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simp [pv, ih]

private theorem pow_succ' (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Determination: the first k parities depend only on b mod 2^k. -/
theorem pv_mod (k : Nat) : ∀ b b', b % 2 ^ k = b' % 2 ^ k → pv k b = pv k b' := by
  induction k with
  | zero => intro b b' _; rfl
  | succ k ih =>
    intro b b' h
    rw [pow_succ'] at h
    -- same parity
    have hp : b % 2 = b' % 2 := by
      have e1 := Nat.mod_mod_of_dvd b (Nat.dvd_mul_right 2 (2 ^ k))
      have e2 := Nat.mod_mod_of_dvd b' (Nat.dvd_mul_right 2 (2 ^ k))
      rw [← e1, ← e2, h]
    -- T b ≡ T b' (mod 2^k): write both as r + 2·(2^k·m)
    have key0 : ∀ r m, T (r + 2 * (2 ^ k * m)) % 2 ^ k = T r % 2 ^ k := by
      intro r m
      rw [T_shift]
      have : 3 * (2 ^ k * m) = 2 ^ k * (3 * m) := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm 3 (2 ^ k)]
      rw [this, Nat.add_mul_mod_self_left]
    have key : ∀ x, T x % 2 ^ k = T (x % (2 * 2 ^ k)) % 2 ^ k := by
      intro x
      have hx := Nat.mod_add_div x (2 * 2 ^ k)
      have ex : x = x % (2 * 2 ^ k) + 2 * (2 ^ k * (x / (2 * 2 ^ k))) := by
        rw [← Nat.mul_assoc]; omega
      have hTx : T x = T (x % (2 * 2 ^ k) + 2 * (2 ^ k * (x / (2 * 2 ^ k)))) :=
        congrArg T ex
      rw [hTx]; exact key0 _ _
    have hT : T b % 2 ^ k = T b' % 2 ^ k := by rw [key b, key b', h]
    simp only [pv, hp, ih _ _ hT]

/-- 3 is invertible modulo 2^k. -/
theorem cancel3 (k x y : Nat) (h : 3 * x % 2 ^ k = 3 * y % 2 ^ k) :
    x % 2 ^ k = y % 2 ^ k := by
  have cop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by decide)
  rcases Nat.le_total x y with hxy | hxy
  · have h0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    have hd : 2 ^ k ∣ 3 * (y - x) := by
      have : 3 * y - 3 * x = 3 * (y - x) := by omega
      rw [← this]; exact Nat.dvd_of_mod_eq_zero h0
    obtain ⟨c, hc⟩ := cop.dvd_of_dvd_mul_left hd
    have : y = x + c * 2 ^ k := by rw [Nat.mul_comm]; omega
    rw [this, Nat.add_mul_mod_self_right]
  · have h0 := Nat.sub_mod_eq_zero_of_mod_eq h
    have hd : 2 ^ k ∣ 3 * (x - y) := by
      have : 3 * x - 3 * y = 3 * (x - y) := by omega
      rw [← this]; exact Nat.dvd_of_mod_eq_zero h0
    obtain ⟨c, hc⟩ := cop.dvd_of_dvd_mul_left hd
    have : x = y + c * 2 ^ k := by rw [Nat.mul_comm]; omega
    rw [this, Nat.add_mul_mod_self_right]

/-- Injectivity: the first k parities determine b mod 2^k. -/
theorem pv_inj (k : Nat) : ∀ b b', pv k b = pv k b' → b % 2 ^ k = b' % 2 ^ k := by
  induction k with
  | zero => intro b b' _; simp [Nat.mod_one]
  | succ k ih =>
    intro b b' h
    simp only [pv, List.cons.injEq] at h
    obtain ⟨hp, hv⟩ := h
    have hp : b % 2 = b' % 2 := by
      revert hp; cases Nat.mod_two_eq_zero_or_one b <;>
        cases Nat.mod_two_eq_zero_or_one b' <;> simp_all
    have hT := ih _ _ hv
    -- T b = 3·(b/2) + c with the same c for b and b'
    have h3 : 3 * (b / 2) % 2 ^ k = 3 * (b' / 2) % 2 ^ k := by
      unfold T at hT
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb
      · have hb' : b' % 2 = 0 := by omega
        rw [if_pos hb, if_pos hb'] at hT
        have := Nat.mod_eq_mod_iff.mp hT
        obtain ⟨k1, k2, e⟩ := this
        exact Nat.mod_eq_mod_iff.mpr ⟨k1, k2, by omega⟩
      · have hb' : b' % 2 = 1 := by omega
        rw [if_neg (by omega), if_neg (by omega)] at hT
        obtain ⟨k1, k2, e⟩ := Nat.mod_eq_mod_iff.mp hT
        exact Nat.mod_eq_mod_iff.mpr ⟨k1, k2, by omega⟩
    have hj := cancel3 k _ _ h3
    -- reassemble: b = 2·(b/2) + parity
    obtain ⟨k1, k2, e⟩ := Nat.mod_eq_mod_iff.mp hj
    rw [pow_succ']
    apply Nat.mod_eq_mod_iff.mpr
    refine ⟨k1, k2, ?_⟩
    have eb := Nat.mod_add_div b 2
    have eb' := Nat.mod_add_div b' 2
    have : k1 * (2 * 2 ^ k) = 2 * (k1 * 2 ^ k) := by
      rw [Nat.mul_left_comm]
    have : k2 * (2 * 2 ^ k) = 2 * (k2 * 2 ^ k) := by
      rw [Nat.mul_left_comm]
    omega


/-! ### Surjectivity: every parity pattern occurs (so `pv k` is a bijection
    between residues mod 2^k and Boolean vectors of length k) -/

theorem pow2_mod3 (k : Nat) :
    (2 ^ k % 3 = 1 ∧ k % 2 = 0) ∨ (2 ^ k % 3 = 2 ∧ k % 2 = 1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- An inverse of 3 modulo 2^k. -/
theorem inv3 (k : Nat) : ∃ u, 3 * u % 2 ^ k = 1 % 2 ^ k := by
  rcases pow2_mod3 k with ⟨h, _⟩ | ⟨h, _⟩
  · refine ⟨(2 ^ k * 2 + 1) / 3, ?_⟩
    have : 3 * ((2 ^ k * 2 + 1) / 3) = 1 + 2 ^ k * 2 := by omega
    rw [this, Nat.add_mul_mod_self_left]
  · refine ⟨(2 ^ k + 1) / 3, ?_⟩
    have : 3 * ((2 ^ k + 1) / 3) = 2 ^ k + 1 := by omega
    rw [this, Nat.add_mod_left]

/-- 3j ≡ d (mod 2^k) is solvable with j < 2^k. -/
theorem solve3 (k d : Nat) : ∃ j, j < 2 ^ k ∧ 3 * j % 2 ^ k = d % 2 ^ k := by
  obtain ⟨u, hu⟩ := inv3 k
  refine ⟨d * u % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k), ?_⟩
  rw [Nat.mul_mod_mod]
  have : 3 * (d * u) = d * (3 * u) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 3 d, Nat.mul_assoc]
  rw [this, Nat.mul_mod, hu, ← Nat.mul_mod, Nat.mul_one]

theorem pv_surj (k : Nat) : ∀ v : List Bool, v.length = k → ∃ b, b < 2 ^ k ∧ pv k b = v := by
  induction k with
  | zero => intro v hv; exact ⟨0, by decide, by cases v <;> simp_all [pv]⟩
  | succ k ih =>
    intro v hv
    cases v with
    | nil => simp at hv
    | cons p v' =>
      simp at hv
      obtain ⟨c, hc, hcv⟩ := ih v' hv
      let e := if p then 1 else 0
      have he : e ≤ 1 := by cases p <;> simp [e]
      obtain ⟨j, hj, hj3⟩ := solve3 k (c + 3 * 2 ^ k - 2 - e)
      have hP := Nat.two_pow_pos k
      refine ⟨2 * j + e, ?_, ?_⟩
      · rw [Nat.pow_succ]; omega
      · have hT : T (2 * j + e) = 3 * j + 2 + e := by
          unfold T; cases p <;> simp [e] <;> omega
        have hmod : T (2 * j + e) % 2 ^ k = c % 2 ^ k := by
          rw [hT]
          obtain ⟨k1, k2, h12⟩ := Nat.mod_eq_mod_iff.mp hj3
          apply Nat.mod_eq_mod_iff.mpr
          refine ⟨k1, k2 + 3, ?_⟩
          have : (k2 + 3) * 2 ^ k = k2 * 2 ^ k + 3 * 2 ^ k := by
            rw [Nat.add_mul]
          omega
        simp only [pv]
        rw [pv_mod k _ _ hmod, hcv]
        cases p <;> simp [e] <;> omega

/-- Sanity check against the trace: 4 → 8 → 14 → 23 → … -/
example : pv 4 4 = [false, false, false, true] := by decide


/-! ### The Möbius pair: the two 2-adic fixed points of T

  Twisting the parity bundle on odd steps (Möbius) or on even steps (anti-Möbius)
  gives an unbalanced connection; the frustrated self-loops are the constant
  parity streams 1111… and 0000…. In 2-adic terms these are the fixed points
  b = −3 (T(−3) = −3, always odd) and b = −4 (T(−4) = −4, always even).
  Below: their finite shadows 2^m·c − 3 and 2^m·c − 4, and what the machine does
  on them — the first halts as fast as possible, the second never within the
  horizon. They sit on opposite sides of the halting boundary. -/

private theorem two_le_mul (m c : Nat) (hc : 2 ≤ c) : 2 ≤ 2 ^ m * c := by
  have := Nat.mul_le_mul_right c (Nat.one_le_two_pow (n := m))
  omega

theorem T_neg3 (m c : Nat) (hc : 2 ≤ c) :
    T (2 ^ (m + 1) * c - 3) = 2 ^ m * (3 * c) - 3 := by
  have hq := two_le_mul m c hc
  have e1 : 2 ^ (m + 1) * c = 2 * (2 ^ m * c) := by rw [pow_succ', Nat.mul_assoc]
  have e2 : 2 ^ m * (3 * c) = 3 * (2 ^ m * c) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ m) 3, Nat.mul_assoc]
  rw [e1, e2]; unfold T; split <;> omega

theorem T_neg4 (m c : Nat) (hc : 2 ≤ c) :
    T (2 ^ (m + 1) * c - 4) = 2 ^ m * (3 * c) - 4 := by
  have hq := two_le_mul m c hc
  have e1 : 2 ^ (m + 1) * c = 2 * (2 ^ m * c) := by rw [pow_succ', Nat.mul_assoc]
  have e2 : 2 ^ m * (3 * c) = 3 * (2 ^ m * c) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ m) 3, Nat.mul_assoc]
  rw [e1, e2]; unfold T; split <;> omega

/-- b ≡ −3 (mod 2^m): m odd steps in a row (the Möbius loop). -/
theorem pv_ones (m : Nat) : ∀ c, 2 ≤ c → pv m (2 ^ m * c - 3) = List.replicate m true := by
  induction m with
  | zero => intro c _; rfl
  | succ m ih =>
    intro c hc
    have hq := two_le_mul m c hc
    have hpar : (2 ^ (m + 1) * c - 3) % 2 = 1 := by
      have : 2 ^ (m + 1) * c = 2 * (2 ^ m * c) := by rw [pow_succ', Nat.mul_assoc]
      omega
    simp only [pv, hpar, T_neg3 m c hc, ih (3 * c) (by omega), List.replicate_succ]
    rfl

/-- b ≡ −4 (mod 2^m): m even steps in a row (the anti-Möbius loop). -/
theorem pv_zeros (m : Nat) : ∀ c, 2 ≤ c → pv m (2 ^ m * c - 4) = List.replicate m false := by
  induction m with
  | zero => intro c _; rfl
  | succ m ih =>
    intro c hc
    have hq := two_le_mul m c hc
    have hpar : (2 ^ (m + 1) * c - 4) % 2 = 0 := by
      have : 2 ^ (m + 1) * c = 2 * (2 ^ m * c) := by rw [pow_succ', Nat.mul_assoc]
      omega
    simp only [pv, hpar, T_neg4 m c hc, ih (3 * c) (by omega), List.replicate_succ]
    rfl

/-! ### The accelerated machine and its exact walk decomposition -/

/-- n-fold iterate of T. -/
def iterT : Nat → Nat → Nat
  | 0, b => b
  | n + 1, b => iterT n (T b)

/-- One Antihydra macro-step on A(a, b); `none` = halt. -/
def step : Nat × Nat → Option (Nat × Nat)
  | (a, b) =>
    if b % 2 = 0 then some (a + 2, 3 * (b / 2) + 2)
    else if a = 0 then none
    else some (a - 1, 3 * (b / 2) + 3)

/-- Run n macro-steps. -/
def run : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, s => some s
  | n + 1, s => (step s).bind (run n)

/-- The bank account driven by a parity stream: +2 on even, −1 on odd,
    `none` when it would go below zero. -/
def walk : Nat → List Bool → Option Nat
  | a, [] => some a
  | a, false :: v => walk (a + 2) v
  | 0, true :: _ => none
  | a + 1, true :: v => walk a v

/-- Exact decomposition: the b-tape evolves autonomously under T, the a-tape is
    the walk on its parity vector, and halting happens exactly when the walk
    would go below zero. -/
theorem run_eq (n : Nat) : ∀ a b,
    run n (a, b) = (walk a (pv n b)).map (fun a' => (a', iterT n b)) := by
  induction n with
  | zero => intro a b; simp [run, pv, walk, iterT]
  | succ n ih =>
    intro a b
    simp only [run, pv, iterT]
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
    · have hT : T b = 3 * (b / 2) + 2 := by simp [T, hb]
      simp [step, hb, hT, walk, ih]
    · have hT : T b = 3 * (b / 2) + 3 := by simp [T, hb]
      cases a with
      | zero => simp [step, hb, walk]
      | succ a => simp [step, hb, hT, walk, ih]

/-- Corollary: Antihydra (from A(0,4)) survives n macro-steps iff the
    ±walk on the first n parities of the T-orbit of 4 never goes below 0. -/
theorem antihydra_survives_iff (n : Nat) :
    (run n (0, 4)).isSome ↔ (walk 0 (pv n 4)).isSome := by
  rw [run_eq]; cases walk 0 (pv n 4) <;> simp


theorem walk_zeros (n : Nat) : ∀ a, walk a (List.replicate n false) = some (a + 2 * n) := by
  induction n with
  | zero => intro a; simp [walk]
  | succ n ih => intro a; simp only [List.replicate_succ, walk, ih]; congr 1; omega

theorem walk_ones (a : Nat) : ∀ n, a < n → walk a (List.replicate n true) = none := by
  induction a with
  | zero => intro n hn; cases n with
    | zero => omega
    | succ n => rfl
  | succ a ih => intro n hn; cases n with
    | zero => omega
    | succ n => simp only [List.replicate_succ, walk]; exact ih n (by omega)

/-- Anti-Möbius side: from b ≡ −4 (mod 2^n) the machine survives n steps, any a. -/
theorem survives_neg4 (n a c : Nat) (hc : 2 ≤ c) :
    run n (a, 2 ^ n * c - 4) = some (a + 2 * n, iterT n (2 ^ n * c - 4)) := by
  rw [run_eq, pv_zeros n c hc, walk_zeros]; rfl

/-- Möbius side: from b ≡ −3 (mod 2^(a+1)) the machine halts within a+1 steps. -/
theorem halts_neg3 (a c : Nat) (hc : 2 ≤ c) : run (a + 1) (a, 2 ^ (a + 1) * c - 3) = none := by
  rw [run_eq, pv_ones (a + 1) c hc, walk_ones a (a + 1) (by omega)]; rfl


/-- Squeeze criterion: if b is 2-adically within 2^-(a+1) of the Möbius fixed
    point −3, the machine halts within a+1 macro-steps. -/
theorem halts_of_near_neg3 (a b : Nat)
    (h : b % 2 ^ (a + 1) = (2 ^ (a + 1) * 2 - 3) % 2 ^ (a + 1)) :
    run (a + 1) (a, b) = none := by
  rw [run_eq, pv_mod (a + 1) b _ h, pv_ones (a + 1) 2 (by decide),
    walk_ones a (a + 1) (by omega)]; rfl


/-! ### The frustration-free direction: a + t is conserved mod 3

  Both counter moves, +2 and −1, are ≡ −1 (mod 3). So the U(1) flux 2π/3,
  maximally frustrated on the parity-window graph alone, becomes exactly
  balanced once the time coordinate joins the base: a_t ≡ a_0 − t (mod 3).
  Consequence: halting can only happen at macro-steps t ≡ a_0 (mod 3). -/

theorem pv_succ_snoc (n : Nat) : ∀ b, pv (n + 1) b = pv n b ++ [iterT n b % 2 == 1] := by
  induction n with
  | zero => intro b; rfl
  | succ n ih => intro b; simp only [pv] at *; rw [ih (T b)]; rfl

theorem walk_append (v w : List Bool) : ∀ a,
    walk a (v ++ w) = (walk a v).bind (fun a' => walk a' w) := by
  induction v with
  | nil => intro a; simp [walk]
  | cons x v ih =>
    intro a
    cases x with
    | false => simp only [List.cons_append, walk]; exact ih _
    | true => cases a with
      | zero => rfl
      | succ a => simp only [List.cons_append, walk]; exact ih _

theorem walk_mod3 (v : List Bool) : ∀ a a', walk a v = some a' →
    (a' + v.length) % 3 = a % 3 := by
  induction v with
  | nil => intro a a' h; simp [walk] at h; subst h; simp
  | cons x v ih =>
    intro a a' h
    cases x with
    | false => simp only [walk] at h; have := ih _ _ h; simp only [List.length_cons]; omega
    | true => cases a with
      | zero => simp [walk] at h
      | succ a => simp only [walk] at h; have := ih _ _ h; simp only [List.length_cons]; omega

/-- Halting times live on a mod-3 lattice: if the machine survives n macro-steps
    and halts at step n+1, then n ≡ a₀ (mod 3). -/
theorem halt_time_mod3 (n a b : Nat) (h1 : (run n (a, b)).isSome)
    (h2 : run (n + 1) (a, b) = none) : n % 3 = a % 3 := by
  rw [run_eq] at h1 h2
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (by simpa using h1)
  have h2' : walk a (pv (n + 1) b) = none := by simpa using h2
  rw [pv_succ_snoc, walk_append, ha'] at h2'
  have hz : a' = 0 := by
    cases a' with
    | zero => rfl
    | succ a' => cases h : (iterT n b % 2 == 1) <;> simp [h, walk] at h2'
  have := walk_mod3 _ _ _ ha'
  rw [hz, pv_length] at this; omega

/-- Antihydra from A(0,4) can only halt after a multiple of 3 macro-steps. -/
theorem antihydra_halt_time_mod3 (n : Nat) (h1 : (run n (0, 4)).isSome)
    (h2 : run (n + 1) (0, 4) = none) : n % 3 = 0 :=
  halt_time_mod3 n 0 4 h1 h2


/-! ### Dyadic towers ℤ/2^k, ℤ/4^k, ℤ/8^k cannot see the conservation law

  Exact form of the mod-3 law: a + t = a₀ + 3·(number of even steps).
  The only affine invariants a + c·t (mod m) of the walk need m ∣ 3, so no
  ℤ/2^k (hence no ℤ/4^k = ℤ/2^(2k), no ℤ/8^k = ℤ/2^(3k)), k ≥ 1, carries one:
  every dyadic connection is frustrated at every level. -/

theorem walk_count (v : List Bool) : ∀ a a', walk a v = some a' →
    a' + v.length = a + 3 * v.count false := by
  induction v with
  | nil => intro a a' h; simp [walk] at h; subst h; simp
  | cons x v ih =>
    intro a a' h
    cases x with
    | false => simp only [walk] at h; have := ih _ _ h; simp; omega
    | true => cases a with
      | zero => simp [walk] at h
      | succ a => simp only [walk] at h; have := ih _ _ h; simp; omega

theorem invariant_needs_dvd3 (m c : Nat)
    (h : ∀ a v a', walk a v = some a' → (a' + c * v.length) % m = a % m) : m ∣ 3 := by
  have h1 := h 0 [false] 2 rfl
  have h2 := h 1 [true] 0 rfl
  simp at h1 h2
  apply Nat.dvd_of_mod_eq_zero
  have h1' : (2 + c) % m = 0 := h1
  have : (2 + c) % m = (2 + 1) % m := by rw [Nat.add_mod, h2, ← Nat.add_mod]
  rw [h1'] at this; exact this.symm

theorem not_pow2_dvd3 (k : Nat) (hk : 1 ≤ k) : ¬ 2 ^ k ∣ 3 := by
  intro h
  have h2 : 2 ∣ 2 ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨2 ^ j, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  have := Nat.dvd_trans h2 h
  omega

/-- No ℤ/2^k, ℤ/4^k or ℤ/8^k (k ≥ 1) affine counter–time invariant exists. -/
theorem no_dyadic_invariant (k c : Nat) (hk : 1 ≤ k) :
    ¬ (∀ a v a', walk a v = some a' → (a' + c * v.length) % 2 ^ k = a % 2 ^ k) ∧
    ¬ (∀ a v a', walk a v = some a' → (a' + c * v.length) % 4 ^ k = a % 4 ^ k) ∧
    ¬ (∀ a v a', walk a v = some a' → (a' + c * v.length) % 8 ^ k = a % 8 ^ k) := by
  have e4 : 4 ^ k = 2 ^ (2 * k) := by rw [Nat.pow_mul]
  have e8 : 8 ^ k = 2 ^ (3 * k) := by rw [Nat.pow_mul]
  refine ⟨fun h => not_pow2_dvd3 k hk (invariant_needs_dvd3 _ c h),
          fun h => not_pow2_dvd3 (2 * k) (by omega) (e4 ▸ invariant_needs_dvd3 _ c h),
          fun h => not_pow2_dvd3 (3 * k) (by omega) (e8 ▸ invariant_needs_dvd3 _ c h)⟩


/-! ### ℤ/3^k and ℤ/p^k

  Positive side: ℤ/3 carries the invariant a + t (`walk_mod3`). Negative side:
  ℤ/9 = ℤ/3² already does not, and no prime power p^k with p ≠ 3 does.
  Dual side: the 3-adic digits of the *current* b record the *past* parities
  (`pv_past3`), mirroring `pv_mod`, where the 2-adic digits fix the future. -/

theorem no_invariant_mod9 (c : Nat) :
    ¬ (∀ a v a', walk a v = some a' → (a' + c * v.length) % 9 = a % 9) :=
  fun h => by have := invariant_needs_dvd3 9 c h; omega

theorem no_invariant_prime_pow (p k c : Nat) (hp : 2 ≤ p) (hp3 : p ≠ 3) (hk : 1 ≤ k) :
    ¬ (∀ a v a', walk a v = some a' → (a' + c * v.length) % p ^ k = a % p ^ k) := by
  intro h
  have h3 := invariant_needs_dvd3 _ c h
  have hpk : p ∣ p ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨p ^ j, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  have hd := Nat.dvd_trans hpk h3
  have hle := Nat.le_of_dvd (by decide) hd
  have : p = 2 := by omega
  subst this; omega

/-- One backward step: T b mod 3^(i+1) fixes the parity of b and b mod 3^i. -/
theorem T_back3 (i b b' : Nat) (h : T b % 3 ^ (i + 1) = T b' % 3 ^ (i + 1)) :
    b % 2 = b' % 2 ∧ b % 3 ^ i = b' % 3 ^ i := by
  have e : ∀ x, T x = 3 * (x / 2) + 2 + x % 2 := by
    intro x; unfold T; split <;> omega
  rw [e, e] at h
  have h3 : (3 * (b / 2) + 2 + b % 2) % 3 = (3 * (b' / 2) + 2 + b' % 2) % 3 := by
    have d : 3 ∣ 3 ^ (i + 1) := ⟨3 ^ i, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    rw [← Nat.mod_mod_of_dvd _ d, h, Nat.mod_mod_of_dvd _ d]
  have hpar : b % 2 = b' % 2 := by omega
  refine ⟨hpar, ?_⟩
  rw [hpar] at h
  obtain ⟨k1, k2, e12⟩ := Nat.mod_eq_mod_iff.mp h
  have hq : (b / 2) % 3 ^ i = (b' / 2) % 3 ^ i := by
    apply Nat.mod_eq_mod_iff.mpr
    refine ⟨k1, k2, ?_⟩
    have : 3 ^ (i + 1) = 3 * 3 ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [this] at e12
    have a1 : k1 * (3 * 3 ^ i) = 3 * (k1 * 3 ^ i) := by rw [Nat.mul_left_comm]
    have a2 : k2 * (3 * 3 ^ i) = 3 * (k2 * 3 ^ i) := by rw [Nat.mul_left_comm]
    omega
  obtain ⟨l1, l2, f⟩ := Nat.mod_eq_mod_iff.mp hq
  apply Nat.mod_eq_mod_iff.mpr
  refine ⟨2 * l1, 2 * l2, ?_⟩
  have := Nat.mod_add_div b 2
  have := Nat.mod_add_div b' 2
  have g1 : 2 * l1 * 3 ^ i = 2 * (l1 * 3 ^ i) := by rw [Nat.mul_assoc]
  have g2 : 2 * l2 * 3 ^ i = 2 * (l2 * 3 ^ i) := by rw [Nat.mul_assoc]
  omega

/-- 3-adic memory: T^j b mod 3^(j+i) determines the j parities that led there
    (and b mod 3^i). The future lives in 2-adic digits, the past in 3-adic ones. -/
theorem pv_past3 (j : Nat) : ∀ i b b', iterT j b % 3 ^ (j + i) = iterT j b' % 3 ^ (j + i) →
    pv j b = pv j b' ∧ b % 3 ^ i = b' % 3 ^ i := by
  induction j with
  | zero => intro i b b' h; simpa [iterT, pv] using h
  | succ j ih =>
    intro i b b' h
    have h' : iterT j (T b) % 3 ^ (j + (i + 1)) = iterT j (T b') % 3 ^ (j + (i + 1)) := by
      have : j + 1 + i = j + (i + 1) := by omega
      simpa [iterT, this] using h
    obtain ⟨hv, hT⟩ := ih (i + 1) _ _ h'
    obtain ⟨hp, hb⟩ := T_back3 i b b' hT
    refine ⟨?_, hb⟩
    simp only [pv, hv, hp]


/-! ### Infinitesimal (torsion-free) exponents

  Passing to infinitesimal exponents replaces ℤ/p^k by its Lie algebra ℝ (or ℤ):
  torsion disappears, and with it the only invariant (mod 3). Over ℤ no linear
  combination a + c·t is conserved: the counter cocycle is never a coboundary. -/

theorem no_integer_invariant (c : Int) :
    ¬ (∀ a v a', walk a v = some a' → (a' : Int) + c * v.length = a) := by
  intro h
  have h1 := h 0 [false] 2 rfl
  have h2 := h 1 [true] 0 rfl
  simp at h1 h2
  omega


/-! ### Bridge to the real place: parities as base-3/2 digits

  2^n · b_n = 3^n · b_0 + S_n with S_{n+1} = 3·S_n + 2^n·(4 − p_n).
  So b_n = (3/2)^n · (b_0 + Σ (4 − p_k)·2^k/3^(k+1)): the orbit is one real number
  ξ = lim b_n/(3/2)^n, and the parities are digits of ⌊ξ·(3/2)^n⌋ (Mahler 3/2 setting). -/

def S : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, b => 3 * S n b + 2 ^ n * (4 - iterT n b % 2)

theorem iterT_succ' (n : Nat) : ∀ b, iterT (n + 1) b = T (iterT n b) := by
  induction n with
  | zero => intro b; rfl
  | succ n ih => intro b; simp only [iterT] at *; exact ih (T b)

theorem T_two (b : Nat) : 2 * T b = 3 * b + 4 - b % 2 := by
  unfold T; split <;> omega

theorem real_bridge (n b : Nat) : 2 ^ n * iterT n b = 3 ^ n * b + S n b := by
  induction n with
  | zero => simp [iterT, S]
  | succ n ih =>
    rw [iterT_succ', S, Nat.pow_succ, Nat.pow_succ]
    have h := T_two (iterT n b)
    have hp : iterT n b % 2 ≤ 1 := by omega
    have e1 : 2 ^ n * 2 * T (iterT n b) = 2 ^ n * (2 * T (iterT n b)) := by
      rw [Nat.mul_assoc]
    rw [e1, h]
    have e2 : 2 ^ n * (3 * iterT n b + 4 - iterT n b % 2)
        = 3 * (2 ^ n * iterT n b) + 2 ^ n * (4 - iterT n b % 2) := by
      rw [show 3 * iterT n b + 4 - iterT n b % 2 = 3 * iterT n b + (4 - iterT n b % 2) by omega,
        Nat.mul_add, Nat.mul_left_comm]
    rw [e2, ih, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 3 (3 ^ n)]
    omega

/-! Axiom audit -/
#print axioms pv_mod
#print axioms pv_inj
#print axioms pv_surj
#print axioms run_eq
#print axioms antihydra_survives_iff
#print axioms survives_neg4
#print axioms halts_neg3
#print axioms halts_of_near_neg3
#print axioms antihydra_halt_time_mod3
#print axioms walk_count
#print axioms no_dyadic_invariant
#print axioms no_invariant_mod9
#print axioms no_invariant_prime_pow
#print axioms pv_past3
#print axioms no_integer_invariant
#print axioms real_bridge
