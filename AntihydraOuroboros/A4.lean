/-
  A.4 (1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA), rules from Appendix A.4 of
  arXiv:2610.22603:
    C(a,b)    → C(2a+2, b-2a-2)               if b > 2a+2      ("expansion")
    C(a,1)    → C(2, 2a+2)
    C(a,2)    → Halt
    C(a,2k)   → C((6a+2k+2)/4, (6a+2k+2)%4+1) if a ≥ 1, 2 ≤ k ≤ a+1   ("contraction")
    C(a,2k+1) → C((6a+2k+6)/4, (6a+2k+6)%4+1) if a ≥ 1, 1 ≤ k ≤ a
  Results: contraction never lands on b = 2; the expansion cascade from C(m,1)
  hits b = 2 exactly when m + s + 4 = 2^(s+2), i.e. m ∈ {0, 3, 10, 25, 56, 119, …}.
-/

/-- Contractions only produce b ∈ {1, 3}: never the halting value 2. -/
theorem con_even_out (a k : Nat) : (6 * a + 2 * k + 2) % 4 + 1 = 1 ∨ (6 * a + 2 * k + 2) % 4 + 1 = 3 := by
  omega

theorem con_odd_out (a k : Nat) : (6 * a + 2 * k + 6) % 4 + 1 = 1 ∨ (6 * a + 2 * k + 6) % 4 + 1 = 3 := by
  omega

/-- One expansion step (guard handled separately). -/
def expand (p : Nat × Nat) : Nat × Nat := (2 * p.1 + 2, p.2 - (2 * p.1 + 2))

def expandIter : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | s + 1, p => expand (expandIter s p)

/-- pw s = 2^(s+2), as a recursion omega can treat as an atom. -/
def pw : Nat → Nat
  | 0 => 4
  | s + 1 => 2 * pw s

theorem pw_eq (s : Nat) : pw s = 2 ^ (s + 2) := by
  induction s with
  | zero => rfl
  | succ s ih => rw [pw, ih, show s + 1 + 2 = (s + 2) + 1 by omega]; exact (Nat.pow_succ 2 (s + 2)).symm ▸ Nat.mul_comm _ _

theorem pw_ge (s : Nat) : 4 ≤ pw s := by
  induction s with
  | zero => decide
  | succ s ih => simp only [pw]; omega

/-- Closed form of s expansion steps from C(2, B), as long as no subtraction truncates:
    a = 2^(s+2) − 2 and b = B + 2s + 8 − 2^(s+3). -/
theorem expand_closed (B : Nat) : ∀ s, 2 * pw s ≤ B + 2 * s + 8 →
    expandIter s (2, B) = (pw s - 2, B + 2 * s + 8 - 2 * pw s) := by
  intro s
  induction s with
  | zero => intro _; simp [expandIter, pw]
  | succ s ih =>
    intro h
    simp only [pw] at h
    have g := pw_ge s
    rw [expandIter, ih (by omega), expand]
    simp only [pw, Prod.mk.injEq]
    constructor <;> omega

/-- The cascade started by C(m,1) → C(2, 2m+2) reaches b = 2 after s expansions
    exactly when m + s + 4 = 2^(s+2). -/
theorem cascade_hits_two (m s : Nat) (h : 2 * 2 ^ (s + 2) ≤ 2 * m + 2 + 2 * s + 8) :
    (expandIter s (2, 2 * m + 2)).2 = 2 ↔ m + s + 4 = 2 ^ (s + 2) := by
  rw [← pw_eq] at h ⊢
  rw [expand_closed _ s h]
  simp only
  omega

example : (List.range 7).map (fun s => 2 ^ (s + 2) - 4 - s) = [0, 3, 10, 25, 56, 119, 246] := by decide

#print axioms con_even_out
#print axioms expand_closed
#print axioms cascade_hits_two

/-! ### The full A.4 halting criterion

  The closed rule system, transcribed from Appendix A.4. Uncovered states (only b = 0)
  are mapped to themselves; the invariant `J` below shows b = 0 is never reached, so
  this modelling choice never matters. `none` = Halt. -/

def step4 (p : Nat × Nat) : Option (Nat × Nat) :=
    let a := p.1; let b := p.2
    if 2 * a + 2 < b then some (2 * a + 2, b - (2 * a + 2))
    else if b = 1 then some (2, 2 * a + 2)
    else if b = 2 then none
    else if b % 2 = 0 then
      (if 1 ≤ a ∧ 2 ≤ b / 2 ∧ b / 2 ≤ a + 1 then some ((6 * a + b + 2) / 4, (6 * a + b + 2) % 4 + 1)
       else some (a, b))
    else
      (if 1 ≤ a ∧ 1 ≤ b / 2 ∧ b / 2 ≤ a then some ((6 * a + (b - 1) + 6) / 4, (6 * a + (b - 1) + 6) % 4 + 1)
       else some (a, b))

def run4 : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, p => some p
  | n + 1, p => (step4 p).bind (run4 n)

theorem run4_succ' (n : Nat) : ∀ p, run4 (n + 1) p = (run4 n p).bind step4 := by
  induction n with
  | zero => intro p; simp [run4]
  | succ n ih =>
    intro p
    show (step4 p).bind (run4 (n + 1)) = ((step4 p).bind (run4 n)).bind step4
    cases step4 p with
    | none => rfl
    | some q => exact ih q

theorem run4_add (k : Nat) : ∀ n p, run4 (n + k) p = (run4 n p).bind (run4 k) := by
  induction k with
  | zero => intro n p; rw [Nat.add_zero]; cases run4 n p <;> rfl
  | succ k ih =>
    intro n p
    rw [← Nat.add_assoc, run4_succ', ih]
    cases run4 n p with
    | none => rfl
    | some q => exact (run4_succ' k q).symm

/-- Invariant: b ∉ {0, 2}, and every state above the contraction band is an
    expansion-cascade state (pw j − 2, 2m + 2j + 10 − 2·pw j) for some m off the halting set. -/
def J : Nat × Nat → Prop
  | (a, b) => b ≠ 0 ∧ b ≠ 2 ∧ (2 * a + 2 < b →
      ∃ m j, (∀ s, m + s + 4 ≠ pw s) ∧ a + 2 = pw j ∧ b + 2 * pw j = 2 * m + 2 * j + 10)

theorem J_noHalt (a b : Nat) (hJ : J (a, b)) : step4 (a, b) ≠ none := by
  obtain ⟨h0, h2, _⟩ := hJ
  dsimp only [step4]
  repeat' split
  all_goals simp_all

theorem J_step (a b a' b' : Nat) (hJ : J (a, b)) (hv : b = 1 → ∀ s, a + s + 4 ≠ pw s)
    (h : step4 (a, b) = some (a', b')) : J (a', b') := by
  obtain ⟨h0, h2, hc⟩ := hJ
  dsimp only [step4] at h
  repeat' split at h
  -- 1. expansion
  next hgt =>
    obtain ⟨m, j, hm, ha, hb⟩ := hc hgt
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by omega, ?_, ?_⟩
    · intro hb2; apply hm (j + 1); simp only [pw]; omega
    · intro _; exact ⟨m, j + 1, hm, by simp only [pw]; omega, by simp only [pw]; omega⟩
  -- 2. b = 1
  next _ h1 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hm := hv h1
    have ha0 : a ≠ 0 := fun ha => hm 0 (by simp only [pw]; omega)
    exact ⟨by omega, by omega, fun _ => ⟨a, 0, hm, by simp [pw], by simp only [pw]; try omega⟩⟩
  -- 4. even contraction
  next =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, fun _ => by omega⟩
  -- 5. even, outside guard (identity)
  next =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h0, h2, hc⟩
  -- 6. odd contraction
  next =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, fun _ => by omega⟩
  -- 7. odd, outside guard (identity)
  next =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h0, h2, hc⟩

theorem a4_inv (Hv : ∀ n m, run4 n (2, 1) = some (m, 1) → ∀ s, m + s + 4 ≠ pw s) :
    ∀ n, ∃ p, run4 n (2, 1) = some p ∧ J p := by
  intro n
  induction n with
  | zero => exact ⟨(2, 1), rfl, by decide, by decide, fun h => by omega⟩
  | succ n ih =>
    obtain ⟨⟨a, b⟩, hp, hJ⟩ := ih
    rw [run4_succ', hp]
    cases hs : step4 (a, b) with
    | none => exact absurd hs (J_noHalt a b hJ)
    | some q =>
      obtain ⟨a', b'⟩ := q
      refine ⟨(a', b'), by simpa [Option.bind] using hs, J_step a b a' b' hJ ?_ hs⟩
      intro h1; subst h1; exact Hv n a hp

theorem pw_grow (i : Nat) : ∀ s, i < s → 2 * pw i + 4 * (s - i - 1) ≤ pw s := by
  intro s
  induction s with
  | zero => intro h; omega
  | succ s ih =>
    intro h
    have g := pw_ge i
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · have := ih h'; simp only [pw]; omega
    · subst h'; simp only [pw]; omega

theorem cascade_run (m : Nat) : ∀ j, (∀ i, i < j → 4 * pw i < 2 * m + 2 * i + 12) →
    run4 j (2, 2 * m + 2) = some (pw j - 2, 2 * m + 2 * j + 10 - 2 * pw j) := by
  intro j
  induction j with
  | zero => intro _; simp [run4, pw]
  | succ j ih =>
    intro hg
    have g := pw_ge j
    have hj := hg j (by omega)
    rw [run4_succ', ih (fun i hi => hg i (by omega))]
    simp only [Option.bind, step4]
    rw [if_pos (by omega)]
    simp only [pw, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega

/-- If A.4 ever visits C(m,1) with m + s + 4 = 2^(s+2), it halts s + 2 steps later. -/
theorem a4_halts_of (n m s : Nat) (h : run4 n (0, 3) = some (m, 1)) (hs : m + s + 4 = 2 ^ (s + 2)) :
    run4 (n + (s + 2)) (0, 3) = none := by
  rw [← pw_eq] at hs
  rw [run4_add, h]
  show (step4 (m, 1)).bind (run4 (s + 1)) = none
  have e1 : step4 (m, 1) = some (2, 2 * m + 2) := by simp [step4]
  rw [e1]
  show run4 (s + 1) (2, 2 * m + 2) = none
  have hg : ∀ i, i < s → 4 * pw i < 2 * m + 2 * i + 12 := by
    intro i hi; have := pw_grow i s hi; have := pw_ge i; omega
  rw [run4_succ', cascade_run m s hg]
  have g := pw_ge s
  simp only [Option.bind, step4]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- If no visited C(m,1) lies on the halting set, A.4 never halts. -/
theorem a4_never_halts_of
    (H : ∀ n m, run4 n (0, 3) = some (m, 1) → ∀ s, m + s + 4 ≠ 2 ^ (s + 2)) :
    ∀ n, run4 n (0, 3) ≠ none := by
  have Hv : ∀ n m, run4 n (2, 1) = some (m, 1) → ∀ s, m + s + 4 ≠ pw s := by
    intro n m h s; rw [pw_eq]; exact H (n + 1) m (by simpa [run4, step4] using h) s
  intro n
  cases n with
  | zero => simp [run4]
  | succ n =>
    obtain ⟨p, hp, _⟩ := a4_inv Hv n
    have : run4 (n + 1) (0, 3) = run4 n (2, 1) := by simp [run4, step4]
    rw [this, hp]; simp

/-- **A.4 halting criterion.** A.4 (from its start C(0,3)) halts iff it visits some C(m,1)
    with m = 2^(s+2) − 4 − s, i.e. m ∈ {0, 3, 10, 25, 56, 119, 246, …}. -/
theorem a4_halts_iff :
    (∃ n, run4 n (0, 3) = none) ↔
      ∃ n m s, run4 n (0, 3) = some (m, 1) ∧ m + s + 4 = 2 ^ (s + 2) := by
  constructor
  · intro ⟨n, hn⟩
    apply Classical.byContradiction
    intro hno
    exact a4_never_halts_of (fun n m h s hs => hno ⟨n, m, s, h, hs⟩) n hn
  · intro ⟨n, m, s, h, hs⟩
    exact ⟨_, a4_halts_of n m s h hs⟩

/-- Sanity check against the paper: C(0,3) → C(2,1) → C(2,6) → C(5,1). -/
example : run4 3 (0, 3) = some (5, 1) := by decide

#print axioms a4_halts_iff
