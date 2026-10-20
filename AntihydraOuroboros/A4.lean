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
