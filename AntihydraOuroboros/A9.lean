/-
  A.9 (1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD), Appendix A.9 of arXiv:2610.22603.

  `step9o` is the paper's verified two-family system (C₀, C₁); `step9` is its merged form
  C(a,b,c) with C₀(a,b,c) = C(2a,b,c), C₁(a,b,c) = C(2a+1,b,c). `step9_enc` proves the
  two agree. Then: sweep compression, the Poincaré-section map S(a,c) := C(a,0,c), and
  the invariant a ≡ 2 (mod 3) along the orbit from C(5,2,0).
-/

/-- Original rules: the Bool is the family (false = C₀, true = C₁). `none` = Halt. -/
def step9o : Bool × Nat × Nat × Nat → Option (Bool × Nat × Nat × Nat)
  | (false, _, 0, 0) => none
  | (false, a, 0, 1) => some (true, 2, 2, a + 1)
  | (false, a, 0, c + 2) => some (false, 1, a + 3, c)
  | (false, a, b + 1, 0) => some (true, a + 1, 0, b)
  | (false, a, b + 1, c + 1) => some (false, a + 3, b, c)
  | (true, _, 0, 0) => none
  | (true, a, 0, 1) => some (false, 1, 0, a + 3)
  | (true, a, 0, c + 2) => some (true, 2, a + 3, c)
  | (true, a, b + 1, 0) => some (false, a + 2, 0, b)
  | (true, a, b + 1, c + 1) => some (true, a + 3, b, c)

/-- Merged rules on C(a,b,c). -/
def step9 (s : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  let a := s.1; let b := s.2.1; let c := s.2.2
  if b = 0 ∧ c = 0 then none
  else if b = 0 ∧ c = 1 then (if a % 2 = 0 then some (5, 2, a / 2 + 1) else some (2, 0, a / 2 + 3))
  else if b = 0 then (if a % 2 = 0 then some (2, a / 2 + 3, c - 2) else some (5, a / 2 + 3, c - 2))
  else if c = 0 then some (a + 3, 0, b - 1)
  else some (a + 6, b - 1, c - 1)

def enc : Bool × Nat × Nat × Nat → Nat × Nat × Nat
  | (false, a, b, c) => (2 * a, b, c)
  | (true, a, b, c) => (2 * a + 1, b, c)

/-- The merged system is exactly the paper's two-family system, read through `enc`. -/
theorem step9_enc (x : Bool × Nat × Nat × Nat) : step9 (enc x) = (step9o x).map enc := by
  obtain ⟨f, a, b, c⟩ := x
  cases f <;> rcases b with _ | b <;> rcases c with _ | _ | c <;>
    simp [step9, step9o, enc] <;> omega

/-- Close `some x = some y` goals by components. -/
macro "fin_eq" : tactic =>
  `(tactic| ((simp (config := {failIfUnchanged := false}) only
      [Option.bind, Option.some.injEq, Prod.mk.injEq, true_and, and_true]) <;> omega))

def run9 : Nat → Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | 0, s => some s
  | n + 1, s => (step9 s).bind (run9 n)

/-- Draining sweep: n applications of C(a,b+1,c+1) → C(a+6,b,c). -/
theorem drain (n : Nat) : ∀ a b c, run9 n (a, b + n, c + n) = some (a + 6 * n, b, c) := by
  induction n with
  | zero => intro a b c; simp [run9]
  | succ n ih =>
    intro a b c
    have e : step9 (a, b + (n + 1), c + (n + 1)) = some (a + 6, b + n, c + n) := by
      dsimp only [step9]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      fin_eq
    show (step9 _).bind (run9 n) = _
    rw [e]; show run9 n (a + 6, b + n, c + n) = _
    rw [ih]; fin_eq

/-- Sweep compression, case b ≤ c. -/
theorem sweep_le (a b c : Nat) (h : b ≤ c) : run9 b (a, b, c) = some (a + 6 * b, 0, c - b) := by
  have := drain b a 0 (c - b)
  rw [Nat.zero_add, Nat.sub_add_cancel h] at this
  exact this

theorem run9_add (k : Nat) : ∀ n s, run9 (n + k) s = (run9 n s).bind (run9 k) := by
  intro n
  induction n with
  | zero => intro s; simp [run9]
  | succ n ih =>
    intro s
    rw [Nat.add_right_comm]
    show (step9 s).bind (run9 (n + k)) = ((step9 s).bind (run9 n)).bind (run9 k)
    cases step9 s with
    | none => rfl
    | some t => exact ih t

/-- Sweep compression, case b > c: C(a,b,c) ↠ C(a + 6c + 3, 0, b − c − 1). -/
theorem sweep_gt (a b c : Nat) (h : c < b) :
    run9 (c + 1) (a, b, c) = some (a + 6 * c + 3, 0, b - c - 1) := by
  have hd := drain c a (b - c) 0
  rw [Nat.zero_add, Nat.sub_add_cancel (Nat.le_of_lt h)] at hd
  rw [run9_add, hd]
  show (step9 (a + 6 * c, b - c, 0)).bind (run9 0) = _
  dsimp only [step9]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  simp only [run9]; fin_eq

/-- Poincaré map, branch 1 (c ≥ k+5): S(2k+p, c) ↠ S(6k+20+3p, c−k−5). -/
theorem section_branch1 (k p c : Nat) (hp : p ≤ 1) (hc : k + 5 ≤ c) :
    run9 (1 + (k + 3)) (2 * k + p, 0, c) = some (6 * k + 20 + 3 * p, 0, c - k - 5) := by
  rw [run9_add]
  have e : run9 1 (2 * k + p, 0, c) = some (2 + 3 * p, k + 3, c - 2) := by
    dsimp only [run9, step9]
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    rcases Nat.lt_or_ge p 1 with h | h
    · rw [if_pos (by omega)]; fin_eq
    · rw [if_neg (by omega)]; fin_eq
  rw [e]
  show run9 (k + 3) (2 + 3 * p, k + 3, c - 2) = _
  rw [sweep_le _ _ _ (by omega)]
  fin_eq

/-- Poincaré map, branch 2 (2 ≤ c < k+5): S(2k+p, c) ↠ S(6c−7+3p, k+4−c). -/
theorem section_branch2 (k p c : Nat) (hp : p ≤ 1) (hc2 : 2 ≤ c) (hc : c < k + 5) :
    run9 (1 + ((c - 2) + 1)) (2 * k + p, 0, c) = some (6 * c - 7 + 3 * p, 0, k + 4 - c) := by
  rw [run9_add]
  have e : run9 1 (2 * k + p, 0, c) = some (2 + 3 * p, k + 3, c - 2) := by
    dsimp only [run9, step9]
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    rcases Nat.lt_or_ge p 1 with h | h
    · rw [if_pos (by omega)]; fin_eq
    · rw [if_neg (by omega)]; fin_eq
  rw [e]
  show run9 ((c - 2) + 1) (2 + 3 * p, k + 3, c - 2) = _
  rw [sweep_gt _ _ _ (by omega)]
  fin_eq

/-- Every rule maps a ≡ 2 (mod 3) to a ≡ 2 (mod 3). -/
theorem step9_mod3 (s t : Nat × Nat × Nat) (hs : s.1 % 3 = 2) (h : step9 s = some t) :
    t.1 % 3 = 2 := by
  obtain ⟨a, b, c⟩ := s
  simp only [step9] at h hs
  repeat' split at h
  all_goals (first
    | (simp only [Option.some.injEq] at h; subst h; (simp (config := {failIfUnchanged := false})) <;> omega)
    | simp at h)

/-- Along the orbit from the start C(5,2,0), a ≡ 2 (mod 3) always. -/
theorem a9_mod3 : ∀ n s, run9 n (5, 2, 0) = some s → s.1 % 3 = 2 := by
  have gen : ∀ n s₀ s, s₀.1 % 3 = 2 → run9 n s₀ = some s → s.1 % 3 = 2 := by
    intro n
    induction n with
    | zero => intro s₀ s h0 h; simp [run9] at h; subst h; exact h0
    | succ n ih =>
      intro s₀ s h0 h
      simp only [run9] at h
      cases hs : step9 s₀ with
      | none => rw [hs] at h; simp at h
      | some t => rw [hs] at h; exact ih t s (step9_mod3 s₀ t h0 hs) h
  intro n s h; exact gen n (5, 2, 0) s (by decide) h

/-- The only halting configurations are C(a,0,0). -/
theorem step9_halt_iff (a b c : Nat) : step9 (a, b, c) = none ↔ b = 0 ∧ c = 0 := by
  dsimp only [step9]
  constructor
  · intro h; repeat' split at h
    all_goals simp_all
  · intro ⟨hb, hc⟩; rw [if_pos ⟨hb, hc⟩]

/-- Sanity check against the trace C(5,2,0) → C(8,0,1) → C(5,2,5). -/
example : run9 2 (5, 2, 0) = some (5, 2, 5) := by decide

#print axioms step9_enc
#print axioms section_branch1
#print axioms section_branch2
#print axioms a9_mod3
#print axioms step9_halt_iff

/-! ### A.9 halting criterion: a race that starts tied, or with b one ahead -/

theorem run9_succ' (n : Nat) : ∀ s, run9 (n + 1) s = (run9 n s).bind step9 := by
  induction n with
  | zero => intro s; simp [run9]
  | succ n ih =>
    intro s
    show (step9 s).bind (run9 (n + 1)) = ((step9 s).bind (run9 n)).bind step9
    cases step9 s with
    | none => rfl
    | some t => exact ih t

/-- A race state: b ≥ 1 and b − c ∈ {0, 1}. -/
def raceHalts (s : Nat × Nat × Nat) : Prop := 1 ≤ s.2.1 ∧ (s.2.1 = s.2.2 ∨ s.2.1 = s.2.2 + 1)

/-- From a race state the machine halts (after b+1 steps). -/
theorem halts_of_race (a b c : Nat) (h : raceHalts (a, b, c)) : run9 (b + 1) (a, b, c) = none := by
  obtain ⟨hb, h | h⟩ := h
  · simp only at h hb; subst h
    rw [run9_succ', sweep_le _ _ _ (Nat.le_refl _)]
    simp only [Option.bind, step9]; rw [Nat.sub_self, if_pos (by simp)]
  · simp only at h hb; subst h
    rw [run9_succ', sweep_gt a (c + 1) c (by omega)]
    simp only [Option.bind, step9]; rw [if_pos (by simp)]

/-- The only predecessors of a halting configuration C(a,0,0) are race states. -/
theorem pred_of_halt (r : Nat × Nat × Nat) (a : Nat) (h : step9 r = some (a, 0, 0)) : raceHalts r := by
  obtain ⟨x, b, c⟩ := r
  dsimp only [step9] at h
  repeat' split at h
  all_goals (first
    | (simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       first | omega | (unfold raceHalts; dsimp only; omega)))

/-- **A.9 halting criterion.** From its start C(5,2,0), A.9 halts iff it reaches a state
    C(a,b,c) with b ≥ 1 and b − c ∈ {0, 1}: a sweep that ends exactly in a tie. -/
theorem a9_halts_iff :
    (∃ n, run9 n (5, 2, 0) = none) ↔ ∃ n s, run9 n (5, 2, 0) = some s ∧ raceHalts s := by
  constructor
  · intro ⟨n, hn⟩
    -- first index where the run dies
    have first : ∀ n, run9 n (5, 2, 0) = none →
        ∃ m s, run9 m (5, 2, 0) = some s ∧ step9 s = none := by
      intro n
      induction n with
      | zero => intro h; simp [run9] at h
      | succ n ih =>
        intro h
        rw [run9_succ'] at h
        cases hr : run9 n (5, 2, 0) with
        | none => exact ih hr
        | some s => rw [hr] at h; exact ⟨n, s, hr, h⟩
    obtain ⟨m, ⟨a, b, c⟩, hm, hs⟩ := first n hn
    obtain ⟨rfl, rfl⟩ := (step9_halt_iff a b c).mp hs
    cases m with
    | zero => simp [run9] at hm
    | succ m =>
      rw [run9_succ'] at hm
      cases hr : run9 m (5, 2, 0) with
      | none => rw [hr] at hm; simp at hm
      | some r => rw [hr] at hm; exact ⟨m, r, hr, pred_of_halt r a hm⟩
  · intro ⟨n, ⟨a, b, c⟩, hn, hr⟩
    refine ⟨n + (b + 1), ?_⟩
    rw [run9_add, hn]; exact halts_of_race a b c hr

#print axioms a9_halts_iff
