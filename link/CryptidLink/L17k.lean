import CryptidLink.L17j
/-!
# L17: symmetry and antisymmetry of the internal D/G graph

* **Antisymmetry:** `internal_trans_decreases_lex` shows that every nonempty internal path decreases the rank.
  Hence `internal_acyclic` (no cycle of any length), `internal_step_irrefl` and `internal_step_asymm`.
* **Backward symmetry (opposite stream):** `internal_unique_root`. Two roots, meaning states with no internal
  predecessor, that reach the same state are equal. Together with `push_entry_is_root`, every internal state is
  descended from at most one push entry, and distinct entries never merge.
* **Where the symmetry stops:** `raw_not_injective`. The raw machine is not reversible: two different
  configurations take one step to the same configuration (GPT's witness). Backward uniqueness is a property of the
  macro domain, not of the machine.
* **No affine rank:** `no_affine_rank`. No score that is affine in (k, m, l, s) in each mode decreases on every
  internal edge (GPT's D1/D2/D12/G1 inequalities). The lexicographic rank of `L17j` supplies a ranking
  outside this excluded class; other nonlinear rankings are not excluded.
-/

open BusyBeaver BusyBeaver.SixState Turing Relation

namespace CryptidLink.L17

theorem lex3_iff (a b : ℕ × ℕ × ℕ) :
    lex3 a b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ a.2.1 = b.2.1 ∧ a.2.2 < b.2.2) := by
  unfold lex3; simp only [Prod.lex_def]

theorem lex3_trans {a b c : ℕ × ℕ × ℕ} (h1 : lex3 a b) (h2 : lex3 b c) : lex3 a c := by
  rw [lex3_iff] at *; omega

theorem lex3_irrefl (a : ℕ × ℕ × ℕ) : ¬ lex3 a a := by
  rw [lex3_iff]; omega

/-! ## Antisymmetry -/

/-- Every nonempty internal path decreases the lexicographic rank. -/
theorem internal_trans_decreases_lex {x y : St} (h : TransGen IStep x y) : lex3 y.rank x.rank := by
  induction h with
  | single h => exact internal_step_decreases_lex h
  | tail _ h ih => exact lex3_trans (internal_step_decreases_lex h) ih

/-- **No internal cycles.** -/
theorem internal_acyclic (x : St) : ¬ TransGen IStep x x :=
  fun h => lex3_irrefl _ (internal_trans_decreases_lex h)

theorem internal_step_irrefl (x : St) : ¬ IStep x x :=
  fun h => internal_acyclic x (TransGen.single h)

theorem internal_step_asymm {x y : St} (h : IStep x y) : ¬ IStep y x :=
  fun h' => internal_acyclic x (TransGen.tail (TransGen.single h) h')

/-! ## Backward symmetry: unique roots -/

/-- A root has no internal predecessor. -/
def IsRoot (r : St) : Prop := ∀ x, ¬ IStep x r

/-- **Opposite stream:** two roots reaching the same state coincide, so paths from distinct roots never merge. -/
theorem internal_unique_root {r₁ r₂ x : St} (h₁ : IsRoot r₁) (h₂ : IsRoot r₂)
    (p₁ : ReflTransGen IStep r₁ x) (p₂ : ReflTransGen IStep r₂ x) : r₁ = r₂ := by
  induction p₁ generalizing r₂ with
  | refl =>
    cases p₂ with
    | refl => rfl
    | tail _ h => exact absurd h (h₁ _)
  | tail q₁ s₁ ih =>
    cases p₂ with
    | refl => exact absurd s₁ (h₂ _)
    | tail q₂ s₂ =>
      have e := internal_step_injective s₁ s₂
      subst e
      exact ih h₂ q₂

/-- Every push entry is a root, so distinct push entries have disjoint internal descendants. -/
theorem push_entries_disjoint (u d u' d' : ℕ) (x : St)
    (p : ReflTransGen IStep (.D (2 * u + 2) 7 (2 * d + 1) 7 3) x)
    (p' : ReflTransGen IStep (.D (2 * u' + 2) 7 (2 * d' + 1) 7 3) x) : u = u' ∧ d = d' := by
  have e := internal_unique_root (fun y => push_entry_is_root u d y) (fun y => push_entry_is_root u' d' y) p p'
  simp only [St.D.injEq] at e
  omega

/-! ## Where the symmetry stops: the raw machine is not injective -/

/-- GPT's witness: A at −1 (ones at +1) and C at +1 (ones at −1, +1) both step to B at 0 (ones at −1, +1). -/
theorem raw_not_injective :
    ∃ c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6), c₁ ≠ c₂ ∧ step target c₁ = some c₃ ∧ step target c₂ = some c₃ := by
  refine ⟨Cfg.headRight A default (ListBlank.append [0, 0, 1] default),
    Cfg.headRight C (ListBlank.append [0, 1] default) (ListBlank.append [1] default),
    Cfg.headRight B (ListBlank.append [1] default) (ListBlank.append [0, 1] default), ?_, rfl, rfl⟩
  intro h
  have := congrArg Cfg.q h
  simp only [Cfg.headRight, Option.some.injEq] at this
  exact absurd this (by decide)

/-! ## No affine rank -/

/-- An affine score in (k, m, l, s) in each mode, independent of the leading counter N. -/
def affScore (aD bD lD sD cD aG lG sG cG : ℤ) : St → ℤ
  | .D _ k m l s => aD * k + bD * m + lD * l + sD * s + cD
  | .G _ k l s => aG * k + lG * l + sG * s + cG

/-- **No affine rank:** no per-mode affine score in (k, m, l, s) decreases along every internal edge. -/
theorem no_affine_rank (aD bD lD sD cD aG lG sG cG : ℤ) :
    ¬ ∀ x y, IStep x y → affScore aD bD lD sD cD aG lG sG cG y < affScore aD bD lD sD cD aG lG sG cG x := by
  intro H
  -- D2 (q = 0, k = 1, m = 1, l = 1, s = 0): aD > 0
  have h2 := H _ _ (IStep.d2 0 1 1 1 0 le_rfl le_rfl rfl rfl)
  -- D1 (p = 0, k = 1, m = 1, l = 1, s = 0): 7 aD − 3 bD < 0
  have h1 := H _ _ (IStep.d1 0 1 1 1 0 le_rfl le_rfl le_rfl rfl rfl)
  simp only [affScore] at h1 h2
  push_cast at h1 h2
  -- D12 at large k: aG ≤ aD
  have h12 : aG ≤ aD := by
    by_contra hc
    rw [not_le] at hc
    set K := (2 * bD + lD + cD - 6 * aG - lG - cG).toNat + 1 with hK
    have h := H _ _ (IStep.d12 0 K 1 0 (by omega) le_rfl rfl rfl)
    simp only [affScore] at h
    push_cast at h
    have hK' : (K : ℤ) ≥ 2 * bD + lD + cD - 6 * aG - lG - cG + 1 := by
      rw [hK]; push_cast; have := Int.self_le_toNat (2 * bD + lD + cD - 6 * aG - lG - cG); omega
    nlinarith
  -- G1 at large k: 2 bD ≤ aG
  have hg1 : 2 * bD ≤ aG := by
    by_contra hc
    rw [not_le] at hc
    set K := (2 * lG + cG - 7 * aD - 4 * bD - lD - cD).toNat + 1 with hK
    have h := H _ _ (IStep.g1 0 K 1 0 le_rfl rfl rfl)
    simp only [affScore] at h
    push_cast at h
    have hK' : (K : ℤ) ≥ 2 * lG + cG - 7 * aD - 4 * bD - lD - cD + 1 := by
      rw [hK]; push_cast; have := Int.self_le_toNat (2 * lG + cG - 7 * aD - 4 * bD - lD - cD); omega
    nlinarith
  omega

end CryptidLink.L17

#print axioms CryptidLink.L17.internal_acyclic
#print axioms CryptidLink.L17.internal_step_asymm
#print axioms CryptidLink.L17.internal_unique_root
#print axioms CryptidLink.L17.push_entries_disjoint
#print axioms CryptidLink.L17.raw_not_injective
#print axioms CryptidLink.L17.no_affine_rank
