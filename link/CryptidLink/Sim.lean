import Mathlib
/-!
# Simulation lemma

If every step of a macro system `f` is matched by one or more steps of a finer system `g`
(through `φ`, on states satisfying an invariant), and every halt of `f` by a halt of `g`,
then `g` halts from `φ s₀` iff `f` halts from `s₀`. Halting is the upstream notion
`∃ n, ((Option.bind · g)^[n] (some t)).isNone`.
-/

namespace CryptidLink

variable {S T : Type*}

def It (g : T → Option T) (n : ℕ) (o : Option T) : Option T := (fun o => o.bind g)^[n] o

theorem It_none (g : T → Option T) (n : ℕ) : It g n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => unfold It at *; rw [Function.iterate_succ_apply]; exact ih

theorem It_add (g : T → Option T) (a b : ℕ) (o : Option T) : It g (a + b) o = It g a (It g b o) := by
  unfold It; rw [Function.iterate_add_apply]

theorem It_succ (g : T → Option T) (n : ℕ) (t : T) : It g (n + 1) (some t) = It g n (g t) := by
  unfold It; rw [Function.iterate_succ_apply]; rfl

theorem sim_halts (f : S → Option S) (g : T → Option T) (φ : S → T) (Inv : S → Prop) (s₀ : S)
    (h0 : Inv s₀)
    (hinv : ∀ s s', Inv s → f s = some s' → Inv s')
    (hsome : ∀ s s', Inv s → f s = some s' → ∃ k, It g (k + 1) (some (φ s)) = some (φ s'))
    (hnone : ∀ s, Inv s → f s = none → ∃ k, It g k (some (φ s)) = none) :
    (∃ m, It g m (some (φ s₀)) = none) ↔ (∃ n, It f n (some s₀) = none) := by
  constructor
  · rintro ⟨m, hm⟩
    by_contra hno
    push_neg at hno
    have key : ∀ n, ∃ s, It f n (some s₀) = some s ∧ Inv s ∧
        ∃ K, n ≤ K ∧ It g K (some (φ s₀)) = some (φ s) := by
      intro n
      induction n with
      | zero => exact ⟨s₀, rfl, h0, 0, le_refl _, rfl⟩
      | succ n ih =>
        obtain ⟨s, hs, hI, K, hK, hG⟩ := ih
        have hn1 := hno (n + 1)
        rw [show n + 1 = 1 + n from by omega, It_add, hs] at hn1
        cases hf : f s with
        | none => exact absurd (by simp [It, hf]) hn1
        | some s' =>
          obtain ⟨k, hk⟩ := hsome s s' hI hf
          refine ⟨s', ?_, hinv s s' hI hf, k + 1 + K, by omega, ?_⟩
          · rw [show n + 1 = 1 + n from by omega, It_add, hs]; simp [It, hf]
          · rw [It_add, hG, hk]
    obtain ⟨s, -, -, K, hK, hG⟩ := key m
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
    rw [Nat.add_comm, It_add, hm, It_none] at hG
    exact Option.noConfusion hG
  · rintro ⟨n, hn⟩
    have P : ∀ n s, Inv s → It f n (some s) = none → ∃ m, It g m (some (φ s)) = none := by
      intro n
      induction n with
      | zero => intro s _ h; exact Option.noConfusion h
      | succ n ih =>
        intro s hI h
        rw [It_succ] at h
        cases hf : f s with
        | none => exact hnone s hI hf
        | some s' =>
          rw [hf] at h
          obtain ⟨m, hm⟩ := ih s' (hinv s s' hI hf) h
          obtain ⟨k, hk⟩ := hsome s s' hI hf
          exact ⟨m + (k + 1), by rw [It_add, hk, hm]⟩
    exact P n s₀ h0 hn

end CryptidLink
