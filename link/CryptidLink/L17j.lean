import CryptidLink.L17i
/-!
# L17: the internal D/G transition graph (GPT, `analysis/l17-frames/CLAUDE-BRIEF.md`)

States: D(N, k, m; l, s) = 𝒞(0; 1^N (01)^k 1^m (01)^l 1^s) and G(N, k; l, s) = 𝒞(0; 1^N (01)^k 0 (01)^l 1^s).
The six guarded internal rows (D1, D2, D12, G1, G2, D11join) form `IStep`. Proved:

* `IStep.sound`: every internal edge is machine reachability (via `Dg1`, `Dg2`, `Dg12`, `Gg1`, `Gg2`, `Dg11J`);
* `internal_step_injective`: every state has at most one internal predecessor (the opposite stream is a function);
* `internal_step_decreases_lex`: the rank (s, l, 3k+8m+3 | 3k) decreases lexicographically on every edge;
* `internal_predecessor_decreases_lex`: (N, k) increases lexicographically on every edge, so ancestry is finite;
* `push_entry_is_root`: an F1100 output D(2u+2, 7, 2d+1; 7, 3) has no internal predecessor;
* `internal_terminates`: from every state the machine reaches a state with no internal successor.

These are statements about the internal rows only. Exits to S, the outer dynamics and the uncovered
JOIN/G guards are not covered here; universal collapse and a stack bound remain open.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Internal D/G states. -/
inductive St where
  | D (N k m l s : ℕ)
  | G (N k l s : ℕ)
  deriving DecidableEq

/-- The terminal (01)^l 1^s, on a blank exterior. -/
def term (l s : ℕ) : ListBlank (Fin 2) :=
  ListBlank.append (([0, 1] : List (Fin 2)) ^ l) (ListBlank.append (([1] : List (Fin 2)) ^ s) default)

/-- The machine configuration of a state. -/
def St.cfg : St → Cfg (Fin 2) (Fin 6)
  | .D N k m l s => Dg N k m (term l s)
  | .G N k l s => Gg N k (term l s)

/-- The six guarded internal rows (GPT's table; every target stays in the canonical domain).
Endpoints are given by equations, so that case analysis never has to unify arithmetic indices. -/
inductive IStep (x y : St) : Prop
  | d1 (p k m l s : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hl : 1 ≤ l)
      (hx : x = .D (3 * p + 4) k (m + 3) l s) (hy : y = .D (10 * p + 4) (k + 7) m l s)
  | d2 (q k m l s : ℕ) (hm : 1 ≤ m) (hl : 1 ≤ l)
      (hx : x = .D (3 * q + 2) (k + 2) m l s) (hy : y = .D (10 * q + 15) (k + 1) m l s)
  | d12 (p k l s : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
      (hx : x = .D (3 * p + 4) k 2 l s) (hy : y = .G (10 * p + 4) (k + 6) l s)
  | g1 (p k l s : ℕ) (hl : 1 ≤ l)
      (hx : x = .G (3 * p + 7) k (l + 1) s) (hy : y = .D (10 * p + 10) 7 (2 * k + 4) l s)
  | g2 (q k l s : ℕ) (hl : 1 ≤ l)
      (hx : x = .G (3 * q + 2) (k + 1) l s) (hy : y = .G (10 * q + 15) k l s)
  | join (p e l s : ℕ)
      (hx : x = .D (3 * p + 7) (e + 5) 1 (l + 1) (s + 3)) (hy : y = .D (10 * p + 10) 7 (2 * e + 1) (l + 8) s)

/-- Every internal edge is machine reachability. -/
theorem IStep.sound {x y : St} (h : IStep x y) : ReachesPlus target x.cfg y.cfg := by
  cases h with
  | d1 p k m l s hk _ _ hx hy => subst hx hy; exact Dg1 p k m (term l s) hk
  | d2 q k m l s _ _ hx hy => subst hx hy; exact Dg2 q k m (term l s)
  | d12 p k l s hk _ hx hy => subst hx hy; exact Dg12 p k (term l s) hk
  | g1 p k l s _ hx hy => subst hx hy; exact Gg1 p k l (ListBlank.append (([1] : List (Fin 2)) ^ s) default)
  | g2 q k l s _ hx hy => subst hx hy; exact Gg2 q k (term l s)
  | join p e l s hx hy => subst hx hy; exact Dg11J p e l s default

/-- **Opposite stream:** an internal state has at most one internal predecessor. -/
theorem internal_step_injective {x y z : St} (hx : IStep x z) (hy : IStep y z) : x = y := by
  cases hx <;> cases hy <;> subst_vars <;> simp only [St.D.injEq, St.G.injEq, reduceCtorEq, true_and] at * <;> omega

/-- Lexicographic forward rank (s, l, R) with R(D) = 3k + 8m + 3, R(G) = 3k. -/
def St.rank : St → ℕ × ℕ × ℕ
  | .D _ k m l s => (s, l, 3 * k + 8 * m + 3)
  | .G _ k l s => (s, l, 3 * k)

/-- The lexicographic order on ℕ × ℕ × ℕ. -/
def lex3 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem lex3_wf : WellFounded lex3 :=
  WellFounded.prod_lex wellFounded_lt (WellFounded.prod_lex wellFounded_lt wellFounded_lt)

/-- **Forward rank:** (s, l, R) decreases lexicographically on every internal edge. -/
theorem internal_step_decreases_lex {x y : St} (h : IStep x y) : lex3 y.rank x.rank := by
  cases h with
  | d1 p k m l s _ _ _ hx hy => subst hx hy; exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
  | d2 q k m l s _ _ hx hy => subst hx hy; exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
  | d12 p k l s _ _ hx hy => subst hx hy; exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
  | g1 p k l s _ hx hy => subst hx hy; exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
  | g2 q k l s _ hx hy => subst hx hy; exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
  | join p e l s hx hy => subst hx hy; exact Prod.Lex.left _ _ (by omega)

/-- The leading counter and pair count (N, k). -/
def St.front : St → ℕ × ℕ
  | .D N k _ _ _ => (N, k)
  | .G N k _ _ => (N, k)

/-- **Backward rank:** (N, k) increases lexicographically on every internal edge, so every ancestry is finite. -/
theorem internal_predecessor_decreases_lex {x y : St} (h : IStep x y) :
    Prod.Lex (· < ·) (· < ·) x.front y.front := by
  cases h with
  | d1 p k m l s _ _ _ hx hy =>
    subst hx hy
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact Prod.Lex.right _ (by omega)
    · exact Prod.Lex.left _ _ (by omega)
  | d2 q k m l s _ _ hx hy => subst hx hy; exact Prod.Lex.left _ _ (by omega)
  | d12 p k l s _ _ hx hy =>
    subst hx hy
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact Prod.Lex.right _ (by omega)
    · exact Prod.Lex.left _ _ (by omega)
  | g1 p k l s _ hx hy => subst hx hy; exact Prod.Lex.left _ _ (by omega)
  | g2 q k l s _ hx hy => subst hx hy; exact Prod.Lex.left _ _ (by omega)
  | join p e l s hx hy => subst hx hy; exact Prod.Lex.left _ _ (by omega)

/-- **Push entries are roots:** the F1100 output D(2u+2, 7, 2d+1; 7, 3) has no internal predecessor. -/
theorem push_entry_is_root (u d : ℕ) (x : St) : ¬ IStep x (.D (2 * u + 2) 7 (2 * d + 1) 7 3) := by
  intro h
  cases h <;> simp only [St.D.injEq, reduceCtorEq] at * <;> omega

/-- The F1100 output is literally the configuration of that root state. -/
theorem push_entry_cfg (u d : ℕ) :
    (St.D (2 * u + 2) 7 (2 * d + 1) 7 3).cfg =
      Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * d + 1)) (ListBlank.append Tl default)))) := rfl

/-- **Finite internal paths:** from every state the machine reaches a state with no internal successor. -/
theorem internal_terminates (x : St) : ∃ y, ReachesStar target x.cfg y.cfg ∧ ∀ z, ¬ IStep y z := by
  induction x using (InvImage.wf St.rank lex3_wf).induction with
  | _ x ih =>
    by_cases h : ∃ z, IStep x z
    · obtain ⟨z, hz⟩ := h
      obtain ⟨y, hy, hy'⟩ := ih z (internal_step_decreases_lex hz)
      exact ⟨y, hz.sound.to_star.trans hy, hy'⟩
    · exact ⟨x, ReachesStar.refl _ _, fun z hz => h ⟨z, hz⟩⟩

end CryptidLink.L17

#print axioms CryptidLink.L17.IStep.sound
#print axioms CryptidLink.L17.internal_step_injective
#print axioms CryptidLink.L17.internal_step_decreases_lex
#print axioms CryptidLink.L17.internal_predecessor_decreases_lex
#print axioms CryptidLink.L17.push_entry_is_root
#print axioms CryptidLink.L17.internal_terminates
