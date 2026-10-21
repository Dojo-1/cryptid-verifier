import CryptidLink.L17h
/-!
# L17: the m = 1 join (GPT, `analysis/l17-general-d/DERIVATION.md`, "JOIN from already known fixed paths")

    JOIN: 𝒞(u+7; (10)^(e+5) 11 (01)^(j+1) 11 v) ⊢⁺ 𝒞(0; 1^(2u+2) (01)^7 1^(2e+1) (01)^(j+7) 0 v)

(GPT's a = u+7, c = e+5, l = j+1.) It composes only kernels and sweeps that are already proved:
entry, A sweep, K11, A sweep; then the local section K7, A sweep, A1/E1/F0 (`segAEF`), D sweep and K22;
then C sweep, K43 and a final C sweep. `Dg11J` instantiates it after entry/countdown:

    D(3p+7, e+5, 1; (01)^(j+1) 1^(s+3) W) ⊢⁺ D(10p+10, 7, 2e+1; (01)^(j+8) 1^s W).
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- **JOIN** (GPT): the m = 1 join, from existing kernels only. -/
theorem JOIN (u e j : ℕ) (v : ListBlank (Fin 2)) :
    ReachesPlus target
      (Ccal (u + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (e + 5))
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v)))))
      (Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * e + 1))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 7)) (ListBlank.append [0] v)))))) := by
  -- outer entry, A sweep and K11
  have hX : ListBlank.append (([1, 0] : List (Fin 2)) ^ (e + 5))
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v))) =
      ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ (e + 4))
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v)))) :=
    ListBlank.append_pow_succ _ _ _
  have h1 := entryC (u + 6) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (e + 5))
    (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v))))
  have h2 := sweepA (u + 8) default (ListBlank.append (([1, 0] : List (Fin 2)) ^ (e + 5))
    (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v))))
  have hs : ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 8)) default =
      ListBlank.append [0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default) := by
    rw [show u + 8 = 2 + (u + 6) by omega, ListBlank.append_pow_add]; rfl
  rw [hs, hX] at h2
  rw [hX] at h1
  have h3 := K11 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (e + 4))
      (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v))))
  rw [rotLB0] at h3
  have hr3 : ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 4)) (ListBlank.append [0]
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v)))) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 5))
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v))) :=
    ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) (e + 4)
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v)))
  rw [hr3] at h3
  have h4 := sweepA (e + 5) (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))
    (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v)))
  -- the local section: K7, A sweep, A1 E1 F0, D sweep, K22
  have hl4 : ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 5))
        (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)) =
      ListBlank.append [0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 4)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
          (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)))) := by
    calc ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 5))
          (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))
        = ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 5)) (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
            (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))) := by
          congr 1
      _ = ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 5 + 2))
            (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)) :=
          (ListBlank.append_pow_add _ _ _ _).symm
      _ = ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 + (4 + (e + 1))))
            (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)) := by
          rw [show e + 5 + 2 = 2 + (4 + (e + 1)) by omega]
      _ = _ := by
          rw [ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 (4 + (e + 1)),
            ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 4 (e + 1)]
          all_goals rfl
  have hr4 : ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 1] v)) =
      ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ j) (ListBlank.append [1, 1] v)) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j]
    all_goals rfl
  rw [hl4, hr4] at h4
  have h5 := K7 (ListBlank.append (([0, 1] : List (Fin 2)) ^ 4)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ j) (ListBlank.append [1, 1] v))
  have hr5 : ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ j) (ListBlank.append [1, 1] v)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 3)) (ListBlank.append [1, 1] v) := by
    calc ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ j) (ListBlank.append [1, 1] v))
        = ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ j) (ListBlank.append [1, 1] v)) := rfl
      _ = ListBlank.append (([0, 1] : List (Fin 2)) ^ (3 + j)) (ListBlank.append [1, 1] v) :=
          (ListBlank.append_pow_add _ _ _ _).symm
      _ = _ := by rw [Nat.add_comm 3 j]
  rw [hr5] at h5
  -- name the remaining left context
  have hl8 : ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 4)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
          (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)))) =
      ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
          (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))) := rfl
  rw [hl8] at h5
  have h6 := sweepA (j + 3) (ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))))
    (ListBlank.append [1, 1] v)
  have h7 := segAEF (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 3))
      (ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
          (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))))) v
  have h8 := sweepD (j + 3) (ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))))
    (ListBlank.append [1, 0] v)
  have hr8 : ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 3)) (ListBlank.append [1, 0] v) =
      ListBlank.append [1, 0, 1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v)) := by
    rw [show j + 3 = 2 + (j + 1) by omega, ListBlank.append_pow_add]; rfl
  rw [hr8] at h8
  have h9 := K22 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
      (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)))
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v))
  -- back in the outer section: C sweep, K43, final C sweep
  have hl9 : ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 1))
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (e + 1))
        (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)) := by
    rw [rotLB (e + 1), show u + 6 = 6 + u by omega, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 6 u]
    all_goals rfl
  rw [hl9] at h9
  have h10 := sweepC (e + 1)
    (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default))
    (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v)))
  rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) e] at h10
  have h11 := K43 (ListBlank.append (([0, 1] : List (Fin 2)) ^ u) default)
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ e) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v))))
  rw [rotLB u default] at h11
  have h12 := sweepC u (ListBlank.append [1] default)
    (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ e) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v)))))
  rw [hconv] at h12
  -- final tape equality
  have eR : ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v)) =
      ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 7)) (ListBlank.append [0] v)) := by
    rw [rotLB (j + 7)]
    calc ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v))
        = ListBlank.append (([1, 0] : List (Fin 2)) ^ 6)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v)) := rfl
      _ = ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 + (j + 1))) (ListBlank.append [1, 0] v) :=
          (ListBlank.append_pow_add _ _ _ _).symm
      _ = _ := by
          rw [show 6 + (j + 1) = j + 7 by omega]
          all_goals rfl
  have e : ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ e) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 1)) (ListBlank.append [1, 0] v)))))) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) (ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * e + 1))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 7)) (ListBlank.append [0] v))))) := by
    rw [eR, one_pow_two_mul u, one_pow_two_mul e, show 2 * u + 2 = (1 + 2 * u) + 1 by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) (1 + 2 * u) 1,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * u),
      ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * e) 1]
    all_goals rfl
  rw [e] at h12
  exact (((((((((((h1.trans_star h2).trans h3).trans_star h4).trans h5).trans_star h6).trans h7).trans_star h8).trans h9).trans_star h10).trans h11).trans_star h12)

/-- D11 with the join: D(3p+7, e+5, 1; (01)^(j+1) 1^(s+3) W) ⊢⁺ D(10p+10, 7, 2e+1; (01)^(j+8) 1^s W). -/
theorem Dg11J (p e j s : ℕ) (W : ListBlank (Fin 2)) :
    ReachesPlus target
      (Dg (3 * p + 7) (e + 5) 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ (s + 3)) W)))
      (Dg (10 * p + 10) 7 (2 * e + 1) (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 8))
        (ListBlank.append (([1] : List (Fin 2)) ^ s) W))) := by
  have h1 := stepEC (3 * p + 7) (p + 2) 1 (1 + 5 * (p + 2))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 5)) (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append (([1] : List (Fin 2)) ^ (s + 3)) W))))
    (by omega) (by omega) rfl
  have es : cfgCt (1 + 5 * (p + 2)) 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (e + 5))
        (ListBlank.append (([1] : List (Fin 2)) ^ 1)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1)) (ListBlank.append (([1] : List (Fin 2)) ^ (s + 3)) W)))) =
      Ccal (5 * p + 4 + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (e + 5))
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 1))
          (ListBlank.append [1, 1] (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ s) W)))))) := by
    unfold cfgCt Ccal
    rw [show 1 + 5 * (p + 2) = 5 * p + 4 + 7 by omega, list_pow_one, rotLB (e + 5),
      show s + 3 = 3 + s by omega, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 s]
    all_goals rfl
  rw [es] at h1
  have h2 := JOIN (5 * p + 4) e j (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ s) W))
  have et : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (5 * p + 4) + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * e + 1))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 7))
              (ListBlank.append [0] (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ s) W))))))) =
      Dg (10 * p + 10) 7 (2 * e + 1) (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 8))
        (ListBlank.append (([1] : List (Fin 2)) ^ s) W)) := by
    unfold Dg
    rw [show 2 * (5 * p + 4) + 2 = 10 * p + 10 by omega, show j + 8 = j + 7 + 1 from rfl,
      ← ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) (j + 7)]
    all_goals rfl
  rw [et] at h2
  exact h1.trans h2

end CryptidLink.L17

#print axioms CryptidLink.L17.JOIN
#print axioms CryptidLink.L17.Dg11J
