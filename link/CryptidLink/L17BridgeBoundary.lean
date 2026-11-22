import CryptidLink.L17BridgeDeepWitness

/-!
# E79 — the actual E60 three-headed bridge exit remains nonblank-left

E78 establishes a genuine counterexample for arbitrary blank left
exterior at bridge t=95. This module proves that the *structured*
E60 left exterior cannot be blank at that same endpoint, by exhibiting
a 1 in its second left cell, for all u,v and arbitrary right tape.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))

private abbrev e79_left (u v : ℕ) : Bits :=
  push (P ^ (v + 2))
    (push [0] (push (P ^ (u + 6)) default))

/-- The structured G3 exterior starts with 01 in head-nearest order.
It is nonblank even though its first bit is zero. -/
theorem e79_structured_left_second_one (u v : ℕ) :
    (e79_left u v).tail.head = (1 : Fin 2) := by
  let X : Bits := push [0] (push (P ^ (u + 6)) default)
  have hsplit : push (P ^ (v + 2)) X =
      push P (push (P ^ (v + 1)) X) := by
    rw [show v + 2 = 1 + (v + 1) by omega,
        ListBlank.append_pow_add P 1 (v + 1) X]
    rfl
  change (push (P ^ (v + 2)) X).tail.head = 1
  rw [hsplit]
  simp only [ListBlank.append, ListBlank.tail_cons,
    ListBlank.head_cons]

private theorem e79_deep_witness {c : Cfg (Fin 2) (Fin 6)}
    (hs : c.tape.left.tail.head = (1 : Fin 2)) :
    ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  have heq := congrArg
    (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.tape.left.tail.head) hz
  have hzero : (Cfg.headRight C (default : Bits) Z).tape.left.tail.head =
      (0 : Fin 2) := by rfl
  have absurdEq : (1 : Fin 2) = 0 := hs.symm.trans (heq.trans hzero)
  exact (by decide : (1 : Fin 2) ≠ 0) absurdEq

/-- For every u,v,R, the actual E60 G3 structured left exterior
guarantees that the t=95 A-to-C bridge endpoint is NOT blank-left C.
Contrast with E78's verified-or-proposed blank-exterior counterexample. -/
theorem e79_three_bridge_C95_nonblank_in_E60_context
    (u v : ℕ) (R : Bits) :
    ∀ c : Cfg (Fin 2) (Fin 6),
      ReachesIn target 95
        (Cfg.headRight A
          (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] (e79_left u v))
          (push [1, 1] R)) c →
      ¬ E76BlankLeftC c := by
  intro c hc
  have hbridge := e67_three_contextual_bridge_exact (e79_left u v) R
  have h : c = Cfg.headRight C (e79_left u v)
      (push [1, 1] (push (P ^ 21) (push [0] R))) :=
    Option.some.inj (hc.symm.trans hbridge)
  subst c
  apply e79_deep_witness
  change (e79_left u v).tail.head = 1
  exact e79_structured_left_second_one u v

end CryptidLink.L17

#print axioms CryptidLink.L17.e79_structured_left_second_one
#print axioms CryptidLink.L17.e79_three_bridge_C95_nonblank_in_E60_context
