import CryptidLink.L17e
/-!
# L17: short-buffer B kernels with exact defined-transition counts

The finite read windows are recorded in `analysis/l17-b-dispatch/kernels.json`.
Both outside contexts are arbitrary `ListBlank`s. The declarations prove exact
raw-machine execution, including its clock. They do not assert that their sources
are on the blank orbit, or that the whole mixed grammar returns to a section.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- The apparent mixed gap is exactly a separator between10 runs. -/
theorem short_gap_rotation (n : ℕ) (v : ListBlank (Fin 2)) :
    ListBlank.append (([0, 1] : List (Fin 2)) ^ n) (ListBlank.append [0, 0] v) =
      ListBlank.append [0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append [0] v)) := by
  exact (rotLB0 n (ListBlank.append [0] v)).symm

/-- Literal execution for exact-length goals. Each step is checked by reduction. -/
macro "l17_exact_steps" : tactic =>
  `(tactic| repeat (first
    | (try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk', List.cons_append, List.nil_append, List.append_nil, ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_default_default, ListBlank.cons_zero_default]
       exact ReachesIn.zero _ _)
    | (refine ReachesIn.step_left (by
         try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk', List.cons_append, List.nil_append, List.append_nil, ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_default_default, ListBlank.cons_zero_default]
         rfl) ?_
       try simp only [Tape.write, Tape.move, ListBlank.head_cons, ListBlank.tail_cons,
         ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
         ListBlank.cons_default_default, ListBlank.cons_zero_default])))

/-- Reads only cells -6 through 3, relative to the entry head. -/
theorem short_C2B_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 38
      (Cfg.headRight C (ListBlank.append [1, 0, 1, 0, 0, 1] L) (ListBlank.append [0, 1, 1, 1] R))
      (Cfg.headRight B (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) R) := by
  l17_exact_steps

/-- Reads only cells -14 through 3, relative to the entry head. -/
theorem short_C5B_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 62
      (Cfg.headRight C (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] L) (ListBlank.append [0, 1, 1, 1] R))
      (Cfg.headRight B (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) R) := by
  l17_exact_steps

/-- Reads only cells -20 through 3, relative to the entry head. -/
theorem short_B1100_n5_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 75
      (Cfg.headRight B (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (ListBlank.append [1, 1, 0, 0] R))
      (Cfg.headLeft C L (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1] R)) := by
  l17_exact_steps

/-- Reads only cells -26 through 3, relative to the entry head. -/
theorem short_B1100_n6_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 95
      (Cfg.headRight B (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (ListBlank.append [1, 1, 0, 0] R))
      (Cfg.headLeft C L (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1] R)) := by
  set_option maxRecDepth 4096 in
    l17_exact_steps

/-- Reads only cells -18 through 3, relative to the entry head. -/
theorem short_B1100_n7_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 65
      (Cfg.headRight B (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0] L) (ListBlank.append [1, 1, 0, 0] R))
      (Cfg.headLeft C L (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1] R)) := by
  l17_exact_steps

/-- Reads only cells -4 through 3, relative to the entry head. -/
theorem short_B1101_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 14
      (Cfg.headRight B (ListBlank.append [1, 0, 1, 0] L) (ListBlank.append [1, 1, 0, 1] R))
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 0] L) R) := by
  l17_exact_steps

end CryptidLink.L17

#print axioms CryptidLink.L17.short_C2B_exact
#print axioms CryptidLink.L17.short_C5B_exact
#print axioms CryptidLink.L17.short_B1100_n5_exact
#print axioms CryptidLink.L17.short_B1100_n6_exact
#print axioms CryptidLink.L17.short_B1100_n7_exact
#print axioms CryptidLink.L17.short_B1101_exact
#print axioms CryptidLink.L17.short_gap_rotation
