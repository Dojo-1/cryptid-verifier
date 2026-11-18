import CryptidLink.L17ab
/-!
# L17: first exact mixed-width [6,7,2,2,3] return

A concrete but *contextual* 166-step result for the first mixed scanner
boundary in analysis/l17-a-stream/mixed-boundary.json.

The initial A stack is spatially (10)^6 0 (10)^7 0 (10)^3, with the
right tape 01·101·01·101·00·R. After exactly 30 A scanning steps
its run widths are [6,7,2,2,3]. The next 10 steps (A00L) leave C at
physical coordinate +2, with an unprocessed width-two pair.

This module proves the complete endpoint in two raw-machine stages:
  40 steps: A head at 0 -> C head at +2 (mixed C checkpoint),
 126 steps: C head at +2 -> C head at -34 (blank-left if L=default).
The *total* clock is 166 transitions.

Both outer contexts are arbitrary ListBlanks. The literal raw-machine
trace reads only within physical coordinates [-33,+11], where the
initial A head is position 0. Accordingly, neither exterior context
is inspected, and the right word after the 12-bit input is untouched.

The left tapes here are head-nearest-first, as in all L17 modules;
a headRight configuration's right list begins at its head coordinate.
No general arbitrary-width return, blank-orbit reachability, stack
boundedness or nonhalting is claimed.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- A source with physical stack [6,7,3] and scanner/terminal prefix
    01·101·01·101·00. The R suffix is arbitrary and unread. -/
def mixed166_source (L R : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
    (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] R)

/-- Framed exact C state at t=40, relative head coordinate +2.
    Both contexts are still unchanged; this is not blank-left. -/
def mixed166_checkpoint (L R : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
    (ListBlank.append [0, 1, 1, 1, 1, 1, 1, 1, 1, 1] R)

/-- End of the mixed return at t=166, head -34. The 46-bit right
    prefix is the exact physical output through coordinate +11. -/
def mixed166_end (L R : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C L
    (ListBlank.append [1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] R)

/-- Exact, context-preserving 40-step mixed scanning and A00L exit. -/
theorem mixed166_scan_C_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 40 (mixed166_source L R) (mixed166_checkpoint L R) := by
  unfold mixed166_source mixed166_checkpoint
  set_option maxRecDepth 8192 in
    l17_exact_steps

/-- Exact, context-preserving 126-step return through two width-2 runs.
    The C head moves from physical coordinate +2 to -34. -/
theorem mixed166_C_return_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 126 (mixed166_checkpoint L R) (mixed166_end L R) := by
  unfold mixed166_checkpoint mixed166_end
  set_option maxRecDepth 16384 in
    l17_exact_steps

/-- All exterior contexts: the mixed width-two stack returns to a C
    configuration in exactly 166 defined raw transitions, without
    reading either exterior tape. -/
theorem mixed166_contextual_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 166 (mixed166_source L R) (mixed166_end L R) := by
  set_option maxRecDepth 16384 in
    exact (mixed166_scan_C_exact L R).trans (mixed166_C_return_exact L R)

/-- With a blank exterior left context, the endpoint is genuinely
    blank-left C. The right exterior context remains arbitrary. -/
theorem mixed166_blankleft_exact (R : ListBlank (Fin 2)) :
    ReachesIn target 166
      (mixed166_source default R)
      (Cfg.headRight C default (ListBlank.append [1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] R)) := by
  set_option maxRecDepth 8192 in
    exact mixed166_contextual_exact default R

end CryptidLink.L17

#print axioms CryptidLink.L17.mixed166_scan_C_exact
#print axioms CryptidLink.L17.mixed166_C_return_exact
#print axioms CryptidLink.L17.mixed166_contextual_exact
#print axioms CryptidLink.L17.mixed166_blankleft_exact
