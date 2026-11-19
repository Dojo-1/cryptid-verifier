import CryptidLink.L17MixedBoundary

/-! Exact L17 scanner entry for arbitrary interleavings of 01 and 101.
The endpoint at the terminator is an intermediate C frame. Its
continuation need not preserve an arbitrary unread suffix. -/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

local notation "push" => @ListBlank.append (Fin 2) _
private abbrev Bits := ListBlank (Fin 2)
private abbrev frameA := ([0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

inductive ScannerToken where
  | a01 | a101

def ScannerToken.input : ScannerToken → List (Fin 2)
  | .a01 => [0, 1]
  | .a101 => [1, 0, 1]

def ScannerToken.deposit : ScannerToken → List (Fin 2)
  | .a01 => [1, 0]
  | .a101 => [0, 1, 0]

def ScannerToken.steps : ScannerToken → ℕ
  | .a01 => 2
  | .a101 => 13

def scannerInput : List ScannerToken → List (Fin 2)
  | [] => []
  | t :: ts => t.input ++ scannerInput ts

def scannerDeposit (L : Bits) : List ScannerToken → Bits
  | [] => L
  | t :: ts => scannerDeposit (push t.deposit L) ts

def scannerSteps : List ScannerToken → ℕ
  | [] => 0
  | t :: ts => t.steps + scannerSteps ts

private theorem scan_token_frame (t : ScannerToken) (L R : Bits) :
    ReachesIn target t.steps
      (Cfg.headRight A (push frameA L) (push t.input R))
      (Cfg.headRight A (push frameA (push t.deposit L)) R) := by
  cases t
  · have h := a01_exact (push frameA L) R
    simp only [ScannerToken.steps, ScannerToken.input, ScannerToken.deposit, ListBlank.append_append] at h ⊢
    exact h
  · exact a101_exact (push [0, 1, 0] L) R

/-- Scan any finite token list while keeping the A frame and both exterior tapes. -/
theorem scan_interleaved_exact (ts : List ScannerToken) (L R : Bits) :
    ReachesIn target (scannerSteps ts)
      (Cfg.headRight A (push frameA L) (push (scannerInput ts) R))
      (Cfg.headRight A (push frameA (scannerDeposit L ts)) R) := by
  induction ts generalizing L with
  | nil => exact ReachesIn.zero _ _
  | cons t ts ih =>
    have h := (scan_token_frame t L (push (scannerInput ts) R)).trans (ih (push t.deposit L))
    simpa only [scannerSteps, scannerInput, scannerDeposit, ListBlank.append_append] using h

theorem scan_interleaved_00_exact (ts : List ScannerToken) (L R : Bits) :
    ReachesIn target (scannerSteps ts + 10)
      (Cfg.headRight A (push frameA L) (push (scannerInput ts) (push [0, 0] R)))
      (Cfg.headLeft C (scannerDeposit L ts) (push [1, 1, 1, 1, 1, 1, 1, 1, 1] R)) :=
  (scan_interleaved_exact ts L (push [0, 0] R)).trans (a00l_exact _ R)

theorem scan_interleaved_100_exact (ts : List ScannerToken) (L R : Bits) :
    ReachesIn target (scannerSteps ts + 19)
      (Cfg.headRight A (push frameA L) (push (scannerInput ts) (push [1, 0, 0] R)))
      (Cfg.headLeft C (push [0, 1, 0] (scannerDeposit L ts)) (push [1, 1, 1, 1, 1, 1, 1] R)) :=
  (scan_interleaved_exact ts L (push [1, 0, 0] R)).trans (a100_exact _ R)

/-- B entry with arbitrary scanner tokens and the 00 terminator. -/
theorem b_mixed_scan_00_exact (ts : List ScannerToken) (L R : Bits) :
    ReachesIn target (14 + (scannerSteps ts + 10))
      (Cfg.headRight B (push [1, 0, 1, 0] L)
        (push [1, 1, 0, 1] (push (scannerInput ts) (push [0, 0] R))))
      (Cfg.headLeft C (scannerDeposit (push [0] L) ts) (push [1, 1, 1, 1, 1, 1, 1, 1, 1] R)) :=
  (short_B1101_exact L (push (scannerInput ts) (push [0, 0] R))).trans (scan_interleaved_00_exact ts (push [0] L) R)

/-- B entry with arbitrary scanner tokens and the 100 terminator. -/
theorem b_mixed_scan_100_exact (ts : List ScannerToken) (L R : Bits) :
    ReachesIn target (14 + (scannerSteps ts + 19))
      (Cfg.headRight B (push [1, 0, 1, 0] L)
        (push [1, 1, 0, 1] (push (scannerInput ts) (push [1, 0, 0] R))))
      (Cfg.headLeft C (push [0, 1, 0] (scannerDeposit (push [0] L) ts))
        (push [1, 1, 1, 1, 1, 1, 1] R)) :=
  (short_B1101_exact L (push (scannerInput ts) (push [1, 0, 0] R))).trans (scan_interleaved_100_exact ts (push [0] L) R)

private abbrev mixedWord := ([1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] : List (Fin 2))
private abbrev mixedWrite := ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2))

private def mixedStart (L R : Bits) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (push [1, 0, 1, 0, 1] L) (push mixedWord R)

set_option maxRecDepth 8192 in
/-- The mixed word reaches A at the start of an arbitrary right suffix. -/
theorem mixed_suffix_boundary (L R : Bits) :
    ReachesIn target 136 (mixedStart L R)
      (Cfg.headRight A (push mixedWrite L) R) := by
  unfold mixedStart
  l17_exact_steps

/-- The following machine step branches to B when the suffix starts with zero. -/
theorem mixed_suffix_next_zero (L R : Bits) :
    ReachesIn target 137 (mixedStart L (push [0] R))
      (Cfg.headRight B (push [1] (push mixedWrite L)) R) := by
  have h : ReachesIn target 1
      (Cfg.headRight A (push mixedWrite L) (push [0] R))
      (Cfg.headRight B (push [1] (push mixedWrite L)) R) := by
    l17_exact_steps
  exact (mixed_suffix_boundary L (push [0] R)).trans h

/-- The same step branches to E when the suffix starts with one. -/
theorem mixed_suffix_next_one (L R : Bits) :
    ReachesIn target 137 (mixedStart L (push [1] R))
      (Cfg.headRight E (push [0] (push mixedWrite L)) R) := by
  have h : ReachesIn target 1
      (Cfg.headRight A (push mixedWrite L) (push [1] R))
      (Cfg.headRight E (push [0] (push mixedWrite L)) R) := by
    l17_exact_steps
  exact (mixed_suffix_boundary L (push [1] R)).trans h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
/-- Exact timed C return for the displayed fixed tape window. -/
theorem mixed_00_return (L R : Bits) :
    ReachesIn target 110
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  l17_exact_steps

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
/-- Exact timed C return for the displayed fixed tape window. -/
theorem mixed_100_00_return (L R : Bits) :
    ReachesIn target 348
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  l17_exact_steps

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
/-- Exact timed C return for the displayed fixed tape window. -/
theorem mixed_100_11_return (L R : Bits) :
    ReachesIn target 272
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  l17_exact_steps

end CryptidLink.L17

#print axioms CryptidLink.L17.scan_interleaved_exact
#print axioms CryptidLink.L17.scan_interleaved_00_exact
#print axioms CryptidLink.L17.scan_interleaved_100_exact
#print axioms CryptidLink.L17.b_mixed_scan_00_exact
#print axioms CryptidLink.L17.b_mixed_scan_100_exact
#print axioms CryptidLink.L17.mixed_suffix_boundary
#print axioms CryptidLink.L17.mixed_suffix_next_zero
#print axioms CryptidLink.L17.mixed_suffix_next_one
#print axioms CryptidLink.L17.mixed_00_return
#print axioms CryptidLink.L17.mixed_100_00_return
#print axioms CryptidLink.L17.mixed_100_11_return
