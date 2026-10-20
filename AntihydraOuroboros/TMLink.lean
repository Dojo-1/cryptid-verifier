import AntihydraOuroboros.Basic
import AntihydraOuroboros.A4
import AntihydraOuroboros.A9
/-
  Mechanical link between the raw Turing machines and the transcribed macro rules.

  Each machine is given by its standard bbchallenge string and parsed in Lean. It is run from the
  blank tape; every configuration that has exactly the shape of the paper's macro configuration is
  decoded. The kernel checks (by `decide`) that the decoded sequence equals the sequence produced by
  our macro step function (`step`, `step4`, `step9`) for the first several macro steps.

  This is a bounded check: it does not prove the macro rules for all parameters (the authors' Lean
  proofs do that); it shows that our transcription agrees with the actual machines where checked.
-/

namespace TMLink

/-- Tape zipper: `left` lists cells nearest-first; `head` is the scanned cell. -/
structure Cfg where
  st : Nat
  left : List Nat
  head : Nat
  right : List Nat

/-- One transition: (symbol written, moves right?, next state). `none` = undefined (halt). -/
def parseTrans : List Char → Option (Nat × Bool × Nat)
  | [w, d, s] => if w = '-' then none else some (if w = '1' then 1 else 0, d = 'R', s.toNat - 65)
  | _ => none

def splitU : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '_' then [] :: splitU cs
    else match splitU cs with
      | [] => [[c]]
      | x :: xs => (c :: x) :: xs

/-- Transition table [A0, A1, B0, B1, …] from the standard string. -/
def tableOf (s : String) : List (Option (Nat × Bool × Nat)) :=
  (splitU s.toList).flatMap fun st => [parseTrans (st.take 3), parseTrans (st.drop 3)]

def tmStep (tbl : List (Option (Nat × Bool × Nat))) (c : Cfg) : Option Cfg :=
  match tbl.getD (2 * c.st + c.head) none with
  | none => none
  | some (w, r, n) =>
    if r then some ⟨n, w :: c.left, c.right.headD 0, c.right.tail⟩
    else some ⟨n, c.left.tail, c.left.headD 0, w :: c.right⟩

def blank : Cfg := ⟨0, [], 0, []⟩

/-- Decoded macro configurations seen in the first `n` raw steps (tail-recursive, reversed). -/
def traceAux {α : Type} (tbl : List (Option (Nat × Bool × Nat))) (dec : Cfg → Option α) :
    Nat → Cfg → List α → List α
  | 0, _, acc => acc
  | n + 1, c, acc =>
    let acc' := match dec c with
      | some x => x :: acc
      | none => acc
    match tmStep tbl c with
    | none => acc'
    | some c' => traceAux tbl dec n c' acc'

def trace {α : Type} (tbl : List (Option (Nat × Bool × Nat))) (dec : Cfg → Option α)
    (n : Nat) (c : Cfg) : List α :=
  (traceAux tbl dec n c []).reverse

/-- Leading ones: count and remainder. -/
def ones : List Nat → Nat × List Nat
  | 1 :: l => let p := ones l; (p.1 + 1, p.2)
  | l => (0, l)

def allZero (l : List Nat) : Bool := l.all (· == 0)

def trimZeros (l : List Nat) : List Nat := (l.reverse.dropWhile (· == 0)).reverse

def pairs10 : List Nat → Option Nat
  | [] => some 0
  | 1 :: 0 :: l => (pairs10 l).map (· + 1)
  | _ => none

def macroList {α : Type} (f : α → Option α) : Nat → α → List α
  | 0, _ => []
  | n + 1, s => s :: (match f s with | none => [] | some t => macroList f n t)

/-! #### Antihydra: A(a,b) = 0^∞ 1^a 0 1^b E> 0^∞ -/

def antihydraTM : String := "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

def decAntihydra (c : Cfg) : Option (Nat × Nat) :=
  if c.st = 4 ∧ c.head = 0 ∧ allZero c.right then
    let (b, r) := ones c.left
    match r with
    | [] => some (0, b)
    | 0 :: r2 => let (a, r3) := ones r2; if allZero r3 then some (a, b) else none
    | _ => none
  else none

/-- First 8 macro configurations of Antihydra (raw steps 11 … 10933) agree with `step`. -/
theorem antihydra_link :
    trace (tableOf antihydraTM) decAntihydra 11000 blank = macroList step 8 (0, 4) := by
  decide +kernel

/-! #### A.4: C(a,b) = 0^∞ E> (10)^a 1^b 0^∞ -/

def a4TM : String := "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA"

def decA4 (c : Cfg) : Option (Nat × Nat) :=
  if c.st = 4 ∧ allZero c.left then
    let (b, pre) := ones (trimZeros (c.head :: c.right)).reverse
    if b = 0 then none else (pairs10 pre.reverse).map (fun a => (a, b))
  else none

/-- On the tape, C(a,1) → C(2, 2a+2) passes through the macro configuration C(0, 2a+4)
    (which then expands to C(2, 2a+2) by the expansion rule); list it explicitly. -/
def expandA4 (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.flatMap fun s => if s.2 = 1 then [s, (0, 2 * s.1 + 4)] else [s]

theorem step4_through_zero (a : Nat) : step4 (0, 2 * a + 4) = some (2, 2 * a + 2) := by
  simp [step4]

/-- First 25 macro configurations of A.4 (raw steps 7 … 8936) agree with `step4`. -/
theorem a4_link :
    trace (tableOf a4TM) decA4 9000 blank = (expandA4 (macroList step4 20 (0, 3))).take 25 := by
  decide +kernel

/-! #### A.9: C(a,b,c) = 0^∞ 1^(a+2) E> 1^(2b+2) 0 1^(2c+2) 0^∞ -/

def a9TM : String := "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD"

def decA9 (c : Cfg) : Option (Nat × Nat × Nat) :=
  if c.st = 4 then
    let (n, r) := ones c.left
    if 2 ≤ n ∧ allZero r then
      let (p, r1) := ones (c.head :: c.right)
      match r1 with
      | 0 :: r2 =>
        let (q, r3) := ones r2
        if allZero r3 ∧ 2 ≤ p ∧ p % 2 = 0 ∧ 2 ≤ q ∧ q % 2 = 0 then
          some (n - 2, p / 2 - 1, q / 2 - 1)
        else none
      | _ => none
    else none
  else none

/-- First 40 macro configurations of A.9 (raw steps 100 … 9738) agree with `step9`. -/
theorem a9_link :
    trace (tableOf a9TM) decA9 9800 blank = macroList step9 40 (5, 2, 0) := by
  decide +kernel

end TMLink

#print axioms TMLink.antihydra_link
#print axioms TMLink.a4_link
#print axioms TMLink.a9_link
