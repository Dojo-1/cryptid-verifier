# Reflection, waggling, elongation, angled clocks and irregular motion

The experiments preserve the original machine. Display coordinates are kept
separate from logical cells; inserting blank physical cells into a raw tape
without changing the transition protocol would instead define another process.

## A reversible display frame

Let positive integer gaps be g0,...,g(p-1), with total B. For x=ap+r,
0<=r<p, define E(x)=aB+sum(gj,j<r). This is strictly increasing on the
integer logical cells, including negative x via floor division. A display
frame is

    F_t(x)=o(t)+sigma*E(x), sigma in{-1,+1}.

Its metadata includes the gaps, sign and offset rule. Inversion subtracts the
offset, applies the sign, divides by B, then checks a prefix-sum residue.
Points between those residues are display filler, not logical zero cells.
The eight frames cover identity, reflection, periodic waggling, uniform and
unequal spacing, digit-dependent irregular offsets, and combined opposite motion.

The complete state is(t,q,F_t(h),{F_t(x): tape[x]=1}). A transformed move:

1. Reads and writes at F_t(h).
2. Moves to logical neighbor h+d using F_(t+1)(h+d).
3. Remaps every nonzero displayed cell when the frame changes.
4. Leaves t unchanged if the raw transition is undefined.

Decoding gives exactly the raw state. The algebra establishes conjugacy of the
extended, clock-tagged system. Tests check its implementation. Metadata, frame
phase and remapping cost are not free computational information.

The measured103368 decoded snapshots are eight views of12921 logical defined
steps across32 inputs. They are not103368 independent or longer raw runs.
The same12921-step aggregate is compared with the literal C++ simulator,
including every read triple and complete endpoint. The scripts share authorship.
Random tapes, negative coordinates, immediate halts and mixed state labels are
included. The new experiment does not extend the blank orbit beyond the prior
3M checkpoint.

## Angled streams and their causal guard

For the logical head worldline, a tilted clock tau=M*t+P*h has increment
M+P*d per raw move, d in{-1,+1}. It is strictly increasing for every possible
move exactly when M>|P|. At equality one direction has zero increment; below
that threshold one direction reverses the ordering. A temporal cut that fails
this condition needs a different section/causal interpretation.

Elongation changes display-head speed. Waggling can add jumps. Thus the same
constant tilt must not be applied naively to display head y=F_t(h). One measured
waggling example has delta(3t+2y)=-15, despite increasing logical time.

For any of these frames, choose a base clock C with

    C(t+1)-C(t)=1+|P|*(max(gaps)+|o(t+1)-o(t)|).

Then C(t)+P*F_t(h) increases by at least1 along every defined move, because
|delta F|<=max(gaps)+|delta o|. This permits nonuniform observation time while
retaining exact order. It changes the units, not the underlying orbit or
available mathematical information. The irregular interval test retains full
interval coverage; endpoint-only observations are not claimed to prove the
absence of an intervening halt.

## What was useful

Literal tape deformations survived the exact-coordinate checks. Their benefit
is a faithful way to choose observations. No numerical simplification or new
halting invariant was demonstrated by these views themselves.

The productive change was in counter coordinates: the opposite stream becomes
single-valued inside the guarded D/G interface, and the forward rank becomes
lexicographic in terminal count, terminal width and local mass. A single affine
score is obstructed by the D1/D2/G1 inequalities. That statement has a precise
scope and does not rule out nonlinear coordinates or a later moving section.

The guarded subsystem is still smaller than the full machine. Raw-machine
reversibility is false, witnessed explicitly by two different states:
A at-1 with ones at+1, and C at+1 with ones at-1,+1. Both take one step to
B at0 with ones at-1,+1. Restricted inverse uniqueness is therefore the result
of the macro domain and retained counters, not a property gained by reflection.
