# E68 — public exact final-unwind interfaces

The E60 all-M checkpoint proof (issue #60) needs to invoke two existing
precise `ReachesIn` theorems from *outside* `L17FiveRun.lean`.

Previously these results were private to that module. E68 publishes
exactly equivalent wrapper statements:

- `e68_a_unwind_exact u p R`: from the guarded A frame,
  **4p + 29 + 2u** steps to blank-left C, preserving the entire
  right exterior and its prefixed pair structure.
- `e68_c_finish_exact u p R`: from the guarded C frame,
  **2(p+1) + 41 + 2u** steps to blank-left C,
  with the complete `five_run_bottom_result` output.

The wrappers have proofs **only by applying the previously kernel-checked
private theorems**; no new machine paths, axioms or trust assumptions
are introduced. Both names have new explicit `#print axioms` entries,
and are added to the public trust inventory.

For E60, instantiate A with `p=v+5` and C with `p=v+2`.
Then the final clocks are respectively `49+2u+4v` and
`47+2u+2v`.

This PR deliberately does **not** include the E60 all-M composition:
it first removes a module-visibility obstruction. After pinned Lean CI
passes, combine it with E65 (#59), E66 (#61), E67 (#62) on a fresh branch
and prove full-tape equations. Keep first-return minimality, blank-orbit
reachability and universal L17 nonhalting as distinct unproved targets.
