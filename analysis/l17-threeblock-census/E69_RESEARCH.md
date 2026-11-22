# E69 — explicit composition, not a nonhalting result

E69 reuses the exact Lean components in E65 (C-to-A prelude and scanner),
E66 (all-natural 4n A sweep), E67 (77/95-step arbitrary-exterior bridges),
and E68 (public exact final-unwind wrappers). The active candidate source
file is `link/CryptidLink/L17WindowComplete.lean`.

The two E69 candidate statements assert `ReachesIn` for an
E65-shaped contextual C configuration, to an exact blank-left C
configuration, with clocks
`214+6*(m+1)+2*u+4*v` and `268+6*(m+1)+2*u+2*v`.
Their logical status remains **H** until pinned Lean CI succeeds and
the new theorem names pass the standard-axiom audit. The positive E60
width is `M=m+1`; there is no E60 M=0 theorem here.

An independently transcribed six-state transition-table harness
`test_e69.py` checks **360** complete raw-machine compositions.
Each case checks the entry, A seam, post-sweep state, post-bridge state,
and C exit, including the entire sparse tape, head coordinate,
control state, clock formula and exact literal E60 output word.
Cases include randomized exterior suffixes, translations, and
`m` up to 400. This is **finite M evidence only**, not a universal
machine proof or independent external review.

Two further proof obligations are deliberately separate:
(1) equate the E65-shaped contextual C source with
`widthFourCutSource u v (G1(M) R)` or the G3 version;
(2) normalize the compositional endpoint into the literal E60
`F1/F3` complete-tape expression. The independent word algebra
sanity check passed 45 finite parameter frames.

No statement of *earliest* return, complete B-scanner language
classification, blank-orbit reachability, or L17 nonhalting is made.
