# E71 — final literal E60 normalization

Two proposed public `ReachesIn` results use the original
`widthFourCutSource` and guarded suffix words
`G1(M)=1(10)^7 1101 (10)^M 111`,
`G3(M)=111(10)^7 1101 (10)^M 111`, for M=m+1 >= 1.

The exact clocks are
`214+6M+2u+4v` and `268+6M+2u+2v`.
The full right-tape outputs proposed for Lean certification are
`1^(2u+6) (01)^(v+8) 010100 (10)^(16+M) R`
and
`1^(2u+1) (10)^7 1^(2v+4) (01)^(21+M) 0 R`.
The proofs only rewrite tape words in already-certified E70 paths;
no additional machine transition is assumed.

E71 remains **H** until the pinned Lean link build and standard-axiom
audit pass. The 360-case E69 raw-machine phase replay is a separate
finite observation. The E60 M=0 counterexample stays outside scope.

Importantly, even a P result here would be **exact reachability**,
not *first-return minimality*, exhaustive scanner grammar, verified
blank-orbit reachability, or global L17 nonhalting.
