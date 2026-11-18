# L17MixedBoundary: the named mixed boundary, now machine-checked

Base: main3983080 (PR #30), whose four concrete166-step theorems are retained.
This generalizes that witness to all guarded counters and adds the original-C
entry. Parameters avoid subtraction: p=u+4,c=v+1,
a=u+5. All thirteen declarations are exact `ReachesIn target` paths.
Outside contexts are arbitrary `ListBlank (Fin 2)` where shown.

| Theorem | Exact clock | Composition / endpoint |
|---|---:|---|
|a01_sweep_exact n|2n|Induction on n using a01_exact; both contexts retained.|
|b111_exact|8|Literal B1,A1,E1,F0,D0,A1,E1,F0 on[-1,2].|
|b_to_d_sweep_exact n|4n+8|b111; D10^n, with n+1 entering01 pairs. Final D zero retained.|
|c2_s2_to_d_exact|62|short_C2B38; b_to_d_sweep_exact4 (24). Ends in D.|
|d_pair1_sweep_exact v n|4v+14|J1K10; D10^(v+1). Right n+1 pairs stay explicit.|
|mixed_scanner_0101_exact|40|01;101;01;101;A00L, checked literally with both exterior contexts. Two width-two runs remain.|
|mixed_c2_s2_blankleft_exact|2u+4v+98|C2S2-to-D62; D-pair(v,5); K22+C01^u. Complete output1^(2u+2)(01)^(v+12)0R.|
|mixed_a_blankleft_exact|2u+4v+138|Scanner40; previous row with three additional suffix ones. Join0111=(01)11.|
|entryC_exact a|2|The original blank-left C entry; exact version of entryC.|
|k11_exact|11|Exact-clock version of K11, with arbitrary L/R.|
|a01101_split_exact n|15|A0;short_B1101_14; retain both zero separators.|
|entry1101_exact u v|2u+2v+40|entryC2;A01^(u+6);K11_11;A01^v;A01101_15.|
|mixed_original_C_exact|4u+6v+178|Original entry; mixed A return. Complete output1^(2u+2)(01)^(v+13)11R.|

The original a≥5,c≥1 rule is exactly4a+6c+152 transitions. It includes
a=7,c=7 in222 steps, and the lower guard corner a=5,c=1 in178 steps.
Literal frames/read intervals are implemented in `check_mixed.py`, while
Lean statements formalize exact endpoints/clocks with arbitrary context.

This proves the C2,s2 row, one of the archived13 four-run rows, plus the
named scanner composition. It does not cover the remaining12 rows or the
five-run source[p,c,1,n−2,3]. No larger blank-tape reachability claim is made.
