# L17: the homogeneous table now has its two complete11 returns

Base: main1297fcd (PR #28), which stops at the complete K22/J1K outputs.
This contribution adds `L17ab.lean` and finishes both outer layers.

For p=u+6,c=v+7 and arbitrary right context R, the source is
`(10)^p0(10)^c0(10)^3 A>(101)^j11R`, with a blank exterior left tape.
Both endpoints below are genuinely blank-left C configurations.

| Theorem | Clock in u,v,h | Complete target |
|---|---:|---|
|a11_even_blankleft_exact|40h+2u+2v+86|1^(2u+2)(01)^7 1^(2v+5)(01)^(3h+7)0R|
|a11_odd_blankleft_exact|40h+2u+4v+92|1^(2u+6)(01)^(v+3h+16)0R|

The j values are2h and2h+1 respectively. The theorem
`a11_homogeneous_blankleft_exact` combines them for every j using
`a11_return_clock` and `a11_return_result`. All parameters are quantified;
no concrete h limit occurs in these Lean statements.

## Composition

Even:

1. `a101_11_even_k22_exact`:40h+37, with the entire K22 word retained.
2. `c01_middle_headRight_exact (v+3)`:2(v+4), consuming the separator.
3. Factor the resulting2v+8 ones as111 followed by2v+5 ones.
4. `k41_c01_last_exact u`:41+2u, retaining the outer head's explicit1.
5. Normalize the entire word; `d11_even_tail` is exactly(10)^(3h+2).

Odd:

1. `a101_11_odd_j1k_exact`:40h+38, in D mode.
2. `d10_sweep_exact (v+7)`:4(v+7), retaining the complete right pairs.
3. `k22_c01_last_exact (u+2)`:22+2(u+2). The outer sweep uses n,
   whereas a middle sweep with a separator uses n+1.
4. Normalize the right tape and transport the explicit head1 to C>.

No new fixed kernel was needed. The D ordering remains
`A11;D10²;D6^h;D10`; it is not a commutation with the old D10³ ordering.
The regression checks its h=1 hostile witness in head-nearest-first order.

## Coverage and remaining work

The five00/100 return families already exist in L17t/u/v/x. This closes
the two remaining cases of the archived seven-row homogeneous table.
The historical handoff files remain archived with their original status;
the current formal status is indexed in the root README.

The next mathematical obligation is the mixed scanner, especially the
five-run source[p,c,1,n−2,3] left by the B1101 normalization. Its small
middle widths do not satisfy the p≥6,c≥7 guard merely because the two
outer runs do. Do not apply this new three-run theorem by dropping those
middle widths. A blank-orbit bridge and a stack bound are still separate.

Checks:1072 literal endpoints,1015 full traces,144 arbitrary-context helper
instances included above,12 planted faults,16 translated controls in each
of three compiler modes. The code paths share authorship. `VALIDATION.md`
records the complete build/trust status and exact execution metadata.
