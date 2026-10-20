# Exact equality of enormous periodic words

The critic compares words without expanding huge counters and without a
probabilistic hash. It is a separate implementation from the actor's `Word`.
Every chunk must have a nonempty pattern and a positive repetition count.
**Zero-count chunks must be removed before suffix trimming.** Missing this
condition caused the critic bug found in this campaign: `("10",0)` was
incorrectly changed into a single `1`. The regression is retained.

After discarding only exterior trailing zeros, compare total lengths. Walk
two chunk cursors. Over an overlap, let the rotated patterns have periods
`p,q`; inspect `min(overlap,p+q-gcd(p,q))` bits. A mismatch rejects equality.
If the inspected prefix matches, the entire overlap matches by the following
period lemma. Advance the cursor by the whole overlap and continue. The
algorithm terminates after at most the sum of the numbers of chunks.

## Period lemma and its justification

Two infinite periodic sequences of positive periods `p,q` that agree for
`p+q-d` initial symbols, where `d=gcd(p,q)`, agree everywhere. Here is a short
argument for the version used by the comparator.

Assume `p<=q`. Their common prefix has length `N=p+q-d`, at least `q` and
`p`. Its `p`-periodic pattern has equal values at residue positions
`i` and `i+q (mod p)` for every `0<=i<p-d`, because positions `i` and `i+q`
both lie in that common prefix. The permutation `i -> i+q (mod p)` has `d`
cycles, one per residue class modulo `d`. Omitting the `d` edges whose sources
are `p-d,...,p-1` removes exactly one edge per cycle; every resulting component
remains connected. Thus the `p`-pattern is constant on each residue class
modulo `d`. The common prefix includes all `q` symbols of the other pattern,
so that pattern has the same values by residue modulo `d`. Both infinite
extensions therefore agree. If `p=q`, the cycles have size one and the same
argument includes the trivial case.

For a shorter overlap, every position is inspected. Cursor offsets rotate
patterns and preserve their periods, so the lemma applies at every overlap.
The argument concerns the comparison algorithm; it does not prove any L17
transition or infinite-orbit property.

This is the classical Fine–Wilf bound. Bibliographic reference: N. J. Fine and
H. S. Wilf, *Uniqueness theorems for periodic functions*, Proceedings of the
AMS 16 (1965), 109–114,
[DOI](https://doi.org/10.1090/S0002-9939-1965-0174934-9).
The original PDF was not retrievable in this environment; no claim of reading
its proof is made. The self-contained argument above states the exact bridge
used here. The bound is also restated in the abstract of the research paper
[*The Parameterized Periodicity Lemma*](https://arxiv.org/abs/2608.21912).

The implementation is checked against explicit strings over all binary
patterns of lengths 1–3 and counts 0–3, plus cursor/slicing cases and the
1,024 actor representation cases. These bounded implementation tests do not
replace formal verification of the comparator.
