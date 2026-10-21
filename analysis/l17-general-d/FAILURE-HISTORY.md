# Corrections retained during this contribution

No endpoint, raw transition count or read-window claim failed the new literal
campaign. The following tooling/documentation corrections occurred before
packaging:

1. The initial protocol copied the old guard report's *input* hash instead of
   its own hash. `protocol-v0.json` is retained. `protocol.json` corrects the
   documentary field. Recovery always read and recorded the actual input hash;
   the computation did not trust the incorrect field.
2. A first attempt to use SymPy for coefficient arithmetic found it unavailable.
   No dependency was installed. `make_spec.py` instead sums exact affine and
   quadratic coefficients using integer arithmetic. The derivation gives the
   full q itinerary and polynomial.
3. The first coarse continuation stopped at2999999, since the next complete
   scalar round would cross3M. One existing E primitive completes the exact3M
   endpoint. The generator now handles partial final rounds. The previous
   report hash and the added edge are retained in the final report. This is not
   an extra search budget or a new rule.
4. The first declarative composition checker had import/dispatch plumbing
   errors: missing legacy path constants, inspecting q for a JOIN case before
   dispatch, and failing to extract the initial pair counter for RET39.
   `composition-attempt-1.log` through `composition-attempt-3.log` are retained;
   attempt4 passed. Helpers were renamed with gd_ prefixes to avoid shadowing
   the preceding folders' modules. The final checker imports no actor/Word.
5. An import-purity test initially mixed multiple flat command-line module
   trees in one interpreter and imported an older validate.py. The failing
   test log and the prior path helper are retained. The current test imports
   each command in a fresh interpreter, and gd_ helpers no longer collide.

The final15 tests, literal response verification, composition checks and
actor-free million-rewrite replay pass. No correction was counted as a second
independent physical measurement. Mutation checks reuse retained raw responses.
One exploratory batch of4 short-join kernel paths (574 transitions) and7 low
N=4 probes (3255 transitions) informed scope only; no short-guard theorem or
continuation is promoted from those probes. The kernel paths are retained;
the seven low probes were not retained individually and are not evidence for
any result in the brief. Their aggregate work is included in the budget total.
