# Historical exploratory scripts

These eleven programs were moved unchanged from `scripts/`. They are research
scratch work, have no dedicated regression tests and are not part of the supported
verification command or CI evidence suite. Their printed conclusions are historical
outputs, not an extension of the current theorem or evidence boundary. Some runs
are expensive and some paths assume the original author's environment.

| Programs | Experiment | Current interpretation |
|---|---|---|
| `a4.py`, `check2.py` | A.4 contraction/cascade scans, residue searches and A.9 section checks | Finite exploratory transcriptions. Use the Lean A.4/A.9 criteria and current literal-machine checks for supported claims. |
| `zk.py` | Magnetic-Laplacian kernels on sampled counter quotients | Sampled quotient evidence only; no universal obstruction to halting follows from a sampled kernel. |
| `mobius.py`, `sing.py` | Twisted binary-window spectra and ground states | Finite floating-point graph calculations; not a proof about the selected Cryptid orbit. |
| `dyadic.py`, `padic.py` | Finite character scans, time gauges and past-parity checks | Numerical motivation for specific arithmetic statements. The exact supported statements are those formalized in Lean. |
| `infinitesimal.py` | Small-flux spectra and tilted transfer matrices | Auxiliary finite models; their spectral formulas do not establish independence or asymptotic laws on the blank orbit. |
| `ouro.py` | Finite parity bijections and random-walk survival counts | Residue/Haar-model calculations. The model's survival probability does not settle survival of the designated orbit. |
| `stream.py` | Blank Antihydra trajectory, moving coordinates and Haar-model risk | A finite orbit sample. The printed model risk is not a certified halting probability for this deterministic start. |
| `stretch.py` | Odd-run records and a logarithmic raw-step cost estimate | Finite measurements and approximate cost summaries, not a proof of a logarithm law or non-halting. |

Dependencies: the spectral programs and `ouro.py` need NumPy; `sing.py` also needs
SciPy. The other programs use the Python standard library. If studying `check2.py`,
run from this directory: it loads `a4.py` by a relative path and executes its initial
rule definitions. `stream.py` writes to `/tmp/zk/antihydra_stream.csv` and assumes
that directory already exists. No compatibility or platform support is promised
for these archived scripts.

Retired interpretations include treating CRT residue coding as statistical
independence on a chosen orbit, identifying a square-root logarithmic envelope
with the iterated-logarithm law, and promoting random-walk analogies to proofs for
the blank-tape start. See the corrected
[conjecture note](../conjecture-logarithm-law.md) and
[finite-evidence audit](../independent-audit.md). This archive preserves provenance;
it does not reinstate those interpretations.
