# L17 short-buffer B dispatch

The saved mixed-return boundary now has an exact108-step return. Eleven
guarded B rows and sixteen C2/C5 compositions dispatch the next tape bits.
Three new paths handle short1100 buffers. Literal gap rotation closes
the 1101+00 subfamily, including the former 52-step checkpoint in 166 steps.
Six finite kernels have formal exact clocks in `link/CryptidLink/L17l.lean`,
which also proves the gap identity. General five-run return stays open.

Read `DERIVATION.md` for the complete words and conditions,
`CLAUDE-BRIEF.md` for proof compositions, and `VALIDATION.md` for the actual
build/check status. No halt/nonhalt or blank-orbit extension is claimed.

From the repository root:

```sh
python3 analysis/l17-b-dispatch/verify_package.py
python3 -m unittest discover -s analysis/l17-b-dispatch -p 'test_*.py' -v
python3 analysis/l17-b-dispatch/verify.py
python3 analysis/l17-b-dispatch/mutations.py
```

Optional fresh literal campaign and compiler controls (C++17 required):

```sh
python3 analysis/l17-b-dispatch/campaign.py
python3 analysis/l17-b-dispatch/controls.py
python3 analysis/l17-b-dispatch/frontier.py
```

Regeneration writes inside this directory and can change report metadata.
Verify integrity first. Binaries are excluded. No script edits its frozen
dependencies or makes network calls. The local budget ledger includes a
conservative charge for the rejected initial trace request.
