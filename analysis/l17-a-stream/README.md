# L17 A-stream continuation

Start with `CLAUDE-BRIEF.md`. `DERIVATION.md` gives the complete word identities,
kernel compositions, times, head positions and read-window arguments.

The new result closes an unbounded subfamily of the old1101 exit: every
consecutive `(101)^j` prefix, followed by00,100 or11, returns to a blank-left
C-section under the stated p/c guards. Two periodic kernels handle pairs of
left gaps. Their outputs are compressed using X=111010 and one repetition
counter. Mixed01/101 scanning is exact, but its general return remains open.

Quick checks from the archive root:

```sh
python3 analysis/l17-a-stream/verify_package.py
python3 -m unittest discover -s analysis/l17-a-stream -p test_a_stream.py -v
python3 analysis/l17-a-stream/verify.py
python3 analysis/l17-a-stream/mutations.py
```

To replay the C++ campaign and build controls:

```sh
python3 analysis/l17-a-stream/campaign.py
python3 analysis/l17-a-stream/controls.py
```

Regeneration writes reports/builds only inside this new directory and may
change cache metadata; verify integrity before regenerating. No script makes
network calls, edits Lean, or writes to the frozen dependencies. A C++17
compiler is needed only for the last two commands. Compiled binaries are not
distributed. The critics and unit tests work without a compiler.

The previous handoff was recovered byte-identically from
`cryptid-l17-halting.zip`, SHA256
`1e6b40a347de6acc0e07c3ed123e4dd88bd9aebcb4fbbec54c3e9c27928d79e7`.
This ZIP contains the additive directory, four unchanged code dependencies and
three prior explanatory documents needed for a standalone replay. It does
not duplicate the unrelated large backward diagram. When merging, add the
new directory and preserve existing dependency files if their versions differ.

Current measured checks:992 endpoints in two literal paths;905 full trace
comparisons;168 arbitrary-context kernel instances;29 translated inputs in
three compiler modes;15 unit tests;20 detected mutations. Same-author paths
and compiler variants are controls, not independent authorship. The main
992 count already includes the168 kernel instances.

`mixed-boundary.json` identifies the next missing width2 return rather than
silently extending the homogeneous formulas. None of the new generic states
is asserted blank-reachable. This is not a halt/nonhalt result or new Lean build.
