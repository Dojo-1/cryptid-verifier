# Generated L17 orbit dependencies

`L17Orbit0.lean` through `L17Orbit4.lean` are generated here and ignored by Git.
The tracked interface is [`../L17Orbit5.lean`](../L17Orbit5.lean), which fixes the
endpoint theorem and its final step. All theorem names remain unchanged.

From the repository root, `python scripts/verify.py --project link` regenerates
the five dependencies, checks their hashes against
[`../../generated-orbit.json`](../../generated-orbit.json), builds them with Lean,
and audits the endpoint's axiom output. CI uploads the generated sources, manifest
and build log as its `l17-orbit` artifact, including when the build fails.

To inspect generation without installing Lean:

```sh
python analysis/leads/l17_gen_orbit.py
python analysis/leads/l17_gen_orbit.py --check
```

Generation uses the tracked arithmetic stepper and fixed step budget, not an
untracked trace or a network service. The hashes detect generation drift; Lean's
kernel checks every generated arithmetic side condition. Review changes to the
generator, manifest, macro lemmas and endpoint together.
