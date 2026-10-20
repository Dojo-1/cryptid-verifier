"""Trust audit: no sorry/admit/native_decide/axiom in sources (comments stripped),
and every `#print axioms` line in the build log uses only the standard axioms."""
import re, sys, pathlib

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", re.M)

def strip_comments(src: str) -> str:
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return "".join(out)

bad = []
src_dirs = sys.argv[2:] or ["AntihydraOuroboros"]
files = [f for d in src_dirs for f in sorted(pathlib.Path(".").glob(f"{d}/**/*.lean"))]
for f in files:
    for m in FORBIDDEN.finditer(strip_comments(f.read_text())):
        bad.append(f"{f}: forbidden `{m.group(0).strip()}`")

log = pathlib.Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else ""
lines = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
if not lines:
    bad.append("build log has no `#print axioms` output (empty or missing log)")
for name, axs in lines:
    extra = {a.strip() for a in axs.split(",") if a.strip()} - ALLOWED
    if extra:
        bad.append(f"{name}: non-standard axioms {sorted(extra)}")

if bad:
    print("\n".join(bad)); sys.exit(1)
print(f"trust audit OK: {len(lines)} audited theorems, standard axioms only")
