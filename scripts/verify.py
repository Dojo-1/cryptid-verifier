"""Build and audit the pinned Lean projects from any working directory.

Only local build products are cleaned; downloaded dependency caches are retained.
No shell, Unix symlinks, NumPy or C++ compiler is needed for this command.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
PROJECTS = {"core": Path("."), "mathlib": Path("mathlib"), "link": Path("link")}


def run(command: list[str], cwd: Path, log: Path | None = None) -> None:
    print(f"[{cwd.name}] {' '.join(command)}", flush=True)
    if log is None:
        subprocess.run(command, cwd=cwd, check=True)
        return
    # Capture stderr too, retain the log on failure, and propagate the child's exit code.
    with log.open("w", encoding="utf-8", newline="\n") as output:
        with subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True,
                              encoding="utf-8", errors="replace") as process:
            assert process.stdout is not None
            for line in process.stdout:
                output.write(line)
                print(line, end="", flush=True)
            status = process.wait()
        if status:
            raise subprocess.CalledProcessError(status, command)


def copy_upstream_data(project: Path) -> None:
    """Mirror upstream's small elaboration inputs without Windows symlink privileges."""
    upstream = project / ".lake/packages/Cryptids"
    for name in ("baselines", "artifacts"):
        source, destination = upstream / name, project / name
        if not source.is_dir():
            raise RuntimeError(f"missing upstream data directory: {source}")
        if destination.is_symlink():
            if destination.resolve() != source.resolve():
                raise RuntimeError(f"unexpected symlink: {destination}")
            destination.unlink()  # Migrate the old documented manual symlink to a copy.
        if destination.exists():
            if not destination.is_dir():
                raise RuntimeError(f"expected a data directory: {destination}")
            existing = {p.relative_to(destination) for p in destination.rglob("*") if p.is_file()}
            expected = {p.relative_to(source) for p in source.rglob("*") if p.is_file()}
            if existing - expected or any(p.is_symlink() for p in destination.rglob("*")):
                raise RuntimeError(f"unexpected files in {destination}; move it aside and retry")
        shutil.copytree(source, destination, dirs_exist_ok=True)


def clean_local_build(project: Path) -> None:
    build = project / ".lake/build"
    if build.is_symlink():
        raise RuntimeError(f"unexpected build-directory symlink: {build}")
    if build.exists():
        shutil.rmtree(build)


def verify(root: Path, projects: tuple[str, ...], lake: str = "lake") -> None:
    for name in projects:
        project = root / PROJECTS[name]
        print(f"\nVerifying {name}: {(project / 'lean-toolchain').read_text().strip()}", flush=True)
        if name == "link":
            run([sys.executable, str(root / "analysis/leads/l17_gen_orbit.py")], root)
        if name != "core":
            run([lake, "exe", "cache", "get"], project)
        if name == "link":
            copy_upstream_data(project)
        # Always compile our sources, including the path dependency, so every
        # inventoried #print result comes from this build rather than an old log.
        clean_local_build(root)
        if project != root:
            clean_local_build(project)
        log = project / "build.log"
        run([lake, "build"], project, log)
        run([sys.executable, str(root / "scripts/audit_trust.py"),
             "--project", name, str(log)], root)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", choices=("all", *PROJECTS), default="all")
    args = parser.parse_args()
    lake = shutil.which("lake")
    if lake is None:
        parser.exit(1, "lake is not on PATH; install elan as described in README.md\n")
    projects = tuple(PROJECTS) if args.project == "all" else (args.project,)
    try:
        verify(ROOT, projects, lake)
    except subprocess.CalledProcessError as error:
        print(f"verification stopped: command exited {error.returncode}", file=sys.stderr)
        return max(1, error.returncode)
    except (OSError, RuntimeError) as error:
        print(f"verification stopped: {error}", file=sys.stderr)
        return 1
    print("\nAll selected builds and trust audits passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
