"""Build and audit the standalone manuscript formalization."""

import argparse
import hashlib
import os
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "formalization"
AUDIT = ROOT / "checks" / "BirchAudit.lean"
IMPORT = re.compile(r"^(?:(?:public|meta) )*import ([^\n]+)", re.MULTILINE)


def check_source_closure():
    modules = {"Birch": PROJECT / "Birch.lean"}
    for directory in (PROJECT / "Birch", PROJECT / "Vendor" / "Wooley" / "GafniTao"):
        for path in directory.rglob("*.lean"):
            parts = path.relative_to(directory.parent).with_suffix("").parts
            modules[".".join(parts)] = path

    pending = ["Birch"]
    visited = set()
    source_count = len(modules) + 1
    for path in (*modules.values(), AUDIT):
        if re.search(r"^\s*axiom\b|\bby\s+(?:sorry|admit)\b|^\s*(?:sorry|admit)\b",
                     path.read_text(encoding="utf-8"), re.MULTILINE):
            raise SystemExit(f"Unexpected axiom or proof placeholder in {path.relative_to(ROOT)}")

    while pending:
        name = pending.pop()
        if name in visited:
            continue
        path = modules.get(name)
        if path is None:
            raise SystemExit(f"Missing local import: {name}")
        visited.add(name)
        for line in IMPORT.findall(path.read_text(encoding="utf-8")):
            pending.extend(dep for dep in line.split()
                           if dep == "Birch" or dep.startswith(("Birch.", "GafniTao.")))

    extra = modules.keys() - visited
    if extra:
        raise SystemExit(f"Lean modules outside the release import closure: {', '.join(sorted(extra))}")
    print(f"Checked {source_count} Lean source files, including the audit.", flush=True)


def check_frozen_snapshot():
    manifest = ROOT / "checks" / "SHA256SUMS"
    expected = {}
    for entry in manifest.read_text(encoding="utf-8").splitlines():
        digest, relative = entry.split("  ", 1)
        expected[relative] = digest

    actual = {}
    for folder, dirs, files in os.walk(ROOT):
        dirs[:] = [name for name in dirs if name not in {".git", ".lake", "__pycache__"}]
        for name in files:
            path = Path(folder) / name
            if path != manifest and name != ".DS_Store":
                actual[path.relative_to(ROOT).as_posix()] = path
    if actual.keys() != expected.keys():
        extra = sorted(actual.keys() - expected.keys())
        missing = sorted(expected.keys() - actual.keys())
        raise SystemExit(f"Release files differ. Extra: {extra}. Missing: {missing}.")

    for relative, path in actual.items():
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected[relative]:
            raise SystemExit(f"Release hash differs: {relative}")
    print("Checked the frozen release hashes.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frozen", action="store_true", help="verify the release SHA-256 manifest")
    args = parser.parse_args()
    check_source_closure()
    if args.frozen:
        check_frozen_snapshot()
    subprocess.run(["lake", "build", "Birch", "GafniTao"], cwd=PROJECT, check=True)
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(AUDIT)],
                   cwd=PROJECT, check=True)


if __name__ == "__main__":
    main()
