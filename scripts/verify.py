"""Build and audit the standalone manuscript formalization."""

import argparse
import hashlib
import os
import re
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "formalization"
AUDIT = ROOT / "checks" / "BirchAudit.lean"
MANIFEST = ROOT / "checks" / "SHA256SUMS"
SNAPSHOT_IGNORED = {".git", ".lake", "__pycache__", ".DS_Store"}
LIBRARIES = (
    PROJECT / "Birch",
    PROJECT / "Vendor" / "Wooley" / "GafniTao",
    PROJECT / "Vendor" / "AxiomMath" / "StacksFrontier",
    PROJECT / "Vendor" / "IndependentWeil" / "WeilConjectures",
    PROJECT / "Vendor" / "IndependentWeil" / "Comparator" / "Weil",
)
SPACE = re.compile(r"[\s\ufeff]*")
HEADER = re.compile(r"\b(?:module|prelude)\b|(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([\w]+(?:\.[\w]+)*)")
COMMENT = re.compile(r"/-|-/")
CODE_MARKER = re.compile(
    r'/\-|--|"(?:\\.|[^"\\])*"|«[^»]*»|(?<![\w\x27])(?:axiom|sorry|admit|sorryAx)(?![\w\x27])',
    re.DOTALL,
)


def comment_end(source, position):
    if source.startswith("--", position):
        end = source.find("\n", position + 2)
        return len(source) if end < 0 else end + 1
    depth = 1
    for match in COMMENT.finditer(source, position + 2):
        depth += 1 if match[0] == "/-" else -1
        if depth == 0:
            return match.end()
    raise ValueError("Unterminated Lean block comment")


def lean_imports(source):
    position = 0
    while True:
        position = SPACE.match(source, position).end()
        if source.startswith(("--", "/-"), position):
            position = comment_end(source, position)
        elif declaration := HEADER.match(source, position):
            position = declaration.end()
            if declaration[1]:
                yield declaration[1]
        else:
            return


def proof_placeholder(source):
    position = 0
    while match := CODE_MARKER.search(source, position):
        token = match[0]
        if token in ("--", "/-"):
            position = comment_end(source, match.start())
        elif token.startswith(('"', '«')):
            position = match.end()
        else:
            return token
    return None


def is_local_import(name):
    return any(name == root.name or name.startswith(root.name + ".") for root in LIBRARIES)


def check_source_closure():
    modules = {"Birch": PROJECT / "Birch.lean"}
    for directory in LIBRARIES:
        for path in directory.rglob("*.lean"):
            name = ".".join(path.relative_to(directory.parent).with_suffix("").parts)
            if name in modules:
                raise SystemExit(f"Duplicate local module: {name}")
            modules[name] = path

    pending = ["Birch"]
    visited = set()
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        path = modules.get(name)
        if path is None:
            raise SystemExit(f"Missing local import: {name}")
        source = path.read_text(encoding="utf-8")
        if marker := proof_placeholder(source):
            raise SystemExit(f"Unexpected {marker} in {path.relative_to(ROOT)}")
        visited.add(name)
        pending.extend(dep for dep in lean_imports(source) if is_local_import(dep))

    extra = modules.keys() - visited
    if extra:
        raise SystemExit(f"Lean modules outside the release import closure: {', '.join(sorted(extra))}")
    if marker := proof_placeholder(AUDIT.read_text(encoding="utf-8")):
        raise SystemExit(f"Unexpected {marker} in {AUDIT.relative_to(ROOT)}")
    print(f"Checked {len(visited) + 1} Lean source files, including the audit.", flush=True)


def snapshot_files():
    def walk_error(error):
        raise SystemExit(f"Cannot inventory release files: {error}")

    actual = {}
    for folder, dirs, files in os.walk(ROOT, onerror=walk_error):
        dirs[:] = [name for name in dirs if name not in SNAPSHOT_IGNORED]
        for name in dirs:
            path = Path(folder) / name
            if path.is_symlink():
                raise SystemExit(f"Release directory is a symbolic link: {path.relative_to(ROOT)}")
        for name in files:
            if name in SNAPSHOT_IGNORED:
                continue
            path = Path(folder) / name
            relative = path.relative_to(ROOT).as_posix()
            if path.is_symlink() or not path.is_file():
                raise SystemExit(f"Release file must be a regular file: {relative}")
            if relative.splitlines() != [relative]:
                raise SystemExit(f"Release path contains a line break: {relative!r}")
            if path != MANIFEST:
                actual[relative] = path
    return actual


def write_frozen_snapshot():
    lines = []
    for relative, path in sorted(snapshot_files().items()):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f"{digest}  {relative}\n")
    with tempfile.TemporaryDirectory(dir=MANIFEST.parent) as directory:
        temporary = Path(directory) / MANIFEST.name
        temporary.write_text("".join(lines), encoding="utf-8", newline="\n")
        temporary.replace(MANIFEST)
    print("Wrote the frozen release hashes.", flush=True)


def check_frozen_snapshot():
    actual = snapshot_files()
    expected = {}
    for number, entry in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), 1):
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", entry)
        if match is None or match[2] in expected:
            raise SystemExit(f"Invalid release hash manifest entry at line {number}.")
        expected[match[2]] = match[1]
    if actual.keys() != expected.keys():
        extra = sorted(actual.keys() - expected.keys())
        missing = sorted(expected.keys() - actual.keys())
        raise SystemExit(f"Release files differ. Extra: {extra}. Missing: {missing}.")

    for relative, path in actual.items():
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected[relative]:
            raise SystemExit(f"Release hash differs: {relative}")
    print("Checked the frozen release hashes.", flush=True)


def fetch_weil_cache():
    """Seed Lake's artifact cache with the pinned upstream Linux build."""
    upstream = "formal-arithmetic-geometry/weil-conjectures"
    revision = "ae6479530ccaaa19b6d7ca02bc3248cbf49611c9"
    endpoint = "https://cache.fuxi.merten.dev/lake-cache"
    scope = f"{upstream}/pt/x86_64-unknown-linux-gnu/tc/leanprover--lean4---4.35.0"
    expected_hash = "835f82e155a852b262b1b9d8f4f01cc31f1d8be2f4cf1117f02c69e6ed921ddd"
    env = dict(os.environ, LAKE_CACHE_DIR=str(PROJECT / ".lake" / "weil-cache"),
               LAKE_ARTIFACT_CACHE="true", LAKE_RESTORE_ARTIFACTS="true")
    with tempfile.TemporaryDirectory() as temp:
        config = Path(temp) / "lake-config.toml"
        config.write_text(
            '[[cache.service]]\nname = "weil"\nkind = "s3"\n'
            f'artifactEndpoint = "{endpoint}/a"\nrevisionEndpoint = "{endpoint}/r"\n',
            encoding="utf-8",
        )
        index = Path(temp) / "outputs.jsonl"
        subprocess.run(["curl", "--fail", "--silent", "--show-error", "--location",
                        "--retry", "3", "--output", str(index),
                        f"{endpoint}/r/{scope}/{revision}.jsonl"], check=True)
        if hashlib.sha256(index.read_bytes()).hexdigest() != expected_hash:
            raise SystemExit("The upstream Weil cache index differs from the pinned SHA-256.")
        subprocess.run(["lake", "cache", "get", str(index), "--service=weil",
                        f"--repo={upstream}", "--package=weil-conjectures"],
                       cwd=PROJECT, env=dict(env, LAKE_CONFIG=str(config)), check=True)
    return env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--weil-cache", action="store_true",
                        help="reuse matching artifacts from the upstream Weil Linux build")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--frozen", action="store_true", help="check the manifest and run the Lean audit")
    modes.add_argument("--write-manifest", action="store_true", help="write the SHA-256 release manifest")
    modes.add_argument("--check-manifest", action="store_true", help="check release hashes without a Lean build")
    args = parser.parse_args()
    if args.write_manifest:
        write_frozen_snapshot()
        return
    if args.check_manifest:
        check_frozen_snapshot()
        return
    check_source_closure()
    if args.frozen:
        check_frozen_snapshot()
    env = fetch_weil_cache() if args.weil_cache else None
    subprocess.run(["lake", "build", "Birch", "GafniTao"], cwd=PROJECT, env=env, check=True)
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(AUDIT)],
                   cwd=PROJECT, env=env, check=True)


if __name__ == "__main__":
    main()
