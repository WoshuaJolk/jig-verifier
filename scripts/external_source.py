#!/usr/bin/env python3
"""A Lean submission pinned to a commit of a public GitHub repository.

A proof package too large to commit through the API (thousands of modules) names
`{repo, commit, dir}` in its manifest instead of carrying a source. This module
fetches exactly that commit, admits the import closure of the root module under the
same static policy as a single-file submission, and stages it as a Lake library of
its own. Nothing from the package runs except Lean elaborating its `.lean` files:
its lakefile, scripts and caches are never read.

    external_source.py --drop-build                 # delete the staged modules' build output
    external_source.py --collect DIR MODULES.txt    # gather those modules' build output
"""

from __future__ import annotations

import hashlib
import os
import pathlib
import re
import shutil
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import lean_policy  # noqa: E402
from conject_common import REPO_ROOT, run  # noqa: E402

REPO_RE = re.compile(r"^https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
DIR_RE = re.compile(r"^[A-Za-z0-9_.-]+(/[A-Za-z0-9_.-]+)*$")
COMPONENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")

# Module roots a package may not define: they belong to the verifier or its dependencies.
RESERVED_ROOTS = (
    lean_policy.ALLOWED_IMPORT_ROOTS
    | frozenset(lean_policy.EXPLAINED_IMPORT_ROOTS)
    | {"Lake", "Main", "Cli", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Qq"}
)

MAX_MODULES = 20_000
MAX_BYTES = 400_000_000

BASE = REPO_ROOT / ".conject" / "external"
CHECKOUT = BASE / "checkout"
SRC = BASE / "src"
MODULES_FILE = BASE / "modules.txt"
LAKEFILE = REPO_ROOT / "lakefile.toml"
LIB_NAME = "ConjectExternal"


class Rejected(Exception):
    """The package cannot be verified. `reason` is a verdict reason."""

    def __init__(self, reason: str, detail: str):
        super().__init__(detail)
        self.reason = reason
        self.detail = detail


def _allow_local() -> bool:
    return os.environ.get("CONJECT_EXTERNAL_ALLOW_LOCAL") == "1"


def validate(spec: object) -> dict:
    if not isinstance(spec, dict):
        raise Rejected("bad_manifest", "`external` must be an object with repo and commit")
    repo = str(spec.get("repo") or "").rstrip("/")
    commit = str(spec.get("commit") or "").lower()
    sub = str(spec.get("dir") or "").strip("/")
    if repo.endswith(".git"):
        repo = repo[:-4]
    if not (REPO_RE.match(repo) or (_allow_local() and repo.startswith("file://"))):
        raise Rejected("bad_manifest", f"external.repo must be https://github.com/<owner>/<repo>, got {repo!r}")
    if not COMMIT_RE.match(commit):
        raise Rejected("bad_manifest", "external.commit must be a full 40-character commit sha")
    if sub and (not DIR_RE.match(sub) or ".." in sub.split("/")):
        raise Rejected("bad_manifest", f"external.dir must be a relative path inside the repo, got {sub!r}")
    return {"repo": repo, "commit": commit, "dir": sub}


def fetch(spec: dict, timeout: float) -> pathlib.Path:
    """Check out exactly `spec.commit` and return the source directory inside it."""
    shutil.rmtree(CHECKOUT, ignore_errors=True)
    CHECKOUT.mkdir(parents=True)
    url = spec["repo"] if spec["repo"].startswith("file://") else spec["repo"] + ".git"
    env = {**os.environ, "GIT_TERMINAL_PROMPT": "0"}
    for cmd in (
        ["git", "init", "-q"],
        ["git", "fetch", "-q", "--depth", "1", "--no-tags", url, spec["commit"]],
        ["git", "-c", "advice.detachedHead=false", "checkout", "-q", "FETCH_HEAD"],
    ):
        proc = run(cmd, cwd=CHECKOUT, timeout=timeout, env=env)
        if proc.returncode != 0:
            raise Rejected(
                "missing_source",
                f"could not fetch {spec['repo']} at {spec['commit']}: {(proc.stderr or proc.stdout).strip()[-400:]}",
            )
    head = run(["git", "rev-parse", "HEAD"], cwd=CHECKOUT, timeout=60).stdout.strip()
    if head != spec["commit"]:
        raise Rejected("missing_source", f"fetched {head}, not the pinned {spec['commit']}")
    src = (CHECKOUT / spec["dir"]) if spec["dir"] else CHECKOUT
    if not src.is_dir() or src.is_symlink():
        raise Rejected("missing_source", f"no directory {spec['dir']!r} at {spec['commit']}")
    return src


def _module_file(src: pathlib.Path, mod: str) -> pathlib.Path:
    return src / (mod.replace(".", "/") + ".lean")


def closure(src: pathlib.Path, root: str) -> dict[str, pathlib.Path]:
    """Every local module `root` reaches, admitted under the static policy.

    An import that resolves to a file in `src` is local; one whose root is an allowed
    dependency (Mathlib, ...) is external; anything else is refused.
    """
    found: dict[str, pathlib.Path] = {}
    todo = [root]
    total = 0
    real_src = src.resolve()
    while todo:
        mod = todo.pop()
        if mod in found:
            continue
        parts = mod.split(".")
        if not all(COMPONENT_RE.match(p) for p in parts):
            raise Rejected("bad_manifest", f"`{mod}` is not a Lean module name")
        if parts[0] in RESERVED_ROOTS:
            raise Rejected(
                "forbidden_syntax",
                f"`{mod}` would shadow a module the verifier owns or depends on; rename its root",
            )
        path = _module_file(src, mod)
        if not path.is_file():
            raise Rejected("missing_source", f"`{mod}` is imported but there is no {path.relative_to(src)}")
        if path.is_symlink() or not path.resolve().is_relative_to(real_src):
            raise Rejected("forbidden_syntax", f"{path.relative_to(src)} is a symlink")
        total += path.stat().st_size
        found[mod] = path
        if len(found) > MAX_MODULES:
            raise Rejected("bad_manifest", f"more than {MAX_MODULES} modules in the import closure")
        if total > MAX_BYTES:
            raise Rejected("bad_manifest", f"more than {MAX_BYTES} source bytes in the import closure")
        for dep in lean_policy.imports(path.read_text(errors="replace")):
            if dep.split(".")[0] in RESERVED_ROOTS and not _module_file(src, dep).is_file():
                continue
            todo.append(dep)
    return found


def admit(found: dict[str, pathlib.Path], src: pathlib.Path) -> list[str]:
    """Policy problems across the whole closure, each prefixed with its file."""
    local = frozenset(found)
    problems: list[str] = []
    for mod in sorted(found):
        for p in lean_policy.scan(found[mod].read_text(errors="replace"), local):
            problems.append(f"{found[mod].relative_to(src)}: {p}")
    return problems


def local_deps(found: dict[str, pathlib.Path]) -> dict[str, list[str]]:
    """Each module's imports that belong to the package itself."""
    return {
        m: [d for d in lean_policy.imports(p.read_text(errors="replace")) if d in found]
        for m, p in found.items()
    }


def layers(found: dict[str, pathlib.Path]) -> list[list[str]]:
    """The closure in dependency order: every module sits above all of its imports.

    A layer can be built entirely in parallel once the layers below it exist, which
    is what lets one package span several runners.
    """
    deps = local_deps(found)
    depth = {m: 0 for m in found}
    changed = True
    while changed:
        changed = False
        for m, ds in deps.items():
            want = max([depth[d] + 1 for d in ds] or [0])
            if want != depth[m]:
                depth[m], changed = want, True
    out: list[list[str]] = [[] for _ in range(max(depth.values(), default=-1) + 1)]
    for m, d in depth.items():
        out[d].append(m)
    return [sorted(layer) for layer in out]


def waves(
    found: dict[str, pathlib.Path], max_shards: int = 12, min_per_shard: int = 150
) -> list[list[list[str]]]:
    """Group the layers into waves of shards: waves run in order, shards in parallel.

    Consecutive layers merge into one wave while the merged batch still fits the
    shard budget, because a wave costs a runner handoff and most layers are thin.
    Within a wave the split is by source size, the only cost estimate available
    before anything is built: a wave is as slow as its slowest shard, so an even
    split is worth more than a tidy one.
    """
    plan: list[list[list[str]]] = []
    batch: list[str] = []
    budget = max_shards * min_per_shard
    for layer in layers(found):
        if batch and len(batch) + len(layer) > budget:
            plan.append(_split(batch, found, max_shards, min_per_shard))
            batch = []
        batch.extend(layer)
    if batch:
        plan.append(_split(batch, found, max_shards, min_per_shard))
    return plan


def _split(
    modules: list[str], found: dict[str, pathlib.Path], max_shards: int, min_per_shard: int
) -> list[list[str]]:
    """Longest-first bin packing by source size, into as few shards as the budget allows."""
    n = max(1, min(max_shards, -(-len(modules) // min_per_shard)))
    shards: list[list[str]] = [[] for _ in range(n)]
    load = [0] * n
    for m in sorted(modules, key=lambda m: -found[m].stat().st_size):
        i = load.index(min(load))
        shards[i].append(m)
        load[i] += found[m].stat().st_size
    return [sorted(sh) for sh in shards if sh]


def stage(found: dict[str, pathlib.Path], root: str) -> tuple[pathlib.Path, str]:
    """Copy the closure into its own source tree and add it to the lakefile.

    Returns the staged root file and one hash over every staged module.
    """
    shutil.rmtree(SRC, ignore_errors=True)
    digest = hashlib.sha256()
    for mod in sorted(found):
        dest = _module_file(SRC, mod)
        dest.parent.mkdir(parents=True, exist_ok=True)
        data = found[mod].read_bytes()
        dest.write_bytes(data)
        digest.update(f"{mod} {hashlib.sha256(data).hexdigest()}\n".encode())
    MODULES_FILE.write_text("\n".join(sorted(found)) + "\n")

    base = LAKEFILE.read_text().split(f'\n[[lean_lib]]\nname = "{LIB_NAME}"', 1)[0].rstrip("\n")
    roots = ", ".join(f'"{m}"' for m in sorted(found))
    LAKEFILE.write_text(
        f'{base}\n\n[[lean_lib]]\nname = "{LIB_NAME}"\nsrcDir = "{SRC.relative_to(REPO_ROOT)}"\nroots = [{roots}]\n'
    )
    return _module_file(SRC, root), "sha256:" + digest.hexdigest()


def unstage() -> None:
    text = LAKEFILE.read_text()
    marker = f'\n[[lean_lib]]\nname = "{LIB_NAME}"'
    if marker in text:
        LAKEFILE.write_text(text.split(marker, 1)[0].rstrip("\n") + "\n")


BUILD_SUFFIXES = (".olean", ".ilean", ".trace")


def collect_build_outputs(dest: pathlib.Path, modules: list[str]) -> int:
    """Copy one shard's build output to `dest`, for the next wave to unpack.

    Lake treats a module as built only when its .olean, .ilean AND .trace are all
    present, so all three travel; the .hash files are rebuilt on demand.
    """
    top = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
    copied = 0
    for mod in modules:
        for suffix in BUILD_SUFFIXES:
            f = top / (mod.replace(".", "/") + suffix)
            if not f.exists():
                continue
            out = dest / f.relative_to(top)
            out.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(f, out)
            copied += 1
    return copied


def drop_build_outputs() -> int:
    """Delete the staged modules' oleans so a shared build cache never saves them."""
    if not MODULES_FILE.exists():
        return 0
    stems = {m.replace(".", "/") for m in MODULES_FILE.read_text().split()}
    gone = 0
    for top in (REPO_ROOT / ".lake" / "build" / "lib" / "lean", REPO_ROOT / ".lake" / "build" / "ir"):
        if not top.is_dir():
            continue
        for path in top.rglob("*"):
            if not path.is_file():
                continue
            rel = path.relative_to(top)
            stem = str(rel.parent / rel.name.split(".", 1)[0])
            if stem.startswith("./"):
                stem = stem[2:]
            if stem in stems:
                path.unlink()
                gone += 1
        for d in sorted((p for p in top.rglob("*") if p.is_dir()), key=lambda p: -len(p.parts)):
            if not any(d.iterdir()):
                d.rmdir()
    return gone


if __name__ == "__main__":
    argv = sys.argv[1:]
    if argv[:1] == ["--drop-build"]:
        print(f"dropped {drop_build_outputs()} external build files")
        sys.exit(0)
    if argv[:1] == ["--collect"] and len(argv) == 3:
        mods = [m for m in pathlib.Path(argv[2]).read_text().split() if m]
        n = collect_build_outputs(pathlib.Path(argv[1]), mods)
        print(f"collected {n} build files for {len(mods)} modules")
        sys.exit(0)
    print(__doc__)
    sys.exit(2)
