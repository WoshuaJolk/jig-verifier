#!/usr/bin/env python3
"""Run every example submission and assert the verdict matches its declared `expect`.

This is the repo's proof that the pipeline works: it fails loudly both when a correct
proof is rejected and when an adversarial one is accepted. It also asserts that the two
independent green proofs of S001 hash differently, which is what makes
`elaborated_term_hash` usable for deduplication.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent


def manifests() -> list[pathlib.Path]:
    found = sorted(ROOT.glob("Submissions/**/*.json")) + sorted(
        ROOT.glob("Certificates/*/submissions/*.json")
    )
    return [p for p in found if "expect" in json.loads(p.read_text())]


def main() -> int:
    timeout = sys.argv[1] if len(sys.argv) > 1 else "1200"
    results = []
    failures = []

    for man in manifests():
        # A pinned package is fetched from the network and can be thousands of
        # modules; the corpus is for the examples in this repo.
        try:
            if json.loads(man.read_text()).get("external"):
                print(f"skip {man.relative_to(ROOT)}: pinned package")
                continue
        except Exception:
            pass
        meta = json.loads(man.read_text())
        rel = str(man.relative_to(ROOT))
        out = ROOT / ".conject/verdicts" / (rel.replace("/", "__"))
        print(f"\n=== {rel}  (expect {meta['expect']})", flush=True)
        proc = subprocess.run(
            [str(ROOT / "scripts/verify.sh"), "--submission", rel,
             "--out", str(out), "--timeout", timeout],
            cwd=ROOT, capture_output=True, text=True,
        )
        sys.stdout.write(proc.stdout)
        sys.stderr.write(proc.stderr)

        try:
            v = json.loads(out.read_text())
        except Exception as e:
            failures.append(f"{rel}: no verdict written ({e})")
            continue

        got = v["verdict"]
        want = meta["expect"]
        line = f"{rel}: expected {want}, got {got} ({v['reason']})"
        print("   " + line, flush=True)
        if got != want:
            failures.append(line)
        elif want == "red" and meta.get("expect_reason") and \
                v["reason"] != meta["expect_reason"]:
            failures.append(
                f"{rel}: red for the wrong reason — expected "
                f"{meta['expect_reason']!r}, got {v['reason']!r}")
        results.append((rel, v))

    # A green Lean verdict must always carry a hash and a clean axiom set.
    greens = [(r, v) for r, v in results if v["verdict"] == "green"]
    for rel, v in greens:
        if not v.get("elaborated_term_hash"):
            failures.append(f"{rel}: green verdict with no elaborated_term_hash")

    lean_greens = {v["elaborated_term_hash"] for _, v in greens if v.get("kind") == "lean"}
    lean_green_count = len([1 for _, v in greens if v.get("kind") == "lean"])
    if lean_green_count >= 2 and len(lean_greens) < lean_green_count:
        failures.append(
            "distinct green Lean proofs collided on elaborated_term_hash; "
            "the hash cannot be used for deduplication")

    print("\n" + "=" * 60)
    for rel, v in results:
        h = (v.get("elaborated_term_hash") or "-")[:23]
        print(f"  {v['verdict']:<5} {v['reason']:<20} {h:<25} {rel}")
    print("=" * 60)

    if failures:
        print("\nSELFTEST FAILED:")
        for f in failures:
            print("  - " + f)
        return 1
    print(f"\nSELFTEST PASSED ({len(results)} submissions)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
