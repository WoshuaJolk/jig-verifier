"""Shared helpers for the Conject verifiers.

Both the Lean path (`verify_lean.py`) and the certificate path (`verify_cert.py`)
emit the same verdict shape, so downstream consumers never branch on submission kind.
"""

from __future__ import annotations

import datetime
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import time

VERDICT_SCHEMA = "conject.verdict.v1"

# The only axioms a green Lean submission may depend on. This is exactly Mathlib's
# standard trusted base.
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    return sha256_bytes(path.read_bytes())


def utc_now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def new_verdict(**kw) -> dict:
    """A verdict starts RED. Every check has to actively turn it green."""
    v = {
        "schema": VERDICT_SCHEMA,
        "verdict": "red",
        "reason": "not_run",
        "detail": "",
        "kind": "lean",
        "statement_id": None,
        "submission": None,
        "decl": None,
        "axioms": [],
        "elaborated_term_hash": None,
        "statement_hash": None,
        "term_hash_kind": "conject-normalized-v1",
        "checks": {},
        "toolchain": {},
        "timings_sec": {},
        "timestamp": utc_now(),
    }
    v.update(kw)
    return v


NEXT_STEP = {
    "ok": "Nothing to do.",
    "restatement": (
        "Your declaration's type is not definitionally the canonical one. Compare "
        "`submitted_type` with `canonical_statement`: weakening a hypothesis or "
        "changing the conclusion both land here."
    ),
    "shadowed_statement": (
        "Your module redeclares a name the statement module already owns. Rename your "
        "declaration, and never open `namespace Statements`."
    ),
    "provenance": (
        "The declaration you named is not declared in the module you named. Check `decl` "
        "and `module` in the manifest against the source you submitted."
    ),
    "forbidden_syntax": (
        "The static scan rejected a construct before Lean ran. The detail names the line "
        "and the construct; remove it. This is not negotiable by proving something else."
    ),
    "sorry": "The proof term reaches `sorryAx`. Something in the chain is still a hole.",
    "native_decide": (
        "`native_decide` trusts the compiler, not the kernel. Replace it with `decide` "
        "or a proof."
    ),
    "disallowed_axiom": (
        "The proof depends on an axiom outside the trusted three. The detail lists the "
        "extras."
    ),
    "build_failed": "The submission does not compile. `output` carries the compiler error.",
    "audit_failed": "The axiom audit did not elaborate. `output` carries the error.",
    "bad_manifest": "The manifest is malformed. The detail says which field.",
    "unknown_statement": "No statement file by that label. Check `verifier_statement_label`.",
    "missing_source": "No source at the path the module name implies.",
    "statement_id_mismatch": "The manifest names a different statement than the dispatch did.",
    "timeout": (
        "A step exceeded its budget. The detail names the step. If it was the build, the "
        "proof is too slow, not wrong. `step=anti_restatement` or `step=refutation` means "
        "the bridge ran out of elaboration budget and decided nothing: make the canonical "
        "statement cheaper to unfold (fold big definitions into named ones) rather than "
        "restating it."
    ),
    "verifier_error": "The verifier crashed. Not your fault; report it rather than resubmitting.",
    "run_cancelled": (
        "Nothing was verified and nothing is known about your proof. The run was cancelled "
        "before the checks ran."
    ),
    "not_a_refutation": (
        "The statement you proved is not definitionally the negation of the one you named "
        "in `refutes`. Either the target is wrong, or your canonical proposition needs to be "
        "written as `¬ Statements.<target>.statement`."
    ),
    "invalid_witness": "The checker rejected the witness. The detail carries its reason.",
    "checker_error": "The checker crashed. Infrastructure, not your certificate.",
}

# Reasons that say nothing about the submission, so a resubmission is the right move.
NOT_ACTIONABLE = {"verifier_error", "checker_error", "run_cancelled"}


def advise(verdict: dict) -> dict:
    """Attach what to do next. Derived from `reason`, never authored per artifact."""
    reason = verdict.get("reason", "")
    verdict.setdefault("next", NEXT_STEP.get(reason, ""))
    verdict.setdefault("agent_actionable", reason not in NOT_ACTIONABLE)
    return verdict


def finish(verdict: dict, out_path: str | None) -> int:
    """Write the verdict, print it, and return the process exit code.

    Exit 0 for green, 1 for red. A crash in the driver itself must never reach here;
    callers wrap `main` so that an unexpected exception still produces a red verdict.
    """
    advise(verdict)
    text = json.dumps(verdict, indent=2, sort_keys=False)
    if out_path:
        p = pathlib.Path(out_path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text + "\n")
    print(text)
    return 0 if verdict["verdict"] == "green" else 1


def record(verdict: dict, name: str, ok: bool, detail: str = "", output: str = "") -> bool:
    """`detail` is the one-line summary. `output` is everything the tool said.

    Keeping only the summary is how a type mismatch reached agents as the words
    "Type mismatch" and nothing else: Lean puts the two types on indented
    continuation lines, which carry no "error:" and were filtered out.
    """
    entry = {"ok": ok, "detail": detail}
    if output:
        entry["output"] = output
    verdict["checks"][name] = entry
    return ok


def fail(verdict: dict, reason: str, detail: str = "") -> dict:
    """Set the primary failure reason, keeping the first one that fired."""
    if verdict["reason"] in ("not_run", "ok"):
        verdict["reason"] = reason
        verdict["detail"] = detail
    return verdict


def run(cmd, cwd=None, timeout=None, env=None):
    """Run a command, capturing output. Raises subprocess.TimeoutExpired on timeout."""
    return subprocess.run(
        cmd,
        cwd=cwd or REPO_ROOT,
        timeout=timeout,
        env=env or os.environ.copy(),
        capture_output=True,
        text=True,
        errors="replace",
    )


class Streamed:
    """What a streamed command did: its output, and how far it got."""

    def __init__(self, returncode: int, output: str, built: int, last: str, seconds: float):
        self.returncode = returncode
        self.stdout = output
        self.stderr = ""
        self.built = built
        self.last = last
        self.seconds = seconds


def run_streamed(cmd, timeout: float, cwd=None, env=None, every: int = 250, keep: int = 400) -> Streamed:
    """Run a build, echoing progress as it goes.

    A capture-everything run tells you nothing until it ends, so a five-hour build
    that timed out reported no output at all. This prints one line per `every`
    modules and keeps the tail for the verdict. Raises TimeoutExpired past
    `timeout`, carrying the progress made.
    """
    import collections
    import threading

    started = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        cwd=cwd or REPO_ROOT,
        env=env or os.environ.copy(),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        errors="replace",
        bufsize=1,
    )
    lines: collections.deque = collections.deque(maxlen=keep)
    state = {"built": 0, "last": ""}

    def reader() -> None:
        assert proc.stdout is not None
        for line in proc.stdout:
            line = line.rstrip()
            lines.append(line)
            if "] Built " in line:
                state["built"] += 1
                state["last"] = line[-140:]
                if state["built"] % every == 0:
                    print(f"[{(time.monotonic() - started) / 60:6.1f}m] built {state['built']}: {state['last']}", flush=True)

    t = threading.Thread(target=reader, daemon=True)
    t.start()
    while proc.poll() is None:
        if time.monotonic() - started > timeout:
            proc.kill()
            t.join(timeout=5)
            raise subprocess.TimeoutExpired(
                cmd, timeout, output=f"{state['built']}\t{state['last']}"
            )
        time.sleep(1)
    t.join(timeout=10)
    return Streamed(proc.returncode, "\n".join(lines), state["built"], state["last"], time.monotonic() - started)


def machine_info() -> dict:
    """Cores and memory, so a slow build can be read against the box it ran on."""
    info: dict = {"cpus": os.cpu_count()}
    try:
        meminfo = pathlib.Path("/proc/meminfo").read_text()
        for ln in meminfo.splitlines():
            if ln.startswith("MemTotal:"):
                info["memory_mb"] = int(ln.split()[1]) // 1024
                break
    except Exception:
        pass
    return info


def tail(s: str, n: int = 4000) -> str:
    s = s.strip()
    return s if len(s) <= n else "…" + s[-n:]


def toolchain_info() -> dict:
    info = {}
    tc = REPO_ROOT / "lean-toolchain"
    if tc.exists():
        info["lean_toolchain"] = tc.read_text().strip()
    manifest = REPO_ROOT / "lake-manifest.json"
    if manifest.exists():
        try:
            data = json.loads(manifest.read_text())
            for pkg in data.get("packages", []):
                if pkg.get("name") == "mathlib":
                    info["mathlib_rev"] = pkg.get("rev")
            info["manifest_hash"] = sha256_file(manifest)
        except Exception:
            pass
    return info


def die(msg: str) -> None:
    print(f"conject: {msg}", file=sys.stderr)
    sys.exit(2)
