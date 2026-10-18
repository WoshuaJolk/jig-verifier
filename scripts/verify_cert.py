#!/usr/bin/env python3
"""Verifier for non-Lean certificate submissions.

A certificate problem owns a checker script under `Certificates/<id>/`. A submission is
a witness file. The checker's only job is to read the witness and print one line:

    CONJECT_CERT: {"ok": true, "reason": "...", "canonical": "<normal form>"}

`canonical` is the witness reduced to a canonical form by the *checker*, not by the
submitter, so it plays the role that the normalized proof term plays on the Lean side:
two submissions of the same witness produce the same `elaborated_term_hash`.

The checker runs with:
  * no network            (Linux user+net namespace, or macOS sandbox-exec)
  * a CPU-seconds rlimit and a wall-clock timeout
  * an address-space rlimit and an output-size rlimit
  * a scratch cwd containing a copy of the witness, the spec, the checker, the
    shared code the spec names, and the fixtures the spec pins
  * no environment inherited except PATH/HOME/LANG

Fixtures are the one way data from outside the repo reaches a checker. Each is pinned
by sha256 in spec.json and resolved BEFORE the sandbox closes: a vendored file under
Certificates/<id>/, a cached download, or a live catalog lookup keyed by a field of the
witness. Whatever was used is recorded in the verdict, hash and source, so the
measurement can be re-derived.

Trust boundary: the checker is repo-owned and reviewed like a canonical statement. The
witness is untrusted. The sandbox protects the runner from the *checker*, since a
checker bug plus a hostile witness is the realistic failure mode.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import platform
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from conject_common import (  # noqa: E402
    REPO_ROOT,
    fail,
    finish,
    new_verdict,
    record,
    sha256_bytes,
    sha256_file,
    tail,
    utc_now,
)

MARKER = "CONJECT_CERT:"

# A checker earns proof-grade by being cheap to re-run: anyone can repeat 30
# seconds of arithmetic, and a claim nobody repeats is testimony with extra
# steps. A checker that needs more than this is doing the search rather than
# checking a witness, which is why the heavy lane exists and why Jig records an
# artifact verified in it as measurement-grade.
DEFAULT_LIMITS = {
    "wall_sec": 60,
    "cpu_sec": 30,
    "address_space_mb": 2048,
    "output_bytes": 1 << 20,
}

# The ceiling a spec may raise itself to, and only in the heavy lane.
HEAVY_LIMITS = {
    "wall_sec": 2700,
    "cpu_sec": 2400,
    "address_space_mb": 8192,
    "output_bytes": 1 << 24,
}

# Where downloaded fixtures live between runs. CI caches it on the spec hashes.
FIXTURE_CACHE = pathlib.Path(
    os.environ.get("CONJECT_FIXTURE_CACHE") or (REPO_ROOT / ".conject" / "fixtures")
)
DOWNLOAD_TIMEOUT_SEC = 600
LIVE_TIMEOUT_SEC = 60

MACOS_SANDBOX_PROFILE = """(version 1)
(allow default)
(deny network*)
(deny mach-lookup (global-name "com.apple.networkd"))
"""

TRUE_BIN = shutil.which("true") or "/bin/true"


def _probe(argv: list[str]) -> bool:
    """Actually run the wrapper on /bin/true; never assume a sandbox works."""
    try:
        p = subprocess.run(argv + [TRUE_BIN], capture_output=True, timeout=20)
        return p.returncode == 0
    except Exception:
        return False


def netns_wrapper() -> tuple[list[str], str]:
    """Return (argv prefix, description) that removes network access, if we can.

    Three routes, tried in order and each actually probed rather than assumed:

    1. An unprivileged user namespace. The clean option, but Ubuntu 24.04 (and so the
       GitHub Actions runners) ships an AppArmor policy that denies it.
    2. A root network namespace via passwordless sudo, immediately dropping back to the
       calling uid with `setpriv`. The checker still runs unprivileged; only the
       `unshare` gets root, and only long enough to create the empty netns.
    3. macOS `sandbox-exec` with a `deny network*` profile.
    """
    system = platform.system()
    if system == "Linux" and shutil.which("unshare"):
        userns = ["unshare", "--net", "--map-root-user", "--"]
        if _probe(userns):
            return (userns, "linux-userns")
        if shutil.which("sudo") and shutil.which("setpriv"):
            sudo_ns = [
                "sudo", "-n", "unshare", "--net", "--",
                "setpriv", f"--reuid={os.getuid()}", f"--regid={os.getgid()}",
                "--clear-groups", "--",
            ]
            if _probe(sudo_ns):
                return (sudo_ns, "linux-sudo-netns")
    if system == "Darwin" and shutil.which("sandbox-exec"):
        prof = ["sandbox-exec", "-p", MACOS_SANDBOX_PROFILE]
        if _probe(prof):
            return (prof, "macos-sandbox-exec")
    return ([], "none")


def make_preexec(limits: dict):
    def preexec():
        cpu = limits["cpu_sec"]
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 1))
        mem = limits["address_space_mb"] * 1024 * 1024
        try:
            resource.setrlimit(resource.RLIMIT_AS, (mem, mem))
        except (ValueError, OSError):
            pass  # RLIMIT_AS is not enforceable on some platforms
        out = limits["output_bytes"]
        resource.setrlimit(resource.RLIMIT_FSIZE, (out, out))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        os.setsid()
    return preexec


# ----------------------------------------------------------------- fixtures

FIXTURE_NAME = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,80}$")
SHA_HEX = re.compile(r"^[0-9a-f]{64}$")
SOURCE_ID = re.compile(r"^[0-9]{1,20}$")

# Live lookups: a catalog row fetched by a key read out of the witness. The
# query is fixed here, never built from anything else in the witness, and the
# raw response is what the checker sees.
GAIA_TAP = "https://gea.esac.esa.int/tap-server/tap/sync"
GAIA_COLUMNS = (
    "source_id, ra, dec, ref_epoch, parallax, parallax_error, pmra, pmra_error, "
    "pmdec, pmdec_error, radial_velocity, radial_velocity_error, phot_g_mean_mag, "
    "bp_rp, ruwe, astrometric_params_solved"
)


def _download(url: str, dest: pathlib.Path) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_suffix(dest.suffix + ".part")
    req = urllib.request.Request(url, headers={"User-Agent": "jig-verifier/1 (+https://jig.so)"})
    with urllib.request.urlopen(req, timeout=DOWNLOAD_TIMEOUT_SEC) as r, open(tmp, "wb") as f:
        shutil.copyfileobj(r, f, length=1 << 20)
    os.replace(tmp, dest)


def _witness_key(witness: pathlib.Path, key: str) -> str | None:
    """Read one top-level scalar out of a JSON witness. Anything else is None."""
    try:
        doc = json.loads(witness.read_text(errors="replace"))
    except Exception:
        return None
    if not isinstance(doc, dict):
        return None
    v = doc.get(key)
    if isinstance(v, bool):
        return None
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str) and v.strip():
        return v.strip()
    return None


def _live_gaia(source_id: str) -> bytes:
    query = f"SELECT {GAIA_COLUMNS} FROM gaiadr3.gaia_source WHERE source_id = {int(source_id)}"
    params = urllib.parse.urlencode(
        {"REQUEST": "doQuery", "LANG": "ADQL", "FORMAT": "json", "QUERY": query}
    )
    req = urllib.request.Request(
        f"{GAIA_TAP}?{params}", headers={"User-Agent": "jig-verifier/1 (+https://jig.so)"}
    )
    last: Exception | None = None
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=LIVE_TIMEOUT_SEC) as r:
                body = r.read()
            json.loads(body)  # must at least be JSON before it is handed on
            return body
        except Exception as e:  # noqa: BLE001
            last = e
            time.sleep(2 * (attempt + 1))
    raise RuntimeError(f"gaia tap: {last}")


LIVE_LOOKUPS = {"gaia_dr3_source": (_live_gaia, SOURCE_ID)}


def resolve_fixtures(
    spec: dict, problem_dir: pathlib.Path, witness: pathlib.Path, tmpdir: pathlib.Path
) -> tuple[list[dict], str | None, str]:
    """Materialise every fixture into `tmpdir`.

    Returns (records, failure_reason, detail). Records go into the verdict whether or
    not the run succeeds: a reader has to be able to see which snapshot a measurement
    was made against.
    """
    records: list[dict] = []
    for fx in spec.get("fixtures", []):
        name = str(fx.get("name", ""))
        if not FIXTURE_NAME.match(name):
            return records, "bad_manifest", f"fixture name {name!r} is not allowed"
        dest = tmpdir / name
        rec: dict = {"name": name}

        live = fx.get("live")
        if live:
            fetch, key_re = LIVE_LOOKUPS.get(str(live), (None, None))
            if fetch is None:
                return records, "bad_manifest", f"unknown live lookup {live!r}"
            key = str(fx.get("key", ""))
            value = _witness_key(witness, key)
            rec.update({"source": "live", "lookup": live, "key": key})
            if value is None or not key_re.match(value):
                # Not an infrastructure failure: the witness did not name a row. The
                # checker sees no file and says so in its own words.
                rec["value"] = None
                records.append(rec)
                continue
            rec["value"] = value
            try:
                body = fetch(value)
            except Exception as e:  # noqa: BLE001
                rec["error"] = str(e)
                records.append(rec)
                return records, "fixture_unavailable", f"{name}: {e}"
            dest.write_bytes(body)
            rec["sha256"] = sha256_bytes(body)
            rec["fetched_at"] = utc_now()
            records.append(rec)
            continue

        want = str(fx.get("sha256", "")).lower().removeprefix("sha256:")
        if not SHA_HEX.match(want):
            return records, "bad_manifest", f"fixture {name}: sha256 missing or malformed"
        rec["sha256"] = "sha256:" + want

        src: pathlib.Path | None = None
        if fx.get("path"):
            rel = pathlib.Path(str(fx["path"]))
            if rel.is_absolute() or ".." in rel.parts:
                return records, "bad_manifest", f"fixture {name}: path must stay inside Certificates/"
            # `_fixtures/...` is the shared vendored store; anything else is the problem's own.
            root = problem_dir.parent if rel.parts and rel.parts[0] == "_fixtures" else problem_dir
            src = root / rel
            rec["source"] = "vendored"
            if not src.exists():
                return records, "fixture_unavailable", f"{name}: no file at {src}"
        else:
            url = str(fx.get("url", ""))
            if not url.startswith("https://"):
                return records, "bad_manifest", f"fixture {name}: needs a path or an https url"
            rec["url"] = url
            cached = FIXTURE_CACHE / want
            if cached.exists():
                src = cached
                rec["source"] = "cached"
            else:
                try:
                    _download(url, cached)
                except Exception as e:  # noqa: BLE001
                    rec["error"] = str(e)
                    records.append(rec)
                    return records, "fixture_unavailable", f"{name}: {e}"
                src = cached
                rec["source"] = "downloaded"
                rec["fetched_at"] = utc_now()

        got = sha256_file(src)
        if got != rec["sha256"]:
            rec["got"] = got
            records.append(rec)
            if rec["source"] != "vendored":
                try:
                    src.unlink()
                except OSError:
                    pass
            return records, "fixture_mismatch", f"{name}: expected {rec['sha256']}, got {got}"
        try:
            os.link(src, dest)
        except OSError:
            shutil.copyfile(src, dest)
        records.append(rec)
    return records, None, ""


def check_requires(spec: dict) -> str | None:
    """Every module the spec names has to import in the interpreter the checker gets."""
    mods = [str(m) for m in spec.get("requires", [])]
    bad = [m for m in mods if not re.match(r"^[A-Za-z_][A-Za-z0-9_.]*$", m)]
    if bad:
        return f"requires names a module that is not an identifier: {bad}"
    if not mods:
        return None
    code = "import importlib,sys\n" + "".join(
        f"importlib.import_module({m!r})\n" for m in mods
    )
    p = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, timeout=120)
    if p.returncode != 0:
        return tail(p.stderr, 500)
    return None


def problem_identity(checker: pathlib.Path, spec_path: pathlib.Path, code: list[pathlib.Path]) -> str:
    """One hash over everything that defines the problem: the checker, its spec
    (thresholds live there) and the shared code it runs. Replaces the old
    checker-only statement_hash for v2 specs."""
    h = hashlib.sha256()
    for p in [checker, spec_path, *code]:
        h.update(p.name.encode() + b"\0" + p.read_bytes() + b"\0")
    return "sha256:" + h.hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--submission", required=True)
    ap.add_argument("--statement")
    ap.add_argument("--out")
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument(
        "--allow-no-netns", action="store_true",
        default=os.environ.get("CONJECT_ALLOW_NO_NETNS") == "1",
        help="run even if network isolation is unavailable (local development only)")
    args = ap.parse_args()

    started = time.monotonic()
    verdict = new_verdict(kind="certificate", submission=args.submission)
    verdict["term_hash_kind"] = "conject-canonical-witness-v1"

    man_path = pathlib.Path(args.submission)
    if not man_path.is_absolute():
        man_path = REPO_ROOT / man_path
    try:
        manifest = json.loads(man_path.read_text())
    except Exception as e:
        record(verdict, "manifest", False, str(e))
        return finish(fail(verdict, "bad_manifest", str(e)), args.out)

    sid = manifest.get("statement_id")
    verdict["statement_id"] = sid
    if args.statement and args.statement != sid:
        d = f"manifest says {sid!r}, caller asked for {args.statement!r}"
        return finish(fail(record(verdict, "manifest", False, d) or verdict,
                           "statement_id_mismatch", d), args.out)

    problem_dir = REPO_ROOT / "Certificates" / str(sid)
    checker = problem_dir / "checker.py"
    witness = man_path.parent / manifest.get("witness", "")
    if not checker.exists():
        d = f"no checker at Certificates/{sid}/checker.py"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "unknown_statement", d), args.out)
    if not witness.exists():
        d = f"no witness file at {witness}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "missing_witness", d), args.out)
    record(verdict, "manifest", True)

    heavy = os.environ.get("CONJECT_LANE") == "heavy"
    limits = dict(DEFAULT_LIMITS)
    spec: dict = {}
    spec_path = problem_dir / "spec.json"
    if spec_path.exists():
        try:
            spec = json.loads(spec_path.read_text())
        except Exception as e:
            d = f"Certificates/{sid}/spec.json: {e}"
            record(verdict, "manifest", False, d)
            return finish(fail(verdict, "bad_manifest", d), args.out)
        limits.update(spec.get("limits", {}))
    # A spec may raise its own limits, but never past the lane it is running in:
    # the sandbox is what makes a checker's cost knowable in advance.
    ceiling = HEAVY_LIMITS if heavy else DEFAULT_LIMITS
    for k, cap in ceiling.items():
        if limits.get(k, cap) > cap:
            limits[k] = cap
    limits["wall_sec"] = min(limits["wall_sec"], args.timeout)
    verdict["lane"] = "heavy" if heavy else "default"
    verdict["limits"] = limits
    verdict["checker_hash"] = sha256_file(checker)
    verdict["witness_hash"] = sha256_file(witness)
    verdict["decl"] = f"Certificates/{sid}/checker.py"

    # Shared code the spec names, resolved relative to the problem directory and
    # confined to Certificates/. Copied flat, so the checker imports by basename.
    code_files: list[pathlib.Path] = []
    for rel in spec.get("code", []):
        p = (problem_dir / str(rel)).resolve()
        try:
            p.relative_to((REPO_ROOT / "Certificates").resolve())
        except ValueError:
            d = f"code file {rel!r} is outside Certificates/"
            record(verdict, "manifest", False, d)
            return finish(fail(verdict, "bad_manifest", d), args.out)
        if not p.exists() or p.suffix != ".py":
            d = f"code file {rel!r} is missing or not a .py"
            record(verdict, "manifest", False, d)
            return finish(fail(verdict, "bad_manifest", d), args.out)
        code_files.append(p)
    verdict["statement_hash"] = (
        problem_identity(checker, spec_path, code_files) if spec_path.exists()
        else sha256_file(checker)
    )

    missing = check_requires(spec)
    if missing:
        record(verdict, "dependencies", False, missing)
        return finish(fail(verdict, "missing_dependency", missing), args.out)
    if spec.get("requires"):
        record(verdict, "dependencies", True, ", ".join(spec["requires"]))

    prefix, iso = netns_wrapper()
    verdict["network_isolation"] = iso
    if iso == "none" and not args.allow_no_netns:
        d = ("no network isolation available on this host; refusing to run an untrusted "
             "witness (set CONJECT_ALLOW_NO_NETNS=1 to override locally)")
        record(verdict, "sandbox", False, d)
        return finish(fail(verdict, "sandbox_unavailable", d), args.out)
    record(verdict, "sandbox", True, f"isolation={iso}, limits={limits}")

    with tempfile.TemporaryDirectory(prefix="conject-cert-") as tmp:
        tmpdir = pathlib.Path(tmp)
        shutil.copyfile(witness, tmpdir / "witness")
        shutil.copyfile(checker, tmpdir / "checker.py")
        if spec_path.exists():
            shutil.copyfile(spec_path, tmpdir / "spec.json")
        for p in code_files:
            shutil.copyfile(p, tmpdir / p.name)

        # Everything from outside the repo arrives here, before the sandbox
        # closes, and is written down.
        t0 = time.monotonic()
        fixtures, why, detail = resolve_fixtures(spec, problem_dir, witness, tmpdir)
        verdict["fixtures"] = fixtures
        verdict["timings_sec"]["fixtures"] = round(time.monotonic() - t0, 2)
        if why:
            record(verdict, "fixtures", False, detail)
            return finish(fail(verdict, why, detail), args.out)
        if fixtures:
            record(verdict, "fixtures", True, ", ".join(f"{f['name']}={f.get('source')}" for f in fixtures))

        env = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": str(tmpdir),
            "LANG": "C.UTF-8",
            "PYTHONHASHSEED": "0",
            "PYTHONDONTWRITEBYTECODE": "1",
            # One thread: a BLAS pool reserves address space the rlimit then
            # refuses, and a checker's cost is only knowable single-threaded.
            "OPENBLAS_NUM_THREADS": "1",
            "OMP_NUM_THREADS": "1",
            "MKL_NUM_THREADS": "1",
        }
        # `env -i` rather than relying on inheritance, because the sudo route sanitizes
        # the environment out from under us. Same command shape on every route.
        cmd = (prefix + ["/usr/bin/env", "-i"]
               + [f"{k}={v}" for k, v in sorted(env.items())]
               + [sys.executable, "checker.py", "witness"])
        t0 = time.monotonic()
        try:
            proc = subprocess.run(
                cmd, cwd=tmpdir, env=env, capture_output=True, text=True,
                errors="replace", timeout=limits["wall_sec"],
                preexec_fn=make_preexec(limits),
            )
        except subprocess.TimeoutExpired:
            d = f"checker exceeded its {limits['wall_sec']}s wall budget"
            record(verdict, "checker_ran", False, d)
            return finish(fail(verdict, "timeout", d), args.out)
        verdict["timings_sec"]["checker"] = round(time.monotonic() - t0, 2)

    verdict["checker_stdout"] = tail(proc.stdout, 2000)
    if proc.returncode != 0:
        d = f"checker exited {proc.returncode}: {tail(proc.stderr, 2000)}"
        record(verdict, "checker_ran", False, d)
        return finish(fail(verdict, "checker_error", d), args.out)
    record(verdict, "checker_ran", True)

    lines = [ln for ln in proc.stdout.splitlines() if ln.startswith(MARKER)]
    if len(lines) != 1:
        d = f"checker must print exactly one {MARKER} line, saw {len(lines)}"
        record(verdict, "checker_protocol", False, d)
        return finish(fail(verdict, "checker_protocol", d), args.out)
    try:
        result = json.loads(lines[0][len(MARKER):].strip())
        ok = bool(result["ok"])
        canonical = str(result.get("canonical", ""))
    except Exception as e:
        d = f"malformed {MARKER} payload: {e}"
        record(verdict, "checker_protocol", False, d)
        return finish(fail(verdict, "checker_protocol", d), args.out)
    record(verdict, "checker_protocol", True)

    verdict["elaborated_term_hash"] = sha256_bytes(canonical.encode())
    # What the checker measured, beyond ok/not: fitted elements, residuals,
    # probabilities. Kept whole; it is the evidence a reader judges the green on.
    if isinstance(result.get("measurement"), dict):
        verdict["measurement"] = result["measurement"]

    if not ok:
        d = result.get("reason", "checker rejected the witness")
        record(verdict, "witness_valid", False, d)
        return finish(fail(verdict, "invalid_witness", d), args.out)
    record(verdict, "witness_valid", True, result.get("reason", ""))

    verdict["timings_sec"]["total"] = round(time.monotonic() - started, 2)
    verdict["verdict"] = "green"
    verdict["reason"] = "ok"
    verdict["detail"] = "all checks passed"
    verdict["timestamp"] = utc_now()
    return finish(verdict, args.out)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:
        v = new_verdict(kind="certificate", reason="verifier_error",
                        detail=f"{type(e).__name__}: {e}")
        out = None
        if "--out" in sys.argv:
            out = sys.argv[sys.argv.index("--out") + 1]
        sys.exit(finish(v, out))
