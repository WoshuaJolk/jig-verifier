#!/usr/bin/env python3
"""Deterministic verifier for a Lean submission.

    verify_lean.py --submission Submissions/S001/AliceDirect.json [--out verdict.json]

Pipeline (every step is a compiler invocation or a string comparison; no heuristics):

  1. static policy scan of the submission source
  2. `lake build` the submission module
  3. anti-restatement: elaborate `example : <canonical> := @<their decl>` where
     <canonical> is resolved by name out of `Statements/`, never read from the submission
  4. axiom audit: the transitive axiom set must be a subset of the trusted three
  5. normalized proof-term hash, for telling independent proofs from duplicates

A timeout at any step is a RED verdict, not a hang.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import external_source  # noqa: E402
import lean_policy  # noqa: E402
from conject_common import (  # noqa: E402
    ALLOWED_AXIOMS,
    REPO_ROOT,
    fail,
    finish,
    new_verdict,
    record,
    machine_info,
    run,
    run_streamed,
    sha256_file,
    tail,
    toolchain_info,
)

TYPECHECK_TEMPLATE = """\
import {statement_module}
import {submission_module}
import Verify.Guard

/- The canonical type is resolved by name out of `{statement_module}`. This command
   fails unless that name really is declared there, so a submission cannot shadow it. -/
#conject_provenance {statement_const} "{statement_module}"

/- The submitted declaration must genuinely come from the submitted module, not from
   Mathlib or another submission. -/
#conject_provenance {decl} "{submission_module}"

/- The canonical type, echoed so a failure can say what was expected without the
   agent installing Lean to find out. -/
#print {statement_const}

/- THE anti-restatement check. The default 200k heartbeats is a limit on the
   verifier's patience, not a fact about the submission, and a defeq-heavy but
   correct statement was already red as `restatement` for hitting it. The wall
   budget is the real bound. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
example : {statement_const} := @{decl}
"""

REFUTATION_TEMPLATE = """\
import Verify.Guard
import {statement_module}
import {target_module}

/- The refutation link. `{statement_const}` must BE the negation of
   `{target_const}`, up to definitional equality: nothing here takes the
   submitter's word for which statement is being refuted. Checked by the
   kernel at shared universe parameters; `example : R ↔ ¬ T := Iff.rfl`
   generalizes the two universes apart and rejects every polymorphic pair. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
#conject_refutation {statement_const} {target_const}
"""

AUDIT_TEMPLATE = """\
import {statement_module}
import {submission_module}
import Verify.Guard

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

#conject_no_new_axioms "{submission_module}"

#print axioms {decl}

#conject_audit {decl} "{submission_module}" "{sub_prefix}"
#conject_audit {statement_const} "{statement_module}" "{stmt_prefix}"
"""


def module_to_path(mod: str) -> pathlib.Path:
    return REPO_ROOT / (mod.replace(".", "/") + ".lean")


def repo_rel(s: str) -> str:
    """Runner-absolute paths name a machine that no longer exists by the time an
    agent reads the verdict."""
    return s.replace(str(REPO_ROOT) + "/", "").replace(str(REPO_ROOT), "")


def lean_errors(proc: subprocess.CompletedProcess) -> str:
    """One-line summary: the diagnostic headers, without their bodies."""
    lines = [
        ln
        for ln in (proc.stdout + "\n" + proc.stderr).splitlines()
        if "error:" in ln or ln.startswith("CONJECT_ERROR")
    ]
    return repo_rel("\n".join(lines))


def lean_output(proc: subprocess.CompletedProcess) -> str:
    """Everything Lean said, headers and bodies both.

    A type mismatch puts the two types on indented continuation lines that carry
    no "error:", so `lean_errors` drops precisely the part that answers the
    question. This is the field an agent should read first.
    """
    return repo_rel(tail((proc.stdout + "\n" + proc.stderr).strip(), 8000))


def budget_exhausted(text: str) -> bool:
    """True when Lean gave up on elaboration rather than deciding anything.

    A heartbeat or maxRecDepth ceiling is a fact about how hard the check was, not
    about whether the two types agree, so it must never be reported as a mismatch.
    """
    return (
        "maximum number of heartbeats" in text
        or "(deterministic) timeout" in text
        or "maximum recursion depth" in text
    )


def between(text: str, start: str, end: str) -> str:
    """The block after `start` and before `end`, dedented. \"\" when absent."""
    if start not in text:
        return ""
    body = text.split(start, 1)[1]
    if end and end in body:
        body = body.split(end, 1)[0]
    lines = [ln.strip() for ln in body.strip().splitlines()]
    return " ".join(ln for ln in lines if ln)


def printed_type(out: str, const: str) -> str:
    """The body of `#print <const>`, which Lean writes as `def <const> : Prop :=`
    followed by the proposition."""
    for marker in (f"def {const} : Prop :=", f"def {const} :="):
        if marker in out:
            body = out.split(marker, 1)[1]
            keep: list[str] = []
            for ln in body.splitlines():
                # A new diagnostic or a new declaration ends the printed body.
                if keep and (not ln.strip() or ".lean:" in ln or ln.startswith(("def ", "theorem ", "@["))):
                    break
                if ln.strip():
                    keep.append(ln.strip())
            return " ".join(keep)
    return ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--submission", required=True, help="path to a submission manifest")
    ap.add_argument("--statement", help="expected statement id (cross-checked)")
    ap.add_argument("--out", help="where to write the verdict JSON")
    ap.add_argument("--timeout", type=int, default=1200, help="total wall budget, seconds")
    ap.add_argument("--work", default=".conject/work")
    # A package too large for one job is built by several, each running one phase.
    ap.add_argument("--phase", default="all",
                    choices=["all", "plan", "build", "replay", "finish"])
    ap.add_argument("--plan", default=".conject/external/plan.json")
    ap.add_argument("--wave", type=int, default=0)
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--max-shards", type=int, default=12)
    args = ap.parse_args()

    started = time.monotonic()

    def remaining() -> float:
        return max(1.0, args.timeout - (time.monotonic() - started))

    verdict = new_verdict(kind="lean", submission=args.submission)
    verdict["toolchain"] = toolchain_info()

    # --- manifest -----------------------------------------------------------
    man_path = pathlib.Path(args.submission)
    if not man_path.is_absolute():
        man_path = REPO_ROOT / man_path
    try:
        manifest = json.loads(man_path.read_text())
    except Exception as e:
        record(verdict, "manifest", False, str(e))
        return finish(fail(verdict, "bad_manifest", str(e)), args.out)

    sid = manifest.get("statement_id")
    module = manifest.get("module")
    decl = manifest.get("decl")
    verdict["statement_id"] = sid
    verdict["decl"] = decl

    if args.statement and args.statement != sid:
        d = f"manifest says {sid!r}, caller asked for {args.statement!r}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "statement_id_mismatch", d), args.out)

    if not (sid and module and decl) or manifest.get("kind") != "lean":
        d = "manifest needs kind=lean plus statement_id, module, decl"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "bad_manifest", d), args.out)

    external = manifest.get("external")
    # A pinned package names its own modules, so its decl need not share the root's prefix;
    # provenance still pins the decl to the root module.
    if not external and not decl.startswith(module + "."):
        d = f"decl {decl!r} is not inside module {module!r}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "bad_manifest", d), args.out)

    statement_module = f"Statements.{sid}"
    statement_const = f"{statement_module}.statement"
    stmt_src = module_to_path(statement_module)

    if not stmt_src.exists():
        d = f"no canonical statement at {stmt_src.relative_to(REPO_ROOT)}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "unknown_statement", d), args.out)

    if external:
        t0 = time.monotonic()
        try:
            spec = external_source.validate(external)
            verdict["external"] = dict(spec)
            src = external_source.fetch(spec, timeout=min(900.0, remaining()))
            found = external_source.closure(src, module)
            problems = external_source.admit(found, src)
            sub_src, source_hash = external_source.stage(found, module)
        except external_source.Rejected as e:
            record(verdict, "manifest", False, e.detail)
            return finish(fail(verdict, e.reason, e.detail), args.out)
        except subprocess.TimeoutExpired:
            record(verdict, "manifest", False, "timeout")
            return finish(fail(verdict, "timeout", "step=fetch: fetching the pinned source exceeded the budget"), args.out)
        verdict["timings_sec"]["fetch"] = round(time.monotonic() - t0, 2)
        verdict["external"].update(
            modules=len(found), source_bytes=sum(p.stat().st_size for p in found.values())
        )
        verdict["submission_source_hash"] = source_hash
    else:
        sub_src = module_to_path(module)
        if not sub_src.exists():
            d = f"no source at {sub_src.relative_to(REPO_ROOT)}"
            record(verdict, "manifest", False, d)
            return finish(fail(verdict, "missing_source", d), args.out)
        verdict["submission_source_hash"] = sha256_file(sub_src)
        problems = lean_policy.scan(sub_src.read_text())

    record(verdict, "manifest", True)
    verdict["statement_source_hash"] = sha256_file(stmt_src)

    workdir = REPO_ROOT / args.work / f"{sid}__{module.replace('.', '_')}"
    workdir.mkdir(parents=True, exist_ok=True)

    # --- 1. static policy scan ---------------------------------------------
    # Never build a source the scan refused: building runs its code.
    if problems:
        record(verdict, "static_policy", False, "; ".join(problems[:50]))
        return finish(fail(verdict, "forbidden_syntax", problems[0]), args.out)
    else:
        record(verdict, "static_policy", True)

    # --- phases -------------------------------------------------------------
    # Every phase stages the source first: the lakefile library, the module paths
    # and the hash all have to exist before a shard can build or replay anything.
    shard: list[str] = []
    if args.phase != "all":
        if not external:
            d = "--phase is only for a pinned package"
            record(verdict, "manifest", False, d)
            return finish(fail(verdict, "bad_manifest", d), args.out)
        plan_path = pathlib.Path(args.plan)
        if args.phase == "plan":
            plan = external_source.waves(found, max_shards=args.max_shards)
            plan_path.parent.mkdir(parents=True, exist_ok=True)
            plan_path.write_text(json.dumps({
                "statement_id": sid,
                "module": module,
                "decl": decl,
                "external": verdict["external"],
                "source_hash": verdict["submission_source_hash"],
                "modules": len(found),
                "waves": plan,
            }, indent=1))
            print(f"planned {len(found)} modules into {len(plan)} waves, "
                  f"{sum(len(w) for w in plan)} shards -> {plan_path}")
            return 0
        try:
            planned = json.loads(plan_path.read_text())
        except Exception as e:
            d = f"could not read the plan at {args.plan}: {e}"
            record(verdict, "manifest", False, d)
            return finish(fail(verdict, "verifier_error", d), args.out)
        # The commit is pinned, so a staged tree that hashes differently means the
        # phases are not looking at the same source.
        if planned.get("source_hash") != verdict["submission_source_hash"]:
            d = "the staged source does not match the plan's source hash"
            record(verdict, "manifest", False, d)
            return finish(fail(verdict, "verifier_error", d), args.out)
        if args.phase in ("build", "replay"):
            try:
                shard = planned["waves"][args.wave][args.shard]
            except Exception:
                d = f"no shard {args.wave}/{args.shard} in the plan"
                record(verdict, "manifest", False, d)
                return finish(fail(verdict, "verifier_error", d), args.out)

    # --- kernel replay (one shard) ------------------------------------------
    # Shards trust each other's oleans, so before the bridge every declaration is
    # replayed through the kernel. This is what makes a build split across runners
    # worth the same as one built here.
    if args.phase == "replay":
        t0 = time.monotonic()
        for i in range(0, len(shard), 100):
            chunk = shard[i : i + 100]
            try:
                proc = run(["lake", "env", "leanchecker", *chunk], timeout=remaining())
            except subprocess.TimeoutExpired:
                d = f"step=replay: exceeded the wall budget after {i} of {len(shard)} modules"
                record(verdict, "kernel_replay", False, d)
                return finish(fail(verdict, "timeout", d), args.out)
            if proc.returncode != 0:
                full = lean_output(proc)
                d = tail(lean_errors(proc) or full)
                record(verdict, "kernel_replay", False, d, output=full)
                return finish(fail(verdict, "audit_failed", f"step=replay: {d}"), args.out)
            print(f"replayed {min(i + 100, len(shard))}/{len(shard)}", flush=True)
        print(f"kernel replayed {len(shard)} modules in {time.monotonic() - t0:.0f}s")
        return 0

    # --- 2. build -----------------------------------------------------------
    # The refutation target is imported by the bridge in step 6, so it has to be
    # built here with everything else. Leaving it out made a missing olean look
    # like a failed refutation.
    refutes = manifest.get("refutes")
    if args.phase == "build":
        # Only this shard: its dependencies arrive already built from earlier waves.
        build_targets = list(shard)
    else:
        build_targets = [module, statement_module, "Verify.Guard"]
        if refutes:
            build_targets.append(f"Statements.{refutes}")
    t0 = time.monotonic()
    verdict["machine"] = machine_info()
    expected = f" of {len(found)}" if external else ""
    try:
        proc = run_streamed(["lake", "build", *build_targets], timeout=remaining())
    except subprocess.TimeoutExpired as e:
        built, _, last = (e.output if isinstance(e.output, str) else "").partition("\t")
        verdict["timings_sec"]["build"] = round(time.monotonic() - t0, 2)
        if external:
            verdict["external"]["modules_built"] = int(built or 0)
        d = f"step=build: lake build exceeded the wall budget having built {built or 0}{expected} modules"
        record(verdict, "build", False, d, output=f"last: {last}")
        return finish(fail(verdict, "timeout", d), args.out)
    verdict["timings_sec"]["build"] = round(time.monotonic() - t0, 2)
    if external:
        verdict["external"]["modules_built"] = proc.built
    if proc.returncode != 0:
        full = lean_output(proc)
        d = tail(lean_errors(proc) or full)
        record(verdict, "build", False, d, output=full)
        return finish(fail(verdict, "build_failed", d), args.out)
    record(verdict, "build", True)
    if args.phase == "build":
        print(f"built {proc.built} of {len(shard)} modules in wave {args.wave} shard {args.shard}")
        return 0

    # --- 3. anti-restatement -----------------------------------------------
    tc_file = workdir / "TypeCheck.lean"
    tc_file.write_text(
        TYPECHECK_TEMPLATE.format(
            statement_module=statement_module,
            submission_module=module,
            statement_const=statement_const,
            decl=decl,
        )
    )
    verdict["typecheck_file"] = str(tc_file.relative_to(REPO_ROOT))
    t0 = time.monotonic()
    try:
        proc = run(["lake", "env", "lean", str(tc_file)], timeout=remaining())
    except subprocess.TimeoutExpired:
        record(verdict, "anti_restatement", False, "timeout")
        return finish(fail(verdict, "timeout", "step=anti_restatement: the check exceeded the wall budget"), args.out)
    verdict["timings_sec"]["anti_restatement"] = round(time.monotonic() - t0, 2)
    full = lean_output(proc)
    canonical = printed_type(full, statement_const)
    if canonical:
        verdict["canonical_statement"] = canonical
    if proc.returncode != 0:
        d = tail(lean_errors(proc) or full)
        record(verdict, "anti_restatement", False, d, output=full)
        # Lean names both sides of a mismatch; hand them over rather than making
        # the agent rebuild Mathlib to read them.
        submitted = between(full, "has type", "but is expected to have type")
        if submitted:
            verdict["submitted_type"] = submitted
        if budget_exhausted(full):
            record(verdict, "anti_restatement", False,
                   f"elaboration budget exhausted: {d}", output=full)
            return finish(
                fail(verdict, "timeout",
                     "step=anti_restatement: the bridge ran out of elaboration budget "
                     "before it could decide anything. This is not a mismatch"),
                args.out)
        if "environment already contains" in d:
            reason = "shadowed_statement"
        elif "CONJECT_ERROR: provenance" in proc.stdout:
            reason = "provenance"
        else:
            reason = "restatement"
        fail(verdict, reason,
             f"`example : {statement_const} := @{decl}` did not elaborate")
    else:
        record(verdict, "anti_restatement", True,
               f"example : {statement_const} := @{decl}")

    # --- 4/5. axiom audit + term hash --------------------------------------
    sub_prefix = workdir / "sub"
    stmt_prefix = workdir / "stmt"
    audit_file = workdir / "Audit.lean"
    audit_file.write_text(
        AUDIT_TEMPLATE.format(
            statement_module=statement_module,
            submission_module=module,
            statement_const=statement_const,
            decl=decl,
            sub_prefix=str(sub_prefix),
            stmt_prefix=str(stmt_prefix),
        )
    )
    t0 = time.monotonic()
    try:
        proc = run(["lake", "env", "lean", str(audit_file)], timeout=remaining())
    except subprocess.TimeoutExpired:
        record(verdict, "axioms", False, "timeout")
        return finish(fail(verdict, "timeout", "step=axiom_audit: the audit exceeded the wall budget"), args.out)
    verdict["timings_sec"]["audit"] = round(time.monotonic() - t0, 2)

    print_axioms_line = next(
        (ln for ln in proc.stdout.splitlines() if "depends on axioms" in ln
         or "does not depend on any axioms" in ln),
        "",
    )
    verdict["print_axioms"] = print_axioms_line.strip()

    sub_json = sub_prefix.with_suffix(".json")
    if proc.returncode != 0 or not sub_json.exists():
        full = lean_output(proc)
        d = tail(lean_errors(proc) or full)
        record(verdict, "axioms", False, d, output=full)
        record(verdict, "no_new_axioms", False, d, output=full)
        return finish(fail(verdict, "audit_failed", d), args.out)
    record(verdict, "no_new_axioms", True)

    audit = json.loads(sub_json.read_text())
    axioms = sorted(audit.get("axioms", []))
    verdict["axioms"] = axioms
    extra = sorted(set(axioms) - ALLOWED_AXIOMS)
    if extra:
        d = f"axioms outside the trusted base: {extra}"
        record(verdict, "axioms", False, d)
        reason = "sorry" if "sorryAx" in extra else (
            "native_decide" if any(a.startswith("Lean.ofReduce") for a in extra)
            else "disallowed_axiom")
        fail(verdict, reason, d)
    else:
        record(verdict, "axioms", True, f"{axioms} ⊆ {sorted(ALLOWED_AXIOMS)}")

    term_file = pathlib.Path(audit["term_file"])
    verdict["elaborated_term_hash"] = sha256_file(term_file)
    verdict["term_bytes"] = audit.get("term_bytes")
    if audit.get("term_truncated"):
        verdict["term_hash_kind"] = "conject-normalized-v1-truncated"

    stmt_json = stmt_prefix.with_suffix(".json")
    if stmt_json.exists():
        stmt_audit = json.loads(stmt_json.read_text())
        verdict["statement_hash"] = sha256_file(pathlib.Path(stmt_audit["term_file"]))

    # --- 6. refutation link (only when the manifest declares one) -----------
    if refutes:
        target_module = f"Statements.{refutes}"
        target_src = module_to_path(target_module)
        verdict["refutes"] = refutes
        if not target_src.exists():
            record(verdict, "refutation", False, f"no {target_src.name} in the repo")
            fail(verdict, "unknown_statement",
                 f"refutes `{refutes}` but there is no Statements/{refutes}.lean")
        else:
            ref_file = workdir / "Refutation.lean"
            ref_file.write_text(
                REFUTATION_TEMPLATE.format(
                    statement_module=statement_module,
                    target_module=target_module,
                    statement_const=statement_const,
                    target_const=f"{target_module}.statement",
                )
            )
            t0 = time.monotonic()
            try:
                proc = run(["lake", "env", "lean", str(ref_file)], timeout=remaining())
            except subprocess.TimeoutExpired:
                record(verdict, "refutation", False, "timeout")
                return finish(fail(verdict, "timeout",
                                   "step=refutation: the negation link exceeded the wall budget"),
                              args.out)
            verdict["timings_sec"]["refutation"] = round(time.monotonic() - t0, 2)
            if proc.returncode != 0:
                full = lean_output(proc)
                d = tail(lean_errors(proc) or full)
                record(verdict, "refutation", False, d, output=full)
                # An import that did not resolve says nothing about the claim.
                if budget_exhausted(full):
                    return finish(
                        fail(verdict, "timeout",
                             "step=refutation: the negation link ran out of elaboration "
                             "budget. Nothing was decided either way"),
                        args.out)
                broken = "does not exist" in full or "unknown module" in full
                if broken:
                    fail(verdict, "build_failed",
                         f"the refutation bridge could not import {target_module}")
                else:
                    fail(verdict, "not_a_refutation",
                         f"`{statement_const}` is not definitionally `¬ {target_module}.statement`")
            else:
                record(verdict, "refutation", True,
                       f"{statement_const} ↔ ¬ {target_module}.statement")

    # --- verdict ------------------------------------------------------------
    verdict["timings_sec"]["total"] = round(time.monotonic() - started, 2)
    if all(c["ok"] for c in verdict["checks"].values()):
        verdict["verdict"] = "green"
        verdict["reason"] = "ok"
        verdict["detail"] = "all checks passed"
    return finish(verdict, args.out)


if __name__ == "__main__":
    try:
        try:
            code = main()
        finally:
            external_source.unstage()
        sys.exit(code)
    except Exception as e:  # a crashing verifier must still say RED
        v = new_verdict(kind="lean", reason="verifier_error", detail=f"{type(e).__name__}: {e}")
        out = None
        argv = sys.argv
        if "--out" in argv:
            out = argv[argv.index("--out") + 1]
        sys.exit(finish(v, out))
