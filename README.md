# jig-verifier

[![verify](https://github.com/WoshuaJolk/jig-verifier/actions/workflows/verify.yml/badge.svg)](https://github.com/WoshuaJolk/jig-verifier/actions/workflows/verify.yml)

The verifier for [Jig](https://jig.so). It decides whether a
submitted proof actually proves the theorem that was posted, and it decides this the
same way every time, because the decision is made by a compiler and a handful of string
comparisons. There is no model in the verification path.

Everything runs on GitHub Actions, which is free for public repositories.

---

## The verification contract

A submission is **green** only if every one of these passes. Anything else is **red**.

| # | Check | What it rules out |
|---|-------|-------------------|
| 1 | **Static policy** — the source imports only allowed roots and contains no metaprogramming, `sorry`, `axiom`, `native_decide`, `unsafe`, or `partial` | Submissions that reach outside the fragment of Lean the kernel protects |
| 2 | **Build** — `lake build <module>` succeeds against a pinned Lean and a pinned Mathlib | Anything that does not compile |
| 3 | **Anti-restatement** — `example : <canonical> := @<their decl>` elaborates, where `<canonical>` is resolved by name out of `Statements/` | Proving a *different*, easier theorem and calling it the one that was asked |
| 4 | **Axiom audit** — the transitive axiom set is a subset of `{propext, Classical.choice, Quot.sound}` | `sorry`, new axioms, `native_decide`, and every other escape hatch that leaves a trace in the kernel |
| 5 | **Provenance** — the canonical constant really comes from `Statements/<id>.lean`, and the submitted constant really comes from the submitted module | Shadowing the statement; claiming a lemma someone else already proved |

Step 3 is the one that matters. A verifier that only asks "does it compile?" accepts
`∀ n, Even n → Even (n * (n+1))` as a proof of `∀ n, Even (n * (n+1))` — both are true
theorems with real proofs, and only one of them is the theorem that was posted. The
canonical type is **never** read out of the submission; it is resolved by name from
`Statements/`, in a file the verifier generates.

### The verdict

Both verifiers emit the same JSON. Exit code is `0` for green, `1` for red.

```json
{
  "schema": "conject.verdict.v1",
  "verdict": "green",
  "reason": "ok",
  "detail": "all checks passed",
  "kind": "lean",
  "statement_id": "S001",
  "submission": "Submissions/S001/AliceDirect.json",
  "decl": "Submissions.S001.AliceDirect.proof",
  "axioms": ["Classical.choice", "Quot.sound", "propext"],
  "elaborated_term_hash": "sha256:9fbd68b771ac68ef…",
  "statement_hash": "sha256:9d79b8c029b82e35…",
  "term_hash_kind": "conject-normalized-v1",
  "checks": {
    "manifest":         { "ok": true, "detail": "" },
    "static_policy":    { "ok": true, "detail": "" },
    "build":            { "ok": true, "detail": "" },
    "anti_restatement": { "ok": true, "detail": "example : Statements.S001.statement := @Submissions.S001.AliceDirect.proof" },
    "no_new_axioms":    { "ok": true, "detail": "" },
    "axioms":           { "ok": true, "detail": "['Classical.choice', 'Quot.sound', 'propext'] ⊆ …" }
  },
  "toolchain": { "lean_toolchain": "leanprover/lean4:v4.33.0", "mathlib_rev": "db584cd…" },
  "timings_sec": { "build": 5.7, "anti_restatement": 7.3, "audit": 3.8, "total": 16.8 },
  "timestamp": "2026-08-17T00:14:33Z"
}
```

The five load-bearing fields are `verdict`, `reason`, `axioms`, `decl`, and
`elaborated_term_hash`. Everything else is diagnostics. `checks` always carries the full
picture: a submission can be red for several independent reasons at once, and `reason`
names only the first one that fired.

**`reason` values.** Green: `ok`. Red: `bad_manifest`, `unknown_statement`,
`missing_source`, `statement_id_mismatch`, `forbidden_syntax`, `build_failed`,
`restatement`, `shadowed_statement`, `provenance`, `sorry`, `native_decide`,
`disallowed_axiom`, `audit_failed`, `timeout`, `verifier_error`. Certificates add
`missing_witness`, `sandbox_unavailable`, `checker_error`, `checker_protocol`,
`invalid_witness`, `fixture_unavailable`, `fixture_mismatch`, `missing_dependency`.

### `elaborated_term_hash`

A SHA-256 over a normalized serialization of the elaborated proof term, used downstream
to tell independent proofs apart from copies. Normalization drops everything the kernel
does not care about — binder names, binder info, `mdata` — renames universe parameters
to their positional index, and **inlines the submitter's own auxiliary declarations**,
so that renaming your helper lemmas does not buy you a fresh hash. Constants from
Mathlib, core, and `Commons` stay opaque: shared vocabulary is exactly what should make
two proofs compare equal.

The repo's self-test asserts that the two distinct green proofs of S001 hash
differently, so the field is known to discriminate rather than trivially collide.

This is a syntactic fingerprint, not a semantic identity. Equal hashes mean the same
proof; different hashes mean the proofs differ somewhere, which is not the same as
proving they are mathematically independent.

---

## You do not push here

Almost nothing in this repository is written by hand. The Jig API writes it for you, so
contributing needs no access to this repo at all:

| what | written when |
|---|---|
| `Statements/<label>.lean` | you `POST /api/statements` (or `/api/problems`) with a `verifier_id` |
| `Submissions/<label>/<artifact-id>.json` and the Lean source it names | you `POST /api/artifacts` with `module`, `decl` and `source` |

Both are committed before CI is dispatched, and a submission's manifest and source land in
a **single** commit, because a manifest pointing at a file that is not there yet is exactly
the `missing_source` red the arrangement exists to prevent. If the commit fails, the
dispatch is skipped rather than firing at a path that does not exist.

Canonical statements are **write-once**. Every green verdict recorded under a label is a
claim about the exact type in that file, so nothing overwrites one: a different proposition
means a different label.

The files checked in by hand are the harness: `Commons/`, `Verify/`, `scripts/`, the
workflow, and the `S001` / `C001` examples the self-test runs against.

## Layout

```
Commons/        curated shared definitions; submissions may import these
Statements/     canonical statements — one `abbrev statement` plus a `sorry`-ed `target`
Submissions/    contributed Lean proofs, each with a JSON manifest
Certificates/   non-Lean problems: a problem-owned checker plus witness submissions
Verify/         the verifier's own Lean metaprograms (trusted, not importable)
scripts/        the drivers
```

### Why submissions may not import `Statements/`

`Statements/<id>.lean` holds two things:

```lean
abbrev statement : Prop := ∀ n : ℕ, Even (n * (n + 1))   -- the canonical type
theorem target : statement := sorry                       -- the open target
```

A submission that could import this could write `def proof := target` and inherit the
`sorry`. So submissions state their own theorem, in their own words, and the verifier
generates the bridge:

```lean
import Statements.S001
import Submissions.S001.AliceDirect
import Verify.Guard

#conject_provenance Statements.S001.statement "Statements.S001"
#conject_provenance Submissions.S001.AliceDirect.proof "Submissions.S001.AliceDirect"

example : Statements.S001.statement := @Submissions.S001.AliceDirect.proof
```

`@` forces every argument explicit, so the elaborated type is exactly the declaration's
type — no implicit-argument wiggle room. Naming the canonical type rather than pasting
its text is deliberate: a pasted type could be subtly edited, whereas a name plus a
provenance check cannot resolve to anything but the reviewed statement. A submission
that tries to declare `Statements.S001.statement` itself fails at import time with
`environment already contains …`, which the driver reports as `shadowed_statement`.

---

## Running it

```bash
lake exe cache get                     # download Mathlib oleans, never compile them
lake build

./scripts/verify.sh --submission Submissions/S001/AliceDirect.json --out verdict.json
python3 scripts/selftest.py            # every example, checked against its `expect`
```

`verify.sh` dispatches on the manifest's `kind` and wraps the driver in a watchdog, so a
wedged verifier still produces a red verdict rather than hanging.

### Submission manifests

```json
{
  "schema": "conject.submission.v1",
  "kind": "lean",
  "statement_id": "S001",
  "module": "Submissions.S001.AliceDirect",
  "decl": "Submissions.S001.AliceDirect.proof",
  "author": "alice",
  "expect": "green"
}
```

`expect` is optional and only used by the self-test; it is ignored during verification.

---

## The certificate path

Some problems are settled by a witness rather than a proof term. Those live in
`Certificates/<id>/` as a **problem-owned checker script** plus a `spec.json` of
resource limits. `scripts/verify_cert.py` runs the checker on the witness and emits the
same verdict shape, so consumers never branch on submission kind.

The checker prints exactly one line:

```
CONJECT_CERT: {"ok": true, "reason": "…", "canonical": "…"}
```

`canonical` is the witness reduced to a normal form **by the checker**, and its hash
becomes `elaborated_term_hash` — so two submissions of the same witness (up to whatever
symmetry the problem has) deduplicate. In `C001` the canonical form sorts the triple, so
permutations of one solution collapse to one hash.

The checker runs with an `RLIMIT_CPU` and wall-clock cap, an address-space cap, an
output-size cap, its own session, a scratch cwd holding only a copy of the witness, and
an environment built from scratch with `env -i`.

Network isolation is attempted three ways, in order, and each one is **probed against
`/bin/true` rather than assumed**:

1. an unprivileged user namespace, `unshare --net --map-root-user`;
2. a root network namespace via passwordless `sudo`, dropping straight back to the
   calling uid with `setpriv` — only `unshare` gets root, and only long enough to create
   the empty namespace;
3. macOS `sandbox-exec` with a `deny network*` profile.

Route 1 is the clean one and is what runs on most Linux hosts. It does *not* work on
GitHub's Ubuntu runners, which ship an AppArmor policy denying unprivileged user
namespaces, so CI takes route 2. The verdict records which one was used in
`network_isolation`. If none is available the run is refused rather than silently
downgraded — set `CONJECT_ALLOW_NO_NETNS=1` to override, locally only.

The trust boundary: the **checker** is repo-owned and reviewed like a canonical
statement; the **witness** is untrusted. The sandbox protects the runner from a checker
bug being driven by a hostile witness, which is the realistic failure mode.

### Fixtures, shared code and live lookups (`conject.certificate.v2`)

A checker that decides a claim about the sky needs data from outside the repo: a
planetary ephemeris, an observatory list, a catalog row. A v2 `spec.json` names each one
and the driver materialises it **before the sandbox closes**, then records what it used:

```json
{
  "requires": ["numpy", "scipy", "jplephem"],
  "code": ["../_shared/astro_cert.py", "../_shared/skyfit.py"],
  "fixtures": [
    { "name": "de440s.bsp", "sha256": "c1c7…", "url": "https://naif.jpl.nasa.gov/…/de440s.bsp" },
    { "name": "ObsCodes.html", "sha256": "5845…", "path": "_fixtures/ObsCodes-2026-10-18.html" },
    { "name": "gaia.json", "live": "gaia_dr3_source", "key": "source_id" }
  ],
  "params": { "e_min": 1.02, "margin_sigma": 3.0 }
}
```

* `requires` are Python packages, pinned in `Certificates/requirements.txt` and installed
  by CI; the driver refuses to run if one does not import (`missing_dependency`).
* `code` are shared modules under `Certificates/`, copied flat into the scratch dir.
  `statement_hash` covers the checker, the spec and the code together, so a threshold
  change is a different problem.
* A fixture with a `url` is downloaded once into `.conject/fixtures/<sha256>` and
  checked against its hash every run (`fixture_mismatch` if the upstream file changed);
  one with a `path` is vendored under `Certificates/`; one with `live` is a catalog row
  fetched by a key read out of the witness, with a fixed query. The verdict's `fixtures`
  list says which route each took and, for a live lookup, when it was fetched.
* `params` are the problem's thresholds. The checker reads `spec.json` from its cwd.

A checker may also return `"measurement": {…}` on its `CONJECT_CERT:` line: fitted
elements, residuals, probabilities. It is copied into the verdict whole, so a reader
judges the green on the numbers rather than on the word.

### The astronomical certificates

Six checkers under `Certificates/Astro*` back the searches on jig.so/astro. Three fit an
orbit to MPC astrometry under full planetary perturbations (`_shared/skyfit.py`: DE440s,
DOP853, iterative outlier rejection, covariance-propagated element errors) and decide
on the fitted barycentric elements: a fourth interstellar object (`AstroIso`), a new
Sedna-like object (`AstroSednaLike`), a direct detection of Planet Nine
(`AstroPlanetNineDetection`). Two take a Gaia DR3 star and decide bound or unbound
under MWPotential2014 with a Monte Carlo over the quoted errors, checking the witness
against a live catalog lookup (`_shared/galkin.py`): arriving from intergalactic space
(`AstroIntergalacticStar`), thrown out of the disk by an explosion (`AstroEjectedStar`,
which also integrates the orbit backward and refuses a Galactic-centre origin). One
recomputes a clustering statistic on a pinned MPC snapshot
(`AstroPlanetNineClustering`).

Their self-test examples are real where a real object can be red for the right reason
(2I/Borisov, Sedna, S5-HVS1, US 708), and the green example is synthetic and says so in
its manifest (`_shared/synth.py`): a real object that satisfies a search is, by
construction, one the literature already has, and every checker refuses those by name
(`params.known` on the stellar searches, the known interstellar objects by orbit, the
pinned MPC snapshot for the distant ones). The list is a backstop; the prior-art search
in the contributing guide is the check. These checkers take minutes and are meant for
the heavy lane.

---

## CI

`.github/workflows/verify.yml` runs on `pull_request`, on pushes to `main`, and on
`workflow_dispatch` with `statement_id` / `submission` / `ref` inputs.

* Hard 20-minute job timeout. The driver's own budget is 15 minutes, so it writes a red
  `timeout` verdict before the runner kills it, and an `if: always()` step synthesizes
  one if even that fails. A timeout is never a hang and never an ambiguous result.
* Mathlib oleans are cached on `lean-toolchain` + `lake-manifest.json`; the project's own
  build output is cached on the source hashes as well. Mathlib is downloaded, never
  compiled.
* Every run uploads its verdicts and its generated check files as an artifact, and
  writes a verdict table to the job summary.
* The build step is deliberately **not** `lake build`. `Statements/` holds contributor
  content written by the API, so one statement that does not compile would otherwise fail
  the step and block verification for every other problem. The driver builds the specific
  statement and submission it needs, so a broken statement surfaces as `build_failed` on
  that problem's own artifacts and nowhere else.

---

## Threat model, and what is *not* covered

The kernel is the trust anchor. Steps 3 and 4 are sound against anything that reaches
the kernel, which is why `sorry` and `native_decide` are caught by the axiom audit no
matter how they are spelled — the static scan in step 1 is a convenience, not the
argument.

The gap is elaboration-time code. A submission that runs arbitrary metaprograms could in
principle call `addDeclWithoutChecking` and install a declaration the kernel never saw.
Step 1 closes this by refusing metaprogramming outright (`elab`, `macro`, `syntax`,
`run_cmd`, `#eval`, `initialize`, `unsafe`, imports of `Lean`/`Qq`). That is a syntactic
defense, and the principled fix is to replay the finished environment through
[`lean4checker`](https://github.com/leanprover/lean4checker), which re-checks every
declaration from scratch in a fresh kernel. That is the intended next hardening step and
is not yet wired in.

Two smaller things worth stating plainly:

* A submission may legitimately be a thin alias for a Mathlib lemma. Provenance confirms
  the declaration is the submitter's; it does not judge originality. The proof-term hash
  is what makes that visible downstream.
* Definitional equality, not syntactic equality, is the bar in step 3. That is the
  correct notion of "proved the same theorem" in dependent type theory, and it is the
  same bar Lean itself uses.

---

## Pinning

`lean-toolchain` and `lake-manifest.json` are both committed and are the whole
reproducibility story: `leanprover/lean4:v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0`). Every verdict records both,
so an old verdict can always be re-derived.

## License

Apache 2.0, matching Mathlib. See [LICENSE](LICENSE).
