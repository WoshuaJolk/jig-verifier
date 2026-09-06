"""Static source policy for Lean submissions.

This is the cheap, syntactic half of the contract. It is *not* the soundness argument:
`sorry`, `native_decide`, and stray `axiom`s are all caught independently by the axiom
audit, which reads the elaborated environment and cannot be fooled by formatting. The
scan exists to reject metaprogramming outright, since a submission that can run
arbitrary elaborator code sits outside the part of Lean the kernel protects.
"""

from __future__ import annotations

import re

# Import roots a submission may use. `Commons` is the curated shared vocabulary.
ALLOWED_IMPORT_ROOTS = frozenset(
    {"Mathlib", "Batteries", "Std", "Init", "Aesop", "Plausible", "Commons"}
)

# Roots that get a specific error message because rejecting them is the point.
EXPLAINED_IMPORT_ROOTS = {
    "Statements": "canonical statements are closed with `sorry`; a submission must "
    "state its own theorem and let the verifier bridge the two",
    "Verify": "the verifier's own metaprograms are not available to submissions",
    "Submissions": "a submission may not depend on another submission",
    "Lean": "metaprogramming can add declarations without kernel checking",
    "Qq": "metaprogramming can add declarations without kernel checking",
}

# Tokens rejected anywhere in the (comment-stripped) source.
FORBIDDEN = [
    (r"\bsorry\b", "sorry"),
    (r"\bsorryAx\b", "sorryAx"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bofReduceBool\b", "native_decide"),
    (r"\bofReduceNat\b", "native_decide"),
    # Not `^\s*axiom`: `section  axiom oracle : ...` put it mid-line and the
    # scan returned clean. The audit still caught it, so the red arrived with
    # the wrong reason rather than not at all.
    (r"\baxiom\b", "axiom declaration"),
    (r"\bunsafe\b", "unsafe"),
    (r"\bpartial\b", "partial"),
    (r"\bimplemented_by\b", "implemented_by"),
    (r"\bextern\b", "extern"),
    (r"^\s*macro\b", "macro"),
    (r"^\s*macro_rules\b", "macro_rules"),
    (r"^\s*syntax\b", "syntax"),
    (r"^\s*elab\b", "elab"),
    (r"^\s*elab_rules\b", "elab_rules"),
    (r"^\s*notation3?\b", "notation"),
    (r"\brun_cmd\b", "run_cmd"),
    (r"#eval\b", "#eval"),
    (r"\binitialize\b", "initialize"),
    (r"\baddDecl\b", "addDecl"),
    (r"\bskipKernelTC\b", "debug.skipKernelTC"),
    (r"set_option\s+debug\b", "set_option debug.*"),
    (r"\bregister_simp_attr\b", "register_simp_attr"),
]

_COMPILED = [(re.compile(p, re.MULTILINE), name) for p, name in FORBIDDEN]


def strip_comments(src: str) -> str:
    """Blank out `--` line comments and nested `/- -/` blocks, preserving line numbers.

    String literals are respected so that a `--` inside a string is not treated as a
    comment. Replaced characters become spaces so offsets stay meaningful.
    """
    out = list(src)
    i, n = 0, len(src)
    depth = 0
    in_str = False
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if c == "-" and nxt == "/":
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if c == "/" and nxt == "-":
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if c == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


def scan(src: str) -> list[str]:
    """Return a list of policy violations. Empty means the source is admissible."""
    clean = strip_comments(src)
    problems: list[str] = []

    for m in re.finditer(r"^\s*import\s+([A-Za-z0-9_.']+)", clean, re.MULTILINE):
        mod = m.group(1)
        root = mod.split(".")[0]
        line = clean[: m.start()].count("\n") + 1
        if root in EXPLAINED_IMPORT_ROOTS:
            problems.append(
                f"line {line}: forbidden import `{mod}` — {EXPLAINED_IMPORT_ROOTS[root]}"
            )
        elif root not in ALLOWED_IMPORT_ROOTS:
            problems.append(
                f"line {line}: import `{mod}` is outside the allowed roots "
                f"({', '.join(sorted(ALLOWED_IMPORT_ROOTS))})"
            )

    for rx, name in _COMPILED:
        m = rx.search(clean)
        if m:
            line = clean[: m.start()].count("\n") + 1
            problems.append(f"line {line}: forbidden construct `{name}`")

    return problems
