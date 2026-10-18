"""The checker protocol, shared by the astronomical certificates.

A checker calls `run(decide)`. `decide(witness, spec)` returns (ok, reason,
canonical, measurement) or raises WitnessError; everything else is a checker
bug and exits non-zero so the driver reports `checker_error` rather than a
verdict about the witness.
"""

from __future__ import annotations

import json
import sys
import traceback

MAX_WITNESS_BYTES = 4 << 20


class WitnessError(ValueError):
    pass


def emit(ok: bool, reason: str, canonical: str = "", measurement: dict | None = None) -> None:
    payload = {"ok": ok, "reason": reason, "canonical": canonical}
    if measurement is not None:
        payload["measurement"] = measurement
    print("CONJECT_CERT: " + json.dumps(payload, sort_keys=True, default=_plain))
    sys.exit(0)


def _plain(x):
    """numpy scalars and arrays, without importing numpy here."""
    if hasattr(x, "tolist"):
        return x.tolist()
    if hasattr(x, "item"):
        return x.item()
    raise TypeError(f"not serialisable: {type(x).__name__}")


def load() -> tuple[dict, dict]:
    spec = json.load(open("spec.json"))
    raw = open(sys.argv[1], "rb").read()
    if len(raw) > MAX_WITNESS_BYTES:
        emit(False, f"witness larger than {MAX_WITNESS_BYTES} bytes")
    try:
        doc = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as e:
        emit(False, f"witness must be UTF-8 JSON: {e}")
    if not isinstance(doc, dict):
        emit(False, "witness must be a JSON object")
    return doc, spec


def run(decide) -> None:
    doc, spec = load()
    try:
        ok, reason, canonical, measurement = decide(doc, spec)
    except WitnessError as e:
        emit(False, str(e))
    except Exception as e:  # noqa: BLE001
        # Shared engines raise their own WitnessError class; treat any exception
        # whose class is so named as the witness's fault, everything else as ours.
        if type(e).__name__ == "WitnessError":
            emit(False, str(e))
        traceback.print_exc()
        sys.exit(3)
    emit(ok, reason, canonical, measurement)


def num(doc: dict, key: str, lo: float | None = None, hi: float | None = None, required: bool = True):
    v = doc.get(key)
    if v is None:
        if required:
            raise WitnessError(f"{key} is required")
        return None
    if isinstance(v, bool) or not isinstance(v, (int, float)):
        raise WitnessError(f"{key} must be a number")
    v = float(v)
    if v != v or v in (float("inf"), float("-inf")):
        raise WitnessError(f"{key} must be finite")
    if lo is not None and v < lo:
        raise WitnessError(f"{key} must be at least {lo}")
    if hi is not None and v > hi:
        raise WitnessError(f"{key} must be at most {hi}")
    return v
