#!/usr/bin/env python3
"""Checker for Jig #398 statement 41 (Erdős #488, explicit k = 48 smooth-band witness).

Witness: one integer S (rounding denominator). The checker recomputes, with exact integer
arithmetic, a rigorous LOWER bound on H(T) = #{odd 257-smooth d <= T} and a rigorous UPPER
bound on |A| = #{257-smooth a in (T, 256T]}, T = 256^48, and accepts iff
        64 * phi(Q) * H_lo  >  Q * A_hi,      Q = product of the odd primes below 257.
By lemma (N) M(n) = |A| and lemma (F) M(m) >= H(T)*phi(Q) (see the statement's message),
this inequality implies n*M(m) > 2*m*M(n) with n = 256T, m = 2TQ.

Rounding is one-directional so every comparison is implied in the right direction:
  lower bound on a count: weights ceil(S*ln p), budget floor(S*ln x)
  upper bound on a count: weights floor(S*ln p), budget ceil(S*ln x)
Decimal.ln is correctly rounded at 60 digits; a 1e-40 pad makes floor/ceil rigorous.
Standard library only, deterministic, no clock, no randomness.
"""
import json
import sys
from decimal import Decimal, getcontext, ROUND_FLOOR, ROUND_CEILING

K = 48
getcontext().prec = 60
EPS = Decimal(10) ** -40


def emit(ok, reason, canonical=""):
    print("CONJECT_CERT: " + json.dumps(
        {"ok": ok, "reason": reason, "canonical": canonical}, sort_keys=True))
    sys.exit(0)


def ln_scaled(x, S, up):
    d = Decimal(x).ln() * S
    if up:
        return int((d + EPS).to_integral_value(rounding=ROUND_CEILING))
    return int((d - EPS).to_integral_value(rounding=ROUND_FLOOR))


def count_le(primes, S, weights_up, budget):
    """Exact number of exponent vectors e >= 0 with sum_p e_p * w_p <= budget."""
    dp = [0] * (budget + 1)
    dp[0] = 1
    for p in primes:
        w = ln_scaled(p, S, weights_up)
        for b in range(w, budget + 1):
            dp[b] += dp[b - w]
    return sum(dp)


def main():
    raw = open(sys.argv[1], "rb").read()
    if len(raw) > 64:
        emit(False, "witness too large")
    try:
        S = int(raw.decode("ascii").strip())
    except (UnicodeDecodeError, ValueError):
        emit(False, "witness must be one decimal integer S")
    if not (1000 <= S <= 50000):
        emit(False, "S must lie in [1000, 50000]")
    canonical = f"ErdosMultiplesSmoothExplicit48:k={K}"

    primes = [p for p in range(2, 257) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
    odd = primes[1:]
    Q, phi = 1, 1
    for p in odd:
        Q *= p
        phi *= p - 1
    if not (Q > 128 and 3 * Q < 16 * phi):
        emit(False, "constant checks failed (should be impossible)")

    T = 256 ** K
    H_lo = count_le(odd, S, True, ln_scaled(T, S, False))
    Psi_big_hi = count_le(primes, S, False, ln_scaled(256 * T, S, True))
    Psi_small_lo = count_le(primes, S, True, ln_scaled(T, S, False))
    A_hi = Psi_big_hi - Psi_small_lo

    lhs, rhs = 64 * phi * H_lo, Q * A_hi
    if lhs > rhs:
        emit(True, f"S={S}: 64*phi(Q)*H_lo > Q*|A|_hi, ratio floor {lhs / rhs:.6f}; "
                   f"hence n*M(m) > 2*m*M(n) for k={K}", canonical)
    emit(False, f"S={S}: bound not certified (ratio floor {lhs / rhs:.6f} <= 1); "
                f"try a larger S", canonical)


if __name__ == "__main__":
    main()
