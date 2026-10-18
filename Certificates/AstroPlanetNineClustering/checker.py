#!/usr/bin/env python3
"""AstroPlanetNineClustering: a recomputation, not a search.

The witness names a selection of extreme TNOs from the pinned MPC snapshot and a
Rayleigh statistic over their longitudes of perihelion. The checker reruns the
selection and the statistic and accepts the witness only when both reproduce.
What the number means is for the statement to say; this only makes it a fact
about a named snapshot that anyone can repeat.
"""

import cmath
import math

import astro_cert
from astro_cert import WitnessError


def read_snapshot(path):
    rows = {}
    for line in open(path, encoding="utf-8", errors="replace"):
        if len(line) < 105 or not line[0:7].strip():
            continue
        try:
            w = float(line[37:46]); node = float(line[48:57]); inc = float(line[59:68])
            e = float(line[70:79]); a = float(line[92:103])
        except ValueError:
            continue
        rows[line[0:7].strip()] = {"a": a, "e": e, "q": a * (1 - e), "i": inc, "varpi": (w + node) % 360.0}
    return rows


def rayleigh(angles_deg):
    n = len(angles_deg)
    z = sum(cmath.exp(1j * math.radians(x)) for x in angles_deg)
    R = abs(z) / n
    zz = n * R * R
    # Rayleigh with the small-sample correction (Zar 1999).
    p = math.exp(-zz) * (1 + (2 * zz - zz * zz) / (4 * n)
                         - (24 * zz - 132 * zz ** 2 + 76 * zz ** 3 - 9 * zz ** 4) / (288 * n * n))
    return n, R, min(max(p, 0.0), 1.0), math.degrees(cmath.phase(z)) % 360.0


def decide(doc, spec):
    p = spec["params"]
    a_min = astro_cert.num(doc, "a_min_au", *p["a_min_allowed"])
    q_min = astro_cert.num(doc, "q_min_au", *p["q_min_allowed"])
    exclude = doc.get("exclude", [])
    if not isinstance(exclude, list) or len(exclude) > p["max_excluded"]:
        raise WitnessError(f"exclude must be a list of at most {p['max_excluded']} entries")
    excluded = {}
    for x in exclude:
        if not isinstance(x, dict) or not isinstance(x.get("designation"), str) or not isinstance(x.get("reason"), str):
            raise WitnessError("each exclude entry is {designation, reason}")
        excluded[x["designation"].strip()] = x["reason"].strip()[:200]
    claimed = doc.get("designations")
    if not isinstance(claimed, list) or not all(isinstance(d, str) for d in claimed):
        raise WitnessError("designations must be a list of packed MPC designations")
    rows = read_snapshot("Distant.txt")
    for d in excluded:
        if d not in rows:
            raise WitnessError(f"excluded designation {d} is not in the snapshot")
    selected = sorted(d for d, r in rows.items() if r["a"] >= a_min and r["q"] >= q_min and d not in excluded)
    if len(selected) < 3:
        raise WitnessError("the selection picks fewer than three objects")
    if sorted(d.strip() for d in claimed) != selected:
        missing = sorted(set(selected) - {d.strip() for d in claimed})
        extra = sorted({d.strip() for d in claimed} - set(selected))
        return False, f"selection does not reproduce: missing {missing[:10]}, extra {extra[:10]}", "", None
    n, R, pv, mean = rayleigh([rows[d]["varpi"] for d in selected])
    got = {"n": n, "mean_resultant_length": R, "p_rayleigh": pv, "mean_longitude_of_perihelion_deg": mean,
           "a_min_au": a_min, "q_min_au": q_min, "excluded": excluded, "designations": selected,
           "snapshot": p["snapshot"]}
    tol = p["tolerance"]
    cn = astro_cert.num(doc, "n", 1)
    cR = astro_cert.num(doc, "mean_resultant_length", 0, 1)
    cp = astro_cert.num(doc, "p_rayleigh", 0, 1)
    cm = astro_cert.num(doc, "mean_longitude_of_perihelion_deg", 0, 360)
    canonical = f"AstroPlanetNineClustering:{p['snapshot']}:a>={a_min:g}:q>={q_min:g}:excl=" + ",".join(sorted(excluded))
    if int(cn) != n:
        return False, f"n = {n}, witness says {int(cn)}", canonical, got
    if abs(cR - R) > tol["R"]:
        return False, f"mean resultant length = {R:.4f}, witness says {cR:.4f}", canonical, got
    if abs(cp - pv) > tol["p"]:
        return False, f"Rayleigh p = {pv:.4f}, witness says {cp:.4f}", canonical, got
    if abs((cm - mean + 180) % 360 - 180) > tol["mean_deg"]:
        return False, f"mean longitude of perihelion = {mean:.1f}, witness says {cm:.1f}", canonical, got
    return True, f"n = {n}, R = {R:.4f}, Rayleigh p = {pv:.4f}, mean varpi = {mean:.1f} deg, reproduced from the snapshot", canonical, got


if __name__ == "__main__":
    astro_cert.run(decide)
