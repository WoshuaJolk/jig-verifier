"""A null result in a fixed form: the engine behind the archive-null statements.

A search that found nothing is progress only when it says exactly where it
looked, when, how deep, and how it knows how deep. The witness carries all of
that as numbers: a sky region, epochs, a band, an injection-recovery table, at
least one control run, and every candidate it raised together with the reason
each was refuted. The checker cannot re-reduce the images; what it does is make
the null repeatable and consistent. It recomputes the area, the 50 and 90
percent completeness depths from the injections, refuses a curve that is not
monotone, a claimed depth the injections do not reproduce, a candidate left
standing, and a region or depth the search cannot bear on. A green here is one
dead route on the problem's ledger, nothing more.
"""

from __future__ import annotations

import hashlib
import json
import math

from astro_cert import WitnessError, num

DEG2_SPHERE = 4 * math.pi * (180 / math.pi) ** 2
REGION_TYPES = ("cone", "polygon", "corridor", "allsky")
METHODS = ("pixel", "catalog")
CONTROL_KINDS = ("reversed_rate", "scrambled", "shifted_aperture", "time_reversed", "shifted_night", "other")


def _str(doc: dict, key: str, max_len: int, required: bool = True) -> str | None:
    v = doc.get(key)
    if v is None:
        if required:
            raise WitnessError(f"{key} is required")
        return None
    if not isinstance(v, str) or not v.strip() or len(v) > max_len:
        raise WitnessError(f"{key} must be a non-empty string of at most {max_len} characters")
    return v.strip()


def _unit(a: float, d: float):
    a, d = math.radians(a), math.radians(d)
    return (math.cos(d) * math.cos(a), math.cos(d) * math.sin(a), math.sin(d))


def _angle(u, v) -> float:
    return math.acos(max(-1.0, min(1.0, u[0] * v[0] + u[1] * v[1] + u[2] * v[2])))


def cone_area_deg2(radius_deg: float) -> float:
    return 2 * math.pi * (1 - math.cos(math.radians(radius_deg))) * (180 / math.pi) ** 2


def polygon_area_deg2(vertices: list[list[float]]) -> float:
    """Spherical polygon area by l'Huilier over a fan from the first vertex."""
    us = [_unit(a, d) for a, d in vertices]
    total = 0.0
    for k in range(1, len(us) - 1):
        a = _angle(us[0], us[k]); b = _angle(us[k], us[k + 1]); c = _angle(us[k + 1], us[0])
        if max(a, b, c) >= math.pi / 2:
            raise WitnessError("polygon edges must be shorter than 90 degrees; split a large region into pieces")
        s = (a + b + c) / 2
        inner = math.tan(s / 2) * math.tan((s - a) / 2) * math.tan((s - b) / 2) * math.tan((s - c) / 2)
        total += 4 * math.atan(math.sqrt(max(inner, 0.0)))
    return total * (180 / math.pi) ** 2


def read_region(doc: dict, p: dict) -> tuple[dict, float, str]:
    region = doc.get("region")
    if not isinstance(region, dict) or region.get("type") not in REGION_TYPES:
        raise WitnessError(f"region.type must be one of {', '.join(REGION_TYPES)}")
    t = region["type"]
    if t == "allsky":
        return {"type": t}, DEG2_SPHERE, "the whole sky"
    if t == "cone":
        ra = num(region, "ra_deg", 0, 360); dec = num(region, "dec_deg", -90, 90)
        rad = num(region, "radius_deg", 1e-4, 90)
        return {"type": t, "ra_deg": ra, "dec_deg": dec, "radius_deg": rad}, cone_area_deg2(rad), \
            f"a {rad:g} deg cone at RA {ra:.3f} Dec {dec:+.3f}"
    if t == "polygon":
        verts = region.get("vertices")
        if not isinstance(verts, list) or not (3 <= len(verts) <= 64):
            raise WitnessError("region.vertices must list 3 to 64 [ra_deg, dec_deg] pairs")
        clean = []
        for v in verts:
            if not (isinstance(v, list) and len(v) == 2 and all(isinstance(x, (int, float)) and not isinstance(x, bool) for x in v)):
                raise WitnessError("each polygon vertex is [ra_deg, dec_deg]")
            if not (0 <= v[0] <= 360 and -90 <= v[1] <= 90):
                raise WitnessError("polygon vertex out of range")
            clean.append([float(v[0]), float(v[1])])
        return {"type": t, "vertices": clean}, polygon_area_deg2(clean), f"a {len(clean)}-vertex polygon"
    cones = region.get("cones")
    if not isinstance(cones, list) or not (1 <= len(cones) <= int(p.get("max_corridor_cones", 500))):
        raise WitnessError(f"region.cones must list 1 to {p.get('max_corridor_cones', 500)} cones")
    clean = []
    area = 0.0
    for c in cones:
        if not isinstance(c, dict):
            raise WitnessError("each corridor cone is {jd_utc, ra_deg, dec_deg, radius_deg}")
        jd = num(c, "jd_utc", 2400000, 2500000)
        ra = num(c, "ra_deg", 0, 360); dec = num(c, "dec_deg", -90, 90); rad = num(c, "radius_deg", 1e-4, 30)
        clean.append({"jd_utc": jd, "ra_deg": ra, "dec_deg": dec, "radius_deg": rad})
        area += cone_area_deg2(rad)
    return {"type": t, "cones": clean}, area, f"a corridor of {len(clean)} cones (areas summed, overlaps not removed)"


def read_epochs(doc: dict, p: dict) -> list[dict]:
    ep = doc.get("epochs")
    if not isinstance(ep, list) or not (1 <= len(ep) <= int(p.get("max_epochs", 2000))):
        raise WitnessError(f"epochs must list 1 to {p.get('max_epochs', 2000)} {{start_jd_utc, end_jd_utc}} intervals")
    out = []
    for e in ep:
        if not isinstance(e, dict):
            raise WitnessError("each epoch is {start_jd_utc, end_jd_utc}")
        a = num(e, "start_jd_utc", 2400000, 2500000); b = num(e, "end_jd_utc", 2400000, 2500000)
        if b < a:
            raise WitnessError("an epoch ends before it starts")
        out.append({"start_jd_utc": a, "end_jd_utc": b})
    out.sort(key=lambda e: e["start_jd_utc"])
    return out


def read_injections(doc: dict, p: dict, unit: str) -> list[dict]:
    inj = doc.get("injections")
    min_bins = int(p.get("min_injection_bins", 3))
    if not isinstance(inj, list) or len(inj) < min_bins or len(inj) > 200:
        raise WitnessError(f"injections must list {min_bins} to 200 bins of {{{unit}, injected, recovered}}")
    out = []
    for b in inj:
        if not isinstance(b, dict):
            raise WitnessError(f"each injection bin is {{{unit}, injected, recovered}}")
        x = num(b, unit, -50, 1e6)
        n = num(b, "injected", 1, 1e7); k = num(b, "recovered", 0, 1e7)
        if n != int(n) or k != int(k):
            raise WitnessError("injected and recovered are counts")
        if k > n:
            raise WitnessError("more recovered than injected")
        if n < int(p.get("min_injected_per_bin", 50)):
            raise WitnessError(f"each injection bin needs at least {p.get('min_injected_per_bin', 50)} injected sources")
        out.append({unit: x, "injected": int(n), "recovered": int(k), "fraction": k / n})
    out.sort(key=lambda b: b[unit])
    if len({b[unit] for b in out}) != len(out):
        raise WitnessError("injection bins must have distinct brightness values")
    return out


def completeness_depth(bins: list[dict], unit: str, level: float, tol: float) -> float | None:
    """Brightness at which the recovered fraction crosses `level`, by linear
    interpolation. Magnitudes fade with increasing value, fluxes the other way;
    the curve must be monotone in the matching sense to within `tol`."""
    xs = [b[unit] for b in bins]
    fs = [b["fraction"] for b in bins]
    decreasing = unit == "mag"
    for a, b in zip(fs, fs[1:]):
        if decreasing and b > a + tol:
            raise WitnessError("recovered fraction rises with magnitude: the injection curve is not monotone")
        if not decreasing and b < a - tol:
            raise WitnessError("recovered fraction falls with flux: the injection curve is not monotone")
    if decreasing:
        if fs[0] < level or fs[-1] >= level:
            return None
        for k in range(len(fs) - 1):
            if fs[k] >= level > fs[k + 1]:
                return xs[k] + (fs[k] - level) / (fs[k] - fs[k + 1]) * (xs[k + 1] - xs[k])
    else:
        if fs[-1] < level or fs[0] >= level:
            return None
        for k in range(len(fs) - 1):
            if fs[k] < level <= fs[k + 1]:
                return xs[k] + (level - fs[k]) / (fs[k + 1] - fs[k]) * (xs[k + 1] - xs[k])
    return None


def read_controls(doc: dict, p: dict) -> list[dict]:
    ctl = doc.get("controls")
    if not isinstance(ctl, list) or not ctl or len(ctl) > 50:
        raise WitnessError("controls must list at least one {kind, trials, false_positives} run")
    out = []
    for c in ctl:
        if not isinstance(c, dict) or c.get("kind") not in CONTROL_KINDS:
            raise WitnessError(f"each control is {{kind, trials, false_positives}} with kind one of {', '.join(CONTROL_KINDS)}")
        n = num(c, "trials", 1, 1e9); k = num(c, "false_positives", 0, 1e9)
        if k > n:
            raise WitnessError("more false positives than control trials")
        out.append({"kind": c["kind"], "trials": int(n), "false_positives": int(k)})
    return out


def read_candidates(doc: dict, p: dict) -> list[dict]:
    cands = doc.get("candidates", [])
    if not isinstance(cands, list) or len(cands) > int(p.get("max_candidates", 200)):
        raise WitnessError(f"candidates must be a list of at most {p.get('max_candidates', 200)} entries")
    out = []
    for c in cands:
        if not isinstance(c, dict):
            raise WitnessError("each candidate is {id, ra_deg, dec_deg, jd_utc, refuted_by}")
        cid = _str(c, "id", 60)
        ra = num(c, "ra_deg", 0, 360); dec = num(c, "dec_deg", -90, 90); jd = num(c, "jd_utc", 2400000, 2500000)
        why = c.get("refuted_by")
        out.append({"id": cid, "ra_deg": ra, "dec_deg": dec, "jd_utc": jd,
                    "refuted_by": why.strip()[:300] if isinstance(why, str) and why.strip() else None})
    return out


def decide_null(doc: dict, spec: dict, label: str):
    p = spec["params"]
    search = _str(doc, "search", 80)
    method = doc.get("method")
    if method not in METHODS:
        raise WitnessError("method must be pixel or catalog")
    src = doc.get("source")
    if not isinstance(src, dict):
        raise WitnessError("source must be {survey, archive_url, station?}")
    survey = _str(src, "survey", 80)
    url = _str(src, "archive_url", 300)
    if not url.startswith("https://"):
        raise WitnessError("source.archive_url must be an https URL")
    station = _str(src, "station", 3, required=False)
    band = _str(doc, "band", 12)
    unit = doc.get("depth_unit", "mag")
    if unit not in ("mag", "mjy"):
        raise WitnessError("depth_unit must be mag or mjy")
    region, area, region_text = read_region(doc, p)
    if area > float(p.get("max_region_deg2", DEG2_SPHERE)) + 1e-6:
        raise WitnessError("region larger than the sky")
    epochs = read_epochs(doc, p)
    rate = doc.get("rate_range_arcsec_hr")
    if rate is not None:
        if not (isinstance(rate, list) and len(rate) == 2 and all(isinstance(x, (int, float)) and not isinstance(x, bool) for x in rate)
                and 0 <= rate[0] <= rate[1]):
            raise WitnessError("rate_range_arcsec_hr is [low, high]")
        rate = [float(rate[0]), float(rate[1])]
    bins = read_injections(doc, p, unit)
    controls = read_controls(doc, p)
    candidates = read_candidates(doc, p)
    claimed = num(doc, "depth_50", -50, 1e6)

    key = json.dumps({"region": region, "epochs": epochs, "band": band, "rate": rate, "survey": survey, "method": method},
                     sort_keys=True, separators=(",", ":"))
    canonical = f"{label}:{survey}:{band}:{hashlib.sha256(key.encode()).hexdigest()[:16]}"

    tol = float(p.get("monotone_tolerance", 0.1))
    depth50 = completeness_depth(bins, unit, 0.5, tol)
    depth90 = completeness_depth(bins, unit, 0.9, tol)
    trials = sum(c["trials"] for c in controls)
    fps = sum(c["false_positives"] for c in controls)
    span = (epochs[0]["start_jd_utc"], max(e["end_jd_utc"] for e in epochs))
    measurement = {
        "search": search, "survey": survey, "method": method, "band": band, "depth_unit": unit, "station": station,
        "region": region, "region_text": region_text, "area_deg2": area, "epochs": epochs,
        "first_jd_utc": span[0], "last_jd_utc": span[1], "rate_range_arcsec_hr": rate,
        "injected_total": sum(b["injected"] for b in bins), "depth_50": depth50, "depth_90": depth90,
        "control_trials": trials, "control_false_positives": fps,
        "candidates": len(candidates), "archive_url": url,
        "route": {"label": f"{search} ({survey}, {band})", "kind": "archive_null"},
    }
    if depth50 is None:
        return False, "the injection bins do not bracket 50 percent recovery, so the depth is not measured", canonical, measurement
    dtol = float(p.get("depth_tolerance", 0.1))
    if abs(claimed - depth50) > dtol:
        return False, f"the injections give a 50 percent depth of {depth50:.2f} {unit}, the witness claims {claimed:.2f}", canonical, measurement
    if trials < int(p.get("min_control_trials", 10)):
        return False, f"only {trials} control trials; at least {p.get('min_control_trials', 10)} are needed to measure the false-positive rate", canonical, measurement
    standing = [c["id"] for c in candidates if not c["refuted_by"]]
    if standing:
        return False, f"candidate(s) {standing[:5]} carry no refutation; a search with a live candidate is not a null", canonical, measurement
    if unit == "mag" and depth50 < float(p.get("min_depth_50_mag", -99)):
        return False, (f"50 percent depth {depth50:.2f} mag is shallower than {p['min_depth_50_mag']} mag, too shallow to bear on "
                       f"{p.get('target', 'this search')}"), canonical, measurement
    d90 = f", 90 percent at {depth90:.2f}" if depth90 is not None else ""
    return True, (f"{search}: nothing found in {region_text} ({area:.3g} deg2), {len(epochs)} epoch interval(s) between JD "
                  f"{span[0]:.1f} and {span[1]:.1f}, {band} band, 50 percent complete at {depth50:.2f} {unit}{d90} from "
                  f"{measurement['injected_total']} injections; controls {fps}/{trials} false positives; {len(candidates)} "
                  f"candidate(s), all refuted. A dead route at that depth"), canonical, measurement
