"""Short-arc geometry for the lead statements on the astro board.

A single tracklet (one station, one night or a few) says where an object is and
how fast it moves on the sky, and nothing else. What it still decides, with no
orbit assumed: the set of topocentric distances at which a bound heliocentric
orbit can reproduce that motion. At a trial distance the object's heliocentric
tangential speed is the observed angular rate times the distance plus the
observer's own transverse speed; where that exceeds the local escape speed no
bound orbit exists. The bound set is one or more intervals in distance. The
farthest interval is the lead; the nearer ones are the ordinary objects that
would also explain the motion.

The trap this engine is built around: slow sky motion implies distance only near
opposition. Away from it a main-belt asteroid near its stationary point crawls
at the rate of a 100 AU body, and two tracklets have already been linked into an
"80 AU dwarf planet" and refuted that way. The near branch is therefore computed
every time, and a lead is refused when an inner solar system orbit reproduces
the motion.

Light time is ignored (a 100 AU body moves well under an arcsecond in the 14
hours its light takes to arrive), and so is the unknown radial speed, which can
only widen the bound set. The test is a necessary condition: a refusal is
final, an acceptance is a lead and never a detection.
"""

from __future__ import annotations

import hashlib
import math

import numpy as np

import skyfit
from skyfit import Observation, WitnessError

ARCSEC_PER_RAD = 1.0 / skyfit.ARCSEC
HOURS_PER_DAY = 24.0


# ----------------------------------------------------------------- observer

def observer_helio(eph: skyfit.Ephemeris, obscodes: dict, obscode: str, jd_utc: float, jd_tt: float) -> np.ndarray:
    """Heliocentric ICRF position of a ground station in AU, as skyfit's SkyModel builds it."""
    if obscode not in obscodes:
        raise WitnessError(f"observatory code {obscode} is not a ground station in the pinned MPC list")
    lon, rc, rs = obscodes[obscode]
    theta = skyfit.gmst_rad(jd_utc) + math.radians(lon)
    geo_date = np.array([rc * math.cos(theta), rc * math.sin(theta), rs]) * skyfit.EARTH_RADIUS_KM / skyfit.AU_KM
    geo_j2000 = skyfit.precession_matrix(jd_tt).T @ geo_date
    return np.asarray(eph.earth_helio(jd_tt)).reshape(3) + geo_j2000


def observer_state(eph: skyfit.Ephemeris, obscodes: dict, obscode: str, jd_utc: float, jd_tt: float,
                   h_days: float = 1.0 / 720) -> tuple[np.ndarray, np.ndarray]:
    """Position (AU) and velocity (AU/day) of the station, the velocity by a central
    difference over two minutes so that Earth's orbit and its rotation both count."""
    p0 = observer_helio(eph, obscodes, obscode, jd_utc, jd_tt)
    pp = observer_helio(eph, obscodes, obscode, jd_utc + h_days, jd_tt + h_days)
    pm = observer_helio(eph, obscodes, obscode, jd_utc - h_days, jd_tt - h_days)
    return p0, (pp - pm) / (2 * h_days)


# ----------------------------------------------------------------- witness

def read_tracklet(doc: dict, spec: dict) -> tuple[str, list[Observation], float]:
    p = spec.get("params", {})
    desig = doc.get("designation")
    if not isinstance(desig, str) or not skyfit.DESIGNATION_RE.match(desig):
        raise WitnessError("designation must be a short string naming the tracklet or object")
    lines = doc.get("observations")
    if not isinstance(lines, list) or not lines:
        raise WitnessError("observations must be a non-empty list of MPC 80-column lines")
    if len(lines) > int(p.get("max_observations", 60)):
        raise WitnessError(f"at most {p.get('max_observations', 60)} observations: this is a tracklet, not an arc")
    obs = []
    for ln in lines:
        if not isinstance(ln, str):
            raise WitnessError("every observation must be a string")
        obs.append(skyfit.parse_obs80(ln.rstrip("\r\n")))
    obs.sort(key=lambda o: o.jd_utc)
    if len(obs) < int(p.get("min_observations", 3)):
        raise WitnessError(f"at least {p.get('min_observations', 3)} observations are required to measure a rate")
    stations = {o.obscode for o in obs}
    if len(stations) != 1:
        raise WitnessError("a tracklet comes from one station; submit one station's observations")
    arc_days = obs[-1].jd_utc - obs[0].jd_utc
    if arc_days * HOURS_PER_DAY < float(p.get("min_arc_hours", 0.5)):
        raise WitnessError(f"the observations must span at least {p.get('min_arc_hours', 0.5)} hours")
    if arc_days > float(p.get("max_arc_days", 5.0)):
        raise WitnessError(f"the observations span {arc_days:.1f} days; a tracklet is at most {p.get('max_arc_days', 5.0)}")
    sigma = doc.get("sigma_arcsec", p.get("default_sigma_arcsec", 0.3))
    if isinstance(sigma, bool) or not isinstance(sigma, (int, float)) or not (0.02 <= float(sigma) <= 5.0):
        raise WitnessError("sigma_arcsec must be between 0.02 and 5")
    return desig, obs, float(sigma)

def read_prediction(doc: dict) -> dict | None:
    """Optional: where the object should be next, as a file the next search can fetch.
    Echoed into the measurement; the checker does not verify it."""
    pred = doc.get("prediction")
    if pred is None:
        return None
    if not isinstance(pred, dict):
        raise WitnessError("prediction must be an object {url, model, note?}")
    url = pred.get("url")
    if not isinstance(url, str) or not url.startswith("https://") or len(url) > 300:
        raise WitnessError("prediction.url must be an https URL to a downloadable position file")
    model = pred.get("model")
    if not isinstance(model, str) or not (3 <= len(model) <= 200):
        raise WitnessError("prediction.model names the propagation and its error model")
    note = pred.get("note", "")
    if not isinstance(note, str) or len(note) > 300:
        raise WitnessError("prediction.note is a string of at most 300 characters")
    return {"url": url, "model": model, "note": note}


# ----------------------------------------------------------------- motion

def linear_motion(obs: list[Observation], sigma_arcsec: float) -> dict:
    """Straight-line fit of the tracklet in the tangent plane about its mean epoch.
    Rates are arcsec per hour; the RA rate already carries cos(dec)."""
    t = np.array([o.jd_tt for o in obs])
    t0 = float(t.mean())
    th = (t - t0) * HOURS_PER_DAY
    ra = np.array([o.ra for o in obs])
    dec = np.array([o.dec for o in obs])
    dec0 = float(dec.mean())
    ra_ref = float(ra[0])
    x = ((ra - ra_ref + math.pi) % (2 * math.pi) - math.pi) * math.cos(dec0) * ARCSEC_PER_RAD
    y = (dec - dec0) * ARCSEC_PER_RAD
    A = np.vstack([np.ones_like(th), th]).T
    (x0, vx), *_ = np.linalg.lstsq(A, x, rcond=None)
    (y0, vy), *_ = np.linalg.lstsq(A, y, rcond=None)
    res = np.concatenate([x - (x0 + vx * th), y - (y0 + vy * th)])
    n = len(obs)
    dof = max(2 * n - 4, 1)
    rms = float(math.sqrt(float(res @ res) / dof)) if n > 2 else 0.0
    sig = max(rms, sigma_arcsec)
    spread = float(((th - th.mean()) ** 2).sum())
    if spread <= 0:
        raise WitnessError("all observations share one epoch")
    rate_sigma = sig / math.sqrt(spread)
    rate = math.hypot(vx, vy)
    return {
        "t0_tt": t0,
        "t0_utc": float(np.mean([o.jd_utc for o in obs])),
        "ra0": (ra_ref + (x0 / ARCSEC_PER_RAD) / math.cos(dec0)) % (2 * math.pi),
        "dec0": dec0 + y0 / ARCSEC_PER_RAD,
        "vx_arcsec_hr": float(vx),
        "vy_arcsec_hr": float(vy),
        "rate_arcsec_hr": rate,
        "rate_sigma_arcsec_hr": rate_sigma,
        "pa_deg": math.degrees(math.atan2(vx, vy)) % 360.0,
        "fit_rms_arcsec": rms,
        "arc_hours": float((t[-1] - t[0]) * HOURS_PER_DAY),
        "n_obs": n,
        "station": obs[0].obscode,
    }


# ----------------------------------------------------------------- bound set

def tangent_frame(ra: float, dec: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    u = np.array([math.cos(dec) * math.cos(ra), math.cos(dec) * math.sin(ra), math.sin(dec)])
    east = np.array([-math.sin(ra), math.cos(ra), 0.0])
    north = np.cross(u, east)
    return u, east, north


def bound_intervals(obs_pos: np.ndarray, obs_vel: np.ndarray, ra: float, dec: float,
                    vx_arcsec_hr: float, vy_arcsec_hr: float, grid: np.ndarray, factor: float) -> list[tuple[int, int]]:
    """Index intervals of `grid` (topocentric distance, AU) where the tangential
    heliocentric speed stays within `factor` times the circular speed."""
    u, east, north = tangent_frame(ra, dec)
    omega = np.array([vx_arcsec_hr, vy_arcsec_hr]) * HOURS_PER_DAY * skyfit.ARCSEC  # rad/day
    vperp = np.array([obs_vel @ east, obs_vel @ north])  # AU/day
    vt = np.linalg.norm(omega[None, :] * grid[:, None] + vperp[None, :], axis=1)
    r = np.linalg.norm(obs_pos[None, :] + grid[:, None] * u[None, :], axis=1)
    ok = vt <= factor * np.sqrt(skyfit.GM_SUN / r)
    idx = np.nonzero(ok)[0]
    if idx.size == 0:
        return []
    breaks = np.nonzero(np.diff(idx) > 1)[0]
    return [(int(seg[0]), int(seg[-1])) for seg in np.split(idx, breaks + 1)]


def helio_r(obs_pos: np.ndarray, ra: float, dec: float, delta: float) -> float:
    u, _, _ = tangent_frame(ra, dec)
    return float(np.linalg.norm(obs_pos + delta * u))


def speed_ratio(obs_pos: np.ndarray, obs_vel: np.ndarray, ra: float, dec: float,
                vx_arcsec_hr: float, vy_arcsec_hr: float, grid: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Tangential speed over circular speed, and heliocentric distance, along the grid."""
    u, east, north = tangent_frame(ra, dec)
    omega = np.array([vx_arcsec_hr, vy_arcsec_hr]) * HOURS_PER_DAY * skyfit.ARCSEC
    vperp = np.array([obs_vel @ east, obs_vel @ north])
    vt = np.linalg.norm(omega[None, :] * grid[:, None] + vperp[None, :], axis=1)
    r = np.linalg.norm(obs_pos[None, :] + grid[:, None] * u[None, :], axis=1)
    return vt / np.sqrt(skyfit.GM_SUN / r), r


def elongation_deg(obs_pos: np.ndarray, ra: float, dec: float) -> float:
    u, _, _ = tangent_frame(ra, dec)
    return math.degrees(math.acos(max(-1.0, min(1.0, float(u @ (-obs_pos)) / float(np.linalg.norm(obs_pos))))))


# ----------------------------------------------------------------- snapshot

MONTH = {**{str(k): k for k in range(1, 10)}, "A": 10, "B": 11, "C": 12}


def unpack_epoch(s: str) -> float:
    century = {"I": 1800, "J": 1900, "K": 2000}.get(s[0])
    if century is None:
        raise ValueError(s)
    year = century + int(s[1:3])
    month = MONTH[s[3]]
    day = int(s[4], 36)
    return skyfit.jd_from_ymd(year, month, float(day))


def read_mpcorb_full(path: str) -> dict[str, dict]:
    """MPCORB-format orbits with every element, for propagation rather than matching."""
    rows: dict[str, dict] = {}
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            if len(line) < 105 or not line[0:7].strip():
                continue
            try:
                epoch = unpack_epoch(line[20:25])
                M = float(line[26:35]); peri = float(line[37:46]); node = float(line[48:57])
                inc = float(line[59:68]); e = float(line[70:79]); n = float(line[80:91]); a = float(line[92:103])
            except (ValueError, KeyError, IndexError):
                continue
            if not (0 <= e < 1) or a <= 0 or n <= 0:
                continue
            # The file quotes n to four figures. Near perihelion on a Sedna-like
            # orbit that rounding is 7 arcminutes of sky, so the mean motion is
            # recomputed from a, as the propagator will recompute it.
            n_from_a = math.degrees(math.sqrt(skyfit.GM_SUN / a ** 3))
            rows[line[0:7].strip()] = {
                "a": a, "e": e, "q": a * (1 - e), "i": inc, "node": node, "peri": peri,
                "tp": epoch - M / n_from_a, "epoch": epoch,
            }
    return rows


def snapshot_neighbours(rows: dict[str, dict], obs_pos: np.ndarray, obs_vel: np.ndarray, t_tt: float,
                        ra: float, dec: float, sep_arcmin: float) -> list[dict]:
    """Snapshot objects within `sep_arcmin` of the tracklet at its epoch, with their
    predicted sky rate (two-body, with the observer moving), so the caller can also
    compare motion. At 80 AU the observer's own motion is most of the rate."""
    u, _, _ = tangent_frame(ra, dec)
    out = []
    cos_tol = math.cos(math.radians(sep_arcmin / 60.0))
    dt = 1.0 / HOURS_PER_DAY
    obs_pos2 = obs_pos + obs_vel * dt
    for d, r in rows.items():
        try:
            st = skyfit.state_from_elements(r["q"], r["e"], r["i"], r["node"], r["peri"], r["tp"], t_tt)
        except (WitnessError, ValueError, ZeroDivisionError, OverflowError):
            continue
        rho = st[:3] - obs_pos
        dist = float(np.linalg.norm(rho))
        if dist <= 0:
            continue
        if float(rho @ u) / dist < cos_tol:
            continue
        st2 = skyfit.state_from_elements(r["q"], r["e"], r["i"], r["node"], r["peri"], r["tp"], t_tt + dt)
        rho2 = st2[:3] - obs_pos2
        ra1, de1 = math.atan2(rho[1], rho[0]), math.asin(rho[2] / dist)
        ra2, de2 = math.atan2(rho2[1], rho2[0]), math.asin(rho2[2] / float(np.linalg.norm(rho2)))
        vx = ((ra2 - ra1 + math.pi) % (2 * math.pi) - math.pi) * math.cos(de1) * ARCSEC_PER_RAD
        vy = (de2 - de1) * ARCSEC_PER_RAD
        sep = math.degrees(math.acos(max(-1.0, min(1.0, float(rho @ u) / dist)))) * 60.0
        out.append({"designation": d, "sep_arcmin": sep, "vx_arcsec_hr": vx, "vy_arcsec_hr": vy,
                    "delta_au": dist, "a": r["a"], "q": r["q"], "i": r["i"]})
    out.sort(key=lambda m: m["sep_arcmin"])
    return out


def rate_matches(m: dict, motion: dict, tol_frac: float) -> bool:
    dv = math.hypot(m["vx_arcsec_hr"] - motion["vx_arcsec_hr"], m["vy_arcsec_hr"] - motion["vy_arcsec_hr"])
    return dv <= max(tol_frac * motion["rate_arcsec_hr"], 3 * motion["rate_sigma_arcsec_hr"])


# ----------------------------------------------------------------- photometry

def apparent_v(obs: list[Observation], band_offsets: dict) -> float | None:
    vs = []
    for o in obs:
        if o.mag is None or o.mag <= 0:
            continue
        off = band_offsets.get(o.band or "V")
        if off is None:
            continue
        vs.append(o.mag + off)
    return float(np.median(vs)) if vs else None


def absolute_mag(v: float, r_au: float, delta_au: float) -> float:
    return v - 5 * math.log10(r_au * delta_au)


# ----------------------------------------------------------------- the analysis

def canonical_id(label: str, obs: list[Observation]) -> str:
    h = hashlib.sha256("\n".join(sorted(o.line.rstrip() for o in obs)).encode()).hexdigest()[:16]
    return f"{label}:{obs[0].obscode}:{np.mean([o.jd_utc for o in obs]):.3f}:{h}"


def analyse(doc: dict, spec: dict, eph_path: str = "de440s.bsp", obscodes_path: str = "ObsCodes.html",
            snapshot_path: str | None = "Distant.txt") -> dict:
    """Everything a lead checker decides on. Raises WitnessError for a witness that
    cannot be measured at all; a measurable witness that fails a predicate is the
    checker's call."""
    p = spec["params"]
    desig, obs, sigma = read_tracklet(doc, spec)
    motion = linear_motion(obs, sigma)
    if motion["fit_rms_arcsec"] > float(p.get("max_fit_rms_arcsec", 0.5)):
        raise WitnessError(f"the observations do not lie on a line: rms {motion['fit_rms_arcsec']:.2f} arcsec")
    snr = motion["rate_arcsec_hr"] / motion["rate_sigma_arcsec_hr"] if motion["rate_sigma_arcsec_hr"] > 0 else math.inf
    if snr < float(p.get("min_rate_snr", 4.0)):
        raise WitnessError(
            f"the motion is not significant: {motion['rate_arcsec_hr']:.2f} ± {motion['rate_sigma_arcsec_hr']:.2f} arcsec/hr"
        )

    eph = skyfit.Ephemeris(eph_path)
    obscodes = skyfit.load_obscodes(obscodes_path)
    pos, vel = observer_state(eph, obscodes, motion["station"], motion["t0_utc"], motion["t0_tt"])
    ra, dec = motion["ra0"], motion["dec0"]
    lo, hi, n = p.get("delta_grid_au", [0.05, 5000.0, 6000])
    grid = np.geomspace(float(lo), float(hi), int(n))
    factor = float(p.get("escape_factor", math.sqrt(2.0)))

    def far_branch(scale: float):
        segs = bound_intervals(pos, vel, ra, dec, motion["vx_arcsec_hr"] * scale, motion["vy_arcsec_hr"] * scale, grid, factor)
        if not segs:
            return None, segs
        a, b = segs[-1]
        return {"delta_min_au": float(grid[a]), "delta_max_au": float(grid[b]),
                "r_min_au": helio_r(pos, ra, dec, float(grid[a])), "r_max_au": helio_r(pos, ra, dec, float(grid[b]))}, segs

    # The far branch for the nominal rate, and its spread over the rate's error:
    # a faster rate brings the bound closer, a slower one pushes it out.
    rel = motion["rate_sigma_arcsec_hr"] / motion["rate_arcsec_hr"]
    far_nom, segs = far_branch(1.0)
    far_fast, _ = far_branch(1.0 + rel)
    far_slow, _ = far_branch(max(1.0 - rel, 1e-6))

    ratio, r_along = speed_ratio(pos, vel, ra, dec, motion["vx_arcsec_hr"], motion["vy_arcsec_hr"], grid)
    r_lo, r_hi = p.get("inner_r_au", [1.3, 6.0])
    inner_mask = (r_along >= float(r_lo)) & (r_along <= float(r_hi)) & (ratio <= float(p.get("inner_speed_ratio_max", 1.3)))
    inner = None
    if inner_mask.any():
        k = int(np.argmin(np.where(inner_mask, ratio, np.inf)))
        inner = {"explains": True, "r_au": float(r_along[k]), "delta_au": float(grid[k]), "speed_ratio": float(ratio[k])}
    else:
        k = int(np.argmin(np.where((r_along >= float(r_lo)) & (r_along <= float(r_hi)), ratio, np.inf)))
        inner = {"explains": False, "closest_speed_ratio": float(ratio[k]) if np.isfinite(ratio[k]) else None}

    v_app = apparent_v(obs, p.get("band_offsets", {}))
    photometry = None
    if v_app is not None and far_nom is not None:
        photometry = {
            "V_apparent": v_app,
            "H_at_r_min": absolute_mag(v_app, far_nom["r_min_au"], far_nom["delta_min_au"]),
            "H_at_r_max": absolute_mag(v_app, far_nom["r_max_au"], far_nom["delta_max_au"]),
        }

    known = []
    if snapshot_path:
        rows = read_mpcorb_full(snapshot_path)
        known = snapshot_neighbours(rows, pos, vel, motion["t0_tt"], ra, dec, float(p.get("known_sep_arcmin", 5.0)))
        for m in known:
            m["rate_matches"] = rate_matches(m, motion, float(p.get("known_rate_tolerance", 0.5)))

    return {
        "designation": desig,
        "canonical": canonical_id(spec["id"], obs),
        "motion": motion,
        "elongation_deg": elongation_deg(pos, ra, dec),
        "ecliptic_latitude_deg": math.degrees(math.asin(float((skyfit.EQ_TO_ECL @ tangent_frame(ra, dec)[0])[2]))),
        "bound_intervals": [{"delta_min_au": float(grid[a]), "delta_max_au": float(grid[b])} for a, b in segs],
        "far_branch": far_nom,
        "far_branch_fast_rate": far_fast,
        "far_branch_slow_rate": far_slow,
        "inner_branch": inner,
        "photometry": photometry,
        "known_nearby": known[:10],
        "snapshot": p.get("snapshot"),
    }


def decide_lead(doc: dict, spec: dict, label: str, extra=None):
    """The shared verdict for a distant-lead checker. `extra(res, p)` may return a
    refusal string for the problem's own extra predicate (brightness, say)."""
    p = spec["params"]
    res = analyse(doc, spec)
    m = {k: v for k, v in res.items() if k != "canonical"}
    m["prediction"] = read_prediction(doc)
    can = f"{label}:{res['canonical']}"
    mo = res["motion"]
    hit = next((k for k in res["known_nearby"] if k["rate_matches"]), None)
    if hit:
        return False, (f"{hit['designation']} in the {p.get('snapshot')} is {hit['sep_arcmin']:.1f} arcmin away at this epoch "
                       f"moving at the same rate; this is a known object"), can, m
    far = res["far_branch"]
    if far is None:
        return False, (f"at {mo['rate_arcsec_hr']:.2f} arcsec/hr no bound heliocentric orbit reproduces the motion at any "
                       f"distance; this is not a distant object"), can, m
    if res["inner_branch"]["explains"]:
        ib = res["inner_branch"]
        return False, (f"an inner solar system orbit at r = {ib['r_au']:.1f} AU reproduces this motion "
                       f"(elongation {res['elongation_deg']:.0f} deg, speed ratio {ib['speed_ratio']:.2f}); slow motion away "
                       f"from opposition does not imply distance"), can, m
    r_floor = float(p["r_min_au"])
    conservative = res["far_branch_fast_rate"] or far
    if conservative["r_min_au"] < r_floor:
        return False, (f"a bound orbit as close as r = {conservative['r_min_au']:.0f} AU reproduces the motion, inside the "
                       f"{r_floor:.0f} AU floor; a lead for this search must be unreachable by nearer orbits"), can, m
    if extra is not None:
        why = extra(res, p)
        if why:
            return False, why, can, m
    phot = res["photometry"]
    htxt = (f", H between {phot['H_at_r_max']:.1f} and {phot['H_at_r_min']:.1f}" if phot else ", no magnitudes")
    return True, (f"{mo['n_obs']} observations from {mo['station']} over {mo['arc_hours']:.1f} h at "
                  f"{mo['rate_arcsec_hr']:.2f} ± {mo['rate_sigma_arcsec_hr']:.2f} arcsec/hr, elongation "
                  f"{res['elongation_deg']:.0f} deg: every bound orbit that reproduces the motion lies at r = "
                  f"{far['r_min_au']:.0f} to {far['r_max_au']:.0f} AU{htxt}; no inner orbit explains it and nothing in the "
                  f"snapshot is there. A lead, to be recovered on another night"), can, m
