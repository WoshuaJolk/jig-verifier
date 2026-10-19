"""Systematic ranging for short arcs that may be unbound.

The root interstellar checker fits a full orbit to a month of two-station
astrometry. A candidate pulled out of a survey's discard pile has a week or two
from one station, and on that arc a least-squares orbit fit wanders into
degenerate near-parabolic solutions. Ranging asks a different question: over a
grid in topocentric distance and range rate at the arc's central epoch, with
the sky position and rates fitted in each cell, which cells reproduce the
observations? The acceptable cells are the orbits the arc allows. If every one
is hyperbolic, the arc cannot be bound and the object is a lead for the root
statement. If some are bound, the arc has not decided anything yet.

Two-body heliocentric motion, Kepler's equation solved in the eccentric or
hyperbolic anomaly so bound and unbound cells share one propagator, light time
applied, observer positions from the pinned ephemeris and station list. Planetary perturbations are left out: over a
few weeks at a few AU they move a position by far less than the survey
astrometry's own error, and the root checker applies them when the arc is long
enough to matter.
"""

from __future__ import annotations

import hashlib
import math

import numpy as np
from scipy.optimize import least_squares

import skyfit
from skyfit import Observation, WitnessError
import shortarc

MU = skyfit.GM_SUN
SQRT_MU = math.sqrt(MU)
C = skyfit.C_AU_PER_DAY
ARCSEC_PER_RAD = 1.0 / skyfit.ARCSEC


# ----------------------------------------------------------------- two-body

def _frame(r0: np.ndarray, v0: np.ndarray):
    """Perifocal basis and elements of a state: (P, Q, a, e, n, M0). P points at
    perihelion, Q is 90 degrees ahead in the orbit. None for a degenerate state."""
    rn = float(np.linalg.norm(r0))
    h = np.cross(r0, v0)
    hn = float(np.linalg.norm(h))
    if rn <= 0 or hn < 1e-12:
        return None
    evec = np.cross(v0, h) / MU - r0 / rn
    e = float(np.linalg.norm(evec))
    if e < 1e-9:
        evec = r0 / rn
        e = 1e-9
    if abs(e - 1.0) < 1e-9:
        e = 1.0 + 1e-9
    P = evec / float(np.linalg.norm(evec))
    Q = np.cross(h, P) / hn
    energy = float(v0 @ v0) / 2 - MU / rn
    if abs(energy) < 1e-15:
        return None
    a = -MU / (2 * energy)
    n = math.sqrt(MU / abs(a) ** 3)
    x, y = float(r0 @ P), float(r0 @ Q)
    nu = math.atan2(y, x)
    if e < 1:
        E = math.atan2(math.sqrt(1 - e * e) * math.sin(nu), e + math.cos(nu))
        M0 = E - e * math.sin(E)
    else:
        sh = math.sqrt(e * e - 1) * math.sin(nu) / (1 + e * math.cos(nu))
        H = math.asinh(sh)
        M0 = e * math.sinh(H) - H
    return P, Q, a, e, n, M0


def propagate(r0: np.ndarray, v0: np.ndarray, dts: np.ndarray) -> np.ndarray:
    """Two-body positions of one state at many times, (n, 3). Kepler's equation is
    solved by Newton in the eccentric or hyperbolic anomaly, vectorised over the
    times, from a starting guess that is already close for any eccentricity. Rows
    are NaN for a degenerate state."""
    dts = np.asarray(dts, dtype=float)
    with np.errstate(all="ignore"):
        fr = _frame(r0, v0)
        if fr is None:
            return np.full((len(dts), 3), np.nan)
        P, Q, a, e, n, M0 = fr
        M = M0 + n * dts
        if e < 1:
            M = np.mod(M + math.pi, 2 * math.pi) - math.pi
            E = M + e * np.sin(M)
            for _ in range(30):
                E = E - (E - e * np.sin(E) - M) / (1 - e * np.cos(E))
            x = a * (np.cos(E) - e)
            y = a * math.sqrt(1 - e * e) * np.sin(E)
        else:
            H = np.arcsinh(M / e)
            for _ in range(40):
                H = H - (e * np.sinh(H) - H - M) / (e * np.cosh(H) - 1)
            x = a * (np.cosh(H) - e)
            y = -a * math.sqrt(e * e - 1) * np.sinh(H)
        out = x[:, None] * P[None, :] + y[:, None] * Q[None, :]
        out[~np.isfinite(out).all(axis=1)] = np.nan
        return out


# ----------------------------------------------------------------- the arc

class Arc:
    """The observations, observer positions, and the frame at the central epoch."""

    def __init__(self, obs: list[Observation], eph: skyfit.Ephemeris, obscodes: dict):
        self.obs = obs
        self.t = np.array([o.jd_tt for o in obs])
        self.t0 = float(np.median(self.t))
        self.ra = np.array([o.ra for o in obs])
        self.dec = np.array([o.dec for o in obs])
        self.observer = np.array([shortarc.observer_helio(eph, obscodes, o.obscode, o.jd_utc, o.jd_tt) for o in obs])
        # The observer at t0 for the state construction: the station of the
        # observation nearest the median epoch, with its velocity.
        k = int(np.argmin(np.abs(self.t - self.t0)))
        o = obs[k]
        self.o0, self.v0 = shortarc.observer_state(eph, obscodes, o.obscode, o.jd_utc + (self.t0 - o.jd_tt), self.t0)

    def attributable(self) -> np.ndarray:
        """Sky position and rates at t0: [ra, dec, dra/dt, ddec/dt] in radians and
        radians/day, from a quadratic in time when the arc has the points for it
        (a month of a fast mover curves by degrees) and a line otherwise."""
        dt = self.t - self.t0
        ra_un = np.unwrap(self.ra)
        cols = [np.ones_like(dt), dt]
        if len(dt) >= 6:
            cols.append(dt * dt)
        A = np.vstack(cols).T
        ca, *_ = np.linalg.lstsq(A, ra_un, rcond=None)
        cd, *_ = np.linalg.lstsq(A, self.dec, rcond=None)
        return np.array([ca[0] % (2 * math.pi), cd[0], ca[1], cd[1]])

    def state(self, attr: np.ndarray, rho: float, rhodot: float) -> np.ndarray:
        ra, de, rad, ded = attr
        cd, sd, ca, sa = math.cos(de), math.sin(de), math.cos(ra), math.sin(ra)
        u = np.array([cd * ca, cd * sa, sd])
        du = rad * np.array([-cd * sa, cd * ca, 0.0]) + ded * np.array([-sd * ca, -sd * sa, cd])
        r = self.o0 + rho * u
        v = self.v0 + rhodot * u + rho * du
        return np.concatenate([r, v])

    def residuals(self, state: np.ndarray) -> np.ndarray:
        """[dRA cos(dec), dDec] in arcsec for every observation, light time applied."""
        r0, v0 = state[:3], state[3:]
        tau = np.zeros_like(self.t)
        for _ in range(2):
            pos = propagate(r0, v0, self.t - tau - self.t0)
            rho = pos - self.observer
            d = np.linalg.norm(rho, axis=1)
            tau = d / C
        if not np.isfinite(d).all():
            return np.full(2 * len(self.t), 1e6)
        ra = np.arctan2(rho[:, 1], rho[:, 0])
        de = np.arcsin(np.clip(rho[:, 2] / d, -1, 1))
        dra = (self.ra - ra + math.pi) % (2 * math.pi) - math.pi
        return np.concatenate([dra * np.cos(self.dec), self.dec - de]) * ARCSEC_PER_RAD

    def chi2(self, state: np.ndarray, sigma: float) -> float:
        res = self.residuals(state) / sigma
        return float(res @ res)


# ----------------------------------------------------------------- the grid

def _fit_cell(arc: Arc, attr0: np.ndarray, rho: float, rhodot: float, max_nfev: int) -> tuple[np.ndarray, float]:
    def fun(x):
        return arc.residuals(arc.state(x, rho, rhodot))
    scale = np.array([1e-4, 1e-4, 1e-5, 1e-5])
    try:
        sol = least_squares(fun, attr0, method="lm", x_scale=scale, max_nfev=max_nfev, xtol=1e-10, ftol=1e-10)
        return sol.x, float(2 * sol.cost)
    except (ValueError, FloatingPointError):
        return attr0, math.inf


def _polish(arc: Arc, attr: np.ndarray, rho: float, rhodot: float):
    """Six-parameter fit from a cell. Returns (attr, rho, rhodot, cov) where cov is
    the unscaled inverse normal matrix over [attr, ln rho, rhodot], or None."""
    def fun(x):
        return arc.residuals(arc.state(x[:4], math.exp(x[4]), x[5]))
    x0 = np.concatenate([attr, [math.log(rho), rhodot]])
    scale = np.array([1e-4, 1e-4, 1e-5, 1e-5, 1e-2, 1e-3])
    try:
        sol = least_squares(fun, x0, method="lm", x_scale=scale, max_nfev=200, xtol=1e-12, ftol=1e-12)
    except (ValueError, FloatingPointError):
        return attr, rho, rhodot, None
    try:
        cov = np.linalg.inv(sol.jac.T @ sol.jac)
    except np.linalg.LinAlgError:
        cov = None
    return sol.x[:4], math.exp(sol.x[4]), float(sol.x[5]), cov


def _local_grid(arc: Arc, best: dict, sigma: float, nfev: int, half_width_sigma: float, n: int) -> list[dict]:
    """Cells on a grid around the polished minimum, spanning its own error
    ellipse in (ln rho, rhodot): the coarse grid is far too wide to resolve the
    valley, and without this the acceptable set is the minimum alone."""
    cov = best.get("cov")
    if cov is None:
        return []
    s_lnr = math.sqrt(max(float(cov[4, 4]), 1e-12)) * sigma
    s_rd = math.sqrt(max(float(cov[5, 5]), 1e-12)) * sigma
    s_lnr = min(s_lnr, 0.5)
    s_rd = min(s_rd, 0.1)
    out = []
    lnr0 = math.log(best["rho"])
    for a in np.linspace(-half_width_sigma, half_width_sigma, n):
        for b in np.linspace(-half_width_sigma, half_width_sigma, n):
            rho = math.exp(lnr0 + a * s_lnr)
            rd = best["rhodot"] + b * s_rd
            attr, chi2 = _fit_cell(arc, best["attr"], rho, rd, nfev)
            if math.isfinite(chi2):
                out.append({"rho": rho, "rhodot": rd, "attr": attr, "chi2": chi2, "i": -1, "j": -1})
    return out


def _constrained_best(arc: Arc, cells: list[dict], polished: list[dict], e_cap: float, n_starts: int) -> dict | None:
    """The best-fitting orbit with eccentricity at most e_cap, by a six-parameter
    fit carrying a penalty residual on the excess over the cap, started from the
    lowest-chi2 cells that already satisfy it and from the polished minima."""
    starts = []
    for c in polished + cells:
        st = c.get("state")
        if st is None:
            st = arc.state(c["attr"], c["rho"], c["rhodot"])
        try:
            e = skyfit.elements_from_state(st, arc.t0)["e"]
        except (ValueError, ZeroDivisionError, FloatingPointError):
            continue
        if math.isfinite(e) and e <= e_cap:
            starts.append(c)
        if len(starts) >= n_starts:
            break
    starts += polished[:2]
    penalty = 1e4  # arcsec of residual per unit of eccentricity over the cap

    def fun(x):
        st = arc.state(x[:4], math.exp(x[4]), x[5])
        res = arc.residuals(st)
        try:
            e = skyfit.elements_from_state(st, arc.t0)["e"]
        except (ValueError, ZeroDivisionError, FloatingPointError):
            e = 1e3
        if not math.isfinite(e):
            e = 1e3
        return np.concatenate([res, [penalty * max(0.0, e - e_cap)]])

    best = None
    scale = np.array([1e-4, 1e-4, 1e-5, 1e-5, 1e-2, 1e-3])
    for c in starts:
        x0 = np.concatenate([c["attr"], [math.log(c["rho"]), c["rhodot"]]])
        try:
            sol = least_squares(fun, x0, method="trf", x_scale=scale, max_nfev=300, xtol=1e-12, ftol=1e-12)
        except (ValueError, FloatingPointError):
            continue
        st = arc.state(sol.x[:4], math.exp(sol.x[4]), sol.x[5])
        try:
            el = skyfit.elements_from_state(st, arc.t0)
        except (ValueError, ZeroDivisionError, FloatingPointError):
            continue
        if not math.isfinite(el["e"]) or el["e"] > e_cap + 1e-3:
            continue
        res = arc.residuals(st)
        chi2 = float(res @ res)
        if best is None or chi2 < best["chi2"]:
            best = {"chi2": chi2, "rms": float(math.sqrt(np.mean(res * res))), "e": el["e"], "q": el["q"],
                    "rho": math.exp(sol.x[4])}
    return best


def run(obs: list[Observation], eph: skyfit.Ephemeris, obscodes: dict, p: dict) -> dict:
    arc = Arc(obs, eph, obscodes)
    attr0 = arc.attributable()
    rhos = np.geomspace(float(p.get("rho_lo_au", 0.3)), float(p.get("rho_hi_au", 15.0)), int(p.get("n_rho", 40)))
    rdmax = float(p.get("rhodot_max_au_day", 0.06))
    rds = np.linspace(-rdmax, rdmax, int(p.get("n_rhodot", 49)))
    nfev = int(p.get("cell_max_nfev", 40))

    # Each row starts from the sky fit and then warm-starts from the cell beside
    # it: neighbouring cells have neighbouring attributables, and a cold start on
    # a long arc can stall before the solver finds the valley.
    cells = []
    for i, rho in enumerate(rhos):
        seed = attr0
        for j, rd in enumerate(rds):
            attr, chi2 = _fit_cell(arc, seed, float(rho), float(rd), nfev)
            if math.isfinite(chi2):
                cells.append({"rho": float(rho), "rhodot": float(rd), "attr": attr, "chi2": chi2, "i": i, "j": j})
                seed = attr
    if not cells:
        raise WitnessError("no cell of the ranging grid reproduces the observations at all")

    # Polish the best cells in all six parameters; the best polished rms sets the
    # chi-square scale so a survey's real centroid error does not shrink the
    # acceptable set to a single cell.
    cells.sort(key=lambda c: c["chi2"])
    polished = []
    for c in cells[: int(p.get("n_polish", 8))]:
        attr, rho, rd, cov = _polish(arc, c["attr"], c["rho"], c["rhodot"])
        st = arc.state(attr, rho, rd)
        res = arc.residuals(st)
        polished.append({"rho": rho, "rhodot": rd, "attr": attr, "chi2": float(res @ res), "state": st,
                         "rms": float(math.sqrt(np.mean(res * res))), "cov": cov})
    polished.sort(key=lambda c: c["chi2"])
    best = polished[0]
    n_res = 2 * len(obs)
    sigma = max(best["rms"] * math.sqrt(n_res / max(n_res - 6, 1)), float(p.get("sigma_floor_arcsec", 0.3)))
    chi2_min = best["chi2"] / sigma ** 2
    dchi2 = float(p.get("dchi2", 9.0))

    def acceptable(c):
        return c["chi2"] / sigma ** 2 <= chi2_min + dchi2

    accepted = [c for c in cells if acceptable(c)]
    accepted += [c for c in _local_grid(arc, best, sigma, nfev, float(p.get("local_half_width_sigma", 3.5)),
                                        int(p.get("local_grid_n", 9))) if acceptable(c)]

    # Refinement: subdivide around every accepted cell, halving the step each
    # pass, so the set is a region rather than a few isolated grid points.
    seen = {(c["i"], c["j"]) for c in accepted}
    lnr = np.log(rhos)
    dl = (lnr[1] - lnr[0]) if len(rhos) > 1 else 0.1
    dr = (rds[1] - rds[0]) if len(rds) > 1 else 0.01
    frontier = list(accepted)
    for level in range(1, int(p.get("refine_passes", 1)) + 1):
        step = 0.5 ** level
        new_cells = []
        for c in frontier:
            for di in (-step, 0.0, step):
                for dj in (-step, 0.0, step):
                    if di == 0.0 and dj == 0.0:
                        continue
                    key = (round(c["i"] + di, 6), round(c["j"] + dj, 6))
                    if key in seen:
                        continue
                    seen.add(key)
                    rho = math.exp(lnr[0] + key[0] * dl)
                    rd = rds[0] + key[1] * dr
                    if not (rhos[0] * 0.5 <= rho <= rhos[-1] * 2) or abs(rd) > rdmax * 1.5:
                        continue
                    attr, chi2 = _fit_cell(arc, c["attr"], rho, rd, nfev)
                    if math.isfinite(chi2):
                        cell = {"rho": rho, "rhodot": rd, "attr": attr, "chi2": chi2, "i": key[0], "j": key[1]}
                        if acceptable(cell):
                            new_cells.append(cell)
        accepted += new_cells
        frontier = new_cells if new_cells else accepted
    for c in polished:
        if acceptable(c):
            accepted.append(c)

    # The question the lead turns on, asked directly rather than read off the
    # grid: how much worse is the best orbit with e capped at the root's bar?
    # Grid sampling can miss a narrow bound valley; a constrained fit cannot.
    e_cap = float(p.get("e_min", 1.02))
    capped = _constrained_best(arc, cells, polished, e_cap, int(p.get("n_capped_starts", 10)))
    chi2_capped = capped["chi2"] / sigma ** 2 if capped else math.inf

    els = []
    for c in accepted:
        st = c.get("state")
        if st is None:
            st = arc.state(c["attr"], c["rho"], c["rhodot"])
        try:
            el = skyfit.elements_from_state(st, arc.t0)
        except (ValueError, ZeroDivisionError, FloatingPointError):
            continue
        if not all(math.isfinite(el[k]) for k in ("e", "q", "i")):
            continue
        els.append({"rho": c["rho"], "rhodot": c["rhodot"], "e": el["e"], "q": el["q"], "i": el["i"],
                    "a": el.get("a"), "chi2_scaled": c["chi2"] / sigma ** 2})
    if not els:
        raise WitnessError("the acceptable orbits could not be converted to elements")
    e_all = np.array([x["e"] for x in els])
    best_el = skyfit.elements_from_state(best["state"], arc.t0)
    return {
        "t0_tt": arc.t0,
        "n_cells": len(cells),
        "n_acceptable": len(els),
        "sigma_arcsec": sigma,
        "rms_best_arcsec": best["rms"],
        "best": {"rho_au": best["rho"], "rhodot_au_day": best["rhodot"],
                 "e": best_el["e"], "q": best_el["q"], "i": best_el["i"], "a": best_el.get("a"),
                 "node": best_el.get("node"), "peri": best_el.get("peri")},
        "unbound_fraction": float(np.mean(e_all > 1.0)),
        "e_cap": e_cap,
        "capped_best": capped and {"e": capped["e"], "q": capped["q"], "rho_au": capped["rho"], "rms_arcsec": capped["rms"]},
        "chi2_excess_at_e_cap": (chi2_capped - chi2_min) if math.isfinite(chi2_capped) else None,
        "dchi2": dchi2,
        "e_min": float(e_all.min()), "e_max": float(e_all.max()),
        "q_min_au": float(min(x["q"] for x in els)), "q_max_au": float(max(x["q"] for x in els)),
        "i_min_deg": float(min(x["i"] for x in els)), "i_max_deg": float(max(x["i"] for x in els)),
        "rho_min_au": float(min(x["rho"] for x in els)), "rho_max_au": float(max(x["rho"] for x in els)),
        "position_t0": {"ra_deg": math.degrees(best["attr"][0]) % 360.0, "dec_deg": math.degrees(best["attr"][1])},
    }


# ----------------------------------------------------------------- known objects

def known_nearby(arc_t0: float, ra: float, dec: float, observer: np.ndarray, known: list[dict], sep_deg: float) -> str | None:
    """Name of a known orbit whose two-body position at t0 falls within sep_deg."""
    u, _, _ = shortarc.tangent_frame(ra, dec)
    for k in known:
        try:
            st = skyfit.state_from_elements(k["q"], k["e"], k["i"], k["node"], k["peri"], k["tp"], arc_t0)
        except (WitnessError, ValueError, OverflowError):
            continue
        rho = st[:3] - observer
        d = float(np.linalg.norm(rho))
        if d > 0 and math.degrees(math.acos(max(-1.0, min(1.0, float(rho @ u) / d)))) <= sep_deg:
            return k["name"]
    return None


# ----------------------------------------------------------------- witness

def read_arc(doc: dict, spec: dict) -> tuple[str, list[Observation]]:
    p = spec["params"]
    desig = doc.get("designation")
    if not isinstance(desig, str) or not skyfit.DESIGNATION_RE.match(desig):
        raise WitnessError("designation must be a short string naming the candidate")
    lines = doc.get("observations")
    if not isinstance(lines, list) or not lines:
        raise WitnessError("observations must be a non-empty list of MPC 80-column lines")
    if len(lines) > int(p.get("max_observations", 400)):
        raise WitnessError(f"at most {p.get('max_observations', 400)} observations")
    obs = []
    for ln in lines:
        if not isinstance(ln, str):
            raise WitnessError("every observation must be a string")
        obs.append(skyfit.parse_obs80(ln.rstrip("\r\n")))
    obs.sort(key=lambda o: o.jd_utc)
    stats = skyfit.arc_stats(obs)
    if stats["n_obs"] < int(p.get("min_observations", 6)):
        raise WitnessError(f"at least {p.get('min_observations', 6)} observations are required")
    if stats["nights"] < int(p.get("min_nights", 4)):
        raise WitnessError(f"observations on at least {p.get('min_nights', 4)} distinct nights are required")
    if stats["arc_days"] < float(p.get("min_arc_days", 10)):
        raise WitnessError(f"the arc must span at least {p.get('min_arc_days', 10)} days; shorter arcs decide nothing about e")
    if stats["arc_days"] > float(p.get("max_arc_days", 60)):
        raise WitnessError(f"the arc spans {stats['arc_days']:.0f} days; past {p.get('max_arc_days', 60)} submit to the root statement instead")
    return desig, obs


def canonical_id(label: str, obs: list[Observation]) -> str:
    h = hashlib.sha256("\n".join(sorted(o.line.rstrip() for o in obs)).encode()).hexdigest()[:16]
    return f"{label}:{obs[0].jd_utc:.2f}:{obs[-1].jd_utc:.2f}:{h}"
