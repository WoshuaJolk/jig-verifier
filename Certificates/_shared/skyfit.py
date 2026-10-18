"""Orbit determination for Jig's astronomical certificates.

Shared by every checker that decides a claim about an orbit: the witness names an
object, an orbit, and the optical astrometry the orbit is supposed to fit. This
module fits the orbit to that astrometry under full planetary perturbations and
reports osculating elements with uncertainties, so a checker's predicate ("e > 1",
"q > 50 AU") is tested against the data and its error bars rather than against a
number the submitter typed.

Deterministic, offline, and bounded. Inputs:
  * `de440s.bsp`, the JPL planetary ephemeris, pinned by hash in the spec
  * `ObsCodes.html`, the MPC observatory list, pinned the same way
  * the witness: MPC 80-column observation lines and starting elements

Nothing here is novel; the model is standard, and every approximation is named:
no relativistic correction, no asteroid perturbers, UT1 taken as UTC, nutation
ignored in the observer's position. Each is far below the arcsecond at the
distances these problems live at, and the spec's residual bound is the check.
"""

from __future__ import annotations

import math
import re
from dataclasses import dataclass

import numpy as np
from jplephem.spk import SPK
from scipy.integrate import solve_ivp
from scipy.interpolate import CubicSpline
from scipy.optimize import least_squares

# ------------------------------------------------------------------ constants

AU_KM = 149597870.7
C_AU_PER_DAY = 173.1446326742403
K_GAUSS = 0.01720209895
GM_SUN = K_GAUSS**2  # AU^3 / day^2
EARTH_RADIUS_KM = 6378.137
OBLIQUITY_J2000_ARCSEC = 84381.448
ARCSEC = math.pi / (180 * 3600)
J2000 = 2451545.0

# Sun/planet mass ratios, DE440. Pluto is left out: below a metre on anything here.
PLANETS = [
    ("mercury", 1, 6023657.945),
    ("venus", 2, 408523.718),
    ("emb", 3, 328900.5596),
    ("mars", 4, 3098703.59),
    ("jupiter", 5, 1047.348625),
    ("saturn", 6, 3497.9018),
    ("uranus", 7, 22902.951),
    ("neptune", 8, 19412.259),
]
GM_PLANETS = {name: GM_SUN / ratio for name, _, ratio in PLANETS}

# TAI-UTC since 1972, as (JD of the step, seconds after it).
LEAP_SECONDS = [
    (2441317.5, 10), (2441499.5, 11), (2441683.5, 12), (2442048.5, 13),
    (2442413.5, 14), (2442778.5, 15), (2443144.5, 16), (2443509.5, 17),
    (2443874.5, 18), (2444239.5, 19), (2444786.5, 20), (2445151.5, 21),
    (2445516.5, 22), (2446247.5, 23), (2447161.5, 24), (2447892.5, 25),
    (2448257.5, 26), (2448804.5, 27), (2449169.5, 28), (2449534.5, 29),
    (2450083.5, 30), (2450630.5, 31), (2451179.5, 32), (2453736.5, 33),
    (2454832.5, 34), (2456109.5, 35), (2457204.5, 36), (2457754.5, 37),
]


class WitnessError(ValueError):
    """The witness is malformed or outside what this problem accepts."""


# ----------------------------------------------------------------- time

def jd_from_ymd(year: int, month: int, day: float) -> float:
    """Gregorian calendar date (UTC day fraction allowed) to Julian date."""
    y, m = (year, month) if month > 2 else (year - 1, month + 12)
    a = y // 100
    b = 2 - a + a // 4
    return math.floor(365.25 * (y + 4716)) + math.floor(30.6001 * (m + 1)) + day + b - 1524.5


def tai_minus_utc(jd_utc: float) -> float:
    if jd_utc < LEAP_SECONDS[0][0]:
        raise WitnessError("observations before 1972 are not accepted: no leap-second table")
    delta = LEAP_SECONDS[0][1]
    for at, seconds in LEAP_SECONDS:
        if jd_utc >= at:
            delta = seconds
    return delta


def tt_from_utc(jd_utc: float) -> float:
    """TT, which this module also uses as TDB: the difference is under 2 ms."""
    return jd_utc + (tai_minus_utc(jd_utc) + 32.184) / 86400.0


def gmst_rad(jd_ut: float) -> float:
    d = jd_ut - J2000
    hours = (18.697374558 + 24.06570982441908 * d) % 24.0
    return hours * math.pi / 12.0


def precession_matrix(jd_tt: float) -> np.ndarray:
    """IAU 1976 precession: J2000 mean equator -> mean equator of date."""
    t = (jd_tt - J2000) / 36525.0
    zeta = (2306.2181 * t + 0.30188 * t * t + 0.017998 * t**3) * ARCSEC
    z = (2306.2181 * t + 1.09468 * t * t + 0.018203 * t**3) * ARCSEC
    theta = (2004.3109 * t - 0.42665 * t * t - 0.041833 * t**3) * ARCSEC
    return rot_z(-z) @ rot_y(theta) @ rot_z(-zeta)


def rot_x(a: float) -> np.ndarray:
    c, s = math.cos(a), math.sin(a)
    return np.array([[1, 0, 0], [0, c, s], [0, -s, c]])


def rot_y(a: float) -> np.ndarray:
    c, s = math.cos(a), math.sin(a)
    return np.array([[c, 0, -s], [0, 1, 0], [s, 0, c]])


def rot_z(a: float) -> np.ndarray:
    c, s = math.cos(a), math.sin(a)
    return np.array([[c, s, 0], [-s, c, 0], [0, 0, 1]])


ECL_TO_EQ = rot_x(-OBLIQUITY_J2000_ARCSEC * ARCSEC)
EQ_TO_ECL = ECL_TO_EQ.T


# ----------------------------------------------------------------- MPC input

OBSCODE_RE = re.compile(r"^[A-Z0-9][A-Z0-9][A-Z0-9]$")
# Second lines of two-line formats, and anything not a ground-based optical measure.
REJECTED_NOTE2 = set("SsVvRrXx")


@dataclass
class Observation:
    jd_utc: float
    jd_tt: float
    ra: float  # radians, ICRF
    dec: float
    obscode: str
    mag: float | None
    band: str
    line: str


def parse_obs80(line: str) -> Observation:
    """One MPC 80-column optical observation line."""
    if len(line) < 80:
        line = line.ljust(80)
    if len(line) > 80:
        raise WitnessError(f"observation line longer than 80 columns: {line[:20]!r}")
    note2 = line[14]
    if note2 in REJECTED_NOTE2:
        raise WitnessError(
            f"only ground-based optical observations are accepted (note2={note2!r}): {line[:32].strip()!r}"
        )
    try:
        year = int(line[15:19])
        month = int(line[20:22])
        day = float(line[23:32])
        rah = int(line[32:34])
        ram = int(line[35:37])
        ras = float(line[38:44]) if line[38:44].strip() else 0.0
        sign = -1.0 if line[44] == "-" else 1.0
        dd = int(line[45:47])
        dm = int(line[48:50])
        ds = float(line[51:56]) if line[51:56].strip() else 0.0
    except ValueError as e:
        raise WitnessError(f"unparseable observation line {line[:32].strip()!r}: {e}") from e
    if not (1 <= month <= 12 and 1.0 <= day < 32.0):
        raise WitnessError(f"bad date in observation line {line[:32].strip()!r}")
    obscode = line[77:80].strip()
    if not OBSCODE_RE.match(obscode):
        raise WitnessError(f"bad observatory code {obscode!r} in {line[:32].strip()!r}")
    jd_utc = jd_from_ymd(year, month, day)
    ra = (rah + ram / 60.0 + ras / 3600.0) * math.pi / 12.0
    dec = sign * (dd + dm / 60.0 + ds / 3600.0) * math.pi / 180.0
    mag_txt = line[65:70].strip()
    mag = None
    if mag_txt:
        try:
            mag = float(mag_txt)
        except ValueError:
            mag = None
    return Observation(jd_utc, tt_from_utc(jd_utc), ra, dec, obscode, mag, line[70].strip(), line)


def load_obscodes(path: str) -> dict[str, tuple[float, float, float]]:
    """MPC ObsCodes.html: code -> (east longitude deg, rho cos phi', rho sin phi')
    in Earth radii. Codes with no geocentric parallax (satellites, roving) are
    left out, so a lookup failure means "not a ground station"."""
    out: dict[str, tuple[float, float, float]] = {}
    with open(path, encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.rstrip("\n")
            if len(line) < 30 or not OBSCODE_RE.match(line[0:3]):
                continue
            lon, cos_, sin_ = line[4:13].strip(), line[13:21].strip(), line[21:30].strip()
            if not (lon and cos_ and sin_):
                continue
            try:
                out[line[0:3]] = (float(lon), float(cos_), float(sin_))
            except ValueError:
                continue
    return out


# ----------------------------------------------------------------- ephemeris

class Ephemeris:
    """Heliocentric ICRF positions in AU from a JPL SPK file."""

    def __init__(self, path: str):
        self.kernel = SPK.open(path)
        self._seg = {}
        for (center, target) in [(0, 10), (0, 3), (3, 399)] + [(0, b) for _, b, _ in PLANETS]:
            self._seg[(center, target)] = self.kernel[center, target]

    def _pos(self, center: int, target: int, jd: float | np.ndarray) -> np.ndarray:
        return np.asarray(self._seg[(center, target)].compute(jd)) / AU_KM

    def sun_ssb(self, jd):
        return self._pos(0, 10, jd)

    def planet_helio(self, body: int, jd):
        return self._pos(0, body, jd) - self._pos(0, 10, jd)

    def earth_helio(self, jd):
        return self._pos(0, 3, jd) + self._pos(3, 399, jd) - self._pos(0, 10, jd)

    def sun_state_ssb(self, jd: float) -> tuple[np.ndarray, np.ndarray]:
        p, v = self._seg[(0, 10)].compute_and_differentiate(jd)
        return np.asarray(p) / AU_KM, np.asarray(v) / AU_KM


class Perturbers:
    """Planet positions on a fine grid, spline-interpolated: the right-hand side of
    the equations of motion is evaluated thousands of times per integration and
    the kernel is slow to read at that rate. Quarter-day knots keep the
    interpolation error under a kilometre for every body including the EMB."""

    def __init__(self, eph: Ephemeris, jd_lo: float, jd_hi: float, step: float = 0.25):
        pad = 5.0
        n = int(math.ceil((jd_hi - jd_lo + 2 * pad) / step)) + 1
        grid = jd_lo - pad + step * np.arange(n)
        self.grid = grid
        self.splines = []
        for name, body, _ in PLANETS:
            pos = eph.planet_helio(body, grid).T  # (n, 3)
            self.splines.append((GM_PLANETS[name], CubicSpline(grid, pos, axis=0)))

    def accel(self, t: float, r: np.ndarray) -> np.ndarray:
        rr = r @ r
        a = -GM_SUN * r / (rr * math.sqrt(rr))
        for gm, spl in self.splines:
            p = spl(t)
            d = p - r
            dd = d @ d
            pp = p @ p
            a += gm * (d / (dd * math.sqrt(dd)) - p / (pp * math.sqrt(pp)))
        return a


# ----------------------------------------------------------------- two-body

def solve_kepler_elliptic(M: float, e: float) -> float:
    E = M if e < 0.8 else math.pi
    for _ in range(60):
        f = E - e * math.sin(E) - M
        dE = -f / (1 - e * math.cos(E))
        E += dE
        if abs(dE) < 1e-14:
            break
    return E


def solve_kepler_hyperbolic(M: float, e: float) -> float:
    H = math.asinh(M / e) if e > 1 else M
    for _ in range(80):
        f = e * math.sinh(H) - H - M
        dH = -f / (e * math.cosh(H) - 1)
        H += dH
        if abs(dH) < 1e-14:
            break
    return H


def state_from_elements(q: float, e: float, inc: float, node: float, peri: float,
                        tp: float, epoch: float, mu: float = GM_SUN) -> np.ndarray:
    """Heliocentric ecliptic J2000 elements (degrees, JD) -> equatorial ICRF state
    [x, y, z, vx, vy, vz] in AU and AU/day at `epoch`."""
    if q <= 0 or e < 0:
        raise WitnessError("q must be positive and e non-negative")
    i, O, w = (math.radians(x) for x in (inc, node, peri))
    dt = epoch - tp
    if abs(e - 1.0) < 1e-9:
        e = 1.0 + 1e-9
    if e < 1:
        a = q / (1 - e)
        n = math.sqrt(mu / a**3)
        E = solve_kepler_elliptic(math.fmod(n * dt, 2 * math.pi), e)
        xp = a * (math.cos(E) - e)
        yp = a * math.sqrt(1 - e * e) * math.sin(E)
        rnorm = a * (1 - e * math.cos(E))
        vxp = -math.sqrt(mu * a) * math.sin(E) / rnorm
        vyp = math.sqrt(mu * a * (1 - e * e)) * math.cos(E) / rnorm
    else:
        a = q / (1 - e)  # negative
        n = math.sqrt(mu / (-a) ** 3)
        H = solve_kepler_hyperbolic(n * dt, e)
        xp = a * (math.cosh(H) - e)
        yp = -a * math.sqrt(e * e - 1) * math.sinh(H)
        rnorm = a * (1 - e * math.cosh(H))
        vxp = -math.sqrt(mu * -a) * math.sinh(H) / rnorm
        vyp = math.sqrt(mu * -a * (e * e - 1)) * math.cosh(H) / rnorm
    R = rot_z(-O) @ rot_x(-i) @ rot_z(-w)  # perifocal -> ecliptic
    r_ecl = R @ np.array([xp, yp, 0.0])
    v_ecl = R @ np.array([vxp, vyp, 0.0])
    return np.concatenate([ECL_TO_EQ @ r_ecl, ECL_TO_EQ @ v_ecl])


def elements_from_state(state: np.ndarray, epoch: float, mu: float = GM_SUN) -> dict:
    """Osculating ecliptic J2000 elements from an equatorial ICRF state."""
    r = EQ_TO_ECL @ state[:3]
    v = EQ_TO_ECL @ state[3:]
    rn = np.linalg.norm(r)
    h = np.cross(r, v)
    hn = np.linalg.norm(h)
    evec = np.cross(v, h) / mu - r / rn
    e = float(np.linalg.norm(evec))
    energy = v @ v / 2 - mu / rn
    a = -mu / (2 * energy) if abs(energy) > 1e-18 else math.inf
    p = hn * hn / mu
    q = p / (1 + e)
    inc = math.acos(max(-1.0, min(1.0, h[2] / hn)))
    nvec = np.array([-h[1], h[0], 0.0])
    nn = np.linalg.norm(nvec)
    node = math.atan2(nvec[1], nvec[0]) % (2 * math.pi) if nn > 1e-15 else 0.0
    if nn > 1e-15 and e > 1e-15:
        cw = (nvec @ evec) / (nn * e)
        peri = math.acos(max(-1.0, min(1.0, cw)))
        if evec[2] < 0:
            peri = 2 * math.pi - peri
    else:
        peri = 0.0
    if e > 1e-15:
        cnu = (evec @ r) / (e * rn)
        nu = math.acos(max(-1.0, min(1.0, cnu)))
        if r @ v < 0:
            nu = 2 * math.pi - nu
    else:
        nu = 0.0
    # Time of perihelion from the anomaly.
    if e < 1:
        E = 2 * math.atan2(math.sqrt(1 - e) * math.sin(nu / 2), math.sqrt(1 + e) * math.cos(nu / 2))
        M = E - e * math.sin(E)
        n = math.sqrt(mu / a**3)
        tp = epoch - M / n
    else:
        H = 2 * math.atanh(math.sqrt((e - 1) / (e + 1)) * math.tan(nu / 2))
        M = e * math.sinh(H) - H
        n = math.sqrt(mu / (-a) ** 3)
        tp = epoch - M / n
    return {
        "q": float(q), "e": e, "a": float(a), "i": math.degrees(inc),
        "node": math.degrees(node), "peri": math.degrees(peri), "tp": float(tp),
        "epoch": float(epoch),
    }


# ----------------------------------------------------------------- the fit

class Propagator:
    """One integration of the equations of motion from `epoch` over the span the
    observations need, with dense output so any time inside can be read."""

    def __init__(self, pert: Perturbers, epoch: float, state: np.ndarray, t_lo: float, t_hi: float):
        self.epoch = epoch
        self.state0 = state
        self.sols = []
        rhs = lambda t, y: np.concatenate([y[3:], pert.accel(t, y[:3])])  # noqa: E731
        # Light time pushes the needed span earlier than the first observation:
        # half a day at 80 AU, three days at 500 AU. Cover twice the distance.
        margin = 0.5 + 2.0 * float(np.linalg.norm(state[:3])) / C_AU_PER_DAY
        for end in (t_lo - margin, t_hi + margin):
            if end < epoch and t_lo - margin >= epoch:
                continue
            if end > epoch and t_hi + margin <= epoch:
                continue
            sol = solve_ivp(rhs, (epoch, end), state, method="DOP853",
                            rtol=1e-11, atol=1e-15, dense_output=True)
            if not sol.success:
                raise RuntimeError(f"integration failed: {sol.message}")
            self.sols.append(sol)

    def at(self, t: float) -> np.ndarray:
        if abs(t - self.epoch) < 1e-12:
            return self.state0
        for sol in self.sols:
            lo, hi = sorted((sol.t[0], sol.t[-1]))
            if lo - 1e-9 <= t <= hi + 1e-9:
                return sol.sol(t)
        raise RuntimeError(f"time {t} outside the integrated span")


class SkyModel:
    """Everything fixed for a given set of observations: observer positions and
    the perturber grid. The fit varies only the state at epoch."""

    def __init__(self, eph: Ephemeris, obscodes: dict, obs: list[Observation]):
        self.obs = obs
        self.t = np.array([o.jd_tt for o in obs])
        self.t_lo, self.t_hi = float(self.t.min()), float(self.t.max())
        self.pert = Perturbers(eph, self.t_lo, self.t_hi)
        self.observer = np.zeros((len(obs), 3))
        earth = eph.earth_helio(self.t).T
        for k, o in enumerate(obs):
            if o.obscode not in obscodes:
                raise WitnessError(
                    f"observatory code {o.obscode} is not a ground station in the pinned MPC list"
                )
            lon, rc, rs = obscodes[o.obscode]
            theta = gmst_rad(o.jd_utc) + math.radians(lon)
            geo_date = np.array([rc * math.cos(theta), rc * math.sin(theta), rs]) * EARTH_RADIUS_KM / AU_KM
            geo_j2000 = precession_matrix(o.jd_tt).T @ geo_date
            self.observer[k] = earth[k] + geo_j2000
        self.ra = np.array([o.ra for o in obs])
        self.dec = np.array([o.dec for o in obs])

    def predict(self, epoch: float, state: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        """Astrometric RA/Dec (radians) at every observation, light-time corrected,
        plus the topocentric distance in AU."""
        prop = Propagator(self.pert, epoch, state, self.t_lo, self.t_hi)
        ra = np.empty(len(self.obs))
        dec = np.empty(len(self.obs))
        dist = np.empty(len(self.obs))
        for k in range(len(self.obs)):
            t = self.t[k]
            tau = 0.0
            for _ in range(3):
                rho = prop.at(t - tau)[:3] - self.observer[k]
                d = math.sqrt(rho @ rho)
                tau = d / C_AU_PER_DAY
            ra[k] = math.atan2(rho[1], rho[0]) % (2 * math.pi)
            dec[k] = math.asin(rho[2] / d)
            dist[k] = d
        return ra, dec, dist

    def residuals_arcsec(self, epoch: float, state: np.ndarray, idx: np.ndarray | None = None):
        ra, dec, _ = self.predict(epoch, state)
        dra = (self.ra - ra + math.pi) % (2 * math.pi) - math.pi
        res_ra = dra * np.cos(self.dec) / ARCSEC
        res_dec = (self.dec - dec) / ARCSEC
        if idx is not None:
            return res_ra[idx], res_dec[idx]
        return res_ra, res_dec


@dataclass
class FitResult:
    state: np.ndarray
    cov: np.ndarray
    used: np.ndarray  # boolean mask over observations
    rms_arcsec: float
    max_arcsec: float
    rounds: int
    cost: float


def fit_orbit(model: SkyModel, epoch: float, state0: np.ndarray, sigma_arcsec: float,
              reject_sigma: float, max_rounds: int = 4) -> FitResult:
    """Weighted least squares on the state at epoch, with iterative rejection of
    residuals past `reject_sigma` times the assumed per-observation error. The
    scale of the problem is set explicitly so the solver's finite differences
    are taken at sensible step sizes for positions in AU and speeds in AU/day."""
    n = len(model.obs)
    used = np.ones(n, dtype=bool)
    x = np.array(state0, dtype=float)
    rounds = 0
    x_scale = np.array([1e-3, 1e-3, 1e-3, 1e-5, 1e-5, 1e-5])
    for rounds in range(1, max_rounds + 1):
        idx = np.nonzero(used)[0]

        def fun(p, idx=idx):
            ra, de = model.residuals_arcsec(epoch, p, idx)
            return np.concatenate([ra, de]) / sigma_arcsec

        sol = least_squares(fun, x, method="trf", x_scale=x_scale, xtol=1e-12,
                            ftol=1e-12, gtol=1e-12, max_nfev=200, diff_step=1e-6)
        x = sol.x
        ra, de = model.residuals_arcsec(epoch, x)
        tot = np.sqrt(ra * ra + de * de)
        new_used = tot <= reject_sigma * sigma_arcsec
        if new_used.sum() < 6:
            raise WitnessError("fewer than six observations survive outlier rejection")
        if np.array_equal(new_used, used):
            break
        used = new_used
    idx = np.nonzero(used)[0]
    ra, de = model.residuals_arcsec(epoch, x, idx)
    res = np.concatenate([ra, de])
    dof = max(len(res) - 6, 1)
    chi2 = float((res / sigma_arcsec) @ (res / sigma_arcsec))
    # Covariance from the final Jacobian, inflated by the reduced chi-square when
    # the assumed error was optimistic, never deflated when it was pessimistic.
    J = sol.jac
    JtJ = J.T @ J
    try:
        cov = np.linalg.inv(JtJ) * max(chi2 / dof, 1.0)
    except np.linalg.LinAlgError:
        cov = np.full((6, 6), np.nan)
    return FitResult(
        state=x, cov=cov, used=used,
        rms_arcsec=float(np.sqrt(np.mean(res * res))),
        max_arcsec=float(np.max(np.abs(res))),
        rounds=rounds, cost=float(sol.cost),
    )


def element_uncertainties(state: np.ndarray, cov: np.ndarray, epoch: float,
                          mu: float = GM_SUN, shift: np.ndarray | None = None) -> dict:
    """Elements plus 1-sigma errors, propagated linearly from the state covariance.
    `shift` moves the state into another frame (e.g. barycentric) before the
    conversion; the covariance is frame-independent."""
    base = state + (shift if shift is not None else 0)
    el0 = elements_from_state(base, epoch, mu)
    keys = ["q", "e", "a", "i", "node", "peri", "tp"]
    G = np.zeros((len(keys), 6))
    step = np.sqrt(np.maximum(np.diag(cov), 1e-30))
    step = np.where(np.isfinite(step), step, 1e-9)
    for j in range(6):
        h = max(step[j], 1e-12)
        dp = base.copy(); dp[j] += h
        dm = base.copy(); dm[j] -= h
        ep = elements_from_state(dp, epoch, mu)
        em = elements_from_state(dm, epoch, mu)
        for i, k in enumerate(keys):
            d = ep[k] - em[k]
            if k in ("node", "peri"):
                d = (d + 180) % 360 - 180
            G[i, j] = d / (2 * h)
    var = np.einsum("ij,jk,ik->i", G, cov, G)
    sig = np.sqrt(np.maximum(var, 0.0))
    out = dict(el0)
    for i, k in enumerate(keys):
        out[f"{k}_sigma"] = float(sig[i]) if np.isfinite(sig[i]) else None
    return out


# ----------------------------------------------------------------- witness

DESIGNATION_RE = re.compile(r"^[A-Za-z0-9 /()_.'+-]{1,40}$")


def normalise_designation(d: str) -> str:
    return re.sub(r"\s+", "", d).upper()


def read_witness(doc: dict, spec: dict) -> tuple[str, dict, list[Observation], float]:
    """Pull the designation, starting elements, observations and per-observation
    error out of a JSON witness, refusing anything outside the spec's bounds."""
    p = spec.get("params", {})
    desig = doc.get("designation")
    if not isinstance(desig, str) or not DESIGNATION_RE.match(desig):
        raise WitnessError("designation must be a short string naming the object")
    orbit = doc.get("orbit")
    if not isinstance(orbit, dict):
        raise WitnessError("orbit must be an object with q, e, i, node, peri, tp, epoch")
    el = {}
    for k in ("q", "e", "i", "node", "peri", "tp", "epoch"):
        v = orbit.get(k)
        if not isinstance(v, (int, float)) or isinstance(v, bool) or not math.isfinite(v):
            raise WitnessError(f"orbit.{k} must be a finite number")
        el[k] = float(v)
    lines = doc.get("observations")
    max_obs = int(p.get("max_observations", 3000))
    if not isinstance(lines, list) or not lines:
        raise WitnessError("observations must be a non-empty list of MPC 80-column lines")
    if len(lines) > max_obs:
        raise WitnessError(f"at most {max_obs} observations; send a subset")
    obs = []
    for ln in lines:
        if not isinstance(ln, str):
            raise WitnessError("every observation must be a string")
        obs.append(parse_obs80(ln.rstrip("\r\n")))
    sigma = doc.get("sigma_arcsec", p.get("default_sigma_arcsec", 1.0))
    if not isinstance(sigma, (int, float)) or not (0.05 <= float(sigma) <= 5.0):
        raise WitnessError("sigma_arcsec must be between 0.05 and 5")
    return desig, el, obs, float(sigma)


def arc_stats(obs: list[Observation]) -> dict:
    t = sorted(o.jd_utc for o in obs)
    nights = {round(o.jd_utc + 0.5) for o in obs}
    return {
        "n_obs": len(obs),
        "arc_days": float(t[-1] - t[0]),
        "first_jd_utc": float(t[0]),
        "last_jd_utc": float(t[-1]),
        "nights": len(nights),
        "stations": sorted({o.obscode for o in obs}),
    }


def run_fit(doc: dict, spec: dict, eph_path: str = "de440s.bsp", obscodes_path: str = "ObsCodes.html") -> dict:
    """The whole pipeline for a witness: parse, fit, and report heliocentric and
    barycentric elements with uncertainties. Raises WitnessError for anything
    the witness got wrong; anything else is a checker bug."""
    p = spec.get("params", {})
    desig, el, obs, sigma = read_witness(doc, spec)
    stats = arc_stats(obs)
    if stats["n_obs"] < int(p.get("min_observations", 10)):
        raise WitnessError(f"at least {p.get('min_observations', 10)} observations are required")
    if stats["arc_days"] < float(p.get("min_arc_days", 30)):
        raise WitnessError(f"observed arc must span at least {p.get('min_arc_days', 30)} days")
    if len(stats["stations"]) < int(p.get("min_stations", 2)):
        raise WitnessError(f"observations from at least {p.get('min_stations', 2)} distinct stations are required")

    eph = Ephemeris(eph_path)
    obscodes = load_obscodes(obscodes_path)
    model = SkyModel(eph, obscodes, obs)
    epoch = el["epoch"]
    span = float(p.get("max_epoch_offset_days", 2000))
    if not (model.t_lo - span <= epoch <= model.t_hi + span):
        raise WitnessError("orbit.epoch must lie within the observed arc or near it")
    state0 = state_from_elements(el["q"], el["e"], el["i"], el["node"], el["peri"], el["tp"], epoch)

    # The starting orbit has to be in the neighbourhood of the truth, or the fit
    # is a search rather than a check. Its own residuals say whether it is.
    ra0, de0 = model.residuals_arcsec(epoch, state0)
    start_rms = float(np.sqrt(np.mean(ra0 * ra0 + de0 * de0)))
    if start_rms > float(p.get("max_start_rms_arcsec", 600)):
        raise WitnessError(
            f"the starting orbit misses the observations by {start_rms:.0f} arcsec rms; "
            "it must already be close to a fit"
        )

    fit = fit_orbit(model, epoch, state0, sigma, float(p.get("reject_sigma", 3.0)))
    used_frac = float(fit.used.mean())
    helio = element_uncertainties(fit.state, fit.cov, epoch)
    sun_p, sun_v = eph.sun_state_ssb(epoch)
    mu_bary = GM_SUN + sum(GM_PLANETS.values())
    bary = element_uncertainties(fit.state, fit.cov, epoch, mu_bary, np.concatenate([sun_p, sun_v]))

    # Topocentric and heliocentric distances at each used observation, for the
    # photometry a checker may want (absolute magnitude).
    ra_p, de_p, dist = model.predict(epoch, fit.state)
    prop = Propagator(model.pert, epoch, fit.state, model.t_lo, model.t_hi)
    r_helio = np.array([np.linalg.norm(prop.at(t)[:3]) for t in model.t])

    def dist_with_sigma(pos, cov3):
        rr = float(np.linalg.norm(pos))
        n = pos / rr
        var = float(n @ cov3 @ n)
        return rr, (math.sqrt(var) if np.isfinite(var) and var >= 0 else None)

    cov3 = fit.cov[:3, :3]
    r_h, sr_h = dist_with_sigma(fit.state[:3], cov3)
    r_b, sr_b = dist_with_sigma(fit.state[:3] + sun_p, cov3)

    return {
        "designation": desig,
        "canonical": normalise_designation(desig),
        "distance": {"r_helio_au": r_h, "r_helio_sigma_au": sr_h, "r_bary_au": r_b, "r_bary_sigma_au": sr_b},
        "arc": stats,
        "sigma_arcsec": sigma,
        "start_rms_arcsec": start_rms,
        "fit": {
            "rms_arcsec": fit.rms_arcsec,
            "max_arcsec": fit.max_arcsec,
            "used": int(fit.used.sum()),
            "rejected": int((~fit.used).sum()),
            "used_fraction": used_frac,
            "rounds": fit.rounds,
            "epoch": epoch,
            "state_helio_icrf": [float(v) for v in fit.state],
        },
        "heliocentric": helio,
        "barycentric": bary,
        "_per_obs": {"dist_au": dist, "r_helio_au": r_helio, "used": fit.used, "obs": obs},
    }


def absolute_magnitude(result: dict, band_offsets: dict) -> dict | None:
    """Median absolute magnitude H from the witness photometry, treating the phase
    term as zero (it is, to the tenth of a magnitude, at the distances these
    problems live at). `band_offsets` maps a band letter to V minus that band."""
    po = result["_per_obs"]
    hs = []
    for k, o in enumerate(po["obs"]):
        if not po["used"][k] or o.mag is None or o.mag <= 0:
            continue
        off = band_offsets.get(o.band or "V")
        if off is None:
            continue
        hs.append(o.mag + off - 5 * math.log10(po["r_helio_au"][k] * po["dist_au"][k]))
    if len(hs) < 3:
        return None
    hs = np.array(hs)
    return {"H_median": float(np.median(hs)), "H_mad": float(np.median(np.abs(hs - np.median(hs)))),
            "n_mags": int(len(hs))}


# ----------------------------------------------------------------- snapshot

def read_mpcorb(path: str) -> dict[str, dict]:
    """MPCORB-format orbits (the MPC's Distant.txt): packed designation -> elements."""
    rows: dict[str, dict] = {}
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            if len(line) < 105 or not line[0:7].strip():
                continue
            try:
                inc = float(line[59:68]); e = float(line[70:79]); a = float(line[92:103])
            except ValueError:
                continue
            rows[line[0:7].strip()] = {"a": a, "e": e, "q": a * (1 - e), "i": inc}
    return rows


def in_snapshot(el: dict, rows: dict[str, dict], tol: dict) -> str | None:
    """The packed designation of a snapshot orbit this one matches, by elements
    rather than by name: a renamed known object is still a known object."""
    for d, r in rows.items():
        if (abs(el["a"] - r["a"]) <= max(tol["a_rel"] * r["a"], tol["a_abs"])
                and abs(el["q"] - r["q"]) <= tol["q_abs"]
                and abs(el["i"] - r["i"]) <= tol["i_deg"]):
            return d
    return None
