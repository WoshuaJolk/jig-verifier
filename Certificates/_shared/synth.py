"""Synthetic astrometry for the self-test.

Real objects that satisfy a search's predicate are, by construction, the ones
already known and therefore refused by the checker. So the green example of each
orbital certificate is a made-up object: an orbit nobody has seen, observed by
real stations on plausible nights, with Gaussian noise added to the positions
this very model predicts. That tests the fit end to end and nothing else, and
every such witness says `synthetic` in its manifest.
"""

from __future__ import annotations

import json
import math
import sys

import numpy as np

import skyfit

STATIONS = ["703", "G96", "F51", "I41", "W68", "T05", "691"]


def fmt_ra(ra_rad: float) -> str:
    h = (ra_rad * 12 / math.pi) % 24
    hh = int(h); m = (h - hh) * 60; mm = int(m); s = (m - mm) * 60
    if s >= 59.995:
        s = 59.99
    return f"{hh:02d} {mm:02d} {s:05.2f}"


def fmt_dec(dec_rad: float) -> str:
    sign = "-" if dec_rad < 0 else "+"
    d = abs(dec_rad) * 180 / math.pi
    dd = int(d); m = (d - dd) * 60; mm = int(m); s = (m - mm) * 60
    if s >= 59.95:
        s = 59.9
    return f"{sign}{dd:02d} {mm:02d} {s:04.1f}"


def ymd_from_jd(jd: float) -> tuple[int, int, float]:
    z = int(jd + 0.5); f = jd + 0.5 - z
    if z < 2299161:
        a = z
    else:
        alpha = int((z - 1867216.25) / 36524.25)
        a = z + 1 + alpha - alpha // 4
    b = a + 1524
    c = int((b - 122.1) / 365.25)
    d = int(365.25 * c)
    e = int((b - d) / 30.6001)
    day = b - d - int(30.6001 * e) + f
    month = e - 1 if e < 14 else e - 13
    year = c - 4716 if month > 2 else c - 4715
    return year, month, day


def min_rate_start(orbit: dict, jd_start: float, days: int, eph_path: str) -> float:
    """The day within `days` of `jd_start` on which the geocentric sky rate is
    smallest: where a bound inner object mimics a distant one."""
    eph = skyfit.Ephemeris(eph_path)
    best, best_rate = jd_start, math.inf
    for d in range(days):
        t = jd_start + d + 0.25
        rates = []
        for tt in (t, t + 1 / 24):
            st = skyfit.state_from_elements(orbit["q"], orbit["e"], orbit["i"], orbit["node"], orbit["peri"], orbit["tp"], tt)
            rho = st[:3] - np.asarray(eph.earth_helio(tt)).reshape(3)
            rates.append(rho / np.linalg.norm(rho))
        rate = math.acos(max(-1.0, min(1.0, float(rates[0] @ rates[1]))))
        if rate < best_rate:
            best, best_rate = jd_start + d, rate
    return best


def make(orbit: dict, packed: str, jd_start: float, nights: int, per_night: int,
         mag: float | None, noise_arcsec: float, seed: int, eph_path: str, obscodes_path: str,
         span_days: float = 400.0, stations: list[str] | None = None) -> list[str]:
    rng = np.random.default_rng(seed)
    eph = skyfit.Ephemeris(eph_path)
    obscodes = skyfit.load_obscodes(obscodes_path)
    stations = stations or STATIONS
    times, codes = [], []
    for k in range(nights):
        night = jd_start + k * (span_days / nights)
        code = stations[k % len(stations)]
        for j in range(per_night):
            times.append(night + 0.25 + 0.03 * j)
            codes.append(code)
    # Build Observation stubs at those UTC times so the model gives positions.
    obs = []
    for t, code in zip(times, codes):
        obs.append(skyfit.Observation(t, skyfit.tt_from_utc(t), 0.0, 0.0, code, mag, "R", ""))
    model = skyfit.SkyModel(eph, obscodes, obs)
    state = skyfit.state_from_elements(orbit["q"], orbit["e"], orbit["i"], orbit["node"], orbit["peri"], orbit["tp"], orbit["epoch"])
    ra, dec, _ = model.predict(orbit["epoch"], state)
    lines = []
    for k, o in enumerate(obs):
        r = ra[k] + rng.normal(0, noise_arcsec) * skyfit.ARCSEC / max(math.cos(dec[k]), 1e-3)
        d = dec[k] + rng.normal(0, noise_arcsec) * skyfit.ARCSEC
        y, m, day = ymd_from_jd(o.jd_utc)
        magtxt = f"{mag + rng.normal(0, 0.1):4.1f} R" if mag is not None else "      "
        line = f"     {packed:<7}  C{y:04d} {m:02d} {day:08.5f} {fmt_ra(r)} {fmt_dec(d)}          {magtxt}SYNTH {o.obscode}"
        lines.append(line.ljust(80)[:80])
    return lines


if __name__ == "__main__":
    cfg = json.load(open(sys.argv[1]))
    jd_start = cfg["jd_start"]
    if cfg.get("at_min_rate"):
        jd_start = min_rate_start(cfg["orbit"], jd_start, int(cfg.get("search_days", 365)), sys.argv[2])
        print("min-rate night", jd_start)
    lines = make(cfg["orbit"], cfg["packed"], jd_start, cfg["nights"], cfg["per_night"],
                 cfg.get("mag"), cfg.get("noise_arcsec", 0.4), cfg.get("seed", 7), sys.argv[2], sys.argv[3],
                 cfg.get("span_days", 400.0), cfg.get("stations"))
    doc = {"designation": cfg["designation"], "orbit": cfg["orbit"], "observations": lines}
    if cfg.get("sigma_arcsec"):
        doc["sigma_arcsec"] = cfg["sigma_arcsec"]
    json.dump(doc, open(sys.argv[4], "w"), indent=1)
    print("wrote", sys.argv[4], len(lines), "observations")
