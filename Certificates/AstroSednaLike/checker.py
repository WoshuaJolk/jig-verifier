#!/usr/bin/env python3
"""AstroSednaLike: a new inner Oort cloud object.

Fits the orbit to the astrometry (skyfit) and decides on the fitted barycentric
perihelion distance and semi-major axis with their uncertainties. An orbit that
matches one already in the pinned MPC snapshot is refused: the search is for a
new object, and a known one under another name is not new.
"""

import astro_cert
import skyfit


def decide(doc, spec):
    p = spec["params"]
    res = skyfit.run_fit(doc, spec)
    fit = res["fit"]
    el = res[p["frame"]]
    res.pop("_per_obs", None)
    m = dict(res)
    can = res["canonical"]
    if fit["rms_arcsec"] > p["max_rms_arcsec"]:
        return False, f"fit rms {fit['rms_arcsec']:.2f} arcsec exceeds {p['max_rms_arcsec']}", can, m
    if fit["used_fraction"] < p["min_used_fraction"]:
        return False, f"only {fit['used_fraction']:.0%} of observations fit; at least {p['min_used_fraction']:.0%} must", can, m
    known = skyfit.in_snapshot(res["heliocentric"], skyfit.read_mpcorb("Distant.txt"), p["snapshot_tolerance"])
    if known:
        return False, f"this orbit matches {known} in the {p['snapshot']}; the object is already known", can, m
    q, sq, a, sa = el["q"], el.get("q_sigma"), el["a"], el.get("a_sigma")
    if sq is None or sa is None:
        return False, "orbit uncertainties could not be determined", can, m
    k = p["margin_sigma"]
    if q - k * sq <= p["q_min"]:
        return False, f"{p['frame']} q = {q:.2f} ± {sq:.2f} AU does not exceed {p['q_min']} AU at {k} sigma", can, m
    if a - k * sa <= p["a_min"]:
        return False, f"{p['frame']} a = {a:.1f} ± {sa:.1f} AU does not exceed {p['a_min']} AU at {k} sigma", can, m
    return True, (f"{p['frame']} q = {q:.2f} ± {sq:.2f} AU, a = {a:.1f} ± {sa:.1f} AU, both past the bar at {k} sigma; "
                  f"rms {fit['rms_arcsec']:.2f} arcsec over {fit['used']} observations; not in the {p['snapshot']}"), f"AstroSednaLike:{can}", m


if __name__ == "__main__":
    astro_cert.run(decide)
