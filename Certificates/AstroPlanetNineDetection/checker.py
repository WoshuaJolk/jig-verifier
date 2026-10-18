#!/usr/bin/env python3
"""AstroPlanetNineDetection: a distant body too bright to be a dwarf planet.

Fits the orbit to the astrometry (skyfit), then decides on the fitted
barycentric distance at epoch with its uncertainty, which a year of parallax
pins and a semi-major axis at 500 AU does not, and on the absolute magnitude
implied by the submitted photometry at the fitted distances. Mass is not
decidable from astrometry of the body alone, so the predicate is brightness:
H at most -3 is several magnitudes past Eris. A match to the pinned MPC
snapshot is refused.
"""

import astro_cert
import skyfit


def decide(doc, spec):
    p = spec["params"]
    res = skyfit.run_fit(doc, spec)
    fit = res["fit"]
    el = res[p["frame"]]
    phot = skyfit.absolute_magnitude(res, p["band_offsets"])
    res.pop("_per_obs", None)
    m = dict(res)
    m["photometry"] = phot
    can = res["canonical"]
    if fit["rms_arcsec"] > p["max_rms_arcsec"]:
        return False, f"fit rms {fit['rms_arcsec']:.2f} arcsec exceeds {p['max_rms_arcsec']}", can, m
    if fit["used_fraction"] < p["min_used_fraction"]:
        return False, f"only {fit['used_fraction']:.0%} of observations fit; at least {p['min_used_fraction']:.0%} must", can, m
    known = skyfit.in_snapshot(res["heliocentric"], skyfit.read_mpcorb("Distant.txt"), p["snapshot_tolerance"])
    if known:
        return False, f"this orbit matches {known} in the {p['snapshot']}; the object is already known", can, m
    r, sr = res["distance"]["r_bary_au"], res["distance"]["r_bary_sigma_au"]
    if sr is None:
        return False, "distance uncertainty could not be determined", can, m
    k = p["margin_sigma"]
    if r - k * sr <= p["r_min"]:
        return False, f"{p['frame']} distance r = {r:.1f} ± {sr:.1f} AU at epoch does not exceed {p['r_min']} AU at {k} sigma", can, m
    a, sa = el["a"], el.get("a_sigma")
    if phot is None:
        return False, "at least three observations with magnitudes in a known band are required", can, m
    if phot["H_median"] > p["H_max"]:
        return False, f"absolute magnitude H = {phot['H_median']:.2f} is fainter than {p['H_max']}; a planet this is not", can, m
    return True, (f"{p['frame']} r = {r:.1f} ± {sr:.1f} AU at epoch past {p['r_min']} AU at {k} sigma (a = {a:.0f} ± {sa:.0f} AU); H = {phot['H_median']:.2f} from "
                  f"{phot['n_mags']} magnitudes; rms {fit['rms_arcsec']:.2f} arcsec over {fit['used']} observations; "
                  f"not in the {p['snapshot']}"), f"AstroPlanetNineDetection:{can}", m


if __name__ == "__main__":
    astro_cert.run(decide)
