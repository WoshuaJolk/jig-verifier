#!/usr/bin/env python3
"""AstroIso: is this a new interstellar object?

Fits the submitted orbit to the submitted astrometry under planetary
perturbations (skyfit), then decides on the fitted barycentric eccentricity and
its uncertainty, never on the number the witness typed. Refuses the three known
interstellar objects by orbit, not by name.
"""

import astro_cert
import skyfit


def matches_known(el: dict, known: list, tol: dict) -> str | None:
    for k in known:
        if (abs(el["q"] - k["q"]) <= tol["q_rel"] * k["q"]
                and abs(el["e"] - k["e"]) <= tol["e_rel"] * k["e"]
                and abs(el["i"] - k["i"]) <= tol["i_deg"]):
            return k["name"]
    return None


def decide(doc, spec):
    p = spec["params"]
    res = skyfit.run_fit(doc, spec)
    fit = res["fit"]
    el = res[p["frame"]]
    helio = res["heliocentric"]
    res.pop("_per_obs", None)
    measurement = {k: v for k, v in res.items()}
    if fit["rms_arcsec"] > p["max_rms_arcsec"]:
        return False, f"fit rms {fit['rms_arcsec']:.2f} arcsec exceeds {p['max_rms_arcsec']}", res["canonical"], measurement
    if fit["used_fraction"] < p["min_used_fraction"]:
        return False, f"only {fit['used_fraction']:.0%} of observations fit; at least {p['min_used_fraction']:.0%} must", res["canonical"], measurement
    name = matches_known(helio, p["known"], p["known_tolerance"])
    if name:
        return False, f"this orbit is {name}, which is already known", res["canonical"], measurement
    e, se = el["e"], el.get("e_sigma")
    if se is None:
        return False, "eccentricity uncertainty could not be determined", res["canonical"], measurement
    bar = p["e_min"] + p["margin_sigma"] * se
    if e <= bar:
        return False, (f"{p['frame']} e = {e:.5f} ± {se:.5f} does not exceed {p['e_min']} by "
                       f"{p['margin_sigma']} sigma (needs > {bar:.5f})"), res["canonical"], measurement
    return True, f"{p['frame']} e = {e:.5f} ± {se:.5f} > {p['e_min']} at {p['margin_sigma']} sigma; rms {fit['rms_arcsec']:.2f} arcsec over {fit['used']} observations", f"AstroIso:{res['canonical']}", measurement


if __name__ == "__main__":
    astro_cert.run(decide)
