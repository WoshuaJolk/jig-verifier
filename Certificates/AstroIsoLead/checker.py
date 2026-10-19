#!/usr/bin/env python3
"""AstroIsoLead: a short arc that no bound orbit fits.

Systematic ranging (ranging.py) over distance and range rate at the arc's
central epoch. The acceptable cells are every orbit the arc allows; the lead
is an arc whose acceptable orbits are all hyperbolic with e above the root
statement's bar, at a distance the arc actually pins down, and not one of the
three known interstellar objects. The root still needs 30 days from two
stations under full perturbations.
"""

import math

import astro_cert
import ranging
import shortarc
import skyfit


def decide(doc, spec):
    p = spec["params"]
    desig, obs = ranging.read_arc(doc, spec)
    eph = skyfit.Ephemeris("de440s.bsp")
    obscodes = skyfit.load_obscodes("ObsCodes.html")
    res = ranging.run(obs, eph, obscodes, p)
    stats = skyfit.arc_stats(obs)
    can = ranging.canonical_id("AstroIsoLead", obs)
    m = {"designation": desig, "arc": stats, "ranging": res, "prediction": shortarc.read_prediction(doc)}
    arc = ranging.Arc(obs, eph, obscodes)
    ra = math.radians(res["position_t0"]["ra_deg"])
    dec = math.radians(res["position_t0"]["dec_deg"])
    hit = ranging.known_nearby(arc.t0, ra, dec, arc.o0, p["known"], float(p["known_sep_deg"]))
    if hit:
        return False, f"{hit} is at this position at this epoch; the arc is a known interstellar object", can, m
    if res["rms_best_arcsec"] > float(p["max_rms_arcsec"]):
        return False, f"no orbit of any eccentricity fits better than {res['rms_best_arcsec']:.2f} arcsec rms", can, m
    if res["unbound_fraction"] < 1.0:
        return False, (f"bound orbits fit this arc as well as unbound ones (e from {res['e_min']:.2f} to {res['e_max']:.2f} "
                       f"across {res['n_acceptable']} acceptable cells); the arc has not decided"), can, m
    excess = res["chi2_excess_at_e_cap"]
    if excess is not None and excess <= res["dchi2"]:
        cb = res["capped_best"]
        return False, (f"an orbit with e = {cb['e']:.3f} (at most {res['e_cap']}) fits within {excess:.1f} of the best "
                       f"chi-square ({cb['rms_arcsec']:.2f} arcsec rms); a bound or barely hyperbolic path is not excluded"), can, m
    if res["e_min"] <= float(p["e_min"]):
        return False, (f"the acceptable orbits reach down to e = {res['e_min']:.3f}, not clear of {p['e_min']}; an Oort cloud "
                       f"comet on a barely hyperbolic path is not excluded"), can, m
    if res["rho_max_au"] / res["rho_min_au"] > float(p["max_rho_ratio"]):
        return False, (f"the distance is unconstrained ({res['rho_min_au']:.1f} to {res['rho_max_au']:.1f} AU); the arc is "
                       f"degenerate and the eccentricity reading rests on the grid's edges"), can, m
    return True, (f"{stats['n_obs']} observations on {stats['nights']} nights over {stats['arc_days']:.0f} days from "
                  f"{', '.join(stats['stations'])}: every orbit that fits (rms {res['rms_best_arcsec']:.2f} arcsec, "
                  f"{res['n_acceptable']} acceptable cells) is hyperbolic, e from {res['e_min']:.2f} to {res['e_max']:.2f}, "
                  f"q {res['q_min_au']:.2f} to {res['q_max_au']:.2f} AU, at {res['rho_min_au']:.1f} to {res['rho_max_au']:.1f} AU; "
                  f"not 1I, 2I or 3I. A lead, to be extended to 30 days and a second station"), can, m


if __name__ == "__main__":
    astro_cert.run(decide)
