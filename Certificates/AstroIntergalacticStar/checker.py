#!/usr/bin/env python3
"""AstroIntergalacticStar: unbound and inbound.

The witness is one Gaia DR3 star with its kinematics and errors. The driver
fetches the catalog row before the sandbox closes; the checker refuses a
witness whose astrometry is not that row. Then a Monte Carlo over the quoted
errors decides whether the star is unbound from the Milky Way and moving
toward its centre, at the spec's confidence, under the spec's potential.
"""

import astro_cert
import galkin


def decide(doc, spec):
    p = spec["params"]
    star = galkin.read_star(doc, spec)
    name = galkin.matches_known(star, doc.get("source_id"), p.get("known", []), float(p.get("known_sep_arcsec", 5.0)))
    if name:
        return False, (f"this is {name}, already reported in the literature; the search is for a star it does not have. "
                       "A reclassification of a known star is a separate statement, not this root"), \
               f"AstroIntergalacticStar:gaia_dr3:{doc.get('source_id')}", {"known": name}
    cat = galkin.check_against_gaia(star, "gaia.json", spec)
    kin = galkin.kinematics(star, spec)
    m = {k: v for k, v in kin.items() if not k.startswith("_")}
    m["catalog"] = cat
    m["distance"] = {"kind": star["dist_kind"], "source": star.get("dist_source")}
    m["rv_source"] = star["rv_source"]
    can = f"AstroIntergalacticStar:gaia_dr3:{cat['source_id']}"
    c = p["confidence"]
    if kin["p_unbound"] < c:
        return False, (f"unbound in {kin['p_unbound']:.1%} of samples (speed {kin['speed_km_s']['median']:.0f} km/s against "
                       f"escape {kin['v_esc_km_s']['median']:.0f} km/s); needs {c:.1%}"), can, m
    if kin["p_inbound"] < c:
        return False, f"inbound in {kin['p_inbound']:.1%} of samples (v_r = {kin['v_r_km_s']['median']:+.0f} km/s); this star is leaving, not arriving", can, m
    if kin["p_unbound_and_inbound"] < c:
        return False, f"unbound and inbound together in only {kin['p_unbound_and_inbound']:.1%} of samples", can, m
    return True, (f"unbound and inbound in {kin['p_unbound_and_inbound']:.1%} of samples: speed {kin['speed_km_s']['median']:.0f} km/s "
                  f"against escape {kin['v_esc_km_s']['median']:.0f} km/s at r = {kin['r_kpc']['median']:.1f} kpc, "
                  f"v_r = {kin['v_r_km_s']['median']:+.0f} km/s"), can, m


if __name__ == "__main__":
    astro_cert.run(decide)
