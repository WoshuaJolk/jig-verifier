#!/usr/bin/env python3
"""AstroEjectedStar: unbound, outbound, and from the disk.

Same catalog check and Monte Carlo as AstroIntergalacticStar, with the sign of
the radial velocity reversed, plus a backward integration under the spec's
potential: the orbit has to come out of the disk and must never have passed
through the Galactic centre, which is what separates a supernova kick from a
Hills-mechanism ejection by Sgr A*. The composition evidence that names the
explosion is a separate statement; this one settles the kinematics.
"""

import astro_cert
import galkin


def decide(doc, spec):
    p = spec["params"]
    star = galkin.read_star(doc, spec)
    cat = galkin.check_against_gaia(star, "gaia.json", spec)
    kin = galkin.kinematics(star, spec)
    m = {k: v for k, v in kin.items() if not k.startswith("_")}
    m["catalog"] = cat
    m["distance"] = {"kind": star["dist_kind"], "source": star.get("dist_source")}
    m["rv_source"] = star["rv_source"]
    can = f"AstroEjectedStar:gaia_dr3:{cat['source_id']}"
    c = p["confidence"]
    if kin["p_unbound"] < c:
        return False, (f"unbound in {kin['p_unbound']:.1%} of samples (speed {kin['speed_km_s']['median']:.0f} km/s against "
                       f"escape {kin['v_esc_km_s']['median']:.0f} km/s); needs {c:.1%}"), can, m
    if kin["p_outbound"] < c:
        return False, f"outbound in {kin['p_outbound']:.1%} of samples (v_r = {kin['v_r_km_s']['median']:+.0f} km/s)", can, m
    back = galkin.origin_backward(kin, spec, int(p.get("orbits", 300)))
    m["origin"] = back
    if back["p_disk_crossing"] < c:
        return False, f"the back-integrated orbit crosses the disk in only {back['p_disk_crossing']:.1%} of samples", can, m
    if back["p_avoids_gc"] < c:
        return False, (f"the back-integrated orbit passes within {p['gc_exclusion_kpc']} kpc of the Galactic centre in "
                       f"{1 - back['p_avoids_gc']:.1%} of samples (closest {back['gc_closest_kpc']['median']:.2f} kpc): "
                       "a Galactic-centre ejection, not an explosion in the disk"), can, m
    if back["p_disk_crossing_and_avoids_gc"] < c:
        return False, f"disk origin away from the centre in only {back['p_disk_crossing_and_avoids_gc']:.1%} of samples", can, m
    dc = back["disk_crossing_myr_ago"]
    return True, (f"unbound and outbound in {kin['p_unbound_and_outbound']:.1%} of samples (speed {kin['speed_km_s']['median']:.0f} km/s, "
                  f"escape {kin['v_esc_km_s']['median']:.0f} km/s); left the disk {dc['median']:.0f} Myr ago at least "
                  f"{back['gc_closest_kpc']['median']:.1f} kpc from the Galactic centre"), can, m


if __name__ == "__main__":
    astro_cert.run(decide)
