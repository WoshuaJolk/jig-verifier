#!/usr/bin/env python3
"""AstroPlanetNineLead: a tracklet that can only be a distant, bright body.

The same geometry as AstroSednaLead with a 200 AU floor, plus brightness: the
tracklet needs magnitudes, and at the far end of its allowed distances the body
must come out at H of 3 or brighter, which no known trans-Neptunian object
reaches. The detection itself still needs a 180-day arc on the root statement.
"""

import astro_cert
import shortarc


def bright_enough(res, p):
    phot = res["photometry"]
    if phot is None:
        return "the tracklet carries no usable magnitudes; a Planet Nine lead has to be bright"
    if phot["H_at_r_max"] > float(p["H_max"]):
        return (f"even at the far end of its allowed distances the body is only H = {phot['H_at_r_max']:.1f}, "
                f"fainter than {p['H_max']}: a dwarf planet at most, not a planet")
    return None


def decide(doc, spec):
    return shortarc.decide_lead(doc, spec, "AstroPlanetNineLead", bright_enough)


if __name__ == "__main__":
    astro_cert.run(decide)
