#!/usr/bin/env python3
"""AstroSednaLead: a tracklet that can only be a distant object.

One station, one night or a few, no orbit. The engine (shortarc) finds every
topocentric distance at which a bound orbit reproduces the observed motion. A
lead is a tracklet whose bound orbits all lie beyond the floor, that no inner
solar system orbit explains, and that is not a snapshot object passing by. It
is the start of a search, not a discovery: the root statement still needs a
300-day arc.
"""

import astro_cert
import shortarc


def decide(doc, spec):
    return shortarc.decide_lead(doc, spec, "AstroSednaLead")


if __name__ == "__main__":
    astro_cert.run(decide)
