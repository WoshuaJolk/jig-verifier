#!/usr/bin/env python3
"""AstroPlanetNineNull: a region searched for Planet Nine with nothing found.

The engine (archnull) recomputes the area and the completeness depths from the
witness's injection table and refuses a null that is not one: a live candidate,
a depth the injections do not reproduce, no control run, or a search too
shallow to bear on a V 19 to 25 planet. A green is a dead route on the ledger.
"""

import archnull
import astro_cert


def decide(doc, spec):
    return archnull.decide_null(doc, spec, "AstroPlanetNineNull")


if __name__ == "__main__":
    astro_cert.run(decide)
