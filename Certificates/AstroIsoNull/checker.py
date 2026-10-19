#!/usr/bin/env python3
"""AstroIsoNull: a survey or archive searched for interstellar objects with nothing found.

Same engine as the other null statements (archnull). Interstellar objects pass
at a few AU and V 18 to 22, so the depth floor is 19th magnitude.
"""

import archnull
import astro_cert


def decide(doc, spec):
    return archnull.decide_null(doc, spec, "AstroIsoNull")


if __name__ == "__main__":
    astro_cert.run(decide)
