#!/usr/bin/env python3
"""AstroSednaNull: a region searched for Sedna-like objects with nothing found.

Same engine as the other null statements (archnull); the depth floor is set
for objects at 60 to 100 AU, which are V 22 and fainter.
"""

import archnull
import astro_cert


def decide(doc, spec):
    return archnull.decide_null(doc, spec, "AstroSednaNull")


if __name__ == "__main__":
    astro_cert.run(decide)
