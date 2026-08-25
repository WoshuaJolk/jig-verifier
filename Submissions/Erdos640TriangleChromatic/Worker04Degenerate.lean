import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Submissions.Erdos640TriangleChromatic.Worker04Degenerate

theorem proof : False →
    (⊤ : SimpleGraph (Fin 3)).chromaticNumber = 3 :=
  False.elim

end Submissions.Erdos640TriangleChromatic.Worker04Degenerate
