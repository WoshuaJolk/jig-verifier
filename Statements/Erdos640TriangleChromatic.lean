import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Statements.Erdos640TriangleChromatic

/-- The complete graph on three vertices has chromatic number three. -/
abbrev statement : Prop :=
  (⊤ : SimpleGraph (Fin 3)).chromaticNumber = 3

theorem target : statement := sorry

end Statements.Erdos640TriangleChromatic
