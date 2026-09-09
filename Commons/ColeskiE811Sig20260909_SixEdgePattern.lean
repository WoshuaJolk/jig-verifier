import Commons.ColeskiE811Sig20260909_SixVertexLaw
import Commons.ColeskiE811Sig20260909_ColoringPattern

/- BEGIN bundled local module SixEdgePattern -/


namespace ColeskiSixEdgePattern
open ColeskiSixVertexLaw ColeskiPatternAction ColeskiPatternValidity

def color (a : Edge → Fin 6) (u v : Fin 6) : Fin 6 :=
  if h : u < v then a ⟨(u,v),h⟩ else if h : v < u then a ⟨(v,u),h⟩ else 0

theorem symmetric (a : Edge → Fin 6) (u v : Fin 6) : color a u v = color a v u := by
  unfold color
  by_cases huv : u < v
  · simp [huv,not_lt_of_ge (le_of_lt huv)]
  · by_cases hvu : v < u
    · simp [huv,hvu]
    · simp [huv,hvu]

def pattern (a : Edge → Fin 6) : Pattern (Fin 6) (Fin 6) :=
  ColeskiColoringPattern.coloredPattern (color a)

theorem edge_color (a : Edge → Fin 6) (e : Edge) : color a e.val.1 e.val.2 = a e := by
  simp [color,e.property]

theorem valid (a : Edge → Fin 6)
    (h : ∀ u v w, u ≠ v → u ≠ w → v ≠ w →
      ColeskiK4Coverage.good (color a u v) (color a u w) (color a v w) = true) :
    Valid (pattern a) := ColeskiColoringPattern.valid_colored _ (symmetric a) h

end ColeskiSixEdgePattern
#print axioms ColeskiSixEdgePattern.symmetric
#print axioms ColeskiSixEdgePattern.valid

/- END bundled local module SixEdgePattern -/
