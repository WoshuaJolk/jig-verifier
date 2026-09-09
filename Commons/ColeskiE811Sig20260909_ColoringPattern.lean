import Commons.ColeskiE811Sig20260909_PatternValidity

/- BEGIN bundled local module ColoringPattern -/

namespace ColeskiColoringPattern
open ColeskiPatternAction ColeskiPatternValidity ColeskiK4Coverage

def coloredPattern {V : Type*} [DecidableEq V] (d : V → V → Fin 6) : Pattern V (Fin 6) :=
  fun u v => if u = v then none else some (d u v)

theorem valid_colored {V : Type*} [DecidableEq V] (d : V → V → Fin 6)
    (hs : ∀ u v, d u v = d v u)
    (hg : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → good (d u v) (d u w) (d v w) = true) :
    Valid (coloredPattern d) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u v
    by_cases h : u = v
    · subst v; rfl
    · simp [coloredPattern,h,Ne.symm h,hs u v]
  · intro u
    simp [coloredPattern]
  · intro u v huv
    simp [coloredPattern,huv]
  · intro u v w huv huw hvw
    simpa [coloredPattern,huv,huw,hvw] using hg u v w huv huw hvw
end ColeskiColoringPattern
#print axioms ColeskiColoringPattern.valid_colored

/- END bundled local module ColoringPattern -/
