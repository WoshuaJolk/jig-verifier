import Init

namespace Statements.J4P26SpikeObstruction

def axisSpike {K : Type u} [Lean.Grind.CommRing K] [DecidableEq K]
    (c x y z : K) : K := if x = 0 ∧ y = 0 then c*z else 0


def statement : Prop :=
(∀ {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0),
¬ ∃ a b c : K, ∀ t : K, a*t*t+b*t+c = axisSpike (-1) t 0 1) ∧
(∀ {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h4 : (4 : K) ≠ 0),
¬ ∃ a b c d : K, ∀ t : K, a*t*t*t+b*t*t+c*t+d = axisSpike (-1) t 0 1)

end Statements.J4P26SpikeObstruction
