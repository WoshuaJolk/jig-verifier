import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos830TwoAmicablePairs

open ArithmeticFunction

def IsAmicable (a b : ℕ) : Prop :=
  sigma 1 a = a + b ∧ sigma 1 b = a + b

/-- Two classical, distinct amicable pairs. -/
abbrev statement : Prop :=
  IsAmicable 220 284 ∧ IsAmicable 1184 1210

theorem target : statement := sorry

end Statements.Erdos830TwoAmicablePairs
