import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace Submissions.Erdos830TwoAmicablePairs.Direct

open ArithmeticFunction

def IsAmicable (a b : ℕ) : Prop :=
  sigma 1 a = a + b ∧ sigma 1 b = a + b

set_option maxRecDepth 10000 in
theorem proof : IsAmicable 220 284 ∧ IsAmicable 1184 1210 := by
  constructor <;> constructor <;> decide

end Submissions.Erdos830TwoAmicablePairs.Direct
