import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

open ArithmeticFunction.sigma

namespace Submissions.Erdos412TwoReachesThree.Worker04Smoke

theorem proof : (σ 1) 2 = 3 := by
  norm_num [ArithmeticFunction.sigma_apply]

end Submissions.Erdos412TwoReachesThree.Worker04Smoke
