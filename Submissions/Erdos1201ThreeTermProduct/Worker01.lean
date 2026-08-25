import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Submissions.Erdos1201ThreeTermProduct.Worker01

theorem proof : (∏ i ∈ Finset.range (2 + 1), (5 + i)) = 210 := by
  norm_num

end Submissions.Erdos1201ThreeTermProduct.Worker01
