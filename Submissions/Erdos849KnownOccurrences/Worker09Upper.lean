import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos849KnownOccurrences.Worker09Upper

theorem proof :
    1 ≤ 3 ∧ 2 * 3 ≤ 10 ∧ Nat.choose 10 3 = 120 ∧
    1 ≤ 2 ∧ 2 * 2 ≤ 16 ∧ Nat.choose 16 2 = 120 ∧
    1 ≤ 1 ∧ 2 * 1 ≤ 120 ∧ Nat.choose 120 1 = 120 := by
  norm_num [Nat.choose]

end Submissions.Erdos849KnownOccurrences.Worker09Upper
