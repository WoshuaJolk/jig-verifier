import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace Submissions.Erdos1094BinomialLeastPrimeExceptions.Attacks

abbrev claimedStatement : Prop :=
  {(n, k) : ℕ × ℕ |
      0 < k ∧ 2 * k ≤ n ∧
        (n.choose k).minFac > max (n / k) k}.Finite

theorem vacuousHypothesis : False → claimedStatement := False.elim

theorem admissibleDomainNonempty :
    (0 < 1 ∧ 2 * 1 ≤ 2) := by
  norm_num

end Submissions.Erdos1094BinomialLeastPrimeExceptions.Attacks
