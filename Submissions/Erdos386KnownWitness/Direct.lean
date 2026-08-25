import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

namespace Submissions.Erdos386KnownWitness.Direct

open Finset Nat
open scoped BigOperators

theorem proof : Nat.choose 21 2 =
    ∏ i ∈ Ico 0 4, Nat.nth Nat.Prime i := by
  norm_num [Nat.choose, Finset.prod_Ico_succ_top, Finset.prod_range_succ]

end Submissions.Erdos386KnownWitness.Direct
