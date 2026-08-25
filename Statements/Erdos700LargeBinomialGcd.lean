import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos700LargeBinomialGcd

noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

/-- Erdős Problem 700(b). -/
abbrev statement : Prop :=
  {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ n < (f n) ^ 2}.Infinite

theorem target : statement := sorry

end Statements.Erdos700LargeBinomialGcd
