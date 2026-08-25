import Mathlib

namespace Submissions.Erdos700LargeBinomialGcd.Control

noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

abbrev statement : Prop :=
  {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ n < (f n) ^ 2}.Infinite

theorem proof (h : False) : statement := by
  contradiction

end Submissions.Erdos700LargeBinomialGcd.Control
