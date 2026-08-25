import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos1093BinomialDeficiency

open Finset Nat

noncomputable def deficiency (n k : ℕ) : ℕ :=
  #{i ∈ range k | n - i ∈ smoothNumbers (k + 1)}

def Admissible (n k : ℕ) : Prop :=
  2 * k ≤ n ∧ ∀ p, p.Prime → p ∣ choose n k → k < p

/-- Erdős Problem 1093: deficiency one occurs infinitely often, whereas
deficiency greater than one occurs only finitely often. -/
abbrev statement : Prop :=
  {x : ℕ × ℕ | Admissible x.2 x.1 ∧ deficiency x.2 x.1 = 1}.Infinite ∧
  {x : ℕ × ℕ | Admissible x.2 x.1 ∧ deficiency x.2 x.1 > 1}.Finite

theorem target : statement := sorry

end Statements.Erdos1093BinomialDeficiency
