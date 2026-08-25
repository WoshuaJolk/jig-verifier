import Mathlib.NumberTheory.SmoothNumbers

namespace Statements.Erdos1093KnownDeficiencyOne

open Finset Nat

noncomputable def deficiency (n k : ℕ) : ℕ :=
  #{i ∈ range k | n - i ∈ smoothNumbers (k + 1)}

abbrev statement : Prop := deficiency 7 3 = 1

theorem target : statement := sorry

end Statements.Erdos1093KnownDeficiencyOne
