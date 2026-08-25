import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.PrimeCounting

namespace Statements.Erdos208FirstSquarefree

noncomputable def squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

/-- The first member of the squarefree enumeration is squarefree. -/
abbrev statement : Prop :=
  Squarefree (squarefreeNumber 0)

theorem target : statement := sorry

end Statements.Erdos208FirstSquarefree
