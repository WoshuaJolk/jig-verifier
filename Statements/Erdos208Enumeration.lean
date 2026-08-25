import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.PrimeCounting

namespace Statements.Erdos208Enumeration

noncomputable def squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

/-- The sequence is strictly increasing and enumerates exactly the squarefree naturals. -/
abbrev statement : Prop :=
  StrictMono squarefreeNumber ∧
    Set.range squarefreeNumber = {n : ℕ | Squarefree n}

theorem target : statement := sorry

end Statements.Erdos208Enumeration
