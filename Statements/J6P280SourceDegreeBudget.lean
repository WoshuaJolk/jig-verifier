import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Statements.J6P280SourceDegreeBudget
open Finset
noncomputable section

def CanonicalSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a+b=c+d → a=c ∧ b=d

def sourceNeighbors (A : Set ℕ) (r x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (x+r+1)).filter (fun y => y ∈ A ∧ x ≤ y+r)

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (C : Finset ℕ) (r : ℕ),
    CanonicalSidon A → (∀ x ∈ C, x ∈ A) →
      (∑ x ∈ C, (sourceNeighbors A r x).card) ≤ C.card + 2*r

end
end Statements.J6P280SourceDegreeBudget
