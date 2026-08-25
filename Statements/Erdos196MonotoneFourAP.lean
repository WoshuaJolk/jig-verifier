import Mathlib.Algebra.Module.NatInt

namespace Statements.Erdos196MonotoneFourAP

/-- A list is an arithmetic progression of length `k`, in either orientation. -/
def ListIsAPOfLengthWith (s : List ℕ) (k a d : ℕ) : Prop :=
  s = (List.range k).map (fun n ↦ a + n • d) ∨
  s = (List.range k).reverse.map (fun n ↦ a + n • d)

def ListIsAPOfLength (s : List ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, ListIsAPOfLengthWith s k a d

/-- The values at increasing indices contain an increasing or decreasing arithmetic progression. -/
def HasMonotoneAP (f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ l : List ℕ, ListIsAPOfLength (l.map f) k ∧ l.Pairwise (· < ·)

/-- Erdős Problem 196. -/
abbrev statement : Prop :=
  ∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4

theorem target : statement := sorry

end Statements.Erdos196MonotoneFourAP
