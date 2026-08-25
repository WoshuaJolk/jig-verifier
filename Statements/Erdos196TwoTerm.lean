import Mathlib.Algebra.Module.NatInt

namespace Statements.Erdos196TwoTerm

def ListIsAPOfLengthWith (s : List ℕ) (k a d : ℕ) : Prop :=
  s = (List.range k).map (fun n ↦ a + n • d) ∨
  s = (List.range k).reverse.map (fun n ↦ a + n • d)

def ListIsAPOfLength (s : List ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, ListIsAPOfLengthWith s k a d

def HasMonotoneAP (f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ l : List ℕ, ListIsAPOfLength (l.map f) k ∧ l.Pairwise (· < ·)

/-- Every permutation has a monotone two-term arithmetic progression. -/
abbrev statement : Prop :=
  ∀ f : ℕ ≃ ℕ, HasMonotoneAP f 2

theorem target : statement := sorry

end Statements.Erdos196TwoTerm
