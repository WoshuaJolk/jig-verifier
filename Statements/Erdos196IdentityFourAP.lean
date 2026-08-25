import Mathlib.Algebra.Module.NatInt

namespace Statements.Erdos196IdentityFourAP

def ListIsAPOfLengthWith (s : List ℕ) (k a d : ℕ) : Prop :=
  s = (List.range k).map (fun n ↦ a + n • d) ∨
  s = (List.range k).reverse.map (fun n ↦ a + n • d)

def ListIsAPOfLength (s : List ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, ListIsAPOfLengthWith s k a d

def HasMonotoneAP (f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ l : List ℕ, ListIsAPOfLength (l.map f) k ∧ l.Pairwise (· < ·)

/-- The identity permutation contains the progression 0,1,2,3. -/
abbrev statement : Prop :=
  HasMonotoneAP (Equiv.refl ℕ) 4

theorem target : statement := sorry

end Statements.Erdos196IdentityFourAP
