import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic

open scoped Pointwise

namespace Statements.Erdos52NestedOverlap

abbrev statement : Prop :=
    ∀ m : ℕ, ∃ (S : ℕ) (V : ℕ → Finset ℕ) (p a b : Fin m → ℕ),
      0 < S ∧
      (∀ x ∈ V 0, 0 < x) ∧
      Function.Injective p ∧
      (∀ i : Fin m,
        (p i).Prime ∧ 2 < p i ∧
        V i.val = insert (b i) (V (i.val + 1)) ∧
        b i ∉ V (i.val + 1) ∧
        a i ∈ V (i.val + 1) ∧
        (∀ x ∈ V (i.val + 1), ¬p i ∣ x) ∧
        p i ∣ b i ∧ ¬p i ∣ b i / p i) ∧
      (∀ i : Fin m,
        ({a i} : Finset ℕ) + ({b i / p i} : Finset ℕ).image (fun y => p i * y) = {S}) ∧
      ((Finset.univ : Finset (Fin m)).filter fun i =>
        S ∈ ({a i} : Finset ℕ) +
          ({b i / p i} : Finset ℕ).image (fun y => p i * y)).card = m

theorem target : statement := sorry

end Statements.Erdos52NestedOverlap
