import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs

open scoped Pointwise

namespace Statements.Erdos52SameSumPathProducts

abbrev statement : Prop :=
    ∀ (m S : ℕ) (A : Finset ℕ) (p a b γ : Fin m → ℕ),
      (∀ i, (p i).Prime) →
      (∀ i, 0 < a i ∧ 0 < b i) →
      (∀ i, a i ∈ A ∧ b i ∈ A) →
      (∀ i, a i + b i = S) →
      (∀ i, padicValNat (p i) (a i) < padicValNat (p i) (b i)) →
      (∀ i j, i < j →
        padicValNat (p i) (a j) = γ i ∧ padicValNat (p i) (b j) = γ i) →
      ((Finset.univ.image b) * (Finset.univ.image b)).card = m + m.choose 2 ∧
      m + m.choose 2 ≤ (A * A).card

theorem target : statement := sorry

end Statements.Erdos52SameSumPathProducts
