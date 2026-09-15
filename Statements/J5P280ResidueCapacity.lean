import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.J5P280ResidueCapacity

open Finset
noncomputable section

def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

def UniquePositiveDifferences (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a < b → c < d → b - a = d - c → a = c ∧ b = d

abbrev statement : Prop :=
  (∀ {ι : Type*} [DecidableEq ι]
    (F : Finset ℕ) (key : ℕ → ι) (D : Finset ℕ),
    IsSidon (F : Set ℕ) →
    (∀ a ∈ F, ∀ b ∈ F, a < b → key a = key b → b - a ∈ D) →
    (F.card : ℝ)^2 ≤ ((F.image key).card : ℝ) * ((F.card : ℝ) + 2 * (D.card : ℝ))) ∧
  (∀ (F : Finset ℕ) (N m : ℕ),
    IsSidon (F : Set ℕ) → (∀ a ∈ F, a ≤ N) →
    (F.card : ℝ)^2 ≤ ((F.image (fun a => a % m)).card : ℝ) *
      ((F.card : ℝ) + 2 * ((N / m : ℕ) : ℝ))) ∧
  (∀ {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (H q r : ℕ),
    UniquePositiveDifferences A →
    (∀ i ∈ I, ∀ a ∈ F i, a ∈ A) →
    (I : Set ι).PairwiseDisjoint F →
    (∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b-a < H) →
    (∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → q ∣ b-a) →
    (∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → r ∣ b-a) →
    ∑ i ∈ I, (F i).card.choose 2 ≤ (H-1)/(Nat.lcm q r))

end
end Statements.J5P280ResidueCapacity
