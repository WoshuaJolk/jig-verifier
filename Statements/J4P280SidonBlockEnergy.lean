import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Statements.J4P280SidonBlockEnergy
namespace SidonBlockEnergy
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

end SidonBlockEnergy

open Finset SidonBlockEnergy

abbrev statement : Prop :=
  ∀ (ι : Type) [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset Nat) (A : Set Nat) (H : Nat) (w : ι → ℝ),
    IsSidon A → (∀ i ∈ I, ∀ a ∈ F i, a ∈ A) →
    (I : Set ι).PairwiseDisjoint F →
    (∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b - a < H) →
    (∑ i ∈ I, ((F i).card : ℝ) * w i) ^ 2 ≤
      (2 * ((H - 1 : Nat) : ℝ) + ∑ i ∈ I, ((F i).card : ℝ)) *
        ∑ i ∈ I, (w i) ^ 2

end Statements.J4P280SidonBlockEnergy
