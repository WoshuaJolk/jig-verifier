import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Sqrt

namespace Statements.Erdos734DensePlaneMultiplicity

abbrev statement : Prop :=
  ∀ (q : ℕ) (hq : 16 ≤ q)
    (blocks : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1)))
    (hpairs : ∀ x y,
      (Finset.univ.filter fun i => x ∈ blocks i ∧ y ∈ blocks i).card =
        if x = y then q + 1 else 1)
    (S : Finset (Fin (q ^ 2 + q + 1))) (hdense : q ^ 2 + q + 1 ≤ 2 * S.card)
    (M : ℕ)
    (hmult : ∀ t : ℕ, 2 ≤ t →
      (((Finset.univ.image fun i => S ∩ blocks i).filter fun b => b.card = t).card) ≤ M),
    3 * (q ^ 2 + q + 1) ≤ (8 * Nat.sqrt q + 16) * M

end Statements.Erdos734DensePlaneMultiplicity
