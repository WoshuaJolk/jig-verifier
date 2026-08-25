import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos883SixVertexTriangle

def HasCoprimeCycle {n : ℕ} (A : Finset (Fin n)) (ℓ : ℕ) : Prop :=
  ∃ cycle : Fin ℓ → Fin n,
    Function.Injective cycle ∧
    (∀ i, cycle i ∈ A) ∧
    ∀ i j : Fin ℓ, j.val = (i.val + 1) % ℓ →
      Nat.Coprime ((cycle i : ℕ) + 1)
        ((cycle j : ℕ) + 1)

/-- The full six-vertex set is above the sharp density threshold and its
coprime graph contains the admissible boundary cycle C3. -/
abbrev statement : Prop :=
  6 / 2 + 6 / 3 - 6 / 6 <
      (Finset.univ : Finset (Fin 6)).card ∧
    HasCoprimeCycle (Finset.univ : Finset (Fin 6)) 3

theorem target : statement := sorry

end Statements.Erdos883SixVertexTriangle
