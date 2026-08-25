import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic

namespace Statements.Erdos883CoprimeOddCycles

def HasCoprimeCycle {n : ℕ} (A : Finset (Fin n)) (ℓ : ℕ) : Prop :=
  ∃ cycle : Fin ℓ → Fin n,
    Function.Injective cycle ∧
    (∀ i, cycle i ∈ A) ∧
    ∀ i j : Fin ℓ, j.val = (i.val + 1) % ℓ →
      Nat.Coprime ((cycle i : ℕ) + 1)
        ((cycle j : ℕ) + 1)

/-- The surviving first question of Erdős Problem 883. The second,
tripartite, question is excluded because Sárközy solved it. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ A : Finset (Fin n),
    n / 2 + n / 3 - n / 6 < A.card →
      ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ % 2 = 1 → ℓ ≤ n / 3 + 1 →
        HasCoprimeCycle A ℓ

theorem target : statement := sorry

end Statements.Erdos883CoprimeOddCycles
