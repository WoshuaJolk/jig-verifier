import Mathlib.Data.Nat.Squarefree

namespace Statements.Erdos11LargeNonFermatCore

def Representable (n : ℕ) : Prop :=
  ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

def Root : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → Representable n

def FermatFormFamily : Prop :=
  ∀ l : ℕ, 0 < l → Representable (2 ^ l + 1)

def VerifiedBelow1001 : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → n ≤ 1000 → Representable n

def LargeNonFermatCore : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → 1000 < n →
    (∀ l : ℕ, 0 < l → n ≠ 2 ^ l + 1) →
    Representable n

/-- The verified finite range and the power-of-two-plus-one family leave
exactly the large odd inputs outside that explicit family. -/
abbrev statement : Prop :=
  FermatFormFamily → VerifiedBelow1001 → (Root ↔ LargeNonFermatCore)

theorem target : statement := sorry

end Statements.Erdos11LargeNonFermatCore
