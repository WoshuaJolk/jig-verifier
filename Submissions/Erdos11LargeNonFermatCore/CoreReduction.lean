import Mathlib.Data.Nat.Squarefree

/-!
Erdős 11 reduction: given the power-of-two-plus-one family and the verified
range through 1000, the root is equivalent to the large non-Fermat core.
Pure case analysis; the four propositions are restated verbatim from the
canonical statement.
-/

namespace Submissions.Erdos11LargeNonFermatCore.CoreReduction

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

theorem proof : FermatFormFamily → VerifiedBelow1001 → (Root ↔ LargeNonFermatCore) := by
  intro hF hV
  constructor
  · intro hR n hn h1 _ _
    exact hR n hn h1
  · intro hC n hn h1
    by_cases hle : n ≤ 1000
    · exact hV n hn h1 hle
    · push_neg at hle
      by_cases hf : ∃ l : ℕ, 0 < l ∧ n = 2 ^ l + 1
      · obtain ⟨l, hl, rfl⟩ := hf
        exact hF l hl
      · push_neg at hf
        exact hC n hn h1 hle hf

end Submissions.Erdos11LargeNonFermatCore.CoreReduction
