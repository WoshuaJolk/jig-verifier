import Mathlib.Data.Nat.Factorization.Basic

namespace Submissions.Erdos413OneIsOmegaBarrier.Direct

def omega (n : ℕ) : ℕ :=
  n.factorization.support.card

def IsBarrier (n : ℕ) : Prop :=
  ∀ m < n, m + omega m ≤ n

theorem proof : IsBarrier 1 := by
  intro m hm
  have : m = 0 := by omega
  subst m
  simp [omega]

end Submissions.Erdos413OneIsOmegaBarrier.Direct
