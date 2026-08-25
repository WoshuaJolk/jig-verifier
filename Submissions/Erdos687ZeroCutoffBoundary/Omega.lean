import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos687ZeroCutoffBoundary.Omega

def CoversInitialInterval (X y : ℕ) : Prop :=
  ∃ residue : ℕ → ℕ,
    ∀ m : ℕ, 1 ≤ m → m ≤ y →
      ∃ p : ℕ, p.Prime ∧ p ≤ X ∧
        m % p = residue p % p

theorem proof :
    ∀ y : ℕ, CoversInitialInterval 0 y ↔ y = 0 := by
  intro y
  constructor
  · intro h
    by_contra hy
    obtain ⟨residue, hresidue⟩ := h
    obtain ⟨p, hp, hp0, hmod⟩ :=
      hresidue 1 (by omega) (by omega)
    have hp2 : 2 ≤ p := hp.two_le
    omega
  · intro hy
    subst y
    refine ⟨fun _ => 0, ?_⟩
    omega

end Submissions.Erdos687ZeroCutoffBoundary.Omega
