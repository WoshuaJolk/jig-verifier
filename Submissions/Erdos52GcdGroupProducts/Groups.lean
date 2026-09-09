import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset


/-
Source-inspected draft; no build was run by the drafting agent.
The identity holds for every natural S, including S = 0.

Pinned Lean 4.33 Init/Data/Nat/Coprime.lean signatures used below:
  Nat.exists_coprime (m n : Nat) :
    ∃ m' n', Nat.Coprime m' n' ∧
      m = m' * Nat.gcd m n ∧ n = n' * Nat.gcd m n
  Nat.Coprime.mul_right (H1 : Nat.Coprime k m) (H2 : Nat.Coprime k n) :
    Nat.Coprime k (m * n)
  Nat.Coprime.pow_left (n : Nat) (H1 : Nat.Coprime m k) :
    Nat.Coprime (m ^ n) k
Pinned Init/Data/Nat/Gcd.lean:
  Nat.gcd_mul_right (m n k : Nat) :
    Nat.gcd (m * n) (k * n) = Nat.gcd m k * n
-/

namespace Submissions.Erdos52GcdGroupProducts.Groups

theorem gcd_product_of_same_gcd {S x y g : ℕ}
    (hx : Nat.gcd S x = g) (hy : Nat.gcd S y = g) :
    Nat.gcd (S ^ 2) (x * y) = g ^ 2 := by
  by_cases hS : S = 0
  · subst S
    have hx' : x = g := by simpa using hx
    have hy' : y = g := by simpa using hy
    simp [hx', hy', pow_two]
  have hg : 0 < g :=
    hx ▸ Nat.gcd_pos_of_pos_left x (Nat.pos_of_ne_zero hS)
  obtain ⟨s, u, hu, hSx, hx'⟩ := Nat.exists_coprime S x
  obtain ⟨t, v, hv, hSy, hy'⟩ := Nat.exists_coprime S y
  rw [hx] at hSx hx'
  rw [hy] at hSy hy'
  have hst : s = t := Nat.eq_of_mul_eq_mul_right hg (hSx.symm.trans hSy)
  subst t
  have hcop : Nat.Coprime (s ^ 2) (u * v) := (hu.mul_right hv).pow_left 2
  calc
    Nat.gcd (S ^ 2) (x * y) =
        Nat.gcd ((s ^ 2) * (g ^ 2)) ((u * v) * (g ^ 2)) := by
      simp only [hSx, hx', hy', pow_two,
        Nat.mul_left_comm, Nat.mul_comm]
    _ = g ^ 2 := by rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]

end Submissions.Erdos52GcdGroupProducts.Groups
open scoped Pointwise BigOperators

namespace Submissions.Erdos52GcdGroupProducts.Groups

theorem gcd_groups_product_card_le (S : ℕ) (A G : Finset ℕ) (B : ℕ → Finset ℕ)
    (hsub : ∀ g ∈ G, B g ⊆ A)
    (hgcd : ∀ g ∈ G, ∀ x ∈ B g, Nat.gcd S x = g) :
    (∑ g ∈ G, (B g * B g).card) ≤ (A * A).card := by
  have hlabel (g : ℕ) (hg : g ∈ G) (z : ℕ) (hz : z ∈ B g * B g) :
      Nat.gcd (S ^ 2) z = g ^ 2 := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp hz
    exact gcd_product_of_same_gcd (hgcd g hg x hx) (hgcd g hg y hy)
  have hdisj : (G : Set ℕ).PairwiseDisjoint (fun g => B g * B g) := by
    intro g hg h hh hne
    apply Finset.disjoint_left.mpr
    intro z hzg hzh
    apply hne
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    exact (hlabel g hg z hzg).symm.trans (hlabel h hh z hzh)
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨g, hg, hz⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mul_subset_mul (hsub g hg) (hsub g hg) hz

theorem proof :
    ∀ (S : ℕ) (A G : Finset ℕ) (B : ℕ → Finset ℕ) (m : ℕ → ℕ),
      (∀ g ∈ G, B g ⊆ A) →
      (∀ g ∈ G, ∀ x ∈ B g, Nat.gcd S x = g) →
      (∀ g ∈ G, m g + (m g).choose 2 ≤ (B g * B g).card) →
      (∑ g ∈ G, (m g + (m g).choose 2)) ≤ (A * A).card := by
  intro S A G B m hsub hgcd hcount
  exact (Finset.sum_le_sum hcount).trans (gcd_groups_product_card_le S A G B hsub hgcd)

end Submissions.Erdos52GcdGroupProducts.Groups
