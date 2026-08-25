import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod

open scoped Pointwise

namespace Submissions.Erdos52GeometricAdditiveGrowth.P29

private theorem pow_pos_nat {q : ℕ} (hq : 0 < q) (n : ℕ) : 0 < q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact Nat.mul_pos ih hq

private theorem pow_sum_unique
    {q a b c d : ℕ} (hq : 2 ≤ q)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hsum : q ^ a + q ^ b = q ^ c + q ^ d) :
    a = c ∧ b = d := by
  have hqpos : 0 < q := by omega
  have hpowab : q ^ a ≤ q ^ b :=
    Nat.pow_le_pow_right hqpos hab
  have hpowcd : q ^ c ≤ q ^ d :=
    Nat.pow_le_pow_right hqpos hcd
  have hbnot : ¬b < d := by
    intro hbd
    have hsucc : b + 1 ≤ d := by omega
    have hdouble : 2 * q ^ b ≤ q ^ d := by
      calc
        2 * q ^ b ≤ q * q ^ b := Nat.mul_le_mul_right (q ^ b) hq
        _ = q ^ (b + 1) := by
          rw [pow_succ]
          exact Nat.mul_comm _ _
        _ ≤ q ^ d := Nat.pow_le_pow_right hqpos hsucc
    have hcpos : 0 < q ^ c := pow_pos_nat hqpos c
    omega
  have hdnot : ¬d < b := by
    intro hdb
    have hsucc : d + 1 ≤ b := by omega
    have hdouble : 2 * q ^ d ≤ q ^ b := by
      calc
        2 * q ^ d ≤ q * q ^ d := Nat.mul_le_mul_right (q ^ d) hq
        _ = q ^ (d + 1) := by
          rw [pow_succ]
          exact Nat.mul_comm _ _
        _ ≤ q ^ b := Nat.pow_le_pow_right hqpos hsucc
    have hapos : 0 < q ^ a := pow_pos_nat hqpos a
    omega
  have hbd : b = d := by omega
  subst d
  have hacpow : q ^ a = q ^ c := Nat.add_right_cancel hsum
  exact ⟨Nat.pow_right_injective hq hacpow, rfl⟩

private theorem sidon_sumset_card
    (A : Finset ℤ)
    (hSidon :
      ∀ a ∈ A, ∀ b ∈ A, a ≤ b →
        ∀ c ∈ A, ∀ d ∈ A, c ≤ d →
          a + b = c + d → a = c ∧ b = d) :
    (A + A).card = A.card + A.card.choose 2 := by
  classical
  let P : Finset (ℤ × ℤ) :=
    A.diag ∪ (A ×ˢ A).filter fun p => p.1 < p.2
  have hmem (p : ℤ × ℤ) (hp : p ∈ P) :
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 := by
    simp only [P, Finset.mem_union, Finset.mem_diag, Finset.mem_filter,
      Finset.mem_product] at hp
    rcases hp with hp | hp
    · exact ⟨hp.1, hp.2 ▸ hp.1, hp.2.le⟩
    · exact ⟨hp.1.1, hp.1.2, hp.2.le⟩
  have hdisj :
      Disjoint A.diag ((A ×ˢ A).filter fun p => p.1 < p.2) := by
    simp [Finset.disjoint_left]
  have hcard : P.card = A.card + A.card.choose 2 := by
    dsimp only [P]
    rw [Finset.card_union_of_disjoint hdisj, Finset.diag_card,
      Finset.card_product_filter_lt]
  let f : ℤ × ℤ → ℤ := fun p => p.1 + p.2
  have hinj : Set.InjOn f P := by
    intro x hx y hy hxy
    obtain ⟨hx₁, hx₂, hxle⟩ := hmem x hx
    obtain ⟨hy₁, hy₂, hyle⟩ := hmem y hy
    have h := hSidon x.1 hx₁ x.2 hx₂ hxle y.1 hy₁ y.2 hy₂ hyle hxy
    exact Prod.ext h.1 h.2
  have himage : (P.image f).card = P.card :=
    Finset.card_image_of_injOn hinj
  have hsubset : P.image f ⊆ A + A := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    obtain ⟨hp₁, hp₂, -⟩ := hmem p hp
    exact Finset.add_mem_add hp₁ hp₂
  have hsupset : A + A ⊆ P.image f := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    by_cases hab : a ≤ b
    · apply Finset.mem_image.mpr
      refine ⟨(a, b), ?_, rfl⟩
      simp [P, ha, hb, hab.eq_or_lt]
    · apply Finset.mem_image.mpr
      refine ⟨(b, a), ?_, add_comm b a⟩
      simp [P, ha, hb, lt_of_not_ge hab]
  have heq : P.image f = A + A :=
    Finset.Subset.antisymm hsubset hsupset
  calc
    (A + A).card = (P.image f).card := congrArg Finset.card heq.symm
    _ = P.card := himage
    _ = A.card + A.card.choose 2 := hcard

/--
Every finite subset of a geometric progression with integral ratio at least
two is additively Sidon, hence has the exact quadratic sumset cardinality.
-/
theorem proof :
    ∀ (q : ℕ) (E : Finset ℕ), 2 ≤ q →
      let A : Finset ℤ := E.image fun n : ℕ => (q ^ n : ℤ)
      (A + A).card = E.card + E.card.choose 2 := by
  classical
  intro q E hq
  let A : Finset ℤ := E.image fun n : ℕ => (q ^ n : ℤ)
  have hpw_inj : Function.Injective (fun n : ℕ => (q ^ n : ℤ)) := by
    intro a b hab
    change (q ^ a : ℤ) = (q ^ b : ℤ) at hab
    have hab' : q ^ a = q ^ b := by exact_mod_cast hab
    exact Nat.pow_right_injective hq hab'
  have hAcard : A.card = E.card := by
    dsimp only [A]
    exact Finset.card_image_iff.mpr hpw_inj.injOn
  have hSidon :
      ∀ a ∈ A, ∀ b ∈ A, a ≤ b →
        ∀ c ∈ A, ∀ d ∈ A, c ≤ d →
          a + b = c + d → a = c ∧ b = d := by
    intro x hx y hy hxy z hz w hw hzw hsum
    simp only [A, Finset.mem_image] at hx hy hz hw
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨c, hc, rfl⟩ := hz
    obtain ⟨d, hd, rfl⟩ := hw
    have hab : a ≤ b := by
      by_contra hn
      have hp := Nat.pow_lt_pow_right (by omega : 1 < q) (Nat.lt_of_not_ge hn)
      exact (not_lt_of_ge hxy) (by exact_mod_cast hp)
    have hcd : c ≤ d := by
      by_contra hn
      have hp := Nat.pow_lt_pow_right (by omega : 1 < q) (Nat.lt_of_not_ge hn)
      exact (not_lt_of_ge hzw) (by exact_mod_cast hp)
    have hsum' : q ^ a + q ^ b = q ^ c + q ^ d := by
      exact_mod_cast hsum
    obtain ⟨hac, hbd⟩ := pow_sum_unique hq hab hcd hsum'
    exact ⟨by rw [hac], by rw [hbd]⟩
  change (A + A).card = E.card + E.card.choose 2
  rw [sidon_sumset_card A hSidon, hAcard]

end Submissions.Erdos52GeometricAdditiveGrowth.P29
