import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

open scoped Pointwise

namespace Submissions.Erdos52MixedCubeGrowth.P29

private def scale (q : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => q * x

private theorem scale_card {q : ℕ} (hq : 0 < q) (S : Finset ℕ) :
    (scale q S).card = S.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact Nat.eq_of_mul_eq_mul_left hq hab

private theorem prime_free_mul
    {q : ℕ} (hq : q.Prime) {S T : Finset ℕ}
    (hS : ∀ x ∈ S, ¬q ∣ x) (hT : ∀ x ∈ T, ¬q ∣ x) :
    ∀ z ∈ S * T, ¬q ∣ z := by
  intro z hz
  simp only [Finset.mem_mul] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact fun h => (hq.dvd_mul.mp h).elim (hS x hx) (hT y hy)

private theorem product_split
    {q : ℕ} (A₀ A₁ : Finset ℕ) :
    let A := A₀ ∪ scale q A₁
    A * A =
      (A₀ * A₀) ∪
        (scale q (A₀ * A₁) ∪ scale (q * q) (A₁ * A₁)) := by
  classical
  dsimp only
  ext z
  simp only [Finset.mem_mul, Finset.mem_union, scale, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rcases hx with hx | ⟨a, ha, rfl⟩
    · rcases hy with hy | ⟨b, hb, rfl⟩
      · exact Or.inl ⟨x, hx, y, hy, rfl⟩
      · exact Or.inr (Or.inl ⟨x * b, ⟨x, hx, b, hb, rfl⟩, by ac_rfl⟩)
    · rcases hy with hy | ⟨b, hb, rfl⟩
      · exact Or.inr (Or.inl ⟨y * a, ⟨y, hy, a, ha, rfl⟩, by ac_rfl⟩)
      · exact Or.inr (Or.inr ⟨a * b, ⟨a, ha, b, hb, rfl⟩, by ac_rfl⟩)
  · rintro (hz | hz)
    · obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, Or.inl hx, y, Or.inl hy, rfl⟩
    · rcases hz with hz | hz
      · obtain ⟨xy, ⟨x, hx, y, hy, rfl⟩, rfl⟩ := hz
        exact ⟨x, Or.inl hx, q * y, Or.inr ⟨y, hy, rfl⟩, by ac_rfl⟩
      · obtain ⟨xy, ⟨x, hx, y, hy, rfl⟩, rfl⟩ := hz
        exact ⟨q * x, Or.inr ⟨x, hx, rfl⟩,
          q * y, Or.inr ⟨y, hy, rfl⟩, by ac_rfl⟩

/--
Lossless sibling aggregation: splitting a set into a `q`-free layer and
`q` times another `q`-free layer separates the three product families by
their exact `q`-valuation.
-/
theorem proof :
    ∀ (q : ℕ) (A₀ A₁ : Finset ℕ), q.Prime →
      (∀ x ∈ A₀, ¬q ∣ x) →
      (∀ x ∈ A₁, ¬q ∣ x) →
      let A := A₀ ∪ scale q A₁
      (A * A).card =
        (A₀ * A₀).card + (A₀ * A₁).card + (A₁ * A₁).card := by
  classical
  intro q A₀ A₁ hq hfree₀ hfree₁
  dsimp only
  let S₀ := A₀ * A₀
  let S₁ := scale q (A₀ * A₁)
  let S₂ := scale (q * q) (A₁ * A₁)
  have hfree00 : ∀ z ∈ S₀, ¬q ∣ z :=
    prime_free_mul hq hfree₀ hfree₀
  have hfree01 : ∀ z ∈ A₀ * A₁, ¬q ∣ z :=
    prime_free_mul hq hfree₀ hfree₁
  have hdisj01 : Disjoint S₀ S₁ := by
    simp only [Finset.disjoint_left]
    intro z hz₀ hz₁
    simp only [S₁, scale, Finset.mem_image] at hz₁
    obtain ⟨x, hx, rfl⟩ := hz₁
    exact hfree00 (q * x) hz₀ ⟨x, rfl⟩
  have hdisj02 : Disjoint S₀ S₂ := by
    simp only [Finset.disjoint_left]
    intro z hz₀ hz₂
    simp only [S₂, scale, Finset.mem_image] at hz₂
    obtain ⟨x, hx, rfl⟩ := hz₂
    exact hfree00 ((q * q) * x) hz₀ ⟨q * x, by ac_rfl⟩
  have hdisj12 : Disjoint S₁ S₂ := by
    simp only [Finset.disjoint_left]
    intro z hz₁ hz₂
    simp only [S₁, S₂, scale, Finset.mem_image] at hz₁ hz₂
    obtain ⟨x, hx, rfl⟩ := hz₁
    obtain ⟨y, hy, heq⟩ := hz₂
    have hcancel : x = q * y := by
      apply Nat.eq_of_mul_eq_mul_left hq.pos
      calc
        q * x = (q * q) * y := heq.symm
        _ = q * (q * y) := by ac_rfl
    exact hfree01 x hx ⟨y, hcancel⟩
  have hdisj0 : Disjoint S₀ (S₁ ∪ S₂) :=
    Finset.disjoint_union_right.mpr ⟨hdisj01, hdisj02⟩
  have hsplit :
      (A₀ ∪ scale q A₁) * (A₀ ∪ scale q A₁) =
        S₀ ∪ (S₁ ∪ S₂) := by
    simpa [S₀, S₁, S₂] using product_split (q := q) A₀ A₁
  rw [hsplit, Finset.card_union_of_disjoint hdisj0,
    Finset.card_union_of_disjoint hdisj12]
  rw [scale_card hq.pos, scale_card (Nat.mul_pos hq.pos hq.pos)]
  simp [S₀, Nat.add_assoc]

end Submissions.Erdos52MixedCubeGrowth.P29
