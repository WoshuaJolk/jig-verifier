import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Chojecki's inequality (10) fails at arbitrarily small density.

Scaling: for `G = c • G₀`, `n = c • n₀`, the multiples of `G` in `[1, n]` are exactly `c` times the
multiples of `G₀` in `[1, n₀]`, and `⌊cn₀ / cg⌋ = ⌊n₀/g⌋`; so `f`, the floor sum and `|G|` are all
unchanged while the density divides by `c`.  Apply this to the witness
`G₀ = {8, 12, 18, 20, 28, 30, 42, 44, 52, 68}`, `n₀ = 180` (`f = 45`, floor sum `81`).
-/

namespace Submissions.ErdosMultiplesDoublingSlackAllDensities.Scaling

open Finset

/-- The base witness. -/
def G₀ : Finset ℕ := {8, 12, 18, 20, 28, 30, 42, 44, 52, 68}

lemma mul_left_injective' (c : ℕ) (hc : 0 < c) : Function.Injective (fun g : ℕ => c * g) := by
  intro x y h
  exact Nat.eq_of_mul_eq_mul_left hc h

lemma filter_scale (G : Finset ℕ) (n c : ℕ) (hc : 0 < c) :
    (Icc 1 (c * n)).filter (fun k => ∃ g ∈ G.image (fun g => c * g), g ∣ k) =
      ((Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).image (fun j => c * j) := by
  ext k
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨hk1, hkn⟩, g, hg, hgk⟩
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨t, ht⟩ := hgk
    refine ⟨g₀ * t, ⟨⟨?_, ?_⟩, g₀, hg₀, dvd_mul_right _ _⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos (g₀ * t) with h | h
      · rw [ht, Nat.mul_assoc, h, Nat.mul_zero] at hk1; omega
      · exact h
    · have : c * (g₀ * t) ≤ c * n := by rw [← Nat.mul_assoc, ← ht]; exact hkn
      exact Nat.le_of_mul_le_mul_left this hc
    · rw [ht, Nat.mul_assoc]
  · rintro ⟨j, ⟨⟨hj1, hjn⟩, g, hg, hgj⟩, rfl⟩
    refine ⟨⟨?_, Nat.mul_le_mul_left c hjn⟩, c * g, ⟨g, hg, rfl⟩,
      Nat.mul_dvd_mul_left c hgj⟩
    calc 1 ≤ c := hc
      _ = c * 1 := (Nat.mul_one c).symm
      _ ≤ c * j := Nat.mul_le_mul_left c hj1

lemma card_scale (G : Finset ℕ) (n c : ℕ) (hc : 0 < c) :
    ((Icc 1 (c * n)).filter (fun k => ∃ g ∈ G.image (fun g => c * g), g ∣ k)).card =
      ((Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card := by
  rw [filter_scale G n c hc, card_image_of_injective _ (mul_left_injective' c hc)]

lemma sum_scale (G : Finset ℕ) (n c : ℕ) (hc : 0 < c) :
    (∑ g ∈ G.image (fun g => c * g), (c * n) / g) = ∑ g ∈ G, n / g := by
  rw [sum_image (fun x _ y _ h => mul_left_injective' c hc h)]
  refine sum_congr rfl fun g _ => ?_
  exact Nat.mul_div_mul_left n g hc

theorem proof : ∀ c : ℕ, 0 < c →
    ∃ G : Finset ℕ,
      (∀ g ∈ G, 2 ≤ g) ∧
      (∀ a ∈ G, ∀ b ∈ G, a ∣ b → a = b) ∧
      ∃ n : ℕ, (∀ g ∈ G, g ≤ n) ∧
        4 * c * ((Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card ≤ n ∧
        2 * ((Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card <
          (∑ g ∈ G, n / g) + G.card := by
  intro c hc
  have h2 : ∀ g ∈ G₀, 2 ≤ g := by decide
  have hprim : ∀ a ∈ G₀, ∀ b ∈ G₀, a ∣ b → a = b := by decide
  have hle : ∀ g ∈ G₀, g ≤ 180 := by decide
  have hf : ((Icc 1 180).filter (fun k => ∃ g ∈ G₀, g ∣ k)).card = 45 := by decide
  have hs : (∑ g ∈ G₀, 180 / g) = 81 := by decide
  have hcard : G₀.card = 10 := by decide
  refine ⟨G₀.image (fun g => c * g), ?_, ?_, c * 180, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := mem_image.mp hg
    have := h2 g₀ hg₀
    calc 2 ≤ g₀ := this
      _ = 1 * g₀ := (Nat.one_mul g₀).symm
      _ ≤ c * g₀ := Nat.mul_le_mul_right g₀ hc
  · intro a ha b hb hab
    obtain ⟨a₀, ha₀, rfl⟩ := mem_image.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := mem_image.mp hb
    rw [Nat.mul_dvd_mul_iff_left hc] at hab
    rw [hprim a₀ ha₀ b₀ hb₀ hab]
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := mem_image.mp hg
    exact Nat.mul_le_mul_left c (hle g₀ hg₀)
  · rw [card_scale G₀ 180 c hc, hf]
    omega
  · rw [card_scale G₀ 180 c hc, hf, sum_scale G₀ 180 c hc, hs,
      card_image_of_injective _ (mul_left_injective' c hc), hcard]
    omega

end Submissions.ErdosMultiplesDoublingSlackAllDensities.Scaling
