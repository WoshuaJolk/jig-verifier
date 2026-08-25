import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos654OneThirdBaseline.Direct

open Finset

abbrev Point := ℝ × ℝ

def distSq (x y : Point) : ℝ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

def NoFourCocyclic (P : Finset Point) : Prop :=
  ∀ S : Finset Point, S ⊆ P → S.card = 4 →
    ¬ ∃ o : Point, ∃ r : ℝ, ∀ x ∈ S, distSq o x = r

noncomputable def distanceCount (P : Finset Point) (x : Point) : ℕ := by
  classical
  exact ((P.erase x).image fun y => distSq x y).card

theorem proof :
    ∀ P : Finset Point, NoFourCocyclic P →
      ∀ x ∈ P, P.card - 1 ≤ 3 * distanceCount P x := by
  intro P hfour x hx
  classical
  let D := P.erase x
  let f : Point → ℝ := fun y => distSq x y
  let I := D.image f
  have hfiber : ∀ d ∈ I, (D.filter fun y => f y = d).card ≤ 3 := by
    intro d hd
    by_contra hle
    have hfourcard : 4 ≤ (D.filter fun y => f y = d).card := by omega
    obtain ⟨S, hSsub, hScard⟩ :=
      Finset.exists_subset_card_eq hfourcard
    have hSP : S ⊆ P := by
      intro y hy
      exact Finset.erase_subset x P (Finset.mem_filter.mp (hSsub hy)).1
    have hcircle : ∃ o : Point, ∃ r : ℝ,
        ∀ y ∈ S, distSq o y = r := by
      refine ⟨x, d, ?_⟩
      intro y hy
      exact (Finset.mem_filter.mp (hSsub hy)).2
    exact hfour S hSP hScard hcircle
  have hmaps : Set.MapsTo f (D : Set Point) (I : Set ℝ) := by
    intro y hy
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hcount :
      D.card ≤ 3 * I.card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      (∑ d ∈ I, (D.filter fun y => f y = d).card)
          ≤ ∑ _d ∈ I, 3 := by
            exact Finset.sum_le_sum fun d hd => hfiber d hd
      _ = 3 * I.card := by simp [Nat.mul_comm]
  simpa [D, I, f, distanceCount, hx] using hcount

end Submissions.Erdos654OneThirdBaseline.Direct
