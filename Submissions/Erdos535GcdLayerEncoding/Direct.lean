import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Submissions.Erdos535GcdLayerEncoding.Direct

private def layers (n : ℕ) : Finset (ℕ × ℕ) :=
  n.factorization.support.biUnion fun p =>
    (Finset.range (n.factorization p)).image fun j => (p, j)

private theorem mem_layers {n p j : ℕ} :
    (p, j) ∈ layers n ↔ j < n.factorization p := by
  constructor
  · intro h
    simp only [layers, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_range] at h
    obtain ⟨q, _, i, hi, hp⟩ := h
    cases hp
    exact hi
  · intro h
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · exact Finsupp.mem_support_iff.mpr (by omega)
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr h, rfl⟩

theorem proof :
    ∀ a b : ℕ, a ≠ 0 → b ≠ 0 →
      layers (Nat.gcd a b) = layers a ∩ layers b := by
  intro a b ha hb
  ext ⟨p, j⟩
  simp only [mem_layers, Finset.mem_inter]
  rw [Nat.factorization_gcd ha hb]
  simp only [Finsupp.inf_apply]
  omega

end Submissions.Erdos535GcdLayerEncoding.Direct
