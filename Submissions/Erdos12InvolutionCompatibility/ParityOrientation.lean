import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Submissions.Erdos12InvolutionCompatibility.ParityOrientation

/-- For any nonempty family of involutions, avoiding every matched pair gives
at most half of the ambient finite set.  Even if the involutions commute and
generate a hypercube, the constraints do not multiply: equality is precisely
a simultaneous parity orientation, with every involution swapping membership
and nonmembership. -/
theorem proof :
    ∀ {X I : Type} [Fintype X] [DecidableEq X] [Nonempty I]
      (σ : I → X → X) (A : Finset X),
      (∀ i x, σ i (σ i x) = x) →
      (∀ i x, x ∈ A → σ i x ∉ A) →
      2 * A.card ≤ Fintype.card X ∧
        (2 * A.card = Fintype.card X →
          ∀ i x, (x ∈ A ↔ σ i x ∉ A)) := by
  intro X I _ _ _ σ A hinvol havoid
  have hinj : ∀ i, Function.Injective (σ i) := by
    intro i x y hxy
    have h := congrArg (σ i) hxy
    simpa [hinvol i x, hinvol i y] using h
  have himage_subset : ∀ i, A.image (σ i) ⊆ Finset.univ \ A := by
    intro i y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp [havoid i x hx]
  let i₀ : I := Classical.choice inferInstance
  have hcard_image : (A.image (σ i₀)).card = A.card :=
    Finset.card_image_of_injOn (hinj i₀).injOn
  have hbound : 2 * A.card ≤ Fintype.card X := by
    have hle := Finset.card_le_card (himage_subset i₀)
    rw [hcard_image] at hle
    simp only [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ] at hle
    omega
  refine ⟨hbound, ?_⟩
  intro hmax i x
  have hcard_image_i : (A.image (σ i)).card = A.card :=
    Finset.card_image_of_injOn (hinj i).injOn
  have himage_eq : A.image (σ i) = Finset.univ \ A := by
    apply Finset.eq_of_subset_of_card_le (himage_subset i)
    rw [hcard_image_i]
    simp only [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
    omega
  constructor
  · exact havoid i x
  · intro hxnot
    have hxcomp : σ i x ∈ Finset.univ \ A := by simp [hxnot]
    rw [← himage_eq] at hxcomp
    obtain ⟨y, hy, hsig⟩ := Finset.mem_image.mp hxcomp
    have hyx : y = x := hinj i hsig
    rwa [hyx] at hy

end Submissions.Erdos12InvolutionCompatibility.ParityOrientation
