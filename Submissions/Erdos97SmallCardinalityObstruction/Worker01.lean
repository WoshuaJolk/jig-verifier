import Mathlib.Analysis.InnerProductSpace.PiL2
namespace Submissions.Erdos97SmallCardinalityObstruction.Worker01
open Finset Metric
open scoped Classical
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def HasNEquidistantPointsAt (n : ℕ) (A : Finset Plane) (p : Plane) : Prop := ∃ r : ℝ, r > 0 ∧ (A.filter fun q ↦ dist p q = r).card ≥ n
def HasNEquidistantProperty (n : ℕ) (A : Finset Plane) : Prop := ∀ p ∈ A, HasNEquidistantPointsAt n A p
theorem proof : ∀ A : Finset Plane, A.Nonempty → A.card ≤ 4 → ¬HasNEquidistantProperty 4 A := by
 intro A hA hc hprop
 obtain ⟨p,hp⟩ := hA
 obtain ⟨r,hr,hfour⟩ := hprop p hp
 have hpn : p ∉ A.filter (fun q ↦ dist p q = r) := by
  simp only [mem_filter,hp,true_and,dist_self]
  exact ne_of_lt hr
 have hs : A.filter (fun q ↦ dist p q = r) ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,by
  intro heq
  apply hpn
  rw [heq]
  exact hp⟩
 have hlt := card_lt_card hs
 omega
end Submissions.Erdos97SmallCardinalityObstruction.Worker01
