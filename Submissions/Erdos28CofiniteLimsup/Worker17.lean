import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Order.LiminfLimsup

open Filter Set
open scoped Pointwise

namespace Submissions.Erdos28CofiniteLimsup.Worker17

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A).card

theorem proof :
    ∀ A : Set ℕ, Aᶜ.Finite →
      limsup (fun n : ℕ => (representationCount A n : ℕ∞)) atTop = (⊤ : ℕ∞) := by
  intro A hA
  classical
  obtain ⟨N, hN⟩ := hA.bddAbove
  apply Filter.Tendsto.limsup_eq
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro k
  filter_upwards [eventually_ge_atTop (2 * (N + 1) + k + 1)] with n hn
  let f : ℕ → ℕ × ℕ := fun i => (N + 1 + i, n - (N + 1 + i))
  let candidates := (Finset.range (k + 1)).image f
  have hf : Function.Injective f := by
    intro i j hij
    have hfirst := congrArg Prod.fst hij
    simp only [f] at hfirst
    omega
  have hcandidates : candidates.card = k + 1 := by
    simp only [candidates, Finset.card_image_of_injective _ hf, Finset.card_range]
  have hsubset :
      candidates ⊆
        (Finset.antidiagonal n).filter
          (fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A) := by
    intro p hp
    simp only [candidates, Finset.mem_image, Finset.mem_range] at hp
    rcases hp with ⟨i, hi, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_antidiagonal.mpr
      simp only [f]
      omega
    · constructor
      · by_contra hnot
        have hcomp : N + 1 + i ∈ Aᶜ := hnot
        have := hN hcomp
        omega
      · by_contra hnot
        have hcomp : n - (N + 1 + i) ∈ Aᶜ := hnot
        have := hN hcomp
        omega
  have hcard := Finset.card_le_card hsubset
  rw [representationCount]
  exact ENat.natCast_lt_natCast.mpr (by omega)

end Submissions.Erdos28CofiniteLimsup.Worker17
