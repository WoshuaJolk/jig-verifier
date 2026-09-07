import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Signed-kernel Sidon energy on a finite additive commutative group.
The diagonal/off-diagonal expansion follows the standard finite Sidon
convolution argument (see declangessel's Erdos30ThreeSmoothingLosses).
Here each complete autocorrelation is grouped before comparing sums;
individual kernel products may be negative. This is an energy lemma,
not a construction of a kernel or a proof of the sharp Sidon conjecture.
-/
noncomputable section
namespace SignedSidonEnergy
open Finset

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- Uniqueness of unordered two-term sums, including repeated summands. -/
def IsSidon (A : Finset G) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

omit [Fintype G] [DecidableEq G] in
/-- The usual sum condition makes nonzero ordered differences injective. -/
theorem difference_injective {A : Finset G} (hA : IsSidon A) :
    Set.InjOn (fun p : G × G => p.1-p.2) (A.offDiag : Set (G × G)) := by
  intro p hp q hq he
  obtain ⟨ha, hb, hab⟩ := mem_offDiag.mp hp
  obtain ⟨hc, hd, _hcd⟩ := mem_offDiag.mp hq
  have hs : p.1+q.2=q.1+p.2 := sub_eq_sub_iff_add_eq_add.mp he
  rcases hA p.1 ha q.2 hd q.1 hc p.2 hb hs with hh | hh
  · exact Prod.ext hh.1 hh.2.symm
  · exact (hab hh.1).elim

/-- Complete autocorrelation; its summands are allowed to have either sign. -/
def autocorrelation (K : G → ℝ) (d : G) : ℝ := ∑ x, K x*K (x+d)

omit [DecidableEq G] in
theorem autocorrelation_zero (K : G → ℝ) :
    autocorrelation K 0 = ∑ x, K x^2 := by
  simp [autocorrelation, pow_two]

omit [DecidableEq G] in
theorem autocorrelation_total (K : G → ℝ) :
    (∑ d, autocorrelation K d) = (∑ x, K x)^2 := by
  unfold autocorrelation
  rw [sum_comm]
  simp_rw [← mul_sum]
  have hshift : ∀ x, (∑ d, K (x+d)) = ∑ d, K d :=
    fun x => Equiv.sum_comp (Equiv.addLeft x) K
  simp_rw [hshift]
  rw [← sum_mul, pow_two]

omit [DecidableEq G] in
theorem translated_product (K : G → ℝ) (a b : G) :
    (∑ x, K (x-a)*K (x-b)) = autocorrelation K (a-b) := by
  calc
    _ = ∑ x, K (x-a)*K ((x-a)+(a-b)) := by
      simp only [sub_add_sub_cancel]
    _ = _ := (Equiv.subRight a).sum_comp (fun x => K x*K (x+(a-b)))

/-- Exact expansion into the diagonal and complete difference correlations. -/
theorem energy_identity (A : Finset G) (K : G → ℝ) :
    (∑ x, (∑ a ∈ A, K (x-a))^2) =
      (A.card : ℝ)*(∑ x, K x^2) +
        ∑ p ∈ A.offDiag, autocorrelation K (p.1-p.2) := by
  calc
    _ = ∑ x, ∑ p ∈ A ×ˢ A, K (x-p.1)*K (x-p.2) := by
      apply sum_congr rfl
      intro x _
      rw [pow_two, sum_mul_sum, sum_product]
    _ = ∑ p ∈ A ×ˢ A, autocorrelation K (p.1-p.2) := by
      rw [sum_comm]
      exact sum_congr rfl fun p _ => translated_product K p.1 p.2
    _ = _ := by
      rw [← diag_union_offDiag, sum_union (disjoint_diag_offDiag A), sum_diag]
      simp [autocorrelation_zero, nsmul_eq_mul]

/-- Signed kernels need only nonnegative complete nonzero autocorrelations.
No sign restriction is imposed on K or on its individual pair products.
The statement also includes the empty Sidon set. -/
theorem signed_kernel_energy_le (A : Finset G) (K : G → ℝ)
    (hA : IsSidon A) (hmass : ∑ x, K x = 1)
    (hcor : ∀ d, d ≠ 0 → 0 ≤ autocorrelation K d) :
    (∑ x, (∑ a ∈ A, K (x-a))^2) ≤
      1 + ((A.card : ℝ)-1)*(∑ x, K x^2) := by
  have hoff : (∑ p ∈ A.offDiag, autocorrelation K (p.1-p.2)) ≤
      ∑ d ∈ (univ : Finset G).erase 0, autocorrelation K d := by
    rw [← sum_image (difference_injective hA)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
      exact mem_erase.mpr ⟨sub_ne_zero.mpr (mem_offDiag.mp hp).2.2, mem_univ _⟩
    · intro d hd _
      exact hcor d (mem_erase.mp hd).1
  have htotal := sum_erase_add (univ : Finset G) (autocorrelation K) (mem_univ 0)
  rw [autocorrelation_total, hmass, autocorrelation_zero] at htotal
  rw [energy_identity]
  nlinarith

end SignedSidonEnergy

namespace Submissions.Erdos30SignedCorrelationEnergy.Savcab
open Finset
theorem proof : ∀ (G : Type) [Fintype G] [AddCommGroup G] [DecidableEq G],
    ∀ (A : Finset G) (K : G → ℝ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)) →
    (∑ x, K x = 1) →
    (∀ d : G, d ≠ 0 → 0 ≤ ∑ x, K x*K (x+d)) →
    (∑ x, (∑ a ∈ A, K (x-a))^2) ≤
      1 + ((A.card : ℝ)-1)*(∑ x, K x^2) := by
  intro G _ _ _ A K hA hmass hcor
  exact SignedSidonEnergy.signed_kernel_energy_le A K hA hmass hcor
end Submissions.Erdos30SignedCorrelationEnergy.Savcab
