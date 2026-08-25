import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos1SqrtLowerBound.Erdos1SqrtLowerBoundProof

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

private theorem square_mass (s : Finset ℤ) (r q : ℕ)
    (hcard : 2 * r - 1 + q ≤ s.card) :
    (q : ℤ) * (r : ℤ) ^ 2 ≤ ∑ x ∈ s, x ^ 2 := by
  let inside := s.filter fun x => |x| < (r : ℤ)
  have hi_sub : inside ⊆ Finset.Ioo (-(r : ℤ)) (r : ℤ) := by
    intro x hx
    simp only [inside, Finset.mem_filter] at hx
    simp only [Finset.mem_Ioo]
    exact abs_lt.mp hx.2
  have hi_card : inside.card ≤ 2 * r - 1 := by
    have hle := Finset.card_le_card hi_sub
    simp only [Int.card_Ioo] at hle
    omega
  have hq : q ≤ (s \ inside).card := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    change q ≤ s.card - inside.card
    omega
  calc
    (q : ℤ) * (r : ℤ) ^ 2 ≤ ((s \ inside).card : ℤ) * (r : ℤ) ^ 2 := by
      gcongr
    _ = ∑ _x ∈ s \ inside, (r : ℤ) ^ 2 := by
      simp [mul_comm]
    _ ≤ ∑ x ∈ s \ inside, x ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hx_not : ¬ |x| < (r : ℤ) := by
        intro h
        exact (Finset.mem_sdiff.mp hx).2
          (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1, h⟩)
      have hr : (r : ℤ) ≤ |x| := le_of_not_gt hx_not
      nlinarith [sq_nonneg x, sq_abs x]
    _ ≤ ∑ x ∈ s, x ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.sdiff_subset
      · intro x _ _
        positivity

private def centered (A S : Finset ℕ) : ℤ :=
  2 * ((S.sum id : ℕ) : ℤ) - ((A.sum id : ℕ) : ℤ)

private theorem centered_second_moment (A : Finset ℕ) :
    ∑ S ∈ A.powerset, centered A S ^ 2 =
      2 ^ A.card * ∑ x ∈ A, (x : ℤ) ^ 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [centered]
  | @insert a A ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hins :
          (∑ S ∈ A.powerset, centered (insert a A) (insert a S) ^ 2) =
            ∑ S ∈ A.powerset,
              (2 * ((a : ℤ) + ((S.sum id : ℕ) : ℤ)) -
                ((a : ℤ) + ((A.sum id : ℕ) : ℤ))) ^ 2 := by
        apply Finset.sum_congr rfl
        intro S hS
        simp only [centered]
        rw [Finset.sum_insert (Finset.notMem_of_mem_powerset_of_notMem hS ha),
          Finset.sum_insert ha]
        push_cast
        simp only [id_eq]
      rw [hins, ← Finset.sum_add_distrib]
      have hpair (S : Finset ℕ) :
          centered (insert a A) S ^ 2 +
              (2 * ((a : ℤ) + ((S.sum id : ℕ) : ℤ)) -
                ((a : ℤ) + ((A.sum id : ℕ) : ℤ))) ^ 2 =
            2 * centered A S ^ 2 + 2 * (a : ℤ) ^ 2 := by
        simp only [centered]
        rw [Finset.sum_insert ha]
        push_cast
        simp only [id_eq]
        ring
      simp_rw [hpair]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih, Finset.sum_const,
        Finset.card_powerset, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      simp only [nsmul_eq_mul]
      norm_cast
      ring

private theorem int_bound (N : ℕ) (A : Finset ℕ)
    (hcard : 2 ≤ A.card)
    (hsub : A ⊆ Finset.Icc 1 N)
    (hinj : (fun (S : A.powerset) => S.1.sum id).Injective) :
    ((2 ^ (A.card - 1) : ℕ) : ℤ) * ((2 ^ (A.card - 2) : ℕ) : ℤ) ^ 2 ≤
      ((2 ^ A.card : ℕ) : ℤ) * (A.card : ℤ) * (N : ℤ) ^ 2 := by
  classical
  let d : Finset ℕ → ℤ := centered A
  let vals : Finset ℤ := A.powerset.image d
  have hd_inj : Set.InjOn d (A.powerset : Set (Finset ℕ)) := by
    intro S hS T hT hST
    have hsum : S.sum id = T.sum id := by
      simp only [d, centered] at hST
      omega
    have hsubeq : (⟨S, hS⟩ : A.powerset) = ⟨T, hT⟩ := hinj hsum
    exact congrArg Subtype.val hsubeq
  have hvals_card : vals.card = 2 ^ A.card := by
    simp only [vals, Finset.card_image_of_injOn hd_inj, Finset.card_powerset]
  have hlarge :
      ((2 ^ (A.card - 1) : ℕ) : ℤ) * ((2 ^ (A.card - 2) : ℕ) : ℤ) ^ 2 ≤
        ∑ x ∈ vals, x ^ 2 := by
    apply square_mass vals (2 ^ (A.card - 2)) (2 ^ (A.card - 1))
    rw [hvals_card]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hcard
    rw [hk]
    rw [show 2 + k - 2 = k by omega, show 2 + k - 1 = k + 1 by omega,
      show 2 + k = (k + 1) + 1 by omega]
    simp only [pow_succ]
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hvals_sum :
      (∑ x ∈ vals, x ^ 2) =
        ((2 ^ A.card : ℕ) : ℤ) * ∑ x ∈ A, (x : ℤ) ^ 2 := by
    rw [show (∑ x ∈ vals, x ^ 2) =
        ∑ S ∈ A.powerset, d S ^ 2 by
      exact Finset.sum_image hd_inj]
    exact centered_second_moment A
  have hsquares :
      (∑ x ∈ A, (x : ℤ) ^ 2) ≤ (A.card : ℤ) * (N : ℤ) ^ 2 := by
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul A (fun x => (x : ℤ) ^ 2) ((N : ℤ) ^ 2)
        (fun x hx => by
          have hxN : x ≤ N := (Finset.mem_Icc.mp (hsub hx)).2
          norm_cast
          nlinarith))
  calc
    _ ≤ ∑ x ∈ vals, x ^ 2 := hlarge
    _ = ((2 ^ A.card : ℕ) : ℤ) * ∑ x ∈ A, (x : ℤ) ^ 2 := hvals_sum
    _ ≤ ((2 ^ A.card : ℕ) : ℤ) * ((A.card : ℤ) * (N : ℤ) ^ 2) := by
      gcongr
    _ = _ := by ring

theorem proof : ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → 2 ≤ A.card →
    2 ^ (A.card - 1) * (2 ^ (A.card - 2)) ^ 2 ≤
      2 ^ A.card * A.card * N ^ 2 := by
  intro N A h hcard
  exact_mod_cast int_bound N A hcard h.1 h.2

end Submissions.Erdos1SqrtLowerBound.Erdos1SqrtLowerBoundProof
