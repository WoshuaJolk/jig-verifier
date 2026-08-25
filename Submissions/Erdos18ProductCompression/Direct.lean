import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

namespace Submissions.Erdos18ProductCompression.Direct

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/-- Every target through `N` has a representation by at most `k` distinct
divisors of `N`. -/
def boundedRep (N k : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ N →
    ∃ D : Finset ℕ,
      D ⊆ N.divisors ∧ D.card ≤ k ∧ m = D.sum id

theorem practicalH_le_of_boundedRep {N k : ℕ} (h : boundedRep N k) :
    practicalH N ≤ k := by
  simp only [practicalH, Finset.sup_le_iff, Finset.mem_Icc]
  intro m hm
  obtain ⟨D, hDsub, hDcard, hDsum⟩ := h m hm.2
  have hmem :
      D.card ∈ {j | ∃ E : Finset ℕ,
        E ⊆ N.divisors ∧ E.card = j ∧ m ∈ subsetSums E} :=
    ⟨D, hDsub, rfl, D, rfl.subset, hDsum⟩
  exact (Nat.sInf_le hmem).trans hDcard

theorem boundedRep_mul {A B ka kb : ℕ}
    (hApos : 0 < A) (hBpos : 0 < B)
    (hA : boundedRep A ka) (hB : boundedRep B kb) :
    boundedRep (A * B) (ka + kb) := by
  intro m hm
  let q := m / A
  let r := m % A
  have hrlt : r < A := Nat.mod_lt m hApos
  have hq : q ≤ B := by
    apply Nat.div_le_of_le_mul
    simpa [mul_comm] using hm
  obtain ⟨DA, hDAsub, hDAcard, hDAsum⟩ := hA r hrlt.le
  obtain ⟨DB, hDBsub, hDBcard, hDBsum⟩ := hB q hq
  let scaled := DB.image (A * ·)
  have hscaledCard : scaled.card = DB.card := by
    rw [show scaled = DB.image (A * ·) from rfl]
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left hApos hxy
  have hscaledSum : scaled.sum id = A * q := by
    rw [show scaled = DB.image (A * ·) from rfl]
    rw [Finset.sum_image (fun x _ y _ hxy =>
      Nat.eq_of_mul_eq_mul_left hApos hxy)]
    simpa [Finset.mul_sum, hDBsum]
  have hDAsub' : DA ⊆ (A * B).divisors := by
    intro d hd
    have hdA : d ∣ A := Nat.dvd_of_mem_divisors (hDAsub hd)
    exact Nat.mem_divisors.mpr
      ⟨hdA.trans (dvd_mul_right A B), Nat.mul_ne_zero hApos.ne' hBpos.ne'⟩
  have hscaledSub : scaled ⊆ (A * B).divisors := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    have heB : e ∣ B := Nat.dvd_of_mem_divisors (hDBsub he)
    exact Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul_left A heB, Nat.mul_ne_zero hApos.ne' hBpos.ne'⟩
  have hdisj : Disjoint DA scaled := by
    rw [Finset.disjoint_left]
    intro d hdA hdS
    have hd_le_r : d ≤ r := by
      rw [hDAsum]
      exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hdA
    obtain ⟨e, he, hde⟩ := Finset.mem_image.mp hdS
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors (hDBsub he)) hBpos
    have hA_le_d : A ≤ d := by
      rw [← hde]
      nlinarith
    omega
  refine ⟨DA ∪ scaled, ?_, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact hDAsub' hd
    · exact hscaledSub hd
  · rw [Finset.card_union_of_disjoint hdisj, hscaledCard]
    omega
  · rw [Finset.sum_union hdisj, hscaledSum]
    rw [← hDAsum]
    simpa [q, r, add_comm] using (Nat.div_add_mod m A).symm

theorem boundedRep_pow_succ {A k : ℕ}
    (hApos : 0 < A) (hA : boundedRep A k) :
    ∀ t : ℕ, boundedRep (A ^ (t + 1)) ((t + 1) * k) := by
  intro t
  induction t with
  | zero =>
      simpa using hA
  | succ t ih =>
      have hprod := boundedRep_mul (pow_pos hApos (t + 1)) hApos ih hA
      simpa [pow_succ, Nat.succ_eq_add_one, add_assoc, add_mul, two_mul] using hprod

theorem proof :
    (∀ A B ka kb : ℕ,
        0 < A → 0 < B →
        boundedRep A ka → boundedRep B kb →
        boundedRep (A * B) (ka + kb) ∧
          practicalH (A * B) ≤ ka + kb) ∧
      (∀ A k t : ℕ,
        0 < A → boundedRep A k →
        boundedRep (A ^ (t + 1)) ((t + 1) * k) ∧
          practicalH (A ^ (t + 1)) ≤ (t + 1) * k) := by
  constructor
  · intro A B ka kb hApos hBpos hA hB
    have hprod := boundedRep_mul hApos hBpos hA hB
    exact ⟨hprod, practicalH_le_of_boundedRep hprod⟩
  · intro A k t hApos hA
    have hpow := boundedRep_pow_succ hApos hA t
    exact ⟨hpow, practicalH_le_of_boundedRep hpow⟩

end Submissions.Erdos18ProductCompression.Direct
