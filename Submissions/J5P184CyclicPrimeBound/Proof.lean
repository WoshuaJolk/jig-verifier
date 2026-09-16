import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.IntegralDomain

/-! Saved finite prime-parameter Sidon bound. Ruzsa's cyclic construction and
prior campaign compression/transfer are credited; no asymptotic root or novelty claim.
Exact original declaration bodies are retained below in separate sections. -/

namespace Submissions.J5P184CyclicPrimeBound.Proof

-- BEGIN original 00: p184/verifier/Submissions/Erdos530IntegerFreimanCompression/Main.lean
section Original0

namespace Submissions.Erdos530IntegerFreimanCompression.Main

/-- A sufficiently large half-cell modulus can be coprime to every divisor of `D`.
No prime existence theorem is needed. -/
theorem exists_auxiliary_modulus (m D T : ℕ) (hm : 0 < m) (hD : 0 < D) :
    ∃ K Q : ℕ, 0 < K ∧ D ∣ K ∧ Q + 1 = 2 * m * K ∧
      1 < Q ∧ T < Q ∧ Nat.Coprime D Q := by
  let K := D * (T + 2)
  have hK : T + 2 ≤ K := by
    dsimp [K]
    nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ D by omega) (Nat.zero_le (T + 2))]
  have hM : T + 3 ≤ 2 * m * K := by
    nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ m by omega) (Nat.zero_le K)]
  let Q := 2 * m * K - 1
  have hQ : Q + 1 = 2 * m * K := Nat.sub_add_cancel (by omega)
  have hcop : Nat.Coprime Q (2 * m * K) := by
    exact (Nat.coprime_self_sub_left (show 1 ≤ 2 * m * K by omega)).mpr (by simp)
  have hdvd : D ∣ 2 * m * K := by
    refine ⟨2 * m * (T + 2), ?_⟩
    dsimp [K]
    ring
  exact ⟨K, Q, by omega, ⟨T + 2, rfl⟩, hQ, by omega, by omega,
    (hcop.of_dvd_right hdvd).symm⟩

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

/-- Every finite integer set admits arbitrarily large half-cell moduli for which
all distinct input differences are units. Empty and singleton sets are included. -/
theorem exists_difference_unit_modulus (A : Finset ℤ) (m T : ℕ) (hm : 0 < m) :
    ∃ K Q : ℕ, 0 < K ∧ Q + 1 = 2 * m * K ∧ 1 < Q ∧ T < Q ∧
      ∀ a ∈ A, ∀ b ∈ A, a ≠ b → IsUnit ((a : ZMod Q) - (b : ZMod Q)) := by
  classical
  let D := ∏ p ∈ A.offDiag, (p.1 - p.2).natAbs
  have hD : 0 < D := by
    apply Finset.prod_pos
    intro p hp
    exact Int.natAbs_pos.mpr (sub_ne_zero.mpr (Finset.mem_offDiag.mp hp).2.2)
  obtain ⟨K, Q, hK, _, hQ, hQ1, hT, hcop⟩ := exists_auxiliary_modulus m D T hm hD
  refine ⟨K, Q, hK, hQ, hQ1, hT, ?_⟩
  intro a ha b hb hab
  have hdvd : (a - b).natAbs ∣ D :=
    Finset.dvd_prod_of_mem (a := (a, b)) (s := A.offDiag)
      (fun p : ℤ × ℤ => (p.1 - p.2).natAbs)
      (Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩)
  have hu : IsUnit (((a - b).natAbs : ℕ) : ZMod Q) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (hcop.of_dvd_left hdvd)
  have hu' : IsUnit ((a - b : ℤ) : ZMod Q) := by
    rcases Int.natAbs_eq_iff.mp (rfl : (a - b).natAbs = (a - b).natAbs) with h | h
    · rw [h, Int.cast_natCast]
      exact hu
    · rw [h, Int.cast_neg, Int.cast_natCast]
      exact hu.neg
  simpa only [Int.cast_sub] using hu'

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

/-- Common-phase affine evaluation at two input points. -/
def affinePair {R : Type*} [CommRing R] (a b : R) (p : R × R) : R × R :=
  (a * p.1 + p.2, b * p.1 + p.2)

/-- The two evaluations are jointly bijective whenever the input difference is a unit.
No primality, nonzero-modulus or nontrivial-ring assumption is needed. -/
theorem affinePair_bijective {R : Type*} [CommRing R] (a b : R)
    (hab : IsUnit (a - b)) : Function.Bijective (affinePair a b) := by
  obtain ⟨u, hu⟩ := hab
  let g : R × R → R × R := fun p =>
    ((↑u⁻¹ : R) * (p.1 - p.2), p.1 - a * ((↑u⁻¹ : R) * (p.1 - p.2)))
  have hleft : Function.LeftInverse g (affinePair a b) := by
    rintro ⟨s, t⟩
    have hs : (↑u⁻¹ : R) * ((a * s + t) - (b * s + t)) = s := by
      calc
        _ = ((↑u⁻¹ : R) * (a - b)) * s := by ring
        _ = s := by rw [← hu, u.inv_mul, one_mul]
    dsimp [g, affinePair]
    rw [hs]
    apply Prod.ext
    · rfl
    · ring
  have hright : Function.RightInverse g (affinePair a b) := by
    rintro ⟨x, y⟩
    have hs : (a - b) * ((↑u⁻¹ : R) * (x - y)) = x - y := by
      calc
        _ = ((a - b) * (↑u⁻¹ : R)) * (x - y) := by ring
        _ = x - y := by rw [← hu, u.mul_inv, one_mul]
    dsimp [g, affinePair]
    apply Prod.ext
    · ring
    · change b * ((↑u⁻¹ : R) * (x - y)) +
        (x - a * ((↑u⁻¹ : R) * (x - y))) = y
      calc
        _ = x - (a - b) * ((↑u⁻¹ : R) * (x - y)) := by ring
        _ = y := by rw [hs]; ring
  exact ⟨hleft.injective, hright.surjective⟩

/-- In particular, no field structure is required for the auxiliary modulus. -/
theorem zmod_affinePair_bijective (Q : ℕ) (a b : ZMod Q)
    (hab : IsUnit (a - b)) :
    Function.Bijective (fun p : ZMod Q × ZMod Q =>
      (a * p.1 + p.2, b * p.1 + p.2)) :=
  affinePair_bijective a b hab

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

/-- An affine pair with unit input difference has exactly one sample in every fiber.
This uses the existing bijection, with no field or primality assumption. -/
theorem affinePair_fiber_card {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (a b : R) (hab : IsUnit (a - b)) (r : R × R) :
    ((Finset.univ : Finset (R × R)).filter fun p => affinePair a b p = r).card = 1 := by
  have h := Finset.card_bijective
    (s := (Finset.univ : Finset (R × R)).filter fun p => affinePair a b p = r)
    (t := {r}) (affinePair a b) (affinePair_bijective a b hab) (by
      intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton])
  simpa only [Finset.card_singleton] using h

/-- For each slope there is exactly one phase, `r - a*s`, giving a chosen output.
Zero slopes are included, and no second input point or unit condition is needed. -/
theorem affine_onepoint_fiber_card {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (a r : R) :
    ((Finset.univ : Finset (R × R)).filter fun p => a * p.1 + p.2 = r).card =
      Fintype.card R := by
  symm
  change (Finset.univ : Finset R).card = _
  apply Finset.card_bij (fun s _ => (s, r - a * s))
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ring
  · intro s₁ hs₁ s₂ hs₂ h
    exact congrArg Prod.fst h
  · intro p hp
    refine ⟨p.1, Finset.mem_univ _, ?_⟩
    have he : a * p.1 + p.2 = r := (Finset.mem_filter.mp hp).2
    apply Prod.ext
    · rfl
    · change r - a * p.1 = p.2
      rw [← he]
      ring

/-- `NeZero Q` is the positive-natural-modulus condition needed for the finite sample space. -/
theorem zmod_onepoint_fiber_card (Q : ℕ) [NeZero Q] (a r : ZMod Q) :
    ((Finset.univ : Finset (ZMod Q × ZMod Q)).filter
      fun p => a * p.1 + p.2 = r).card = Q := by
  simpa only [ZMod.card] using affine_onepoint_fiber_card a r

/-- This is the joint-fiber premise used by `sum_ordered_collisions_of_pair_fibers`. -/
theorem zmod_pair_fiber_card (Q : ℕ) [NeZero Q] (a b : ZMod Q)
    (hab : IsUnit (a - b)) (r : ZMod Q × ZMod Q) :
    ((Finset.univ : Finset (ZMod Q × ZMod Q)).filter
      fun p => (a * p.1 + p.2, b * p.1 + p.2) = r).card = 1 := by
  obtain ⟨p, hp⟩ := (affinePair_bijective a b hab).surjective r
  apply Finset.card_eq_one.mpr
  refine ⟨p, ?_⟩
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hq
    exact (affinePair_bijective a b hab).injective (hq.trans hp.symm)
  · rintro rfl
    exact hp

theorem zmod_affine_sample_card (Q : ℕ) [NeZero Q] :
    (Finset.univ : Finset (ZMod Q × ZMod Q)).card = Q ^ 2 := by
  simp only [Finset.card_univ, Fintype.card_prod, ZMod.card, Nat.pow_two]

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

private theorem offset_half_cell_iff {m K j d : ℤ}
    (hm : 0 < m) (hj : 0 ≤ j) (hjm : j < m) :
    (0 ≤ m * d + j ∧ 2 * (m * d + j) < 2 * m * K - 1) ↔
      0 ≤ d ∧ d < K := by
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_contra hd
      have hd' : d ≤ -1 := by
        simpa using Int.le_sub_one_of_lt (lt_of_not_ge hd)
      have hp := mul_le_mul_of_nonneg_left hd' hm.le
      nlinarith
    · by_contra hd
      have hp := mul_le_mul_of_nonneg_left (le_of_not_gt hd) hm.le
      nlinarith
  · rintro ⟨hd, hdK⟩
    refine ⟨add_nonneg (mul_nonneg hm.le hd) hj, ?_⟩
    have hp := mul_le_mul_of_nonneg_left (Int.le_sub_one_of_lt hdK) hm.le
    have hj' := Int.le_sub_one_of_lt hjm
    nlinarith

/-- Exact half-cell endpoints, expressed without division. -/
theorem half_cell_inequalities_iff {m K j r : ℤ}
    (hm : 0 < m) (hj : 0 ≤ j) (hjm : j < m) :
    (j * (2 * m * K - 1) ≤ m * r ∧
      2 * (m * r - j * (2 * m * K - 1)) < 2 * m * K - 1) ↔
      2 * j * K ≤ r ∧ r < (2 * j + 1) * K := by
  have h := offset_half_cell_iff (K := K) (d := r - 2 * j * K) hm hj hjm
  have heq : m * (r - 2 * j * K) + j =
      m * r - j * (2 * m * K - 1) := by ring
  rw [heq] at h
  constructor
  · rintro ⟨hlo, hhi⟩
    have hd := h.mp ⟨sub_nonneg.mpr hlo, hhi⟩
    constructor <;> nlinarith [hd.1, hd.2]
  · rintro ⟨hlo, hhi⟩
    have hd := h.mpr (show 0 ≤ r - 2 * j * K ∧
        r - 2 * j * K < K by constructor <;> nlinarith)
    exact ⟨sub_nonneg.mp hd.1, hd.2⟩

/-- The quotient/remainder version with an explicit positive auxiliary modulus.
The hypotheses imply the endpoints lie inside `[0,Q)`; no bound on `r` is needed. -/
theorem nat_half_cell_iff_of_eq {m K Q j r : ℕ}
    (hm : 0 < m) (hQ : 0 < Q) (hQeq : Q + 1 = 2 * m * K) (hj : j < m) :
    (m * r / Q = j ∧ 2 * (m * r % Q) < Q) ↔
      2 * j * K ≤ r ∧ r < (2 * j + 1) * K := by
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hjz : (j : ℤ) < m := by exact_mod_cast hj
  have hQz : (Q : ℤ) = 2 * (m : ℤ) * K - 1 := by
    have he : (Q : ℤ) + 1 = 2 * (m : ℤ) * K := by exact_mod_cast hQeq
    linarith
  have h := half_cell_inequalities_iff (K := (K : ℤ)) (r := (r : ℤ))
    hmz (Int.natCast_nonneg j) hjz
  rw [← hQz] at h
  constructor
  · rintro ⟨hq, hr⟩
    have hdivision : ((m * r % Q : ℕ) : ℤ) + (Q : ℤ) * j = (m : ℤ) * r := by
      have hn := Nat.mod_add_div (m * r) Q
      rw [hq] at hn
      exact_mod_cast hn
    have hrz : 2 * ((m * r % Q : ℕ) : ℤ) < Q := by exact_mod_cast hr
    have hc : (j : ℤ) * Q ≤ (m : ℤ) * r ∧
        2 * ((m : ℤ) * r - (j : ℤ) * Q) < Q := by
      constructor <;> nlinarith [Int.natCast_nonneg (m * r % Q)]
    have he := h.mp hc
    exact_mod_cast he
  · intro he
    have hez : 2 * (j : ℤ) * K ≤ r ∧ (r : ℤ) < (2 * (j : ℤ) + 1) * K := by
      exact_mod_cast he
    have hc := h.mpr hez
    have hlo : j * Q ≤ m * r := by exact_mod_cast hc.1
    have hQpos : (0 : ℤ) < Q := by exact_mod_cast hQ
    have hhiZ : (m : ℤ) * r < ((j : ℤ) + 1) * Q := by
      nlinarith [hc.1, hc.2]
    have hhi : m * r < (j + 1) * Q := by exact_mod_cast hhiZ
    have hq := Nat.div_eq_of_lt_le hlo hhi
    have hdivision : ((m * r % Q : ℕ) : ℤ) + (Q : ℤ) * j = (m : ℤ) * r := by
      have hn := Nat.mod_add_div (m * r) Q
      rw [hq] at hn
      exact_mod_cast hn
    have hrz : 2 * ((m * r % Q : ℕ) : ℤ) < Q := by nlinarith [hc.2]
    exact ⟨hq, by exact_mod_cast hrz⟩

/-- For `Q = 2*m*K-1`, the accepted residues in cell `j` are exactly `K`
consecutive integers, starting at `2*j*K`. -/
theorem nat_half_cell_iff {m K j r : ℕ}
    (hm : 0 < m) (hK : 0 < K) (hj : j < m) :
    (m * r / (2 * m * K - 1) = j ∧
      2 * (m * r % (2 * m * K - 1)) < 2 * m * K - 1) ↔
      2 * j * K ≤ r ∧ r < (2 * j + 1) * K := by
  have htwo : 1 < 2 * m * K := by nlinarith [Nat.mul_pos hm hK]
  exact nat_half_cell_iff_of_eq hm (Nat.sub_pos_of_lt htwo)
    (Nat.sub_add_cancel (Nat.le_of_lt htwo)) hj

theorem half_cell_card (j K : ℕ) :
    (Finset.Ico (2 * j * K) ((2 * j + 1) * K)).card = K := by
  simp [Nat.card_Ico, add_mul]

/-- Counting the accepted residues by their exact interval description. -/
theorem filtered_half_cell_card {m K j : ℕ}
    (hm : 0 < m) (hK : 0 < K) (hj : j < m) :
    ((Finset.range (2 * m * K - 1)).filter fun r =>
      m * r / (2 * m * K - 1) = j ∧
        2 * (m * r % (2 * m * K - 1)) < 2 * m * K - 1).card = K := by
  have htwo : 1 < 2 * m * K := by nlinarith [Nat.mul_pos hm hK]
  have hQeq := Nat.sub_add_cancel (Nat.le_of_lt htwo)
  have hJK : (2 * j + 2) * K ≤ 2 * m * K :=
    Nat.mul_le_mul_right K (by nlinarith [Nat.succ_le_of_lt hj])
  have hsets : ((Finset.range (2 * m * K - 1)).filter fun r =>
      m * r / (2 * m * K - 1) = j ∧
        2 * (m * r % (2 * m * K - 1)) < 2 * m * K - 1) =
      Finset.Ico (2 * j * K) ((2 * j + 1) * K) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
      nat_half_cell_iff hm hK hj]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by nlinarith [h.2, Nat.succ_le_of_lt hK], h⟩
  rw [hsets, half_cell_card]

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

/-- Positivity hypotheses provide the instance needed to enumerate the residue ring. -/
theorem half_modulus_neZero {m K : ℕ} (hm : 0 < m) (hK : 0 < K) :
    NeZero (2 * m * K - 1) := by
  have htwo : 1 < 2 * m * K := by nlinarith [Nat.mul_pos hm hK]
  exact ⟨(Nat.sub_pos_of_lt htwo).ne'⟩

/-- Accepted residues with quotient label `j`. -/
def zmodHalfCell (m K : ℕ) [NeZero (2 * m * K - 1)] (j : ℕ) :
    Finset (ZMod (2 * m * K - 1)) :=
  Finset.univ.filter fun r : ZMod (2 * m * K - 1) =>
    m * r.val / (2 * m * K - 1) = j ∧
      2 * (m * r.val % (2 * m * K - 1)) < 2 * m * K - 1

@[simp] theorem mem_zmodHalfCell {m K j : ℕ} [NeZero (2 * m * K - 1)]
    {r : ZMod (2 * m * K - 1)} :
    r ∈ zmodHalfCell m K j ↔
      m * r.val / (2 * m * K - 1) = j ∧
        2 * (m * r.val % (2 * m * K - 1)) < 2 * m * K - 1 := by
  simp [zmodHalfCell]

/-- The residue-ring cell has exactly the previously proved integer endpoints. -/
theorem mem_zmodHalfCell_iff_interval {m K j : ℕ} [NeZero (2 * m * K - 1)]
    (hm : 0 < m) (hK : 0 < K) (hj : j < m)
    {r : ZMod (2 * m * K - 1)} :
    r ∈ zmodHalfCell m K j ↔
      2 * j * K ≤ r.val ∧ r.val < (2 * j + 1) * K :=
  mem_zmodHalfCell.trans (nat_half_cell_iff hm hK hj)

theorem image_val_zmodHalfCell {m K j : ℕ} [NeZero (2 * m * K - 1)] :
    (zmodHalfCell m K j).image ZMod.val =
      (Finset.range (2 * m * K - 1)).filter (fun r =>
        m * r / (2 * m * K - 1) = j ∧
          2 * (m * r % (2 * m * K - 1)) < 2 * m * K - 1) := by
  ext n
  constructor
  · intro hn
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt r), mem_zmodHalfCell.mp hr⟩
  · intro hn
    obtain ⟨hrange, hcell⟩ := Finset.mem_filter.mp hn
    have hv : (n : ZMod (2 * m * K - 1)).val = n :=
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)
    refine Finset.mem_image.mpr ⟨(n : ZMod (2 * m * K - 1)), ?_, hv⟩
    apply mem_zmodHalfCell.mpr
    simpa only [hv] using hcell

/-- Transport the exact K-point count through the injective canonical representative map. -/
theorem card_zmodHalfCell {m K j : ℕ} [NeZero (2 * m * K - 1)]
    (hm : 0 < m) (hK : 0 < K) (hj : j < m) :
    (zmodHalfCell m K j).card = K := by
  calc
    (zmodHalfCell m K j).card = ((zmodHalfCell m K j).image ZMod.val).card :=
      (Finset.card_image_of_injective _ (ZMod.val_injective (2 * m * K - 1))).symm
    _ = K := by
      rw [image_val_zmodHalfCell]
      exact filtered_half_cell_card hm hK hj

/-- Distinct quotient labels give disjoint cells, even without restricting the labels. -/
theorem disjoint_zmodHalfCell {m K i j : ℕ} [NeZero (2 * m * K - 1)]
    (hij : i ≠ j) : Disjoint (zmodHalfCell m K i) (zmodHalfCell m K j) := by
  apply Finset.disjoint_left.mpr
  intro r hi hj
  exact hij ((mem_zmodHalfCell.mp hi).1.symm.trans (mem_zmodHalfCell.mp hj).1)

theorem pairwiseDisjoint_zmodHalfCell {m K : ℕ} [NeZero (2 * m * K - 1)] :
    (Finset.range m : Set ℕ).PairwiseDisjoint (zmodHalfCell m K) := by
  intro i _ j _ hij
  exact disjoint_zmodHalfCell hij

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

open scoped BigOperators

/-- Count a finite incidence relation in either order. -/
theorem sum_card_filter_swap {α β : Type*} (S : Finset α) (T : Finset β)
    (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
    (∑ a ∈ S, (T.filter (p a)).card) =
      ∑ b ∈ T, (S.filter fun a => p a b).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Uniform fibers over the accepted residues give the exact retained-point total.
The finite affine map and its uniformity are explicit premises, not established here. -/
theorem sum_retained_of_uniform_fibers {Ω α R : Type*} [DecidableEq R]
    (samples : Finset Ω) (S : Finset α) (accepted : Finset R)
    (e : Ω → α → R) (Q : ℕ)
    (hfiber : ∀ x ∈ S, ∀ r ∈ accepted,
      (samples.filter fun ω => e ω x = r).card = Q) :
    (∑ ω ∈ samples, (S.filter fun x => e ω x ∈ accepted).card) =
      S.card * accepted.card * Q := by
  rw [sum_card_filter_swap]
  calc
    (∑ x ∈ S, (samples.filter fun ω => e ω x ∈ accepted).card) =
        ∑ x ∈ S, ∑ r ∈ accepted, (samples.filter fun ω => e ω x = r).card := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Finset.sum_card_fiberwise_eq_card_filter samples accepted (fun ω => e ω x)).symm
    _ = ∑ _x ∈ S, accepted.card * Q := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_const_nat (hfiber x hx)
    _ = S.card * accepted.card * Q := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_assoc]

/-- Each distinct input pair hits each accepted residue pair exactly once.
Residue pairs on the diagonal remain included: only equal input points are excluded. -/
theorem sum_ordered_collisions_of_pair_fibers {Ω α R : Type*}
    [DecidableEq α] [DecidableEq R]
    (samples : Finset Ω) (S : Finset α) (pairs : Finset (R × R))
    (e : Ω → α → R)
    (hfiber : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ r ∈ pairs,
      (samples.filter fun ω => (e ω x, e ω y) = r).card = 1) :
    (∑ ω ∈ samples,
      ((S ×ˢ S).filter fun xy => xy.1 ≠ xy.2 ∧ (e ω xy.1, e ω xy.2) ∈ pairs).card) =
      S.card * (S.card - 1) * pairs.card := by
  have hshape (ω : Ω) :
      ((S ×ˢ S).filter fun xy => xy.1 ≠ xy.2 ∧ (e ω xy.1, e ω xy.2) ∈ pairs) =
        S.offDiag.filter (fun xy => (e ω xy.1, e ω xy.2) ∈ pairs) := by
    apply Finset.ext
    intro xy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag, and_assoc]
  simp_rw [hshape]
  have h := sum_retained_of_uniform_fibers samples S.offDiag pairs
    (fun ω xy => (e ω xy.1, e ω xy.2)) 1 (by
      intro xy hxy r hr
      obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
      exact hfiber xy.1 hx xy.2 hy hne r hr)
  simpa only [Finset.offDiag_card, Nat.mul_sub_one, mul_one] using h

/-- `m` disjoint cells of size `K` contain `m*K` residues and `m*K²` same-cell pairs.
Together with the two uniform-fiber lemmas this gives the exact affine totals.
No half-cell geometry or affine uniformity is proved by this cardinality identity. -/
theorem equal_disjoint_cell_counts {ι R : Type*} [DecidableEq R]
    (I : Finset ι) (cell : ι → Finset R) (K : ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint cell)
    (hsize : ∀ i ∈ I, (cell i).card = K) :
    (I.biUnion cell).card = I.card * K ∧
      (I.biUnion fun i => cell i ×ˢ cell i).card = I.card * K ^ 2 := by
  constructor
  · rw [Finset.card_biUnion hdisj]
    exact Finset.sum_const_nat hsize
  · have hpairs : (I : Set ι).PairwiseDisjoint (fun i => cell i ×ˢ cell i) := by
      intro i hi j hj hij
      exact Finset.disjoint_product.mpr (Or.inl (hdisj hi hj hij))
    rw [Finset.card_biUnion hpairs]
    apply Finset.sum_const_nat
    intro i hi
    simp only [Finset.card_product, hsize i hi, Nat.pow_two]

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

open scoped BigOperators

/-- Exact totals for the retained affine family and its ordered same-label collisions.
Distinct input differences must be units; residue pairs may lie on the diagonal.
The empty input set is included. This theorem asserts counts, not Freiman preservation. -/
theorem compression_counts (A : Finset ℤ) (m K : ℕ) [NeZero (2 * m * K - 1)]
    (hm : 0 < m) (hK : 0 < K)
    (hunit : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      IsUnit ((a : ZMod (2 * m * K - 1)) - (b : ZMod (2 * m * K - 1)))) :
    let Q := 2 * m * K - 1
    let accepted := (Finset.range m).biUnion (zmodHalfCell m K)
    let e : (ZMod Q × ZMod Q) → ℤ → ZMod Q := fun ω a => (a : ZMod Q) * ω.1 + ω.2
    let B := fun ω => A.filter fun a => e ω a ∈ accepted
    let label := fun ω a => m * (e ω a).val / Q
    (∑ ω : ZMod Q × ZMod Q, (B ω).card) = A.card * m * K * Q ∧
      (∑ ω : ZMod Q × ZMod Q,
        ((B ω ×ˢ B ω).filter fun ab =>
          ab.1 ≠ ab.2 ∧ label ω ab.1 = label ω ab.2).card) =
        A.card * (A.card - 1) * m * K ^ 2 := by
  let Q := 2 * m * K - 1
  let accepted := (Finset.range m).biUnion (zmodHalfCell m K)
  let pairs := (Finset.range m).biUnion fun j => zmodHalfCell m K j ×ˢ zmodHalfCell m K j
  let e : (ZMod Q × ZMod Q) → ℤ → ZMod Q := fun ω a => (a : ZMod Q) * ω.1 + ω.2
  let B := fun ω => A.filter fun a => e ω a ∈ accepted
  let label := fun ω a => m * (e ω a).val / Q
  change (∑ ω : ZMod Q × ZMod Q, (B ω).card) = A.card * m * K * Q ∧
    (∑ ω : ZMod Q × ZMod Q,
      ((B ω ×ˢ B ω).filter fun ab =>
        ab.1 ≠ ab.2 ∧ label ω ab.1 = label ω ab.2).card) =
      A.card * (A.card - 1) * m * K ^ 2
  have hcells := equal_disjoint_cell_counts (Finset.range m) (zmodHalfCell m K) K
    pairwiseDisjoint_zmodHalfCell (by
      intro j hj
      exact card_zmodHalfCell hm hK (Finset.mem_range.mp hj))
  have haccepted : accepted.card = m * K := by
    simpa only [accepted, Finset.card_range] using hcells.1
  have hpairs : pairs.card = m * K ^ 2 := by
    simpa only [pairs, Finset.card_range] using hcells.2
  have hpair (r s : ZMod Q) :
      (r, s) ∈ pairs ↔ r ∈ accepted ∧ s ∈ accepted ∧ m * r.val / Q = m * s.val / Q := by
    constructor
    · intro hrs
      obtain ⟨j, hj, hrs⟩ := Finset.mem_biUnion.mp hrs
      obtain ⟨hr, hs⟩ := Finset.mem_product.mp hrs
      refine ⟨Finset.mem_biUnion.mpr ⟨j, hj, hr⟩,
        Finset.mem_biUnion.mpr ⟨j, hj, hs⟩, ?_⟩
      exact (mem_zmodHalfCell.mp hr).1.trans (mem_zmodHalfCell.mp hs).1.symm
    · rintro ⟨hr, hs, heq⟩
      obtain ⟨i, hi, hri⟩ := Finset.mem_biUnion.mp hr
      obtain ⟨j, hj, hsj⟩ := Finset.mem_biUnion.mp hs
      refine Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_product.mpr ⟨hri, ?_⟩⟩
      exact mem_zmodHalfCell.mpr
        ⟨heq.symm.trans (mem_zmodHalfCell.mp hri).1, (mem_zmodHalfCell.mp hsj).2⟩
  have hcollision (ω : ZMod Q × ZMod Q) :
      ((B ω ×ˢ B ω).filter fun ab =>
        ab.1 ≠ ab.2 ∧ label ω ab.1 = label ω ab.2) =
      ((A ×ˢ A).filter fun ab => ab.1 ≠ ab.2 ∧ (e ω ab.1, e ω ab.2) ∈ pairs) := by
    apply Finset.ext
    intro ab
    simp only [B, label, Finset.mem_filter, Finset.mem_product, hpair]
    constructor
    · rintro ⟨⟨⟨ha, har⟩, ⟨hb, hbr⟩⟩, hab, heq⟩
      exact ⟨⟨ha, hb⟩, hab, har, hbr, heq⟩
    · rintro ⟨⟨ha, hb⟩, hab, har, hbr, heq⟩
      exact ⟨⟨⟨ha, har⟩, ⟨hb, hbr⟩⟩, hab, heq⟩
  constructor
  · have h := sum_retained_of_uniform_fibers Finset.univ A accepted e Q (by
      intro a ha r hr
      exact zmod_onepoint_fiber_card Q (a : ZMod Q) r)
    simpa only [B, haccepted, Nat.mul_assoc] using h
  · have h := sum_ordered_collisions_of_pair_fibers Finset.univ A pairs e (by
      intro a ha b hb hab r hr
      exact zmod_pair_fiber_card Q (a : ZMod Q) (b : ZMod Q) (hunit a ha b hb hab) r)
    calc
      _ = ∑ ω : ZMod Q × ZMod Q,
          ((A ×ˢ A).filter fun ab => ab.1 ≠ ab.2 ∧ (e ω ab.1, e ω ab.2) ∈ pairs).card := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [hcollision]
      _ = A.card * (A.card - 1) * pairs.card := h
      _ = A.card * (A.card - 1) * m * K ^ 2 := by
        rw [hpairs]
        simp only [Nat.mul_assoc]

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

open scoped BigOperators

/-- Select one sample from the retained-point and ordered-collision totals.
The score may be negative; neither independence nor a sign assumption is needed here. -/
theorem exists_affine_sample_bound {α : Type*} (Ω : Finset α) (hΩ : Ω.Nonempty)
    (B P : α → ℤ) (n m K Q : ℤ)
    (hB : ∑ ω ∈ Ω, B ω = n * m * K * Q)
    (hP : ∑ ω ∈ Ω, P ω = n * (n - 1) * m * K ^ 2) :
    ∃ ω ∈ Ω, 2 * n * m * K * Q - n * (n - 1) * m * K ^ 2 ≤
      (Ω.card : ℤ) * (2 * B ω - P ω) := by
  have htotal : (∑ ω ∈ Ω, (2 * B ω - P ω)) =
      2 * n * m * K * Q - n * (n - 1) * m * K ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hB, hP]
    ring
  apply Finset.exists_le_of_sum_le hΩ
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, htotal, le_refl]

/-- A two-sample total selects the larger sample; no pointwise bound was assumed. -/
example : ∃ ω ∈ ({0, 1} : Finset ℤ), (2 : ℤ) ≤ 4 * ω := by
  obtain ⟨ω, hω, h⟩ := exists_affine_sample_bound ({0, 1} : Finset ℤ)
    (by simp) (fun ω => ω) (fun _ => 0) 1 1 1 1 (by norm_num) (by norm_num)
  refine ⟨ω, hω, ?_⟩
  norm_num at h
  omega

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Each lost image representative is paid for by two ordered distinct collisions. -/
theorem two_card_le_two_card_image_add_collisions (S : Finset α) (f : α → β) :
    2 * S.card ≤ 2 * (S.image f).card +
      ((S ×ˢ S).filter fun ab => ab.1 ≠ ab.2 ∧ f ab.1 = f ab.2).card := by
  classical
  let P : Finset α → Finset (α × α) := fun T =>
    (T ×ˢ T).filter fun ab => ab.1 ≠ ab.2 ∧ f ab.1 = f ab.2
  change 2 * S.card ≤ 2 * (S.image f).card + (P S).card
  induction S using Finset.induction_on with
  | empty => simp [P]
  | @insert a S ha ih =>
    have hsub : P S ⊆ P (insert a S) :=
      Finset.filter_subset_filter _
        (Finset.product_subset_product (Finset.subset_insert a S)
          (Finset.subset_insert a S))
    rw [Finset.card_insert_of_notMem ha, Finset.image_insert]
    by_cases hf : f a ∈ S.image f
    · rw [Finset.card_insert_of_mem hf]
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hf
      have hab : a ≠ b := by
        intro h
        exact ha (h.symm ▸ hb)
      have habn : (a, b) ∉ P S := by simp [P, ha]
      have hban : (b, a) ∉ P S := by simp [P, ha]
      have hpairs : (a, b) ≠ (b, a) := by
        intro h
        exact hab (congrArg Prod.fst h)
      have hnew : (a, b) ∉ insert (b, a) (P S) := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hpairs, habn⟩
      have hcard : (P S).card + 2 ≤ (P (insert a S)).card := by
        calc
          (P S).card + 2 = (insert (a, b) (insert (b, a) (P S))).card := by
            rw [Finset.card_insert_of_notMem hnew, Finset.card_insert_of_notMem hban]
          _ ≤ (P (insert a S)).card := by
            apply Finset.card_le_card
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · simp [P, hb, hab, hba]
            rcases Finset.mem_insert.mp hx with rfl | hx
            · simp [P, hb, hab.symm, hba]
            · exact hsub hx
      omega
    · rw [Finset.card_insert_of_notMem hf]
      have hcard := Finset.card_le_card hsub
      omega

/-- Delete repeated fiber members, keeping an injective subset with the collision bound.
This is only a finite counting ingredient for the Sidon compression argument. -/
theorem exists_injective_subset_collision_bound (S : Finset α) (f : α → β) :
    ∃ C : Finset α, C ⊆ S ∧ Set.InjOn f C ∧
      2 * S.card ≤ 2 * C.card +
        ((S ×ˢ S).filter fun ab => ab.1 ≠ ab.2 ∧ f ab.1 = f ab.2).card := by
  classical
  have hsurj : (S : Set α).SurjOn f (S.image f) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx, rfl⟩
  obtain ⟨C, hC, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (S : Set α) (S.image f) hsurj
  refine ⟨C, (fun _ hx => hC hx), hinj, ?_⟩
  have hcard : (S.image f).card = C.card := by
    rw [← himage]
    exact Finset.card_image_of_injOn hinj
  simpa only [hcard] using two_card_le_two_card_image_add_collisions S f

/-- A two-point constant fiber saturates the bound, including both collision orientations. -/
example :
    2 * ({0, 1} : Finset ℕ).card =
      2 * (({0, 1} : Finset ℕ).image (fun _ => ())).card +
        ((({0, 1} : Finset ℕ) ×ˢ ({0, 1} : Finset ℕ)).filter
          fun ab => ab.1 ≠ ab.2 ∧ (fun _ : ℕ => ()) ab.1 = ()).card := by
  decide

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

/-- The exact finite averaging inequality implies the desired rational bound by
integer-lattice rounding. `L` may be negative, as retained size minus collisions can be. -/
theorem compression_lattice_rounding (n m Q L : ℤ)
    (hn : 0 ≤ n) (hm : 0 < m) (hQ : 1 < Q)
    (hlarge : 3 * (n * (n - 1)) < Q)
    (haverage : 4 * m * n * (Q + 1) * Q - n * (n - 1) * (Q + 1) ^ 2 ≤
      8 * m * L * Q ^ 2) :
    4 * m * n - n * (n - 1) ≤ 8 * m * L := by
  let c := n * (n - 1)
  have hc : 0 ≤ c := by
    rcases (show n = 0 ∨ 1 ≤ n by omega) with rfl | hn1
    · simp [c]
    · dsimp [c]; positivity
  change 4 * m * n - c ≤ 8 * m * L
  change 3 * c < Q at hlarge
  change 4 * m * n * (Q + 1) * Q - c * (Q + 1) ^ 2 ≤
    8 * m * L * Q ^ 2 at haverage
  by_contra! hbad
  have hsmall : 8 * m * L ≤ 4 * m * n - c - 1 := by omega
  have hp := mul_le_mul_of_nonneg_right hsmall (sq_nonneg Q)
  have hq : 0 < (Q - 3 * c) * Q := mul_pos (by omega) (by omega)
  have hqc : 0 ≤ c * (Q - 1) := mul_nonneg hc (by omega)
  have hmn : 0 ≤ 4 * m * n * Q := by positivity
  nlinarith only [haverage, hp, hq, hqc, hmn]

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

open scoped BigOperators

/-- Exact finite totals imply a large injective representative set for one sample.
This is conditional on the sample counts: it does not construct the affine family,
establish those totals, or prove Freiman preservation. -/
theorem finite_compression_of_exact_totals {Ω α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (samples : Finset Ω) (hne : samples.Nonempty)
    (B : Ω → Finset α) (f : Ω → α → β) (n m K Q : ℕ)
    (hm : 0 < m) (hQ : 1 < Q) (hrel : Q + 1 = 2 * m * K)
    (hlarge : 3 * n * (n - 1) < Q) (hcard : samples.card = Q ^ 2)
    (hB : (∑ ω ∈ samples, ((B ω).card : ℤ)) = (n : ℤ) * m * K * Q)
    (hP : (∑ ω ∈ samples,
      (((B ω ×ˢ B ω).filter fun xy =>
        xy.1 ≠ xy.2 ∧ f ω xy.1 = f ω xy.2).card : ℤ)) =
      (n : ℤ) * ((n : ℤ) - 1) * m * (K : ℤ) ^ 2) :
    ∃ ω ∈ samples, ∃ C : Finset α, C ⊆ B ω ∧ Set.InjOn (f ω) C ∧
      4 * (m : ℤ) * n - (n : ℤ) * ((n : ℤ) - 1) ≤ 8 * (m : ℤ) * C.card := by
  let P : Ω → ℤ := fun ω =>
    ((B ω ×ˢ B ω).filter fun xy =>
      xy.1 ≠ xy.2 ∧ f ω xy.1 = f ω xy.2).card
  change (∑ ω ∈ samples, P ω) =
    (n : ℤ) * ((n : ℤ) - 1) * m * (K : ℤ) ^ 2 at hP
  obtain ⟨ω, hω, havg⟩ := exists_affine_sample_bound samples hne
    (fun ω => ((B ω).card : ℤ)) P n m K Q hB hP
  obtain ⟨C, hCB, hinj, hdel⟩ := exists_injective_subset_collision_bound (B ω) (f ω)
  refine ⟨ω, hω, C, hCB, hinj, ?_⟩
  have hdelZ : 2 * ((B ω).card : ℤ) ≤ 2 * (C.card : ℤ) + P ω := by
    dsimp [P]
    exact_mod_cast hdel
  have hscore : 2 * ((B ω).card : ℤ) - P ω ≤ 2 * (C.card : ℤ) := by omega
  have hcardZ : (samples.card : ℤ) = (Q : ℤ) ^ 2 := by exact_mod_cast hcard
  rw [hcardZ] at havg
  have hbound := havg.trans (mul_le_mul_of_nonneg_left hscore (sq_nonneg (Q : ℤ)))
  have hrelZ : (Q : ℤ) + 1 = 2 * (m : ℤ) * K := by exact_mod_cast hrel
  have hrounding :
      4 * (m : ℤ) * n * ((Q : ℤ) + 1) * Q -
        (n : ℤ) * ((n : ℤ) - 1) * ((Q : ℤ) + 1) ^ 2 ≤
      8 * (m : ℤ) * C.card * (Q : ℤ) ^ 2 := by
    calc
      _ = (4 * (m : ℤ)) * (2 * (n : ℤ) * m * K * Q -
          (n : ℤ) * ((n : ℤ) - 1) * m * (K : ℤ) ^ 2) := by
        rw [hrelZ]
        ring
      _ ≤ (4 * (m : ℤ)) * ((Q : ℤ) ^ 2 * (2 * (C.card : ℤ))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by ring
  -- The product cast is valid even at n = 0, where casting n-1 alone would be wrong.
  have hpred : ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    cases n with
    | zero => simp
    | succ n => simp [Nat.cast_mul]
  have hlargeN : 3 * (n * (n - 1)) < Q := by
    simpa only [Nat.mul_assoc] using hlarge
  have hlargeZ : 3 * ((n : ℤ) * ((n : ℤ) - 1)) < (Q : ℤ) := by
    have h : (3 : ℤ) * ((n * (n - 1) : ℕ) : ℤ) < (Q : ℤ) := by
      exact_mod_cast hlargeN
    rwa [hpred] at h
  exact compression_lattice_rounding n m Q C.card (by positivity)
    (by exact_mod_cast hm) (by exact_mod_cast hQ) hlargeZ hrounding

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

/-- Integer quotient preservation on half-cells. Inputs may repeat or be negative;
only the auxiliary modulus `Q` must be positive. -/
theorem quotient_pair_difference_eq_mul
    {m Q r₁ r₂ r₃ r₄ z : ℤ} (hQ : 0 < Q)
    (h₁ : 2 * (m * r₁ % Q) < Q) (h₂ : 2 * (m * r₂ % Q) < Q)
    (h₃ : 2 * (m * r₃ % Q) < Q) (h₄ : 2 * (m * r₄ % Q) < Q)
    (hsum : r₁ + r₂ - r₃ - r₄ = Q * z) :
    m * r₁ / Q + m * r₂ / Q - m * r₃ / Q - m * r₄ / Q = m * z := by
  let k : ℤ := m * r₁ / Q + m * r₂ / Q - m * r₃ / Q - m * r₄ / Q - m * z
  have hbalance : Q * k + m * r₁ % Q + m * r₂ % Q -
      m * r₃ % Q - m * r₄ % Q = 0 := by
    have hscaled := congrArg (fun x : ℤ => m * x) hsum
    dsimp [k]
    nlinarith [Int.emod_add_mul_ediv (m * r₁) Q,
      Int.emod_add_mul_ediv (m * r₂) Q,
      Int.emod_add_mul_ediv (m * r₃) Q,
      Int.emod_add_mul_ediv (m * r₄) Q]
  have hupper : Q * k < Q := by
    nlinarith [Int.emod_nonneg (m * r₁) hQ.ne', Int.emod_nonneg (m * r₂) hQ.ne']
  have hlower : -Q < Q * k := by
    nlinarith [Int.emod_nonneg (m * r₃) hQ.ne', Int.emod_nonneg (m * r₄) hQ.ne']
  have hkhi : k < 1 := (mul_lt_mul_iff_right₀ hQ).mp (by simpa using hupper)
  have hklo : -1 < k := (mul_lt_mul_iff_right₀ hQ).mp (by simpa using hlower)
  have hkzero : k = 0 := le_antisymm
    (Int.le_of_lt_add_one (by simpa using hkhi))
    (Int.le_of_sub_one_lt (by simpa using hklo))
  exact sub_eq_zero.mp hkzero

/-- Equal residue-pair sums modulo `Q` become equal quotient-pair sums modulo `m`
when all four residues lie in the accepted half-cells. -/
theorem quotient_pair_difference_dvd
    {m Q r₁ r₂ r₃ r₄ : ℤ} (hQ : 0 < Q)
    (h₁ : 2 * (m * r₁ % Q) < Q) (h₂ : 2 * (m * r₂ % Q) < Q)
    (h₃ : 2 * (m * r₃ % Q) < Q) (h₄ : 2 * (m * r₄ % Q) < Q)
    (hsum : Q ∣ r₁ + r₂ - r₃ - r₄) :
    m ∣ m * r₁ / Q + m * r₂ / Q - m * r₃ / Q - m * r₄ / Q := by
  obtain ⟨z, hz⟩ := hsum
  exact ⟨z, quotient_pair_difference_eq_mul hQ h₁ h₂ h₃ h₄ hz⟩

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

/-- The natural label of a residue, before casting into the smaller cyclic group. -/
def quotientLabel {Q : ℕ} (m : ℕ) (x : ZMod Q) : ℕ := m * x.val / Q

/-- Natural labels stay in the fundamental interval of the target modulus. -/
theorem quotientLabel_lt {m Q : ℕ} [NeZero Q] (hm : 0 < m) (hQ : 0 < Q)
    (x : ZMod Q) : quotientLabel m x < m := by
  apply (Nat.div_lt_iff_lt_mul hQ).2
  exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x) hm

/-- Equal pair sums of residues give divisible pair sums of their integer representatives. -/
theorem zmod_val_pair_difference_dvd {Q : ℕ} [NeZero Q]
    {x₁ x₂ x₃ x₄ : ZMod Q} (hsum : x₁ + x₂ = x₃ + x₄) :
    (Q : ℤ) ∣ (x₁.val : ℤ) + (x₂.val : ℤ) - (x₃.val : ℤ) - (x₄.val : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ Q).mp
  simpa only [Int.cast_add, Int.cast_sub, Int.cast_natCast,
    ZMod.natCast_zmod_val, sub_sub, sub_eq_zero] using hsum

/-- Compression preserves pair sums modulo `m` on the accepted half-cells.
The four inputs may repeat. -/
theorem zmod_quotientLabel_pair_sum {m Q : ℕ} [NeZero Q] (hQ : 0 < Q)
    {x₁ x₂ x₃ x₄ : ZMod Q}
    (h₁ : 2 * (m * x₁.val % Q) < Q) (h₂ : 2 * (m * x₂.val % Q) < Q)
    (h₃ : 2 * (m * x₃.val % Q) < Q) (h₄ : 2 * (m * x₄.val % Q) < Q)
    (hsum : x₁ + x₂ = x₃ + x₄) :
    (quotientLabel m x₁ : ZMod m) + (quotientLabel m x₂ : ZMod m) =
      (quotientLabel m x₃ : ZMod m) + (quotientLabel m x₄ : ZMod m) := by
  have hdvd := quotient_pair_difference_dvd
    (m := (m : ℤ)) (Q := (Q : ℤ))
    (r₁ := (x₁.val : ℤ)) (r₂ := (x₂.val : ℤ))
    (r₃ := (x₃.val : ℤ)) (r₄ := (x₄.val : ℤ))
    (by exact_mod_cast hQ) (by exact_mod_cast h₁) (by exact_mod_cast h₂)
    (by exact_mod_cast h₃) (by exact_mod_cast h₄)
    (zmod_val_pair_difference_dvd hsum)
  have hdvd' : (m : ℤ) ∣ (quotientLabel m x₁ : ℤ) + (quotientLabel m x₂ : ℤ) -
      (quotientLabel m x₃ : ℤ) - (quotientLabel m x₄ : ℤ) := by
    simpa only [quotientLabel, Int.natCast_ediv, Int.natCast_mul] using hdvd
  have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hdvd'
  simpa only [Int.cast_add, Int.cast_sub, Int.cast_natCast, sub_sub, sub_eq_zero]
    using hzero

/-- The affine residue map with a common slope and translation. -/
def affineZModValue {Q : ℕ} (s t : ZMod Q) (a : ℤ) : ZMod Q := (a : ZMod Q) * s + t

theorem affineZModValue_pair_sum {Q : ℕ} (s t : ZMod Q)
    {a b c d : ℤ} (hsum : a + b = c + d) :
    affineZModValue s t a + affineZModValue s t b =
      affineZModValue s t c + affineZModValue s t d := by
  have hcast : (a : ZMod Q) + (b : ZMod Q) = (c : ZMod Q) + (d : ZMod Q) := by
    simpa only [Int.cast_add] using congrArg (fun z : ℤ => (z : ZMod Q)) hsum
  dsimp [affineZModValue]
  calc
    (a : ZMod Q) * s + t + ((b : ZMod Q) * s + t) =
        ((a : ZMod Q) + (b : ZMod Q)) * s + (t + t) := by ring
    _ = ((c : ZMod Q) + (d : ZMod Q)) * s + (t + t) := by rw [hcast]
    _ = (c : ZMod Q) * s + t + ((d : ZMod Q) * s + t) := by ring

/-- The affine half-cell compression is a Freiman homomorphism on accepted inputs. -/
theorem affineZMod_quotientLabel_pair_sum {m Q : ℕ} [NeZero Q] (hQ : 0 < Q)
    (s t : ZMod Q) {a b c d : ℤ}
    (ha : 2 * (m * (affineZModValue s t a).val % Q) < Q)
    (hb : 2 * (m * (affineZModValue s t b).val % Q) < Q)
    (hc : 2 * (m * (affineZModValue s t c).val % Q) < Q)
    (hd : 2 * (m * (affineZModValue s t d).val % Q) < Q)
    (hsum : a + b = c + d) :
    (quotientLabel m (affineZModValue s t a) : ZMod m) +
        (quotientLabel m (affineZModValue s t b) : ZMod m) =
      (quotientLabel m (affineZModValue s t c) : ZMod m) +
        (quotientLabel m (affineZModValue s t d) : ZMod m) :=
  zmod_quotientLabel_pair_sum hQ ha hb hc hd (affineZModValue_pair_sum s t hsum)

/-- Selecting distinct natural labels also selects distinct labels in `ZMod m`. -/
theorem quotientLabel_injOn_cast {α : Type*} {m Q : ℕ} [NeZero Q]
    (hm : 0 < m) (hQ : 0 < Q) (f : α → ZMod Q) (S : Set α)
    (hinj : Set.InjOn (fun a => quotientLabel m (f a)) S) :
    Set.InjOn (fun a => (quotientLabel m (f a) : ZMod m)) S := by
  intro a ha b hb hab
  apply hinj ha hb
  have hval := congrArg (fun x : ZMod m => x.val) hab
  simpa only [ZMod.val_natCast_of_lt (quotientLabel_lt hm hQ (f a)),
    ZMod.val_natCast_of_lt (quotientLabel_lt hm hQ (f b))] using hval

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

open scoped BigOperators

/-- Every finite integer set admits a large subset with injective half-cell labels.
The explicit sample and half-window bounds are retained for the separate Freiman proof.
Empty and singleton input sets require no separate nonemptiness assumption. -/
theorem exists_integer_halfcell_compression (A : Finset ℤ) (m : ℕ) (hm : 0 < m) :
    ∃ K Q : ℕ, 0 < K ∧ Q + 1 = 2 * m * K ∧ 1 < Q ∧
      ∃ ω : ZMod Q × ZMod Q, ∃ C : Finset ℤ, C ⊆ A ∧
        (∀ a ∈ C,
          m * (((a : ZMod Q) * ω.1 + ω.2).val) / Q < m ∧
            2 * (m * (((a : ZMod Q) * ω.1 + ω.2).val) % Q) < Q) ∧
        Set.InjOn (fun a : ℤ => m * (((a : ZMod Q) * ω.1 + ω.2).val) / Q) C ∧
        4 * (m : ℤ) * A.card - (A.card : ℤ) * ((A.card : ℤ) - 1) ≤
          8 * (m : ℤ) * C.card := by
  obtain ⟨K, Q, hK, hrel, hQ, hlarge, hunit⟩ :=
    exists_difference_unit_modulus A m (3 * A.card * (A.card - 1)) hm
  have hQeq : Q = 2 * m * K - 1 := by omega
  subst Q
  let Q := 2 * m * K - 1
  letI : NeZero (2 * m * K - 1) := half_modulus_neZero hm hK
  let accepted := (Finset.range m).biUnion (zmodHalfCell m K)
  let e : (ZMod Q × ZMod Q) → ℤ → ZMod Q := fun ω a => (a : ZMod Q) * ω.1 + ω.2
  let B := fun ω => A.filter fun a => e ω a ∈ accepted
  let label := fun ω a => m * (e ω a).val / Q
  have hcounts := compression_counts A m K hm hK hunit
  change
    (∑ ω : ZMod Q × ZMod Q, (B ω).card) = A.card * m * K * Q ∧
      (∑ ω : ZMod Q × ZMod Q,
        ((B ω ×ˢ B ω).filter fun ab =>
          ab.1 ≠ ab.2 ∧ label ω ab.1 = label ω ab.2).card) =
        A.card * (A.card - 1) * m * K ^ 2 at hcounts
  have hB : (∑ ω : ZMod Q × ZMod Q, ((B ω).card : ℤ)) =
      (A.card : ℤ) * m * K * Q := by
    exact_mod_cast hcounts.1
  have hpred (n : ℕ) : ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    cases n with
    | zero => simp
    | succ n => simp [Nat.cast_mul]
  have hP : (∑ ω : ZMod Q × ZMod Q,
      (((B ω ×ˢ B ω).filter fun ab =>
        ab.1 ≠ ab.2 ∧ label ω ab.1 = label ω ab.2).card : ℤ)) =
      (A.card : ℤ) * ((A.card : ℤ) - 1) * m * (K : ℤ) ^ 2 := by
    have h : (∑ ω : ZMod Q × ZMod Q,
        (((B ω ×ˢ B ω).filter fun ab =>
          ab.1 ≠ ab.2 ∧ label ω ab.1 = label ω ab.2).card : ℤ)) =
        ((A.card * (A.card - 1) : ℕ) : ℤ) * m * (K : ℤ) ^ 2 := by
      exact_mod_cast hcounts.2
    rwa [hpred] at h
  obtain ⟨ω, hω, C, hCB, hinj, hsize⟩ := finite_compression_of_exact_totals
    (Finset.univ : Finset (ZMod Q × ZMod Q)) Finset.univ_nonempty
    B label A.card m K Q hm hQ hrel hlarge (zmod_affine_sample_card Q) hB hP
  refine ⟨K, Q, hK, hrel, hQ, ω, C, ?_, ?_, hinj, hsize⟩
  · intro a ha
    exact (Finset.mem_filter.mp (hCB ha)).1
  · intro a ha
    have hacc : e ω a ∈ accepted := (Finset.mem_filter.mp (hCB ha)).2
    obtain ⟨j, hj, hcell⟩ := Finset.mem_biUnion.mp hacc
    have hc := mem_zmodHalfCell.mp hcell
    refine ⟨?_, hc.2⟩
    calc
      _ = j := hc.1
      _ < m := Finset.mem_range.mp hj

/-- Finite common-phase compression into the cyclic group, with an injective
Freiman 2-morphism on at least `|A|/2 - |A|(|A|-1)/(8m)` points.
The displayed integer inequality avoids division and includes the empty set.
This finite compression theorem does not establish the root's sharp constant one. -/
theorem exists_integer_freiman_compression (A : Finset ℤ) (m : ℕ) (hm : 0 < m) :
    ∃ C : Finset ℤ, C ⊆ A ∧ ∃ f : ℤ → ZMod m, Set.InjOn f C ∧
      (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ d ∈ C,
        a + b = c + d → f a + f b = f c + f d) ∧
      4 * (m : ℤ) * A.card - (A.card : ℤ) * ((A.card : ℤ) - 1) ≤
        8 * (m : ℤ) * C.card := by
  obtain ⟨K, Q, hK, hrel, hQ, ω, C, hCA, hacc, hinj, hsize⟩ :=
    exists_integer_halfcell_compression A m hm
  have hQpos : 0 < Q := by omega
  letI : NeZero Q := ⟨Nat.ne_of_gt hQpos⟩
  let f : ℤ → ZMod m := fun a =>
    (quotientLabel m (affineZModValue ω.1 ω.2 a) : ZMod m)
  refine ⟨C, hCA, f, ?_, ?_, hsize⟩
  · apply quotientLabel_injOn_cast hm hQpos (affineZModValue ω.1 ω.2) (C : Set ℤ)
    simpa only [quotientLabel, affineZModValue] using hinj
  · intro a ha b hb c hc d hd hsum
    exact affineZMod_quotientLabel_pair_sum hQpos ω.1 ω.2
      (hacc a ha).2 (hacc b hb).2 (hacc c hc).2 (hacc d hd).2 hsum

end Submissions.Erdos530IntegerFreimanCompression.Main

namespace Submissions.Erdos530IntegerFreimanCompression.Main

theorem proof :
    ∀ (A : Finset ℤ) (m : ℕ), 0 < m →
  ∃ C : Finset ℤ, C ⊆ A ∧ ∃ f : ℤ → ZMod m, Set.InjOn f C ∧
    (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ d ∈ C,
      a + b = c + d → f a + f b = f c + f d) ∧
    4 * (m : ℤ) * A.card - (A.card : ℤ) * ((A.card : ℤ) - 1) ≤
      8 * (m : ℤ) * C.card :=
  exists_integer_freiman_compression

end Submissions.Erdos530IntegerFreimanCompression.Main
end Original0
-- END original 00

-- BEGIN original 01: p184/verifier/Submissions/P184Transfer/RationalTransfer.lean
section Original1

namespace P184Transfer

/-- A rational linear functional separates any finite set of real numbers.
Finite avoidance of proper hyperplanes is already available in Mathlib. -/
theorem exists_rat_linear_injOn (D : Finset ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, Set.InjOn f D := by
  classical
  let X := (D ×ˢ D).filter fun p => p.1 ≠ p.2
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero
    (K := ℚ) (fun p : ↥X => p.val.1 - p.val.2)
    (fun p => sub_ne_zero.mpr (Finset.mem_filter.mp p.property).2)
  refine ⟨f, ?_⟩
  intro a ha b hb hab
  by_contra hne
  have hpair : (a, b) ∈ X :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hne⟩
  have hnz := hf ⟨(a, b), hpair⟩
  apply hnz
  change f (a - b) = 0
  rw [map_sub, hab, sub_self]

/-- No loss of points or pair-sum relations is needed to pass from reals to rationals. -/
theorem exists_rat_freiman_model (A : Finset ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, Set.InjOn f A ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        f a + f b = f c + f d ↔ a + b = c + d := by
  classical
  let D := A ∪ (A ×ˢ A).image (fun p => p.1 + p.2)
  obtain ⟨f, hf⟩ := exists_rat_linear_injOn D
  have hsum {a b : ℝ} (ha : a ∈ A) (hb : b ∈ A) : a + b ∈ D :=
    Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)
  refine ⟨f, fun _ ha _ hb hab => hf (Finset.mem_union_left _ ha)
    (Finset.mem_union_left _ hb) hab, ?_⟩
  intro a ha b hb c hc d hd
  constructor
  · intro h
    exact hf (hsum ha hb) (hsum hc hd) (by simpa only [map_add] using h)
  · intro h
    simpa only [map_add] using congrArg f h

end P184Transfer

end Original1
-- END original 01

-- BEGIN original 02: p184/verifier/Submissions/P184Transfer/DenominatorTransfer.lean
section Original2

namespace P184Transfer

/-- Clear all denominators in a finite rational set with one positive integer.
The total function is only specified on B, and no nonemptiness is required. -/
theorem exists_positive_integer_scaling (B : Finset ℚ) :
    ∃ D : ℤ, 0 < D ∧ ∃ g : ℚ → ℤ, ∀ b ∈ B, (g b : ℚ) = (D : ℚ) * b := by
  classical
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples
    (S := ℚ) (Submonoid.pos ℤ) B id
  let g : ℚ → ℤ := fun b => if hb : b ∈ B then (hD b hb).choose else 0
  refine ⟨(D : ℤ), D.property, g, ?_⟩
  intro b hb
  dsimp only [g]
  rw [dif_pos hb]
  simpa only [Algebra.smul_def, eq_intCast, id_eq] using (hD b hb).choose_spec

end P184Transfer


/- Intake and scope: the parent alone compiles this unbuilt candidate. Read the
complete Localization/Integer.lean, including its finite-family product proof,
and the rational positive-integer localization instance in FractionRing.lean.
This specializes existing denominator-clearing machinery. It introduces no
admitted proof, custom axiom, native evaluator, or external execution path.
The separation of real pair sums and the composed Freiman equivalence are
separate parent-owned obligations; this theorem does not assume either one. -/
end Original2
-- END original 02

-- BEGIN original 03: p184/verifier/Submissions/P184Transfer/RealIntegerTransfer.lean
section Original3

namespace P184Transfer

/-- Every finite real set has an integer model with exactly the same pair-sum
relations, without deleting points and including all repeated summands. -/
theorem exists_integer_freiman_model (A : Finset ℝ) :
    ∃ f : ℝ → ℤ, Set.InjOn f A ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        f a + f b = f c + f d ↔ a + b = c + d := by
  classical
  obtain ⟨q, hqinj, hqsum⟩ := exists_rat_freiman_model A
  obtain ⟨D, hD, g, hg⟩ := exists_positive_integer_scaling (A.image q)
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hgA (a : ℝ) (ha : a ∈ A) : (g (q a) : ℚ) = (D : ℚ) * q a :=
    hg (q a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hginj {a b : ℝ} (ha : a ∈ A) (hb : b ∈ A)
      (h : g (q a) = g (q b)) : a = b := by
    apply hqinj ha hb
    apply mul_left_cancel₀ hD0
    rw [← hgA a ha, ← hgA b hb, h]
  refine ⟨fun a => g (q a), fun _ ha _ hb h => hginj ha hb h, ?_⟩
  intro a ha b hb c hc d hd
  constructor
  · intro h
    apply (hqsum a ha b hb c hc d hd).mp
    apply mul_left_cancel₀ hD0
    have hr := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hr
    rw [hgA a ha, hgA b hb, hgA c hc, hgA d hd] at hr
    simpa only [mul_add] using hr
  · intro h
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hgA a ha, hgA b hb, hgA c hc, hgA d hd,
      ← mul_add, ← mul_add, (hqsum a ha b hb c hc d hd).mpr h]

end P184Transfer

end Original3
-- END original 03

-- BEGIN original 04: p184/verifier/Submissions/P184Transfer/SidonTransfer.lean
section Original4

namespace P184Transfer

def IsSidon {α : Type*} [Add α] (S : Finset α) : Prop :=
  ∀ ⦃a b c d : α⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- An injective Freiman map pulls Sidon subsets back without changing their size. -/
theorem pullback_sidon {α β : Type*} [Add α] [Add β] [DecidableEq β]
    (A : Finset α) (f : α → β) (hinj : Set.InjOn f A)
    (hfreiman : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → f a + f b = f c + f d)
    (T : Finset β) (hT : T ⊆ A.image f) (hSidon : IsSidon T) :
    ∃ S : Finset α, S ⊆ A ∧ IsSidon S ∧ S.card = T.card := by
  classical
  obtain ⟨S, hSA, hST⟩ := Finset.subset_image_iff.mp hT
  refine ⟨S, hSA, ?_, ?_⟩
  · intro a b c d ha hb hc hd hsum
    have himage {x : α} (hx : x ∈ S) : f x ∈ T := by
      rw [← hST]
      exact Finset.mem_image_of_mem f hx
    have h := hSidon (himage ha) (himage hb) (himage hc) (himage hd)
      (hfreiman a (hSA ha) b (hSA hb) c (hSA hc) d (hSA hd) hsum)
    rcases h with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact Or.inl ⟨hinj (hSA ha) (hSA hc) hac, hinj (hSA hb) (hSA hd) hbd⟩
    · exact Or.inr ⟨hinj (hSA ha) (hSA hd) had, hinj (hSA hb) (hSA hc) hbc⟩
  · rw [← hST, Finset.card_image_of_injOn (hinj.mono hSA)]

/-- The exact attainable Sidon cardinalities of A can be represented by an integer set. -/
theorem exists_integer_sidon_model (A : Finset ℝ) :
    ∃ B : Finset ℤ, B.card = A.card ∧ ∀ k : ℕ,
      (∃ S : Finset ℝ, S ⊆ A ∧ IsSidon S ∧ S.card = k) ↔
      (∃ T : Finset ℤ, T ⊆ B ∧ IsSidon T ∧ T.card = k) := by
  classical
  obtain ⟨f, hinj, hfreiman⟩ := exists_integer_freiman_model A
  refine ⟨A.image f, Finset.card_image_of_injOn hinj, ?_⟩
  intro k
  constructor
  · rintro ⟨S, hSA, hSidon, hcard⟩
    refine ⟨S.image f, Finset.image_subset_image hSA, ?_, ?_⟩
    · intro a b c d ha hb hc hd hsum
      obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨c, hcS, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨d, hdS, rfl⟩ := Finset.mem_image.mp hd
      have h := hSidon haS hbS hcS hdS
        ((hfreiman a (hSA haS) b (hSA hbS) c (hSA hcS) d (hSA hdS)).mp hsum)
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rw [Finset.card_image_of_injOn (hinj.mono hSA), hcard]
  · rintro ⟨T, hTA, hSidon, hcard⟩
    obtain ⟨S, hSA, hS, hST⟩ := pullback_sidon A f hinj
      (fun a ha b hb c hc d hd => (hfreiman a ha b hb c hc d hd).mpr) T hTA hSidon
    exact ⟨S, hSA, hS, hST.trans hcard⟩

end P184Transfer

end Original4
-- END original 04

-- BEGIN original 05: p184/CyclicTemplate.lean
section Original5

/-!
# Ruzsa's strong cyclic Sidon template

The construction is the graph of an isomorphism from the additive cyclic group
`ZMod (p - 1)` to the multiplicative group of nonzero elements of `ZMod p`,
transported by the Chinese remainder equivalence. The sum/product argument
includes repeated summands and does not divide by two.

Mathematical source: I. Z. Ruzsa, "Solving a linear equation in a set of integers I",
Acta Arithmetica 65 (1993), Theorem 4.4, pp. 267-268. The local source and API
audit is recorded in `p184/cyclic-template-assembly.md`.
-/

namespace Submissions.P184Cyclic

private theorem first_eq_of_sum_prod {F : Type*} [Field F]
    {a b c d : F} (hs : a + b = c + d) (hm : a * b = c * d) :
    a = c ∨ a = d := by
  have hz : (a - c) * (a - d) = 0 := by
    calc
      (a - c) * (a - d) = a * (a + b - c - d) + (c * d - a * b) := by ring
      _ = 0 := by
        rw [hs, hm]
        ring
  exact (mul_eq_zero.mp hz).imp sub_eq_zero.mp sub_eq_zero.mp

/-- Ruzsa's `p - 1` element cyclic template, with all repeated-summand cases. -/
theorem exists_ruzsa_cyclic_template (p : ℕ) (hp : p.Prime) :
    ∃ D : Finset (ZMod ((p - 1) * p)), D.card = p - 1 ∧
      ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p - 1) := ⟨ne_of_gt (Nat.sub_pos_of_lt hp.one_lt)⟩
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, ZMod.card]
  let e : Multiplicative (ZMod (p - 1)) ≃* (ZMod p)ˣ := by
    rw [← hcard]
    exact zmodCyclicMulEquiv (G := (ZMod p)ˣ) inferInstance
  let u : ZMod (p - 1) → ZMod p := fun i => (e (Multiplicative.ofAdd i) : ZMod p)
  have hu_inj : Function.Injective u := by
    intro i j h
    apply Multiplicative.ofAdd.injective
    apply e.injective
    apply Units.val_injective
    exact h
  have hu_add (i j : ZMod (p - 1)) : u (i + j) = u i * u j := by
    simp only [u, ofAdd_add, map_mul, Units.val_mul]
  have hcoprime : (p - 1).Coprime p := by
    exact (Nat.coprime_self_sub_left (Nat.le_of_lt hp.one_lt)).2 (by simp)
  let crt : ZMod ((p - 1) * p) ≃+* ZMod (p - 1) × ZMod p :=
    ZMod.chineseRemainder hcoprime
  let f : ZMod (p - 1) → ZMod ((p - 1) * p) := fun i => crt.symm (i, u i)
  have hcrt (i : ZMod (p - 1)) : crt (f i) = (i, u i) := by
    simp only [f, RingEquiv.apply_symm_apply]
  have hf_inj : Function.Injective f := by
    intro i j h
    have h' := congrArg (fun z => (crt z).1) h
    simpa only [hcrt] using h'
  have hf_sidon (i j k l : ZMod (p - 1))
      (h : f i + f j = f k + f l) :
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    have hpair : (i, u i) + (j, u j) = (k, u k) + (l, u l) := by
      simpa only [map_add, hcrt] using congrArg crt h
    have hi : i + j = k + l := congrArg Prod.fst hpair
    have hs : u i + u j = u k + u l := congrArg Prod.snd hpair
    have hm : u i * u j = u k * u l := by
      rw [← hu_add, ← hu_add, hi]
    rcases first_eq_of_sum_prod hs hm with hval | hval
    · have hik : i = k := hu_inj hval
      have hjl : j = l := by
        rw [hik] at hi
        exact add_left_cancel hi
      exact Or.inl ⟨hik, hjl⟩
    · have hil : i = l := hu_inj hval
      have hjk : j = k := by
        rw [hil, add_comm l j] at hi
        exact add_right_cancel hi
      exact Or.inr ⟨hil, hjk⟩
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, ZMod.card]
  · intro a ha b hb c hc d hd hsum
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hd
    rcases hf_sidon i j k l hsum with h | h
    · exact Or.inl ⟨congrArg f h.1, congrArg f h.2⟩
    · exact Or.inr ⟨congrArg f h.1, congrArg f h.2⟩

end Submissions.P184Cyclic
end Original5
-- END original 05

-- BEGIN original 06: p184/CyclicExtraction.lean
section Original6

namespace Submissions.P184Cyclic

open scoped BigOperators
open Submissions.Erdos530IntegerFreimanCompression.Main

/-- A strong cyclic Sidon template extracts an integer Sidon subset from the
checked finite compression. The template is an explicit hypothesis. -/
theorem exists_integer_cyclic_extraction (A : Finset ℤ) (m : ℕ) (hm : 0 < m)
    (D : Finset (ZMod m)) (hD : P184Transfer.IsSidon D) :
    ∃ S : Finset ℤ, S ⊆ A ∧ P184Transfer.IsSidon S ∧
      (D.card : ℤ) * (4 * (m : ℤ) * A.card - (A.card : ℤ) * ((A.card : ℤ) - 1)) ≤
        8 * (m : ℤ) ^ 2 * S.card := by
  classical
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨C, hCA, f, hinj, hfreiman, hsize⟩ :=
    exists_integer_freiman_compression A m hm
  let B : ZMod m → Finset ℤ := fun t => C.filter fun a => f a + t ∈ D
  have htotal : (∑ t : ZMod m, (B t).card) = C.card * D.card := by
    have h := sum_retained_of_uniform_fibers
      (Finset.univ : Finset (ZMod m)) C D (fun t a => f a + t) 1 (by
        intro a ha r hr
        have hset : ((Finset.univ : Finset (ZMod m)).filter
            fun t => f a + t = r) = {r - f a} := by
          ext t
          simp [eq_sub_iff_add_eq, add_comm]
        rw [hset, Finset.card_singleton])
    simpa only [B, mul_one] using h
  have havg : ∃ t ∈ (Finset.univ : Finset (ZMod m)),
      C.card * D.card ≤ m * (B t).card := by
    apply Finset.exists_le_of_sum_le Finset.univ_nonempty
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card,
      ← Finset.mul_sum, htotal, Nat.cast_id, le_refl]
  obtain ⟨t, ht, hlarge⟩ := havg
  refine ⟨B t, ?_, ?_, ?_⟩
  · intro a ha
    exact hCA (Finset.mem_filter.mp ha).1
  · intro a b c d ha hb hc hd hsum
    have haC := (Finset.mem_filter.mp ha).1
    have hbC := (Finset.mem_filter.mp hb).1
    have hcC := (Finset.mem_filter.mp hc).1
    have hdC := (Finset.mem_filter.mp hd).1
    have hmapped : (f a + t) + (f b + t) = (f c + t) + (f d + t) := by
      calc
        _ = (f a + f b) + (t + t) := by ring
        _ = (f c + f d) + (t + t) := by rw [hfreiman a haC b hbC c hcC d hdC hsum]
        _ = _ := by ring
    rcases hD (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hd).2 hmapped with
      ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact Or.inl ⟨hinj haC hcC (add_right_cancel hac), hinj hbC hdC (add_right_cancel hbd)⟩
    · exact Or.inr ⟨hinj haC hdC (add_right_cancel had), hinj hbC hcC (add_right_cancel hbc)⟩
  · have hlargeZ : (C.card : ℤ) * D.card ≤ (m : ℤ) * (B t).card := by
      exact_mod_cast hlarge
    have hmZ : 0 ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
    have hDZ : 0 ≤ (D.card : ℤ) := by exact_mod_cast Nat.zero_le D.card
    calc
      _ ≤ (D.card : ℤ) * (8 * (m : ℤ) * C.card) :=
        mul_le_mul_of_nonneg_left hsize hDZ
      _ = (8 * (m : ℤ)) * ((C.card : ℤ) * D.card) := by ring
      _ ≤ (8 * (m : ℤ)) * ((m : ℤ) * (B t).card) :=
        mul_le_mul_of_nonneg_left hlargeZ (mul_nonneg (by norm_num) hmZ)
      _ = _ := by ring

/-- The same exact finite bound holds for real sets, using the already checked
lossless real-to-integer Sidon model. Empty sets and repeated summands are included. -/
theorem exists_real_cyclic_extraction (A : Finset ℝ) (m : ℕ) (hm : 0 < m)
    (D : Finset (ZMod m)) (hD : P184Transfer.IsSidon D) :
    ∃ S : Finset ℝ, S ⊆ A ∧ P184Transfer.IsSidon S ∧
      (D.card : ℤ) * (4 * (m : ℤ) * A.card - (A.card : ℤ) * ((A.card : ℤ) - 1)) ≤
        8 * (m : ℤ) ^ 2 * S.card := by
  obtain ⟨B, hcard, hmodel⟩ := P184Transfer.exists_integer_sidon_model A
  obtain ⟨T, hTB, hT, hbound⟩ := exists_integer_cyclic_extraction B m hm D hD
  obtain ⟨S, hSA, hS, hST⟩ := (hmodel T.card).mpr ⟨T, hTB, hT, rfl⟩
  refine ⟨S, hSA, hS, ?_⟩
  simpa only [hcard, hST] using hbound

end Submissions.P184Cyclic

end Original6
-- END original 06

-- BEGIN original 07: p184/CyclicLower.lean
section Original7

namespace Submissions.P184Cyclic

/-- The exact finite real Sidon bound obtained from Ruzsa's template at a prime.
All subtraction in the bound is integer subtraction, including `p - 1`. -/
theorem exists_real_prime_sidon_bound (A : Finset ℝ) (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset ℝ, S ⊆ A ∧ P184Transfer.IsSidon S ∧
      4 * (p : ℤ) * ((p : ℤ) - 1) * A.card -
          (A.card : ℤ) * ((A.card : ℤ) - 1) ≤
        8 * (p : ℤ) ^ 2 * ((p : ℤ) - 1) * S.card := by
  obtain ⟨D, hcard, hD⟩ := exists_ruzsa_cyclic_template p hp
  have hm : 0 < (p - 1) * p :=
    Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) hp.pos
  have hsidon : P184Transfer.IsSidon D := by
    intro a b c d ha hb hc hd hsum
    exact hD a ha b hb c hc d hd hsum
  obtain ⟨S, hSA, hS, hbound⟩ :=
    exists_real_cyclic_extraction A ((p - 1) * p) hm D hsidon
  refine ⟨S, hSA, hS, ?_⟩
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    simp only [Nat.cast_sub (Nat.le_of_lt hp.one_lt), Nat.cast_one]
  simp only [hcard, Nat.cast_mul, hcast] at hbound
  have hpZ : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  refine le_of_mul_le_mul_left (a := (p : ℤ) - 1) ?_ (sub_pos.mpr hpZ)
  calc
    _ = ((p : ℤ) - 1) *
        (4 * (((p : ℤ) - 1) * p) * A.card -
          (A.card : ℤ) * ((A.card : ℤ) - 1)) := by ring
    _ ≤ 8 * (((p : ℤ) - 1) * p) ^ 2 * S.card := hbound
    _ = _ := by ring

end Submissions.P184Cyclic

end Original7
-- END original 07

/-- Exact saved finite theorem, with the Sidon predicate expanded definitionally. -/
theorem proof (A : Finset ℝ) (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset ℝ, S ⊆ A ∧
      (∀ ⦃a b c d : ℝ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      4 * (p : ℤ) * ((p : ℤ) - 1) * A.card -
          (A.card : ℤ) * ((A.card : ℤ) - 1) ≤
        8 * (p : ℤ) ^ 2 * ((p : ℤ) - 1) * S.card :=
  Submissions.P184Cyclic.exists_real_prime_sidon_bound A p hp

end Submissions.J5P184CyclicPrimeBound.Proof
