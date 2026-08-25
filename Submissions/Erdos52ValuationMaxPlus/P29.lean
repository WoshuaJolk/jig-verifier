import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic

open scoped Pointwise

namespace Submissions.Erdos52ValuationMaxPlus.P29

private def scale (c : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => c * x

private theorem scale_card {c : ℕ} (hc : 0 < c) (S : Finset ℕ) :
    (scale c S).card = S.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact Nat.eq_of_mul_eq_mul_left hc hab

private theorem prime_free_mul
    {q : ℕ} (hq : q.Prime) {S T : Finset ℕ}
    (hS : ∀ x ∈ S, ¬q ∣ x) (hT : ∀ x ∈ T, ¬q ∣ x) :
    ∀ z ∈ S * T, ¬q ∣ z := by
  intro z hz
  simp only [Finset.mem_mul] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact fun h => (hq.dvd_mul.mp h).elim (hS x hx) (hT y hy)

private theorem pow_pos_nat {q : ℕ} (hq : 0 < q) (n : ℕ) : 0 < q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact Nat.mul_pos ih hq

private theorem q_dvd_pow {q d : ℕ} (hd : 0 < d) : q ∣ q ^ d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact ⟨q ^ e, by simp [pow_succ, Nat.mul_comm]⟩

private theorem scaled_disjoint
    {q k l : ℕ} (hq : q.Prime) (hkl : k ≠ l)
    {S T : Finset ℕ}
    (hS : ∀ x ∈ S, ¬q ∣ x) (hT : ∀ x ∈ T, ¬q ∣ x) :
    Disjoint (scale (q ^ k) S) (scale (q ^ l) T) := by
  simp only [Finset.disjoint_left]
  intro z hzk hzl
  simp only [scale, Finset.mem_image] at hzk hzl
  obtain ⟨x, hx, rfl⟩ := hzk
  obtain ⟨y, hy, heq⟩ := hzl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hpow :
        q ^ l = q ^ k * q ^ (l - k) := by
      rw [← pow_add]
      congr
      omega
    have hcancel : x = q ^ (l - k) * y := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos_nat hq.pos k)
      calc
        q ^ k * x = q ^ l * y := heq.symm
        _ = q ^ k * (q ^ (l - k) * y) := by rw [hpow, Nat.mul_assoc]
    have hdvd : q ∣ q ^ (l - k) * y :=
      dvd_mul_of_dvd_left (q_dvd_pow (by omega)) y
    exact hS x hx (hcancel ▸ hdvd)
  · have hpow :
        q ^ k = q ^ l * q ^ (k - l) := by
      rw [← pow_add]
      congr
      omega
    have hcancel : y = q ^ (k - l) * x := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos_nat hq.pos l)
      calc
        q ^ l * y = q ^ k * x := heq
        _ = q ^ l * (q ^ (k - l) * x) := by rw [hpow, Nat.mul_assoc]
    have hdvd : q ∣ q ^ (k - l) * x :=
      dvd_mul_of_dvd_left (q_dvd_pow (by omega)) x
    exact hT y hy (hcancel ▸ hdvd)

private def indices (m : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range m ×ˢ Finset.range m

private def totals (m : ℕ) : Finset ℕ :=
  (indices m).image fun p => p.1 + p.2

private def fiber (q m : ℕ) (L : ℕ → Finset ℕ) (k : ℕ) : Finset ℕ :=
  ((indices m).filter fun p => p.1 + p.2 = k).biUnion fun p =>
    scale (q ^ k) (L p.1 * L p.2)

private def profile (m : ℕ) (L : ℕ → Finset ℕ) (k : ℕ) : ℕ :=
  ((indices m).filter fun p => p.1 + p.2 = k).sup fun p =>
    (L p.1 * L p.2).card

private def layeredSet (q m : ℕ) (L : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range m).biUnion fun i => scale (q ^ i) (L i)

/--
Arbitrary `q`-valuation layers decompose the product set exactly by total
valuation.  Distinct totals are disjoint, so the product set dominates the
sum of the max-plus convolution of the layer product cardinalities.
-/
theorem proof :
    ∀ (q m : ℕ) (L : ℕ → Finset ℕ), q.Prime →
      (∀ i < m, ∀ x ∈ L i, ¬q ∣ x) →
      let A := layeredSet q m L
      let K := totals m
      let F := fiber q m L
      A * A = K.biUnion F ∧
        ∑ k ∈ K, profile m L k ≤ (A * A).card := by
  classical
  intro q m L hq hfree
  dsimp only
  let A := layeredSet q m L
  let K := totals m
  let F := fiber q m L
  have hcomponent_free (i j : ℕ) (hi : i < m) (hj : j < m) :
      ∀ z ∈ L i * L j, ¬q ∣ z :=
    prime_free_mul hq (hfree i hi) (hfree j hj)
  have hFdisj : (K : Set ℕ).PairwiseDisjoint F := by
    intro k hk l hl hkl
    simp only [F, fiber, Finset.disjoint_left]
    intro z hzk hzl
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hzk hzl
    obtain ⟨ij, ⟨hij, hijsum⟩, hzij⟩ := hzk
    obtain ⟨rs, ⟨hrs, hrssum⟩, hzrs⟩ := hzl
    have hij' : ij.1 < m ∧ ij.2 < m := by simpa [indices] using hij
    have hrs' : rs.1 < m ∧ rs.2 < m := by simpa [indices] using hrs
    exact Finset.disjoint_left.mp
      (scaled_disjoint hq hkl
        (hcomponent_free ij.1 ij.2 hij'.1 hij'.2)
        (hcomponent_free rs.1 rs.2 hrs'.1 hrs'.2)) hzij hzrs
  have hdecomp : A * A = K.biUnion F := by
    ext z
    simp only [A, layeredSet, Finset.mem_mul, Finset.mem_biUnion,
      Finset.mem_range, scale, Finset.mem_image, K, totals, F, fiber,
      Finset.mem_filter, indices, Finset.mem_product]
    constructor
    · rintro ⟨x, ⟨i, hi, a, ha, rfl⟩,
        y, ⟨j, hj, b, hb, rfl⟩, rfl⟩
      refine ⟨i + j, ⟨(i, j), ⟨hi, hj⟩, rfl⟩,
        (i, j), ⟨⟨hi, hj⟩, rfl⟩, ?_⟩
      refine ⟨a * b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
      simp [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · rintro ⟨k, ⟨ij, ⟨hi, hj⟩, hijk⟩, rs, ⟨⟨hr, hs⟩, hrsk⟩,
        ab, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      refine ⟨q ^ rs.1 * a, ⟨rs.1, hr, a, ha, rfl⟩,
        q ^ rs.2 * b, ⟨rs.2, hs, b, hb, rfl⟩, ?_⟩
      simp [← hrsk, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hprofile (k : ℕ) (hk : k ∈ K) :
      profile m L k ≤ (F k).card := by
    apply Finset.sup_le
    intro ij hij
    have hij' := hij
    simp only [Finset.mem_filter] at hij'
    have hijmem : ij.1 < m ∧ ij.2 < m := by
      simpa [indices] using hij'.1
    have hsubset :
        scale (q ^ k) (L ij.1 * L ij.2) ⊆ F k := by
      intro z hz
      simp only [F, fiber, Finset.mem_biUnion]
      exact ⟨ij, hij, hz⟩
    calc
      (L ij.1 * L ij.2).card =
          (scale (q ^ k) (L ij.1 * L ij.2)).card :=
        (scale_card (pow_pos_nat hq.pos k) _).symm
      _ ≤ (F k).card := Finset.card_le_card hsubset
  constructor
  · exact hdecomp
  · rw [hdecomp, Finset.card_biUnion hFdisj]
    exact Finset.sum_le_sum hprofile

end Submissions.Erdos52ValuationMaxPlus.P29
