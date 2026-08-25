import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic

open scoped Pointwise

namespace Submissions.Erdos52CrossLayerAdditive.P29

private def scale (c : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => c * x

private def layeredSet (q m : ℕ) (L : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range m).biUnion fun i => scale (q ^ i) (L i)

private def orderedLayers (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m ×ˢ Finset.range m).filter fun p => p.1 < p.2

private theorem pow_pos_nat {q : ℕ} (hq : 0 < q) (n : ℕ) : 0 < q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact Nat.mul_pos ih hq

private theorem q_dvd_pow {q d : ℕ} (hd : 0 < d) : q ∣ q ^ d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact ⟨q ^ e, by simp [pow_succ, Nat.mul_comm]⟩

private theorem valuation_unique
    {q i j u v : ℕ} (hq : q.Prime)
    (hu : ¬q ∣ u) (hv : ¬q ∣ v)
    (heq : q ^ i * u = q ^ j * v) :
    i = j ∧ u = v := by
  by_cases hij : i = j
  · subst j
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos_nat hq.pos i) heq⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hpow : q ^ j = q ^ i * q ^ (j - i) := by
      rw [← pow_add]
      congr
      omega
    have huv : u = q ^ (j - i) * v := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos_nat hq.pos i)
      calc
        q ^ i * u = q ^ j * v := heq
        _ = q ^ i * (q ^ (j - i) * v) := by rw [hpow, Nat.mul_assoc]
    have hdvd : q ∣ q ^ (j - i) * v :=
      dvd_mul_of_dvd_left (q_dvd_pow (by omega)) v
    exact False.elim (hu (huv ▸ hdvd))
  · have hpow : q ^ i = q ^ j * q ^ (i - j) := by
      rw [← pow_add]
      congr
      omega
    have hvu : v = q ^ (i - j) * u := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos_nat hq.pos j)
      calc
        q ^ j * v = q ^ i * u := heq.symm
        _ = q ^ j * (q ^ (i - j) * u) := by rw [hpow, Nat.mul_assoc]
    have hdvd : q ∣ q ^ (i - j) * u :=
      dvd_mul_of_dvd_left (q_dvd_pow (by omega)) u
    exact False.elim (hv (hvu ▸ hdvd))

private theorem inner_free
    {q i j x y : ℕ} (hx : ¬q ∣ x) (hij : i < j) :
    ¬q ∣ x + q ^ (j - i) * y := by
  have hdvd : q ∣ q ^ (j - i) * y :=
    dvd_mul_of_dvd_left (q_dvd_pow (by omega)) y
  intro hsum
  exact hx ((Nat.dvd_add_iff_left hdvd).mpr hsum)

/--
Choosing one anchor in every nonempty `q`-free valuation layer gives an
injective family of cross-layer sums.  Its cardinality is the weighted sum
`∑_{i<j} |L_j|`.
-/
theorem proof :
    ∀ (q m : ℕ) (L : ℕ → Finset ℕ) (x : ℕ → ℕ), q.Prime →
      (∀ i < m, ∀ y ∈ L i, ¬q ∣ y) →
      (∀ i < m, x i ∈ L i) →
      let A := layeredSet q m L
      ∑ p ∈ orderedLayers m, (L p.2).card ≤ (A + A).card := by
  classical
  intro q m L x hq hfree hanchor
  dsimp only
  let I := orderedLayers m
  let D := I.sigma fun p => L p.2
  let f : ((p : ℕ × ℕ) × ℕ) → ℕ := fun t =>
    q ^ t.1.1 * x t.1.1 + q ^ t.1.2 * t.2
  have hinj : Set.InjOn f D := by
    intro a ha b hb hab
    have ha' : a.1 ∈ I ∧ a.2 ∈ L a.1.2 := Finset.mem_sigma.mp ha
    have hb' : b.1 ∈ I ∧ b.2 ∈ L b.1.2 := Finset.mem_sigma.mp hb
    have haidx' :
        (a.1.1 < m ∧ a.1.2 < m) ∧ a.1.1 < a.1.2 := by
      simpa [I, orderedLayers] using ha'.1
    have hbidx' :
        (b.1.1 < m ∧ b.1.2 < m) ∧ b.1.1 < b.1.2 := by
      simpa [I, orderedLayers] using hb'.1
    have haidx : a.1.1 < m ∧ a.1.2 < m ∧ a.1.1 < a.1.2 :=
      ⟨haidx'.1.1, haidx'.1.2, haidx'.2⟩
    have hbidx : b.1.1 < m ∧ b.1.2 < m ∧ b.1.1 < b.1.2 :=
      ⟨hbidx'.1.1, hbidx'.1.2, hbidx'.2⟩
    have hafactor :
        f a = q ^ a.1.1 *
          (x a.1.1 + q ^ (a.1.2 - a.1.1) * a.2) := by
      dsimp only [f]
      rw [Nat.mul_add]
      congr 1
      calc
        q ^ a.1.2 * a.2 =
            (q ^ a.1.1 * q ^ (a.1.2 - a.1.1)) * a.2 := by
          congr 1
          rw [← pow_add]
          congr
          omega
        _ = q ^ a.1.1 * (q ^ (a.1.2 - a.1.1) * a.2) :=
          Nat.mul_assoc _ _ _
    have hbfactor :
        f b = q ^ b.1.1 *
          (x b.1.1 + q ^ (b.1.2 - b.1.1) * b.2) := by
      dsimp only [f]
      rw [Nat.mul_add]
      congr 1
      calc
        q ^ b.1.2 * b.2 =
            (q ^ b.1.1 * q ^ (b.1.2 - b.1.1)) * b.2 := by
          congr 1
          rw [← pow_add]
          congr
          omega
        _ = q ^ b.1.1 * (q ^ (b.1.2 - b.1.1) * b.2) :=
          Nat.mul_assoc _ _ _
    have houter := valuation_unique hq
      (inner_free (hfree a.1.1 haidx.1 (x a.1.1)
        (hanchor a.1.1 haidx.1)) haidx.2.2)
      (inner_free (hfree b.1.1 hbidx.1 (x b.1.1)
        (hanchor b.1.1 hbidx.1)) hbidx.2.2)
      (hafactor ▸ hbfactor ▸ hab)
    have hi : a.1.1 = b.1.1 := houter.1
    have hinner : q ^ (a.1.2 - a.1.1) * a.2 =
        q ^ (b.1.2 - b.1.1) * b.2 := by
      have h := houter.2
      rw [hi] at h
      have hh := Nat.add_left_cancel h
      simpa [hi] using hh
    have hsecond := valuation_unique hq
      (hfree a.1.2 haidx.2.1 a.2 ha'.2)
      (hfree b.1.2 hbidx.2.1 b.2 hb'.2) hinner
    have hj : a.1.2 = b.1.2 := by omega
    apply Sigma.ext
    · exact Prod.ext hi hj
    · exact heq_of_eq hsecond.2
  have hcardD :
      D.card = ∑ p ∈ orderedLayers m, (L p.2).card := by
    simp [D, I, Finset.card_sigma]
  have hsubset :
      D.image f ⊆ layeredSet q m L + layeredSet q m L := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have ht' : t.1 ∈ I ∧ t.2 ∈ L t.1.2 := Finset.mem_sigma.mp ht
    have hidx' :
        (t.1.1 < m ∧ t.1.2 < m) ∧ t.1.1 < t.1.2 := by
      simpa [I, orderedLayers] using ht'.1
    have hidx : t.1.1 < m ∧ t.1.2 < m ∧ t.1.1 < t.1.2 :=
      ⟨hidx'.1.1, hidx'.1.2, hidx'.2⟩
    apply Finset.add_mem_add
    · simp only [layeredSet, Finset.mem_biUnion]
      refine ⟨t.1.1, Finset.mem_range.mpr hidx.1, ?_⟩
      simp only [scale, Finset.mem_image]
      exact ⟨x t.1.1, hanchor t.1.1 hidx.1, rfl⟩
    · simp only [layeredSet, Finset.mem_biUnion]
      refine ⟨t.1.2, Finset.mem_range.mpr hidx.2.1, ?_⟩
      simp only [scale, Finset.mem_image]
      exact ⟨t.2, ht'.2, rfl⟩
  calc
    ∑ p ∈ orderedLayers m, (L p.2).card = D.card := hcardD.symm
    _ = (D.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (layeredSet q m L + layeredSet q m L).card :=
      Finset.card_le_card hsubset

end Submissions.Erdos52CrossLayerAdditive.P29
