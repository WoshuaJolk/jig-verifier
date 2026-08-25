import Mathlib

namespace Submissions.Erdos14UniformStability.Direct

open scoped BigOperators

set_option maxHeartbeats 800000

noncomputable def initialSegment (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 M).filter fun a => a ∈ A

noncomputable def upperBlock (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (M + 1) (2 * M)).filter fun a => a ∈ A

noncomputable def crossPairs (A : Set ℕ) (M : ℕ) : Finset (ℕ × ℕ) := by
  classical
  let B := initialSegment A M
  let C := upperBlock A M
  exact (B ×ˢ C) ∪ (C ×ˢ B)

noncomputable def crossRepCount (A : Set ℕ) (M n : ℕ) : ℕ := by
  classical
  exact ((crossPairs A M).filter fun p => p.1 + p.2 = n).card

noncomputable def crossEnergy (A : Set ℕ) (M : ℕ) : ℕ := by
  classical
  exact ∑ n ∈ Finset.Icc (M + 1) (3 * M), (crossRepCount A M n) ^ 2

def uniformCross (A : Set ℕ) (M : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc (M + 1) (3 * M),
    ∀ j ∈ Finset.Icc (M + 1) (3 * M),
      crossRepCount A M i = crossRepCount A M j

lemma blocks_disjoint (A : Set ℕ) (M : ℕ) :
    Disjoint (initialSegment A M) (upperBlock A M) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [initialSegment, upperBlock, Finset.mem_filter, Finset.mem_Icc] at ha hb
  omega

lemma crossPairs_card (A : Set ℕ) (M : ℕ) :
    (crossPairs A M).card =
      2 * (initialSegment A M).card * (upperBlock A M).card := by
  classical
  let B := initialSegment A M
  let C := upperBlock A M
  have hBC : Disjoint B C := blocks_disjoint A M
  have hprod : Disjoint (B ×ˢ C) (C ×ˢ B) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_product] at hp hq
    exact (Finset.disjoint_left.mp hBC hp.1 hq.1).elim
  unfold crossPairs
  dsimp only
  rw [Finset.card_union_of_disjoint hprod]
  simp only [Finset.card_product]
  ring

lemma crossPairs_sum_mem (A : Set ℕ) (M : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ crossPairs A M) :
    p.1 + p.2 ∈ Finset.Icc (M + 1) (3 * M) := by
  classical
  simp only [crossPairs, Finset.mem_union, Finset.mem_product] at hp
  simp only [Finset.mem_Icc]
  rcases hp with hp | hp
  · have hp₁ := hp.1
    have hp₂ := hp.2
    simp only [initialSegment, upperBlock, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
    omega
  · have hp₁ := hp.1
    have hp₂ := hp.2
    simp only [initialSegment, upperBlock, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
    omega

lemma cross_mass (A : Set ℕ) (M : ℕ) :
    ∑ n ∈ Finset.Icc (M + 1) (3 * M), crossRepCount A M n =
      2 * (initialSegment A M).card * (upperBlock A M).card := by
  classical
  let T := Finset.Icc (M + 1) (3 * M)
  have hmap : (crossPairs A M : Set (ℕ × ℕ)).MapsTo
      (fun p => p.1 + p.2) T := by
    intro p hp
    exact crossPairs_sum_mem A M hp
  rw [← crossPairs_card A M]
  simpa [crossRepCount, T] using (Finset.card_eq_sum_card_fiberwise hmap).symm

lemma cauchy_eq_iff_constant {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℕ) :
    s.card * (∑ i ∈ s, f i ^ 2) = (∑ i ∈ s, f i) ^ 2 ↔
      ∀ i ∈ s, ∀ j ∈ s, f i = f j := by
  constructor
  · intro heq i hi j hj
    have hi_mean : s.card * f i = ∑ x ∈ s, f x := by
      let t := s.erase i
      have hcard : t.card + 1 = s.card := Finset.card_erase_add_one hi
      have hsum : (∑ x ∈ t, f x) + f i = ∑ x ∈ s, f x :=
        Finset.sum_erase_add s f hi
      have hsq : (∑ x ∈ t, f x ^ 2) + f i ^ 2 = ∑ x ∈ s, f x ^ 2 :=
        Finset.sum_erase_add s (fun x => f x ^ 2) hi
      have hc := sq_sum_le_card_mul_sum_sq (s := t) (f := f)
      have hdiff :
          2 * f i * (∑ x ∈ t, f x) ≤
            (∑ x ∈ t, f x ^ 2) + t.card * f i ^ 2 := by
        calc
          2 * f i * (∑ x ∈ t, f x) =
              ∑ x ∈ t, 2 * f i * f x := by
                simp only [Finset.mul_sum]
          _ ≤ ∑ x ∈ t, (f i ^ 2 + f x ^ 2) := by
                apply Finset.sum_le_sum
                intro x hx
                exact two_mul_le_add_sq (f i) (f x)
          _ = (∑ x ∈ t, f x ^ 2) + t.card * f i ^ 2 := by
                simp [Finset.sum_add_distrib]
                ring
      have heqZ :
          (s.card : ℤ) * (∑ x ∈ s, f x ^ 2 : ℕ) =
            (∑ x ∈ s, f x : ℕ) ^ 2 := by exact_mod_cast heq
      have hcardZ : (t.card : ℤ) + 1 = s.card := by exact_mod_cast hcard
      have hsumZ :
          (∑ x ∈ t, f x : ℕ) + (f i : ℤ) = ∑ x ∈ s, f x := by
        exact_mod_cast hsum
      have hsqZ :
          (∑ x ∈ t, f x ^ 2 : ℕ) + ((f i : ℤ) ^ 2) =
            ∑ x ∈ s, f x ^ 2 := by exact_mod_cast hsq
      have hcZ :
          ((∑ x ∈ t, f x : ℕ) : ℤ) ^ 2 ≤
            (t.card : ℤ) * (∑ x ∈ t, f x ^ 2 : ℕ) := by exact_mod_cast hc
      have hdiffZ :
          2 * (f i : ℤ) * (∑ x ∈ t, f x : ℕ) ≤
            (∑ x ∈ t, f x ^ 2 : ℕ) + (t.card : ℤ) * (f i : ℤ) ^ 2 := by
        exact_mod_cast hdiff
      have hmeanZ :
          (s.card : ℤ) * f i = ∑ x ∈ s, f x := by
        let u : ℤ := ((∑ x ∈ t, f x : ℕ) : ℤ)
        let v : ℤ := ((∑ x ∈ t, f x ^ 2 : ℕ) : ℤ)
        let x : ℤ := f i
        let q : ℤ := t.card
        change q + 1 = (s.card : ℤ) at hcardZ
        change u + x = ((∑ x ∈ s, f x : ℕ) : ℤ) at hsumZ
        change v + x ^ 2 = ((∑ x ∈ s, f x ^ 2 : ℕ) : ℤ) at hsqZ
        change u ^ 2 ≤ q * v at hcZ
        change 2 * x * u ≤ v + q * x ^ 2 at hdiffZ
        have hg₁ : 0 ≤ q * v - u ^ 2 := by
          nlinarith
        have hg₂ : 0 ≤ v + q * x ^ 2 - 2 * x * u := by
          nlinarith
        have hmaster : (q + 1) * (v + x ^ 2) - (u + x) ^ 2 = 0 := by
          rw [hcardZ, hsumZ, hsqZ, heqZ]
          ring
        have htotal : (q * v - u ^ 2) + (v + q * x ^ 2 - 2 * x * u) = 0 := by
          calc
            (q * v - u ^ 2) + (v + q * x ^ 2 - 2 * x * u) =
                (q + 1) * (v + x ^ 2) - (u + x) ^ 2 := by ring
            _ = 0 := hmaster
        have hg₁z : q * v - u ^ 2 = 0 := by nlinarith
        have hg₂z : v + q * x ^ 2 - 2 * x * u = 0 := by nlinarith
        have hsquare : (q * x - u) ^ 2 = 0 := by
          calc
            (q * x - u) ^ 2 =
                q * (v + q * x ^ 2 - 2 * x * u) - (q * v - u ^ 2) := by ring
            _ = 0 := by rw [hg₁z, hg₂z]; ring
        have hqu : q * x = u := by
          exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
        calc
          (s.card : ℤ) * f i = (q + 1) * x := by
            rw [hcardZ]
          _ = q * x + x := by ring
          _ = u + x := by rw [hqu]
          _ = ∑ x ∈ s, f x := hsumZ
      exact_mod_cast hmeanZ
    have hj_mean : s.card * f j = ∑ x ∈ s, f x := by
      let t := s.erase j
      have hcard : t.card + 1 = s.card := Finset.card_erase_add_one hj
      have hsum : (∑ x ∈ t, f x) + f j = ∑ x ∈ s, f x :=
        Finset.sum_erase_add s f hj
      have hsq : (∑ x ∈ t, f x ^ 2) + f j ^ 2 = ∑ x ∈ s, f x ^ 2 :=
        Finset.sum_erase_add s (fun x => f x ^ 2) hj
      have hc := sq_sum_le_card_mul_sum_sq (s := t) (f := f)
      have hdiff :
          2 * f j * (∑ x ∈ t, f x) ≤
            (∑ x ∈ t, f x ^ 2) + t.card * f j ^ 2 := by
        calc
          2 * f j * (∑ x ∈ t, f x) =
              ∑ x ∈ t, 2 * f j * f x := by
                simp only [Finset.mul_sum]
          _ ≤ ∑ x ∈ t, (f j ^ 2 + f x ^ 2) := by
                apply Finset.sum_le_sum
                intro x hx
                exact two_mul_le_add_sq (f j) (f x)
          _ = (∑ x ∈ t, f x ^ 2) + t.card * f j ^ 2 := by
                simp [Finset.sum_add_distrib]
                ring
      have heqZ :
          (s.card : ℤ) * (∑ x ∈ s, f x ^ 2 : ℕ) =
            (∑ x ∈ s, f x : ℕ) ^ 2 := by exact_mod_cast heq
      have hcardZ : (t.card : ℤ) + 1 = s.card := by exact_mod_cast hcard
      have hsumZ :
          (∑ x ∈ t, f x : ℕ) + (f j : ℤ) = ∑ x ∈ s, f x := by
        exact_mod_cast hsum
      have hsqZ :
          (∑ x ∈ t, f x ^ 2 : ℕ) + ((f j : ℤ) ^ 2) =
            ∑ x ∈ s, f x ^ 2 := by exact_mod_cast hsq
      have hcZ :
          ((∑ x ∈ t, f x : ℕ) : ℤ) ^ 2 ≤
            (t.card : ℤ) * (∑ x ∈ t, f x ^ 2 : ℕ) := by exact_mod_cast hc
      have hdiffZ :
          2 * (f j : ℤ) * (∑ x ∈ t, f x : ℕ) ≤
            (∑ x ∈ t, f x ^ 2 : ℕ) + (t.card : ℤ) * (f j : ℤ) ^ 2 := by
        exact_mod_cast hdiff
      have hmeanZ :
          (s.card : ℤ) * f j = ∑ x ∈ s, f x := by
        let u : ℤ := ((∑ x ∈ t, f x : ℕ) : ℤ)
        let v : ℤ := ((∑ x ∈ t, f x ^ 2 : ℕ) : ℤ)
        let x : ℤ := f j
        let q : ℤ := t.card
        change q + 1 = (s.card : ℤ) at hcardZ
        change u + x = ((∑ x ∈ s, f x : ℕ) : ℤ) at hsumZ
        change v + x ^ 2 = ((∑ x ∈ s, f x ^ 2 : ℕ) : ℤ) at hsqZ
        change u ^ 2 ≤ q * v at hcZ
        change 2 * x * u ≤ v + q * x ^ 2 at hdiffZ
        have hg₁ : 0 ≤ q * v - u ^ 2 := by
          nlinarith
        have hg₂ : 0 ≤ v + q * x ^ 2 - 2 * x * u := by
          nlinarith
        have hmaster : (q + 1) * (v + x ^ 2) - (u + x) ^ 2 = 0 := by
          rw [hcardZ, hsumZ, hsqZ, heqZ]
          ring
        have htotal : (q * v - u ^ 2) + (v + q * x ^ 2 - 2 * x * u) = 0 := by
          calc
            (q * v - u ^ 2) + (v + q * x ^ 2 - 2 * x * u) =
                (q + 1) * (v + x ^ 2) - (u + x) ^ 2 := by ring
            _ = 0 := hmaster
        have hg₁z : q * v - u ^ 2 = 0 := by nlinarith
        have hg₂z : v + q * x ^ 2 - 2 * x * u = 0 := by nlinarith
        have hsquare : (q * x - u) ^ 2 = 0 := by
          calc
            (q * x - u) ^ 2 =
                q * (v + q * x ^ 2 - 2 * x * u) - (q * v - u ^ 2) := by ring
            _ = 0 := by rw [hg₁z, hg₂z]; ring
        have hqu : q * x = u := by
          exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
        calc
          (s.card : ℤ) * f j = (q + 1) * x := by
            rw [hcardZ]
          _ = q * x + x := by ring
          _ = u + x := by rw [hqu]
          _ = ∑ x ∈ s, f x := hsumZ
      exact_mod_cast hmeanZ
    have hpos : 0 < s.card := Finset.card_pos.mpr hs
    apply Nat.eq_of_mul_eq_mul_left hpos
    exact hi_mean.trans hj_mean.symm
  · intro hconst
    obtain ⟨a, ha⟩ := hs
    have hval : ∀ x ∈ s, f x = f a := by
      intro x hx
      exact hconst x hx a ha
    have hsum : ∑ x ∈ s, f x = s.card * f a :=
      Finset.sum_const_nat hval
    have hsq : ∑ x ∈ s, f x ^ 2 = s.card * f a ^ 2 := by
      apply Finset.sum_const_nat
      intro x hx
      rw [hval x hx]
    rw [hsum, hsq]
    ring

theorem proof :
    ∀ (A : Set ℕ) (M : ℕ), 0 < M →
      let k := (initialSegment A M).card
      let l := (upperBlock A M).card
      let X := crossEnergy A M
      (2 * M * X = 4 * (k * l) ^ 2 ↔ uniformCross A M) ∧
      (¬ uniformCross A M → 4 * (k * l) ^ 2 + 1 ≤ 2 * M * X) := by
  intro A M hM
  classical
  let T := Finset.Icc (M + 1) (3 * M)
  let c := crossRepCount A M
  have hTcard : T.card = 2 * M := by
    simp [T]
    omega
  have hTnonempty : T.Nonempty := by
    apply Finset.card_pos.mp
    rw [hTcard]
    omega
  have hmass : ∑ n ∈ T, c n =
      2 * (initialSegment A M).card * (upperBlock A M).card := by
    simpa [T, c] using cross_mass A M
  have hcauchy := sq_sum_le_card_mul_sum_sq (s := T) (f := c)
  have heq :
      2 * M * crossEnergy A M =
          4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 ↔
        uniformCross A M := by
    have hclass := cauchy_eq_iff_constant T hTnonempty c
    rw [hTcard, hmass] at hclass
    rw [show
      (2 * (initialSegment A M).card * (upperBlock A M).card) ^ 2 =
        4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 by ring] at hclass
    simpa [crossEnergy, uniformCross, T, c] using hclass
  dsimp only
  constructor
  · exact heq
  · intro hnon
    have hbase :
        4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 ≤
          2 * M * crossEnergy A M := by
      calc
        4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 =
            (∑ n ∈ T, c n) ^ 2 := by rw [hmass]; ring
        _ ≤ T.card * ∑ n ∈ T, c n ^ 2 := hcauchy
        _ = 2 * M * crossEnergy A M := by
          rw [hTcard]
          rfl
    have hne :
        2 * M * crossEnergy A M ≠
          4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 := by
      intro h
      exact hnon (heq.mp h)
    omega

end Submissions.Erdos14UniformStability.Direct
