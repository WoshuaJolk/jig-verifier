import Mathlib

namespace Submissions.Erdos14CumulativeDefect.Direct
end Submissions.Erdos14CumulativeDefect.Direct

namespace Submissions.Erdos14ModelObstruction.Direct

open scoped BigOperators

def modelLower (M : ℕ) : Finset ℕ :=
  {0, M} ∪ Finset.Icc (M + 1) (2 * M)

def pairFiber (X Y : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ Y).filter fun p => p.1 + p.2 = n

def tilesNextInterval (M : ℕ) (D : Finset ℕ) : Prop :=
  ∀ n ∈ Finset.Icc (2 * M + 1) (6 * M),
    (pairFiber (modelLower M) D n).card = 1

lemma modelLower_card {M : ℕ} (hM : 1 ≤ M) :
    (modelLower M).card = M + 2 := by
  have hdisj : Disjoint ({0, M} : Finset ℕ) (Finset.Icc (M + 1) (2 * M)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_Icc] at hb
    rcases ha with rfl | rfl <;> omega
  rw [modelLower, Finset.card_union_of_disjoint hdisj]
  have hpair : ({0, M} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]
      omega
  have hinter : (Finset.Icc (M + 1) (2 * M)).card = M := by
    simp
    omega
  rw [hpair, hinter]
  omega

lemma modelLower_mem_zero (M : ℕ) : 0 ∈ modelLower M := by
  simp [modelLower]

lemma modelLower_mem_M (M : ℕ) : M ∈ modelLower M := by
  simp [modelLower]

lemma modelLower_mem_interval {M u : ℕ} (hu₁ : M + 1 ≤ u) (hu₂ : u ≤ 2 * M) :
    u ∈ modelLower M := by
  simp [modelLower, hu₁, hu₂]

lemma modelLower_bounds {M u : ℕ} (hu : u ∈ modelLower M) :
    u ≤ 2 * M := by
  simp only [modelLower, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_Icc] at hu
  rcases hu with hu | hu
  · rcases hu with rfl | rfl <;> omega
  · exact hu.2

lemma nextBlock_gap {M : ℕ} {D : Finset ℕ}
    (hM : 1 ≤ M)
    (hD : D ⊆ Finset.Icc (2 * M + 1) (4 * M))
    (htile : tilesNextInterval M D)
    {d₁ d₂ : ℕ} (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hlt : d₁ < d₂) :
    M < d₂ - d₁ := by
  by_contra hgap
  have hgap_pos : 0 < d₂ - d₁ := by omega
  have hgap_le : d₂ - d₁ ≤ M := by omega
  let u₁ := M + (d₂ - d₁)
  let u₂ := M
  let p : ℕ × ℕ := (u₁, d₁)
  let q : ℕ × ℕ := (u₂, d₂)
  let n := M + d₂
  have hu₁ : u₁ ∈ modelLower M := by
    apply modelLower_mem_interval
    · dsimp only [u₁]
      omega
    · dsimp only [u₁]
      omega
  have hu₂ : u₂ ∈ modelLower M := by
    exact modelLower_mem_M M
  have hsum_p : p.1 + p.2 = n := by
    dsimp only [p, u₁, n]
    omega
  have hsum_q : q.1 + q.2 = n := by
    rfl
  have hp : p ∈ pairFiber (modelLower M) D n := by
    simp [pairFiber, p, hu₁, hd₁, hsum_p]
  have hq : q ∈ pairFiber (modelLower M) D n := by
    simp [pairFiber, q, hu₂, hd₂, hsum_q]
  have hpq : p ≠ q := by
    intro hpq
    have := congrArg Prod.snd hpq
    dsimp only [p, q] at this
    omega
  have htwo : 2 ≤ (pairFiber (modelLower M) D n).card := by
    have hsub : ({p, q} : Finset (ℕ × ℕ)) ⊆ pairFiber (modelLower M) D n := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hp
      · exact hq
    calc
      2 = ({p, q} : Finset (ℕ × ℕ)).card := by simp [hpq]
      _ ≤ (pairFiber (modelLower M) D n).card := Finset.card_le_card hsub
  have hd₂bounds := hD hd₂
  simp only [Finset.mem_Icc] at hd₂bounds
  have hn : n ∈ Finset.Icc (2 * M + 1) (6 * M) := by
    simp only [Finset.mem_Icc]
    dsimp only [n]
    omega
  have hone := htile n hn
  omega

lemma nextBlock_full_gap {M : ℕ} {D : Finset ℕ}
    (hM : 1 ≤ M)
    (hD : D ⊆ Finset.Icc (2 * M + 1) (4 * M))
    (htile : tilesNextInterval M D)
    {d₁ d₂ : ℕ} (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hlt : d₁ < d₂) :
    2 * M < d₂ - d₁ := by
  have hsmall := nextBlock_gap hM hD htile hd₁ hd₂ hlt
  by_contra hgap
  let u₁ := d₂ - d₁
  let u₂ := 0
  let p : ℕ × ℕ := (u₁, d₁)
  let q : ℕ × ℕ := (u₂, d₂)
  let n := d₂
  have hu₁ : u₁ ∈ modelLower M := by
    apply modelLower_mem_interval
    · dsimp only [u₁]
      omega
    · dsimp only [u₁]
      omega
  have hu₂ : u₂ ∈ modelLower M := modelLower_mem_zero M
  have hsum_p : p.1 + p.2 = n := by
    dsimp only [p, u₁, n]
    omega
  have hsum_q : q.1 + q.2 = n := by
    dsimp only [q, u₂, n]
    omega
  have hp : p ∈ pairFiber (modelLower M) D n := by
    simp [pairFiber, p, hu₁, hd₁, hsum_p]
  have hq : q ∈ pairFiber (modelLower M) D n := by
    simp [pairFiber, q, hu₂, hd₂, hsum_q]
  have hpq : p ≠ q := by
    intro hpq
    have := congrArg Prod.snd hpq
    dsimp only [p, q] at this
    omega
  have htwo : 2 ≤ (pairFiber (modelLower M) D n).card := by
    have hsub : ({p, q} : Finset (ℕ × ℕ)) ⊆ pairFiber (modelLower M) D n := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hp
      · exact hq
    calc
      2 = ({p, q} : Finset (ℕ × ℕ)).card := by simp [hpq]
      _ ≤ (pairFiber (modelLower M) D n).card := Finset.card_le_card hsub
  have hd₂bounds := hD hd₂
  simp only [Finset.mem_Icc] at hd₂bounds
  have hn : n ∈ Finset.Icc (2 * M + 1) (6 * M) := by
    simp only [Finset.mem_Icc]
    dsimp only [n]
    omega
  have hone := htile n hn
  omega

lemma nextBlock_card_le_one {M : ℕ} {D : Finset ℕ}
    (hM : 1 ≤ M)
    (hD : D ⊆ Finset.Icc (2 * M + 1) (4 * M))
    (htile : tilesNextInterval M D) :
    D.card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hwide := nextBlock_full_gap hM hD htile ha hb hlt
    have haBounds := hD ha
    have hbBounds := hD hb
    simp only [Finset.mem_Icc] at haBounds hbBounds
    omega
  · exact heq
  · have hwide := nextBlock_full_gap hM hD htile hb ha hgt
    have haBounds := hD ha
    have hbBounds := hD hb
    simp only [Finset.mem_Icc] at haBounds hbBounds
    omega

lemma model_pair_sums_mem {M : ℕ} {D : Finset ℕ}
    (hD : D ⊆ Finset.Icc (2 * M + 1) (4 * M))
    {p : ℕ × ℕ} (hp : p ∈ modelLower M ×ˢ D) :
    p.1 + p.2 ∈ Finset.Icc (2 * M + 1) (6 * M) := by
  simp only [Finset.mem_product] at hp
  have hu := modelLower_bounds hp.1
  have hd := hD hp.2
  simp only [Finset.mem_Icc] at hd ⊢
  omega

theorem proof :
    ∀ (M : ℕ) (D : Finset ℕ), 1 ≤ M →
      D ⊆ Finset.Icc (2 * M + 1) (4 * M) →
      ¬ tilesNextInterval M D := by
  intro M D hM hD htile
  let T := Finset.Icc (2 * M + 1) (6 * M)
  have hmap : Set.MapsTo (fun p : ℕ × ℕ => p.1 + p.2)
      (↑(modelLower M ×ˢ D) : Set (ℕ × ℕ)) (↑T : Set ℕ) := by
    intro p hp
    exact model_pair_sums_mem hD hp
  have hprod :
      (modelLower M ×ˢ D).card = T.card := by
    calc
      (modelLower M ×ˢ D).card =
          ∑ n ∈ T, (pairFiber (modelLower M) D n).card := by
            simpa [pairFiber, T] using Finset.card_eq_sum_card_fiberwise hmap
      _ = ∑ n ∈ T, 1 := by
            apply Finset.sum_congr rfl
            intro n hn
            exact htile n hn
      _ = T.card := by simp
  have hUcard : (modelLower M).card = M + 2 :=
    modelLower_card (by omega)
  have hTcard : T.card = 4 * M := by
    simp [T]
    omega
  have hcardEq : (M + 2) * D.card = 4 * M := by
    simpa [Finset.card_product, hUcard, hTcard] using hprod
  have hDcard := nextBlock_card_le_one hM hD htile
  have hcases : D.card = 0 ∨ D.card = 1 := by omega
  rcases hcases with hcard | hcard <;> rw [hcard] at hcardEq <;> omega

end Submissions.Erdos14ModelObstruction.Direct

namespace Submissions.Erdos14CumulativeDefect.Direct

open scoped BigOperators

open Submissions.Erdos14ModelObstruction.Direct

def modelEnergy (M : ℕ) (D : Finset ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc (2 * M + 1) (6 * M),
    (pairFiber (modelLower M) D n).card ^ 2

def modelDefect (M : ℕ) (D : Finset ℕ) : ℕ :=
  4 * M * modelEnergy M D - ((M + 2) * D.card) ^ 2

lemma cauchy_eq_constant {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℕ)
    (heq : s.card * (∑ i ∈ s, f i ^ 2) = (∑ i ∈ s, f i) ^ 2) :
    ∀ i ∈ s, ∀ j ∈ s, f i = f j := by
  have hmean : ∀ i ∈ s, s.card * f i = ∑ x ∈ s, f x := by
    intro i hi
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
            ∑ x ∈ t, 2 * f i * f x := by simp only [Finset.mul_sum]
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
    let u : ℤ := ((∑ x ∈ t, f x : ℕ) : ℤ)
    let v : ℤ := ((∑ x ∈ t, f x ^ 2 : ℕ) : ℤ)
    let x : ℤ := f i
    let q : ℤ := t.card
    change q + 1 = (s.card : ℤ) at hcardZ
    change u + x = ((∑ x ∈ s, f x : ℕ) : ℤ) at hsumZ
    change v + x ^ 2 = ((∑ x ∈ s, f x ^ 2 : ℕ) : ℤ) at hsqZ
    change u ^ 2 ≤ q * v at hcZ
    change 2 * x * u ≤ v + q * x ^ 2 at hdiffZ
    have hg₁ : 0 ≤ q * v - u ^ 2 := by nlinarith
    have hg₂ : 0 ≤ v + q * x ^ 2 - 2 * x * u := by nlinarith
    have hmaster : (q + 1) * (v + x ^ 2) - (u + x) ^ 2 = 0 := by
      rw [hcardZ, hsumZ, hsqZ, heqZ]
      ring
    have htotal : (q * v - u ^ 2) + (v + q * x ^ 2 - 2 * x * u) = 0 := by
      calc
        _ = (q + 1) * (v + x ^ 2) - (u + x) ^ 2 := by ring
        _ = 0 := hmaster
    have hg₁z : q * v - u ^ 2 = 0 := by nlinarith
    have hg₂z : v + q * x ^ 2 - 2 * x * u = 0 := by nlinarith
    have hsquare : (q * x - u) ^ 2 = 0 := by
      calc
        _ = q * (v + q * x ^ 2 - 2 * x * u) - (q * v - u ^ 2) := by ring
        _ = 0 := by rw [hg₁z, hg₂z]; ring
    have hqu : q * x = u := sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    have hmeanZ : (s.card : ℤ) * f i = ∑ x ∈ s, f x := by
      calc
        (s.card : ℤ) * f i = (q + 1) * x := by rw [hcardZ]
        _ = q * x + x := by ring
        _ = u + x := by rw [hqu]
        _ = ∑ x ∈ s, f x := hsumZ
    exact_mod_cast hmeanZ
  intro i hi j hj
  apply Nat.eq_of_mul_eq_mul_left (Finset.card_pos.mpr hs)
  exact (hmean i hi).trans (hmean j hj).symm

theorem cumulativeProof :
    ∀ (M : ℕ) (D : Finset ℕ), 1 ≤ M →
      D.Nonempty →
      D ⊆ Finset.Icc (2 * M + 1) (4 * M) →
      1 ≤ modelDefect M D := by
  intro M D hM hDnon hD
  let T := Finset.Icc (2 * M + 1) (6 * M)
  let f := fun n => (pairFiber (modelLower M) D n).card
  have hTcard : T.card = 4 * M := by simp [T]; omega
  have hTnon : T.Nonempty := Finset.card_pos.mp (by rw [hTcard]; omega)
  have hmap : Set.MapsTo (fun p : ℕ × ℕ => p.1 + p.2)
      (↑(modelLower M ×ˢ D) : Set (ℕ × ℕ)) (↑T : Set ℕ) := by
    intro p hp
    exact model_pair_sums_mem hD hp
  have hmass : ∑ n ∈ T, f n = (M + 2) * D.card := by
    have hU := modelLower_card hM
    calc
      ∑ n ∈ T, f n = (modelLower M ×ˢ D).card := by
        simpa [f, pairFiber, T] using (Finset.card_eq_sum_card_fiberwise hmap).symm
      _ = (M + 2) * D.card := by simp [Finset.card_product, hU]
  have hc := sq_sum_le_card_mul_sum_sq (s := T) (f := f)
  have hbase : ((M + 2) * D.card) ^ 2 ≤ 4 * M * modelEnergy M D := by
    rw [← hmass, ← hTcard]
    simpa [modelEnergy, T, f] using hc
  by_contra hnot
  have hzero : modelDefect M D = 0 := by
    unfold modelDefect at hnot ⊢
    omega
  have heq : 4 * M * modelEnergy M D = ((M + 2) * D.card) ^ 2 := by
    unfold modelDefect at hzero
    omega
  have heq' : T.card * (∑ n ∈ T, f n ^ 2) = (∑ n ∈ T, f n) ^ 2 := by
    rw [hTcard, hmass]
    simpa [modelEnergy, T, f] using heq
  have hconst := cauchy_eq_constant T hTnon f heq'
  obtain ⟨d, hd⟩ := hDnon
  have hp : (0, d) ∈ modelLower M ×ˢ D := by
    simp [modelLower_mem_zero, hd]
  have hsumT := model_pair_sums_mem hD hp
  have hpositive : 0 < f (0 + d) := by
    apply Finset.card_pos.mpr
    exact ⟨(0, d), by simp [f, pairFiber, modelLower_mem_zero, hd]⟩
  have hend : 2 * M + 1 ∈ T := by simp [T]; omega
  have hsumMem : 0 + d ∈ T := hsumT
  have hendPos : 0 < f (2 * M + 1) := by
    rw [hconst (2 * M + 1) hend (0 + d) hsumMem]
    exact hpositive
  have hendLe : f (2 * M + 1) ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro p q hp hq
    simp only [f, pairFiber, Finset.mem_filter, Finset.mem_product] at hp hq
    have hpD := hD hp.1.2
    have hqD := hD hq.1.2
    simp only [Finset.mem_Icc] at hpD hqD
    apply Prod.ext <;> omega
  have hendOne : f (2 * M + 1) = 1 := by omega
  have htile : tilesNextInterval M D := by
    intro n hn
    change f n = 1
    rw [hconst n hn (2 * M + 1) hend, hendOne]
  exact proof M D hM hD htile

end Submissions.Erdos14CumulativeDefect.Direct
