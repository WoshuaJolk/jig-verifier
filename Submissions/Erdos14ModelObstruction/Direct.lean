import Mathlib

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
