import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos61UniformExponent.Uniform

open Filter SimpleGraph Real

def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) →
      G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

def HasErdosHajnalProperty {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

lemma homogeneous_pair {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) :
    2 ≤ max G.indepNum G.cliqueNum := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  by_cases h : G.Adj a b
  · have hc : G.IsClique (↑({a, b} : Finset (Fin n)) : Set (Fin n)) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, isClique_pair] using
        (fun _ : a ≠ b => h)
    have hb := hc.card_le_cliqueNum
    simp only [Finset.card_pair hab] at hb
    exact hb.trans (le_max_right _ _)
  · have hc : Gᶜ.IsClique (↑({a, b} : Finset (Fin n)) : Set (Fin n)) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, isClique_pair] using
        (fun _ : a ≠ b => show Gᶜ.Adj a b from ⟨hab, h⟩)
    have hb := hc.card_le_cliqueNum
    simp only [Finset.card_pair hab, cliqueNum_compl] at hb
    exact hb.trans (le_max_left _ _)

/-- An eventual positive real power bound can be normalized to a strict integer
power bound at every host size at least two. -/
theorem proof {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α) :
    HasErdosHajnalProperty H ↔
      ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n),
        (¬∃ g : α ↪ Fin n, H = G.comap g) →
          n < (max G.indepNum G.cliqueNum) ^ k := by
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 he
    obtain ⟨k, hk⟩ := exists_nat_gt (max (N : ℝ) c⁻¹)
    have hNk : N < k := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hk)
    have hck : c⁻¹ < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
    have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le N) hNk
    refine ⟨k, hk0, fun n hn G hfree => ?_⟩
    by_cases hnN : N ≤ n
    · have hp : (n : ℝ) ^ c ≤ (max G.indepNum G.cliqueNum : ℕ) := by
        rcases hN n hnN G hfree with hi | hw
        · exact hi.trans (by exact_mod_cast le_max_left G.indepNum G.cliqueNum)
        · exact hw.trans (by exact_mod_cast le_max_right G.indepNum G.cliqueNum)
      have hprod : 1 < c * (k : ℝ) := by
        have hmul := mul_lt_mul_of_pos_left hck hc
        simpa [mul_inv_cancel₀ hc.ne'] using hmul
      have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      have hstrict : (n : ℝ) < ((max G.indepNum G.cliqueNum : ℕ) : ℝ) ^ k := by
        calc
          (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
          _ < (n : ℝ) ^ (c * (k : ℝ)) := rpow_lt_rpow_of_exponent_lt hn1 hprod
          _ = ((n : ℝ) ^ c) ^ k := rpow_mul_natCast (Nat.cast_nonneg n) c k
          _ ≤ ((max G.indepNum G.cliqueNum : ℕ) : ℝ) ^ k :=
            pow_le_pow_left₀ (rpow_nonneg (Nat.cast_nonneg n) c) hp k
      exact_mod_cast hstrict
    · calc
        n < k := (Nat.lt_of_not_ge hnN).trans hNk
        _ < 2 ^ k := Nat.lt_two_pow_self
        _ ≤ (max G.indepNum G.cliqueNum) ^ k :=
          Nat.pow_le_pow_left (homogeneous_pair hn G) k
  · rintro ⟨k, hk, hall⟩
    refine ⟨(k : ℝ)⁻¹, inv_pos.2 (by exact_mod_cast hk), ?_⟩
    apply eventually_atTop.2
    refine ⟨2, fun n hn G hfree => ?_⟩
    have hb : (n : ℝ) ≤ ((max G.indepNum G.cliqueNum : ℕ) : ℝ) ^ (k : ℝ) := by
      rw [rpow_natCast]
      exact_mod_cast (hall n hn G hfree).le
    have hp := (rpow_inv_le_iff_of_pos (Nat.cast_nonneg n)
      (Nat.cast_nonneg (max G.indepNum G.cliqueNum))
      (show 0 < (k : ℝ) by exact_mod_cast hk)).2 hb
    simpa only [Nat.cast_max, le_max_iff] using hp

lemma clique_le_order {n : ℕ} (G : SimpleGraph (Fin n)) : G.cliqueNum ≤ n := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  rw [← hs.card_eq]
  simpa using Finset.card_le_univ s

-- The restriction n >= 2 is essential, even for a nonempty forbidden graph.
example : ¬∃ g : Fin 2 ↪ Fin 1,
    (⊤ : SimpleGraph (Fin 2)) = (⊥ : SimpleGraph (Fin 1)).comap g := by
  rintro ⟨g, _⟩
  have h := Fintype.card_le_of_injective g g.injective
  simp at h

example (G : SimpleGraph (Fin 1)) (k : ℕ) :
    ¬ 1 < (max G.indepNum G.cliqueNum) ^ k := by
  have hi : G.indepNum ≤ 1 := by simpa using clique_le_order Gᶜ
  have hm : max G.indepNum G.cliqueNum ≤ 1 := max_le hi (clique_le_order G)
  have hp : (max G.indepNum G.cliqueNum) ^ k ≤ 1 := by
    simpa using Nat.pow_le_pow_left hm k
  omega

-- For every size >= 2 the normalization admits actual H-free hosts.
example (n : ℕ) : ¬∃ g : Fin 2 ↪ Fin n,
    (⊤ : SimpleGraph (Fin 2)) = (⊥ : SimpleGraph (Fin n)).comap g := by
  rintro ⟨g, hg⟩
  have h : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by simp
  rw [hg] at h
  exact h

example {n : ℕ} (hn : 2 ≤ n) :
    n < (max (⊥ : SimpleGraph (Fin n)).indepNum
      (⊥ : SimpleGraph (Fin n)).cliqueNum) ^ 2 := by
  have hi : n ≤ (⊥ : SimpleGraph (Fin n)).indepNum := by
    have h : (⊥ : SimpleGraph (Fin n)).IsIndepSet
        (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
      simp [SimpleGraph.IsIndepSet]
    simpa using h.card_le_indepNum
  calc
    n < n * n := Nat.lt_mul_self_iff.2 (by omega)
    _ = n ^ 2 := (pow_two n).symm
    _ ≤ (max (⊥ : SimpleGraph (Fin n)).indepNum
      (⊥ : SimpleGraph (Fin n)).cliqueNum) ^ 2 :=
        Nat.pow_le_pow_left (hi.trans (le_max_left _ _)) 2


end Submissions.Erdos61UniformExponent.Uniform
