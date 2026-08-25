import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

namespace Submissions.Erdos450SublinearDivisorWindowsRefuted.Direct

open Filter
open scoped Topology

def HasMediumDivisor (n m : ℕ) : Prop :=
  ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

open scoped Classical in
noncomputable def localCount (n x y : ℕ) : ℕ :=
  ((Finset.Ioo x (x + y)).filter (HasMediumDivisor n)).card

def UniformlySparse (ε : ℝ) (n y : ℕ) : Prop :=
  ∀ x : ℕ, (localCount n x y : ℝ) ≤ ε * (y : ℝ)

def IsSufficientScale (Y : ℝ → ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ y : ℕ, Y ε n ≤ y → UniformlySparse ε n y

lemma dense_factorial_translate (n y : ℕ) (hy : y ≤ n) :
    localCount n (Nat.factorial (2 * n) + n) y = y - 1 := by
  classical
  unfold localCount
  rw [Finset.card_filter_eq_iff.mpr]
  · rw [Nat.card_Ioo]
    omega
  · intro m hm
    rw [Finset.mem_Ioo] at hm
    let k := m - (Nat.factorial (2 * n) + n)
    have hkpos : 0 < k := Nat.sub_pos_of_lt hm.1
    have hklt : k < y := by
      dsimp [k]
      omega
    have hmk : Nat.factorial (2 * n) + n + k = m := by
      dsimp [k]
      omega
    refine ⟨n + k, by omega, by omega, ?_⟩
    have hd : n + k ∣ Nat.factorial (2 * n) :=
      Nat.dvd_factorial (by omega) (by omega)
    have hs : n + k ∣ Nat.factorial (2 * n) + (n + k) :=
      dvd_add hd (dvd_refl (n + k))
    rw [← hmk]
    simpa [Nat.add_assoc] using hs

lemma not_sparse_at_length_n (n : ℕ) (hn : 3 ≤ n) :
    ¬ UniformlySparse (1 / 2 : ℝ) n n := by
  intro h
  have hx := h (Nat.factorial (2 * n) + n)
  rw [dense_factorial_translate n n le_rfl] at hx
  rw [Nat.cast_sub (by omega : 1 ≤ n)] at hx
  norm_num at hx
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem proof :
    ¬ (∃ Y : ℝ → ℕ → ℕ, IsSufficientScale Y ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => (Y ε n : ℝ) / n) atTop (𝓝 0)) := by
  rintro ⟨Y, hY, hsub⟩
  obtain ⟨N, hN⟩ := hY (1 / 2 : ℝ) (by norm_num)
  have hratio :
      ∀ᶠ n : ℕ in atTop, (Y (1 / 2 : ℝ) n : ℝ) / n < 1 := by
    have hlim := hsub (1 / 2 : ℝ) (by norm_num)
    exact (tendsto_order.1 hlim).2 1 (by norm_num)
  rw [eventually_atTop] at hratio
  obtain ⟨M, hM⟩ := hratio
  let n := max (max N M) 3
  have hnN : N ≤ n := by simp [n]
  have hnM : M ≤ n := by simp [n]
  have hn3 : 3 ≤ n := by simp [n]
  have hnpos : (0 : ℝ) < n := by positivity
  have hquot := hM n hnM
  have hYltR : (Y (1 / 2 : ℝ) n : ℝ) < n := by
    have := (div_lt_iff₀ hnpos).mp hquot
    simpa using this
  have hYle : Y (1 / 2 : ℝ) n ≤ n := by
    exact_mod_cast hYltR.le
  exact not_sparse_at_length_n n hn3 (hN n hnN n hYle)

end Submissions.Erdos450SublinearDivisorWindowsRefuted.Direct
