import Mathlib.Combinatorics.Compactness
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Nat

/- A standard specialization of Mathlib's Rado compactness theorem.
   This proves an equivalence, not either side of the Sidon density question. -/
namespace Submissions.Erdos1191FiniteObstruction.Compactness

def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d →
        a = c ∧ b = d

def BoolSidon (A : ℕ → Bool) : Prop := IsSidon (fun n => A n = true)

theorem sidon_compactness
    (P : (ℕ → Bool) → ℕ → Prop)
    (locality : ∀ n A B, (∀ i ≤ n, A i = B i) → (P A n ↔ P B n))
    (N : ℕ)
    (finite_models : ∀ M : ℕ, ∃ A : ℕ → Bool,
      BoolSidon A ∧ ∀ n, N ≤ n → n ≤ M → P A n) :
    ∃ A : ℕ → Bool, BoolSidon A ∧ ∀ n, N ≤ n → P A n := by
  classical
  let g (s : Finset ℕ) : ℕ → Bool := (finite_models (s.sup id)).choose
  have hg (s : Finset ℕ) : BoolSidon (g s) ∧
      ∀ n, N ≤ n → n ≤ s.sup id → P (g s) n :=
    (finite_models (s.sup id)).choose_spec
  obtain ⟨A, hA⟩ := Finset.rado_selection g
  refine ⟨A, ?_, ?_⟩
  · intro a b c d ha hb hc hd hab hcd heq
    obtain ⟨t, _, ht⟩ := hA (Finset.range (a + b + c + d + 1))
    have transfer (k : ℕ) (hk : k ≤ a + b + c + d) (hAk : A k = true) :
        g t k = true := by
      rw [← ht k (Finset.mem_range.mpr (by omega))]
      exact hAk
    exact (hg t).1 (transfer a (by omega) ha) (transfer b (by omega) hb)
      (transfer c (by omega) hc) (transfer d (by omega) hd) hab hcd heq
  · intro n hn
    obtain ⟨t, hsub, ht⟩ := hA (Finset.range (n + 1))
    have hnt : n ∈ t := hsub (Finset.mem_range.mpr (by omega))
    have hbound : n ≤ t.sup id := Finset.le_sup (f := id) hnt
    apply (locality n A (g t) (fun i hi => ht i (Finset.mem_range.mpr (by omega)))).mpr
    exact (hg t).2 n hn hbound

theorem sidon_uniform_witness
    (R : (ℕ → Bool) → ℕ → Prop)
    (locality : ∀ n A B, (∀ i ≤ n, A i = B i) → (R A n ↔ R B n))
    (N : ℕ) :
    (∀ A : ℕ → Bool, BoolSidon A → ∃ n, N ≤ n ∧ R A n) ↔
      ∃ M : ℕ, N ≤ M ∧ ∀ A : ℕ → Bool, BoolSidon A →
        ∃ n, N ≤ n ∧ n ≤ M ∧ R A n := by
  classical
  constructor
  · intro hall
    by_contra h
    push Not at h
    have models (M : ℕ) : ∃ A : ℕ → Bool,
        BoolSidon A ∧ ∀ n, N ≤ n → n ≤ M → ¬ R A n := by
      obtain ⟨A, hsidon, hbad⟩ := h (max N M) (Nat.le_max_left _ _)
      refine ⟨A, hsidon, ?_⟩
      intro n hn hnM
      exact hbad n hn (Nat.le_trans hnM (Nat.le_max_right _ _))
    obtain ⟨A, hsidon, hbad⟩ := sidon_compactness (fun A n => ¬ R A n)
      (fun n A B hEq => not_congr (locality n A B hEq)) N models
    obtain ⟨n, hn, hR⟩ := hall A hsidon
    exact hbad n hn hR
  · rintro ⟨M, _, h⟩ A hA
    obtain ⟨n, hn, _, hR⟩ := h A hA
    exact ⟨n, hn, hR⟩

noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 n).ncard

noncomputable def normalizedCount (A : Set ℕ) (n : ℕ) : ℝ :=
  (countUpTo A n : ℝ) / Real.sqrt n * Real.sqrt (Real.log n)

def Root : Prop := ∀ A : Set ℕ, A.Infinite → IsSidon A →
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ normalizedCount A n < ε

theorem normalizedCount_local (n : ℕ) (A B : Set ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ n → (i ∈ A ↔ i ∈ B)) :
    normalizedCount A n = normalizedCount B n := by
  have heq : A ∩ Set.Icc 1 n = B ∩ Set.Icc 1 n := by
    ext i
    constructor
    · rintro ⟨hi, hlo, hhi⟩
      exact ⟨(h i hlo hhi).mp hi, hlo, hhi⟩
    · rintro ⟨hi, hlo, hhi⟩
      exact ⟨(h i hlo hhi).mpr hi, hlo, hhi⟩
  simp only [normalizedCount, countUpTo, heq]

open Filter Topology in
theorem finite_normalizedCount_small (A : Set ℕ) (hA : A.Finite)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ normalizedCount A n < ε := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hlim : Tendsto (fun n : ℕ => (A.ncard : ℝ) *
      Real.sqrt (Real.log n / (n : ℝ))) atTop (𝓝 0) := by
    simpa using hlog.sqrt.const_mul (A.ncard : ℝ)
  have hsmall := (tendsto_order.mp hlim).2 ε hε
  obtain ⟨n, hn, hbound⟩ := (eventually_ge_atTop N |>.and hsmall).exists
  refine ⟨n, hn, lt_of_le_of_lt ?_ hbound⟩
  rw [normalizedCount, Real.sqrt_div' _ (Nat.cast_nonneg n)]
  calc
    (countUpTo A n : ℝ) / Real.sqrt n * Real.sqrt (Real.log n) =
        (countUpTo A n : ℝ) * (Real.sqrt (Real.log n) / Real.sqrt n) := by ring
    _ ≤ (A.ncard : ℝ) * (Real.sqrt (Real.log n) / Real.sqrt n) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Set.ncard_inter_le_ncard_left A (Set.Icc 1 n) hA
      · exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem root_iff_uniform_all_sets : Root ↔
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
      ∀ A : Set ℕ, IsSidon A →
        ∃ n : ℕ, N ≤ n ∧ n ≤ M ∧ normalizedCount A n < ε := by
  classical
  constructor
  · intro hroot ε hε N
    have hall (A : Set ℕ) (hA : IsSidon A) :
        ∃ n : ℕ, N ≤ n ∧ normalizedCount A n < ε := by
      by_cases hfinite : A.Finite
      · exact finite_normalizedCount_small A hfinite ε hε N
      · exact hroot A hfinite hA ε hε N
    have localR (n : ℕ) (A B : ℕ → Bool) (h : ∀ i ≤ n, A i = B i) :
        (normalizedCount {i | A i = true} n < ε ↔
          normalizedCount {i | B i = true} n < ε) := by
      rw [normalizedCount_local n {i | A i = true} {i | B i = true}
        (fun i _ hi => by simp only [Set.mem_ofPred_eq, h i hi])]
    obtain ⟨M, hNM, hM⟩ := (sidon_uniform_witness
      (fun A n => normalizedCount {i | A i = true} n < ε) localR N).mp
        (fun A hA => hall {i | A i = true} hA)
    refine ⟨M, hNM, ?_⟩
    intro A hA
    have heq : {i | decide (i ∈ A) = true} = A := by ext i; simp
    have hb : BoolSidon (fun i => decide (i ∈ A)) := by
      change IsSidon {i | decide (i ∈ A) = true}
      rwa [heq]
    simpa only [heq] using hM (fun i => decide (i ∈ A)) hb
  · intro h A _ hA ε hε N
    obtain ⟨M, _, hM⟩ := h ε hε N
    obtain ⟨n, hn, _, hsmall⟩ := hM A hA
    exact ⟨n, hn, hsmall⟩

def FiniteObstruction : Prop := ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
  ∃ M : ℕ, N ≤ M ∧ ∀ B : Set ℕ, B ⊆ Set.Icc 1 M → IsSidon B →
    ∃ n : ℕ, N ≤ n ∧ n ≤ M ∧ normalizedCount B n < ε

theorem root_iff_finite_obstruction : Root ↔ FiniteObstruction := by
  rw [root_iff_uniform_all_sets]
  constructor
  · intro h ε hε N
    obtain ⟨M, hNM, hM⟩ := h ε hε N
    exact ⟨M, hNM, fun B _ hB => hM B hB⟩
  · intro h ε hε N
    obtain ⟨M, hNM, hM⟩ := h ε hε N
    refine ⟨M, hNM, ?_⟩
    intro A hA
    have hsidon : IsSidon ((A ∩ Set.Icc 1 M) : Set ℕ) := by
      intro a b c d ha hb hc hd hab hcd heq
      exact hA ha.1 hb.1 hc.1 hd.1 hab hcd heq
    obtain ⟨n, hn, hnM, hsmall⟩ :=
      hM (A ∩ Set.Icc 1 M) Set.inter_subset_right hsidon
    refine ⟨n, hn, hnM, ?_⟩
    rwa [normalizedCount_local n (A ∩ Set.Icc 1 M) A (by
      intro i hlo hhi
      exact ⟨fun hi => hi.1, fun hi => ⟨hi, hlo, hhi.trans hnM⟩⟩)] at hsmall

theorem proof : Root ↔ FiniteObstruction :=
  root_iff_finite_obstruction

end Submissions.Erdos1191FiniteObstruction.Compactness
