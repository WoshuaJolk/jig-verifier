import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68TopDigitArbitraryRuns.TopDigitArbitraryRuns

private lemma perturbation_bounds {m : ℕ} (hm : 3 ≤ m) :
    0 < (1 : ℝ) / (m.factorial - 1 : ℕ) ∧
      (1 : ℝ) / (m.factorial - 1 : ℕ) < 1 := by
  have hfac : 2 < m.factorial := by
    have hmono := Nat.factorial_le hm
    norm_num at hmono
    omega
  have hdenNat : 0 < m.factorial - 1 := by omega
  have hdenR : (0 : ℝ) < (m.factorial - 1 : ℕ) := by
    exact_mod_cast hdenNat
  constructor
  · exact div_pos (by norm_num) hdenR
  · exact (div_lt_one hdenR).2
      (by exact_mod_cast (by omega : 1 < m.factorial - 1))

/-- The perturbed recurrence itself admits maximal digits for an arbitrarily
long consecutive run. Thus positivity of `1/(m!-1)` and shrinking interval
iteration alone cannot give any universal bounded-run exclusion. -/
theorem proof :
    ∀ M : ℕ, 3 ≤ M → ∀ L : ℕ,
      ∃ f : ℕ → ℝ,
        (∀ i : ℕ, i ≤ L → 0 < f i ∧ f i < 1) ∧
        (∀ i : ℕ, i < L →
          let m := M + i
          ⌊(m : ℝ) * f i + 1 / (m.factorial - 1 : ℕ)⌋ =
              (m - 1 : ℕ) ∧
            f (i + 1) =
              (m : ℝ) * f i + 1 / (m.factorial - 1 : ℕ) -
                (m - 1 : ℕ)) := by
  intro M hM L
  induction L generalizing M with
  | zero =>
      refine ⟨fun _ => (1 : ℝ) / 2, ?_, ?_⟩
      · intro i hi
        norm_num
      · intro i hi
        omega
  | succ L ih =>
      obtain ⟨f, hf, hrec⟩ := ih (M + 1) (by omega)
      let e : ℝ := 1 / (M.factorial - 1 : ℕ)
      let f0 : ℝ := (((M - 1 : ℕ) : ℝ) + f 0 - e) / M
      let g : ℕ → ℝ := fun i => if i = 0 then f0 else f (i - 1)
      have he := perturbation_bounds hM
      have he' : 0 < e ∧ e < 1 := by simpa [e] using he
      have hf0tail := hf 0 (by omega)
      have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      have hMthree : (3 : ℝ) ≤ M := by exact_mod_cast hM
      have hf0 : 0 < f0 ∧ f0 < 1 := by
        dsimp [f0]
        constructor
        · apply div_pos
          ·
            have hMR : (((M - 1 : ℕ) : ℝ)) = (M : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ M)]
              norm_num
            rw [hMR]
            linarith [he'.2]
          · exact hMpos
        · apply (div_lt_one hMpos).2
          have hMR : (((M - 1 : ℕ) : ℝ)) = (M : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ M)]
            norm_num
          rw [hMR]
          linarith [he'.1]
      have hfront :
          (M : ℝ) * f0 + e = ((M - 1 : ℕ) : ℝ) + f 0 := by
        dsimp [f0]
        field_simp [ne_of_gt hMpos]
        ring
      refine ⟨g, ?_, ?_⟩
      · intro i hi
        by_cases hi0 : i = 0
        · subst i
          simpa [g] using hf0
        · have hpred : i - 1 ≤ L := by omega
          simpa [g, hi0] using hf (i - 1) hpred
      · intro i hi
        by_cases hi0 : i = 0
        · subst i
          dsimp
          have hfloorTail : ⌊f 0⌋ = 0 := by
            rw [Int.floor_eq_zero_iff]
            exact ⟨hf0tail.1.le, hf0tail.2⟩
          have hfloor :
              ⌊(M : ℝ) * f0 + e⌋ = (M - 1 : ℕ) := by
            rw [hfront, Int.floor_natCast_add, hfloorTail, add_zero]
          constructor
          · simpa [g, e] using hfloor
          · simp only [g, if_pos, zero_add, Nat.reduceAdd,
              if_false, Nat.add_sub_cancel_left]
            rw [show (1 : ℕ) - 1 = 0 by omega]
            dsimp [e]
            rw [hfront]
            norm_num
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
          have hj : j < L := by omega
          have hr := hrec j hj
          dsimp at hr ⊢
          simp only [g, if_false (Nat.succ_ne_zero _),
            Nat.succ_sub_one] at *
          convert hr using 1 <;> norm_num <;> ring

end Submissions.Erdos68TopDigitArbitraryRuns.TopDigitArbitraryRuns
