import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.FieldSimp

/-!
Optimality of the Packomania (Eckard Specht) packing of 6 equal circles in `[0,1] × [0,1/2]`.

Lower bound: zigzag centres `(r + k a/5, y_k)` for `k = 0..5`, `a = 1 - 2r`, `y_k` alternating
`r`, `1/2 - r`, with `r = (27 - 10 * Real.sqrt 7) / 4`.
Upper bound (pigeonhole): the 6 centre abscissae lie in `[r, 1 - r]`, an interval of length
`a`; cut it into 5 strips of width `a/5` (`strip_pigeon`). Two centres share a strip, so
`4r² ≤ (a/5)² + (1/2 - 2r)²`, which with `r ≤ 1/4` forces `r ≤ (27 - 10 * Real.sqrt 7) / 4`.
-/

namespace Submissions.DominoSixCircles.Strips

/-- Pigeonhole on strips: `m + 1` reals in an interval of length `L` contain two within `L / m`
of each other. -/
theorem strip_pigeon (m : ℕ) (hm : 0 < m) (x : Fin (m + 1) → ℝ) (lo L : ℝ) (hL : 0 < L)
    (hlo : ∀ i, lo ≤ x i) (hhi : ∀ i, x i ≤ lo + L) :
    ∃ i j, i ≠ j ∧ (x i - x j) ^ 2 ≤ (L / m) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ, w = L / m := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hw_def]; exact div_pos hL hmR
  have hmw : (m : ℝ) * w = L := by rw [hw_def]; field_simp
  obtain ⟨K, hK_def⟩ : ∃ K : Fin (m + 1) → ℕ,
      ∀ i, K i = min (m - 1) ⌊(x i - lo) / w⌋₊ := ⟨_, fun _ => rfl⟩
  have hKlt : ∀ i, K i < m := by
    intro i
    have : K i ≤ m - 1 := by rw [hK_def i]; exact min_le_left _ _
    omega
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hK : ∀ i, (K i : ℝ) * w ≤ x i - lo ∧ x i - lo ≤ (K i : ℝ) * w + w := by
    intro i
    have ht0 : 0 ≤ (x i - lo) / w := div_nonneg (by linarith [hlo i]) hw.le
    have hfl : ((⌊(x i - lo) / w⌋₊ : ℕ) : ℝ) ≤ (x i - lo) / w := Nat.floor_le ht0
    have hfl2 : (x i - lo) / w < ((⌊(x i - lo) / w⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have htw : (x i - lo) / w * w = x i - lo := div_mul_cancel₀ _ hw.ne'
    rcases le_total (m - 1) ⌊(x i - lo) / w⌋₊ with h | h
    · have hKi : K i = m - 1 := by rw [hK_def i]; exact min_eq_left h
      have hcast : ((m - 1 : ℕ) : ℝ) ≤ ((⌊(x i - lo) / w⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
      rw [hKi, hm1]
      rw [hm1] at hcast
      have h1 := mul_le_mul_of_nonneg_right (hcast.trans hfl) hw.le
      constructor
      · linarith
      · have e : ((m : ℝ) - 1) * w + w = (m : ℝ) * w := by ring
        linarith [hhi i]
    · have hKi : K i = ⌊(x i - lo) / w⌋₊ := by rw [hK_def i]; exact min_eq_right h
      rw [hKi]
      have h1 := mul_le_mul_of_nonneg_right hfl hw.le
      have h2 := mul_lt_mul_of_pos_right hfl2 hw
      have e : (((⌊(x i - lo) / w⌋₊ : ℕ) : ℝ) + 1) * w
          = ((⌊(x i - lo) / w⌋₊ : ℕ) : ℝ) * w + w := by ring
      constructor <;> linarith
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => (⟨K i, hKlt i⟩ : Fin m)) (by simp)
  have hKij : K i = K j := congrArg Fin.val hf
  refine ⟨i, j, hij, ?_⟩
  rw [← hw_def]
  obtain ⟨hi1, hi2⟩ := hK i
  obtain ⟨hj1, hj2⟩ := hK j
  rw [hKij] at hi1 hi2
  have ha : 0 ≤ w - (x i - x j) := by linarith
  have hb : 0 ≤ w + (x i - x j) := by linarith
  nlinarith [mul_nonneg ha hb]

theorem proof : IsGreatest {r : ℝ | 0 < r ∧ ∃ c : Fin 6 → ℝ × ℝ,
    (∀ i, r ≤ (c i).1 ∧ (c i).1 ≤ 1 - r ∧ r ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - r) ∧
    (∀ i j, i ≠ j → (2 * r) ^ 2 ≤ ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2)}
    ((27 - 10 * Real.sqrt 7) / 4) := by
  have hs : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hlo : (2.645 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 7 < (2.6458 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  constructor
  · -- attainment
    have hpos : (0 : ℝ) < (27 - 10 * Real.sqrt 7) / 4 := by linarith
    have hq : (2 * ((27 - 10 * Real.sqrt 7) / 4)) ^ 2 = ((1 - 2 * ((27 - 10 * Real.sqrt 7) / 4)) / 5) ^ 2 + (1 / 2 - 2 * ((27 - 10 * Real.sqrt 7) / 4)) ^ 2 := by
      nlinarith [hs]
    refine ⟨hpos, ![((27 - 10 * Real.sqrt 7) / 4, (27 - 10 * Real.sqrt 7) / 4),
      ((27 - 10 * Real.sqrt 7) / 4 + 1 * ((1 - 2 * ((27 - 10 * Real.sqrt 7) / 4)) / 5), 1 / 2 - ((27 - 10 * Real.sqrt 7) / 4)),
      ((27 - 10 * Real.sqrt 7) / 4 + 2 * ((1 - 2 * ((27 - 10 * Real.sqrt 7) / 4)) / 5), (27 - 10 * Real.sqrt 7) / 4),
      ((27 - 10 * Real.sqrt 7) / 4 + 3 * ((1 - 2 * ((27 - 10 * Real.sqrt 7) / 4)) / 5), 1 / 2 - ((27 - 10 * Real.sqrt 7) / 4)),
      ((27 - 10 * Real.sqrt 7) / 4 + 4 * ((1 - 2 * ((27 - 10 * Real.sqrt 7) / 4)) / 5), (27 - 10 * Real.sqrt 7) / 4),
      ((27 - 10 * Real.sqrt 7) / 4 + 5 * ((1 - 2 * ((27 - 10 * Real.sqrt 7) / 4)) / 5), 1 / 2 - ((27 - 10 * Real.sqrt 7) / 4))], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp <;> (try constructorm* _ ∧ _) <;> nlinarith
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> nlinarith
  · -- upper bound
    intro r hr
    obtain ⟨hpos, c, hc, hd⟩ := hr
    have hr4 : r ≤ 1 / 4 := by
      have := hc 0
      linarith [this.2.2.1, this.2.2.2]
    obtain ⟨i, j, hij, hx⟩ := strip_pigeon 5 (by norm_num) (fun k => (c k).1) r (1 - 2 * r)
      (by linarith) (fun k => (hc k).1) (fun k => by linarith [(hc k).2.1])
    have hx' : ((c i).1 - (c j).1) ^ 2 ≤ ((1 - 2 * r) / 5) ^ 2 := by simpa using hx
    have hdij := hd i j hij
    obtain ⟨-, -, hi3, hi4⟩ := hc i
    obtain ⟨-, -, hj3, hj4⟩ := hc j
    have hy : ((c i).2 - (c j).2) ^ 2 ≤ (1 / 2 - 2 * r) ^ 2 := by
      have ha : 0 ≤ (1 / 2 - 2 * r) - ((c i).2 - (c j).2) := by linarith
      have hb : 0 ≤ (1 / 2 - 2 * r) + ((c i).2 - (c j).2) := by linarith
      nlinarith [mul_nonneg ha hb]
    have hq : (2 * r) ^ 2 ≤ ((1 - 2 * r) / 5) ^ 2 + (1 / 2 - 2 * r) ^ 2 := by linarith
    by_contra hcon0
    have hcon := not_le.mp hcon0
    have hA : 0 < r - ((27 - 10 * Real.sqrt 7) / 4) := by linarith
    have hB : 0 < (27 + 10 * Real.sqrt 7) / 4 - r := by linarith
    nlinarith [mul_pos hA hB, hs]

end Submissions.DominoSixCircles.Strips
