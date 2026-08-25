import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos68ResidueCarryRecurrence.ResidueCarryRecurrence

private lemma denominator_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < n.factorial - 1 := by
  have : 1 < n.factorial := Nat.one_lt_factorial.mpr (by omega)
  omega

private lemma mul_mod_recurrence (m M d : ℕ) :
    (m * M) % d = (m * (M % d)) % d := by
  conv_lhs => rw [Nat.mul_mod]
  conv_rhs => rw [Nat.mul_mod]
  rw [Nat.mod_mod]

private lemma mul_div_recurrence (m M d : ℕ) (hd : 0 < d) :
    (m * M) / d =
      m * (M / d) + (m * (M % d)) / d := by
  let k := m * (M / d) + (m * (M % d)) / d
  let r := (m * (M % d)) % d
  have hM := Nat.div_add_mod M d
  have hmr := Nat.div_add_mod (m * (M % d)) d
  have hr : r < d := Nat.mod_lt _ hd
  have hdecomp : k * d + r = m * M := by
    dsimp [k, r] at *
    calc
      (m * (M / d) + m * (M % d) / d) * d +
          m * (M % d) % d =
          m * (d * (M / d)) +
            (d * (m * (M % d) / d) + m * (M % d) % d) := by ring
      _ = m * (d * (M / d)) + m * (M % d) := by rw [hmr]
      _ = m * (d * (M / d) + M % d) := by ring
      _ = m * M := by rw [hM]
  have hlo : k * d ≤ m * M := by omega
  have hhi : m * M < (k + 1) * d := by
    rw [← hdecomp]
    calc
      k * d + r < k * d + d := Nat.add_lt_add_left hr _
      _ = (k + 1) * d := by ring
  apply Nat.div_eq_of_lt_le
  · exact hlo
  · exact hhi

private lemma factorial_step {m : ℕ} (hm : 1 ≤ m) :
    m.factorial = m * (m - 1).factorial :=
  (Nat.mul_factorial_pred (by omega : m ≠ 0)).symm

/-- Exact recurrence for every old denominator: multiplication by `m` updates
the residue by `r ↦ mr mod d` and the quotient by the carry `⌊mr/d⌋`. -/
theorem proof :
    ∀ m : ℕ, 3 ≤ m →
      ∀ n ∈ Finset.Icc 2 (m - 1),
        let d := n.factorial - 1
        let r := (m - 1).factorial % d
        m.factorial % d = (m * r) % d ∧
          m.factorial / d =
            m * ((m - 1).factorial / d) + (m * r) / d := by
  intro m hm n hn
  dsimp
  rw [factorial_step (by omega : 1 ≤ m)]
  constructor
  · exact mul_mod_recurrence _ _ _
  · exact mul_div_recurrence _ _ _
      (denominator_pos (Finset.mem_Icc.mp hn).1)

private lemma div_mod_decomposition (M D : ℕ) (hD : 0 < D) :
    (M : ℝ) / D =
      (M / D : ℕ) + (M % D : ℕ) / (D : ℝ) := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  field_simp [hDR]
  exact_mod_cast (Nat.div_add_mod M D).symm

private lemma scaled_decomposition (k : ℕ) (hk : 2 ≤ k) :
    let A : ℕ :=
      ∑ n ∈ Finset.Icc 2 k, k.factorial / (n.factorial - 1)
    let R : ℝ :=
      ∑ n ∈ Finset.Icc 2 k,
        (k.factorial % (n.factorial - 1) : ℕ) /
          ((n.factorial - 1 : ℕ) : ℝ)
    (k.factorial : ℝ) *
        ∑ n ∈ Finset.Icc 2 k,
          (1 : ℝ) / (n.factorial - 1 : ℕ) = A + R := by
  dsimp
  rw [Finset.mul_sum, Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn2 := (Finset.mem_Icc.mp hn).1
  calc
    (k.factorial : ℝ) * ((1 : ℝ) / (n.factorial - 1 : ℕ)) =
        (k.factorial : ℝ) / (n.factorial - 1 : ℕ) := by ring
    _ = (k.factorial / (n.factorial - 1) : ℕ) +
        (k.factorial % (n.factorial - 1) : ℕ) /
          ((n.factorial - 1 : ℕ) : ℝ) :=
      div_mod_decomposition _ _ (denominator_pos hn2)

private lemma floor_radix_step (m : ℕ) (y e : ℝ) :
    ⌊(m : ℝ) * y + 1 + e⌋ - (m : ℤ) * ⌊y⌋ =
      1 + ⌊(m : ℝ) * Int.fract y + e⌋ := by
  have hy : (⌊y⌋ : ℝ) + Int.fract y = y := Int.floor_add_fract y
  have hrearrange :
      (m : ℝ) * y + 1 + e =
        ((m : ℤ) * ⌊y⌋ + 1 : ℤ) +
          ((m : ℝ) * Int.fract y + e) := by
    calc
      (m : ℝ) * y + 1 + e =
          (m : ℝ) * ((⌊y⌋ : ℝ) + Int.fract y) + 1 + e := by rw [hy]
      _ = ((m : ℤ) * ⌊y⌋ + 1 : ℤ) +
          ((m : ℝ) * Int.fract y + e) := by
        push_cast
        ring
  rw [hrearrange, Int.floor_intCast_add]
  omega

/-- Aggregating the exact carries gives recurrences for the quotient and
residue sums. All carry indicators cancel from the finite factorial digit,
which is therefore always positive. -/
theorem aggregate :
    ∀ m : ℕ, 4 ≤ m →
      let d : ℕ → ℕ := fun n => n.factorial - 1
      let A : ℕ → ℕ := fun k =>
        ∑ n ∈ Finset.Icc 2 k, k.factorial / d n
      let R : ℕ → ℝ := fun k =>
        ∑ n ∈ Finset.Icc 2 k,
          (k.factorial % d n : ℕ) / (d n : ℝ)
      let C : ℕ :=
        ∑ n ∈ Finset.Icc 2 (m - 1),
          (m * ((m - 1).factorial % d n)) / d n
      let S : ℕ → ℝ := fun k =>
        ∑ n ∈ Finset.Icc 2 k, (1 : ℝ) / d n
      (∀ n ∈ Finset.Icc 2 (m - 1),
        m.factorial % d n =
            (m * ((m - 1).factorial % d n)) % d n ∧
          m.factorial / d n =
            m * ((m - 1).factorial / d n) +
              (m * ((m - 1).factorial % d n)) / d n) ∧
      A m = m * A (m - 1) + C + 1 ∧
      R m =
        (m : ℝ) * R (m - 1) - C +
          1 / (m.factorial - 1 : ℕ) ∧
      ⌊(m.factorial : ℝ) * S m⌋ -
          (m : ℤ) * ⌊((m - 1).factorial : ℝ) * S (m - 1)⌋ =
        1 + ⌊(m : ℝ) *
          Int.fract (((m - 1).factorial : ℝ) * S (m - 1)) +
            1 / (m.factorial - 1 : ℕ)⌋ ∧
      1 ≤
        ⌊(m.factorial : ℝ) * S m⌋ -
          (m : ℤ) * ⌊((m - 1).factorial : ℝ) * S (m - 1)⌋ := by
  intro m hm
  dsimp
  have hm1 : 3 ≤ m - 1 := by omega
  have hfac := factorial_step (by omega : 1 ≤ m)
  have hold :
      ∀ n ∈ Finset.Icc 2 (m - 1),
        m.factorial % (n.factorial - 1) =
            (m * ((m - 1).factorial % (n.factorial - 1))) %
              (n.factorial - 1) ∧
          m.factorial / (n.factorial - 1) =
            m * ((m - 1).factorial / (n.factorial - 1)) +
              (m * ((m - 1).factorial % (n.factorial - 1))) /
                (n.factorial - 1) := by
    intro n hn
    rw [hfac]
    exact ⟨mul_mod_recurrence _ _ _,
      mul_div_recurrence _ _ _
        (denominator_pos (Finset.mem_Icc.mp hn).1)⟩
  have hsplitA :
      (∑ n ∈ Finset.Icc 2 m,
          m.factorial / (n.factorial - 1)) =
        (∑ n ∈ Finset.Icc 2 (m - 1),
          m.factorial / (n.factorial - 1)) +
          m.factorial / (m.factorial - 1) := by
    simpa only [show m - 1 + 1 = m by omega] using
      (Finset.sum_Icc_succ_top (by omega : 2 ≤ (m - 1) + 1)
        (fun n => m.factorial / (n.factorial - 1)))
  have hfacLarge : 2 < m.factorial := by
    have hmono := Nat.factorial_le hm
    norm_num at hmono
    omega
  have hnew :
      m.factorial / (m.factorial - 1) = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  have hA :
      (∑ n ∈ Finset.Icc 2 m, m.factorial / (n.factorial - 1)) =
        m * (∑ n ∈ Finset.Icc 2 (m - 1),
          (m - 1).factorial / (n.factorial - 1)) +
        (∑ n ∈ Finset.Icc 2 (m - 1),
          m * ((m - 1).factorial % (n.factorial - 1)) /
            (n.factorial - 1)) + 1 := by
    rw [hsplitA, hnew, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply congrArg (fun z => z + 1)
    apply Finset.sum_congr rfl
    intro n hn
    exact (hold n hn).2
  have hsplitS :
      (∑ n ∈ Finset.Icc 2 m,
          (1 : ℝ) / (n.factorial - 1 : ℕ)) =
        (∑ n ∈ Finset.Icc 2 (m - 1),
          (1 : ℝ) / (n.factorial - 1 : ℕ)) +
          1 / (m.factorial - 1 : ℕ) := by
    simpa only [show m - 1 + 1 = m by omega] using
      (Finset.sum_Icc_succ_top (by omega : 2 ≤ (m - 1) + 1)
        (fun n => (1 : ℝ) / (n.factorial - 1 : ℕ)))
  have hdenR : ((m.factorial - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : m.factorial - 1 ≠ 0)
  have hnewR :
      (m.factorial : ℝ) *
          (1 / ((m.factorial - 1 : ℕ) : ℝ)) =
        1 + 1 / ((m.factorial - 1 : ℕ) : ℝ) := by
    field_simp [hdenR]
    exact_mod_cast (by omega :
      m.factorial = (m.factorial - 1) + 1)
  have hsumStep :
      (m.factorial : ℝ) *
          ∑ n ∈ Finset.Icc 2 m,
            (1 : ℝ) / (n.factorial - 1 : ℕ) =
        (m : ℝ) *
          (((m - 1).factorial : ℝ) *
            ∑ n ∈ Finset.Icc 2 (m - 1),
              (1 : ℝ) / (n.factorial - 1 : ℕ)) +
          1 + 1 / (m.factorial - 1 : ℕ) := by
    rw [hsplitS, mul_add, hnewR, hfac, Nat.cast_mul]
    ring
  have hscaleM := scaled_decomposition m (by omega : 2 ≤ m)
  have hscalePrev :=
    scaled_decomposition (m - 1) (by omega : 2 ≤ m - 1)
  have hsumResidue := hsumStep
  rw [hscaleM, hscalePrev] at hsumResidue
  have hAcast :
      ((∑ n ∈ Finset.Icc 2 m,
          m.factorial / (n.factorial - 1) : ℕ) : ℝ) =
        (m : ℝ) * (∑ n ∈ Finset.Icc 2 (m - 1),
          (m - 1).factorial / (n.factorial - 1) : ℕ) +
        (∑ n ∈ Finset.Icc 2 (m - 1),
          m * ((m - 1).factorial % (n.factorial - 1)) /
            (n.factorial - 1) : ℕ) + 1 := by
    exact_mod_cast hA
  rw [hAcast] at hsumResidue
  have hR :
      (∑ n ∈ Finset.Icc 2 m,
          (m.factorial % (n.factorial - 1) : ℕ) /
            ((n.factorial - 1 : ℕ) : ℝ)) =
        (m : ℝ) * (∑ n ∈ Finset.Icc 2 (m - 1),
          ((m - 1).factorial % (n.factorial - 1) : ℕ) /
            ((n.factorial - 1 : ℕ) : ℝ)) -
        (∑ n ∈ Finset.Icc 2 (m - 1),
          m * ((m - 1).factorial % (n.factorial - 1)) /
            (n.factorial - 1) : ℕ) +
        1 / (m.factorial - 1 : ℕ) := by
    linarith
  let y : ℝ :=
    ((m - 1).factorial : ℝ) *
      ∑ n ∈ Finset.Icc 2 (m - 1),
        (1 : ℝ) / (n.factorial - 1 : ℕ)
  have hdigit :
      ⌊(m.factorial : ℝ) *
          ∑ n ∈ Finset.Icc 2 m,
            (1 : ℝ) / (n.factorial - 1 : ℕ)⌋ -
        (m : ℤ) * ⌊((m - 1).factorial : ℝ) *
          ∑ n ∈ Finset.Icc 2 (m - 1),
            (1 : ℝ) / (n.factorial - 1 : ℕ)⌋ =
        1 + ⌊(m : ℝ) *
          Int.fract (((m - 1).factorial : ℝ) *
            ∑ n ∈ Finset.Icc 2 (m - 1),
              (1 : ℝ) / (n.factorial - 1 : ℕ)) +
            1 / (m.factorial - 1 : ℕ)⌋ := by
    rw [hsumStep]
    exact floor_radix_step m y (1 / (m.factorial - 1 : ℕ))
  have hnonneg :
      0 ≤ ⌊(m : ℝ) *
        Int.fract (((m - 1).factorial : ℝ) *
          ∑ n ∈ Finset.Icc 2 (m - 1),
            (1 : ℝ) / (n.factorial - 1 : ℕ)) +
          1 / (m.factorial - 1 : ℕ)⌋ := by
    rw [Int.floor_nonneg]
    positivity
  refine ⟨hold, hA, hR, hdigit, ?_⟩
  rw [hdigit]
  omega

private lemma floor_increment_by_unit_tail (y u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ ⌊y + u⌋ - ⌊y⌋ ∧ ⌊y + u⌋ - ⌊y⌋ ≤ 1 := by
  have hflooru : ⌊u⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨hu0, hu1⟩
  constructor
  · exact sub_nonneg.mpr (Int.floor_mono (by linarith))
  · have hadd := Int.le_floor_add_floor y u
    rw [hflooru, add_zero] at hadd
    omega

private theorem finite_digit_tail_criterion :
    ∀ m : ℕ, 3 ≤ m → ∀ y z u v : ℝ,
      0 ≤ u → u < 1 → 0 ≤ v → v < 1 →
      let D : ℤ := ⌊y⌋ - (m : ℤ) * ⌊z⌋
      1 ≤ D → D ≤ (m : ℤ) - 2 →
      ⌊y + u⌋ - (m : ℤ) * ⌊z + v⌋ ≠ 0 := by
  intro m hm y z u v hu0 hu1 hv0 hv1
  dsimp
  intro hD1 hD2 hzero
  have hcu := floor_increment_by_unit_tail y u hu0 hu1
  have hcv := floor_increment_by_unit_tail z v hv0 hv1
  let cu : ℤ := ⌊y + u⌋ - ⌊y⌋
  let cv : ℤ := ⌊z + v⌋ - ⌊z⌋
  have hy : ⌊y + u⌋ = ⌊y⌋ + cu := by
    dsimp [cu]
    omega
  have hz : ⌊z + v⌋ = ⌊z⌋ + cv := by
    dsimp [cv]
    omega
  have hcuBounds : 0 ≤ cu ∧ cu ≤ 1 := hcu
  have hcvBounds : 0 ≤ cv ∧ cv ≤ 1 := hcv
  have hcvCases : cv = 0 ∨ cv = 1 := by omega
  rw [hy, hz] at hzero
  rcases hcvCases with hcv0 | hcv1
  · rw [hcv0] at hzero
    simp only [add_zero] at hzero
    ring_nf at hzero
    omega
  · rw [hcv1, mul_add, mul_one] at hzero
    ring_nf at hzero
    omega

/-- The complete carry recurrence together with a one-unit-tail criterion:
a finite digit in `[1,m-2]` survives both possible tail carries. -/
theorem combined :
    (∀ m : ℕ, 4 ≤ m →
      let d : ℕ → ℕ := fun n => n.factorial - 1
      let A : ℕ → ℕ := fun k =>
        ∑ n ∈ Finset.Icc 2 k, k.factorial / d n
      let R : ℕ → ℝ := fun k =>
        ∑ n ∈ Finset.Icc 2 k,
          (k.factorial % d n : ℕ) / (d n : ℝ)
      let C : ℕ :=
        ∑ n ∈ Finset.Icc 2 (m - 1),
          (m * ((m - 1).factorial % d n)) / d n
      let S : ℕ → ℝ := fun k =>
        ∑ n ∈ Finset.Icc 2 k, (1 : ℝ) / d n
      (∀ n ∈ Finset.Icc 2 (m - 1),
        m.factorial % d n =
            (m * ((m - 1).factorial % d n)) % d n ∧
          m.factorial / d n =
            m * ((m - 1).factorial / d n) +
              (m * ((m - 1).factorial % d n)) / d n) ∧
      A m = m * A (m - 1) + C + 1 ∧
      R m =
        (m : ℝ) * R (m - 1) - C +
          1 / (m.factorial - 1 : ℕ) ∧
      ⌊(m.factorial : ℝ) * S m⌋ -
          (m : ℤ) * ⌊((m - 1).factorial : ℝ) * S (m - 1)⌋ =
        1 + ⌊(m : ℝ) *
          Int.fract (((m - 1).factorial : ℝ) * S (m - 1)) +
            1 / (m.factorial - 1 : ℕ)⌋ ∧
      1 ≤
        ⌊(m.factorial : ℝ) * S m⌋ -
          (m : ℤ) * ⌊((m - 1).factorial : ℝ) * S (m - 1)⌋) ∧
    (∀ m : ℕ, 3 ≤ m → ∀ y z u v : ℝ,
      0 ≤ u → u < 1 → 0 ≤ v → v < 1 →
      let D : ℤ := ⌊y⌋ - (m : ℤ) * ⌊z⌋
      1 ≤ D → D ≤ (m : ℤ) - 2 →
      ⌊y + u⌋ - (m : ℤ) * ⌊z + v⌋ ≠ 0) :=
  ⟨aggregate, finite_digit_tail_criterion⟩

end Submissions.Erdos68ResidueCarryRecurrence.ResidueCarryRecurrence
