import Mathlib

namespace Submissions.CuspAllRankMinor.Explicit

open scoped BigOperators

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

def CrossAdj {r N : ℕ} (i j : ZMod (2 * N)) : Prop :=
  (∃ c : Fin r, j = i + cOffset c) ∨
  (∃ d : Fin r, j = -i + dOffset d)

noncomputable def cuspProduct {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) : ℂ := by
  letI := h
  exact
    (∏ c : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c))) *
      (∏ d : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)))

lemma zeroPattern (r N : ℕ) (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    cuspProduct (r := r) h i j = 0 ↔ CrossAdj (r := r) i j := by
  letI := h
  simp only [cuspProduct, CrossAdj, mul_eq_zero, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero]
  simp only [ZMod.injective_stdAddChar.eq_iff]

def OffsetZ (r u : ℤ) : Prop :=
  (u % 2 = 1 ∧ 0 ≤ u ∧ u < 2 * r - 1) ∨ u = 2 * r + 1

def AdjQFZ (r N i j : ℤ) : Prop :=
  (i ≤ j ∧ (j - i) % 2 = 0 ∧ j - i < 2 * r) ∨
  (j < i ∧ (j + 2 * N - i) % 2 = 0 ∧ j + 2 * N - i < 2 * r) ∨
  OffsetZ r (j + i) ∨ OffsetZ r (j + i - 2 * N)

def rowZ (r N q : ℤ) : ℤ :=
  if q < r + 2 then q
  else if q - (r + 2) < 3 then 2 * N - r + 2 * (q - (r + 2))
  else 2 * N - r + (q - (r + 2)) + 2

def potentialZ (r q : ℤ) : ℤ :=
  if q < r + 2 then q
  else if q - (r + 2) < 3 then r - 2 * (q - (r + 2))
  else r - (q - (r + 2)) - 2

def colZ (r q : ℤ) : ℤ :=
  if q < r then 2 * r - 1 - q
  else if q = r then r - 4
  else if q = r + 1 then r - 2
  else if q - (r + 2) < 3 then r - 1 - 2 * (q - (r + 2))
  else r - (q - (r + 2)) - 3

def rankZ (r q : ℤ) : ℤ :=
  if q < r + 2 then
    if q < 2 then q
    else if r % 2 = 0 then
      if q % 2 = 1 then q
      else if q = r then 2 * r - 2
      else if q + 2 = r then 2 * r - 1
      else r + 1 + q
    else
      if q % 2 = 0 then r - 4 + q
      else if q = r then 2 * r - 2
      else if q + 2 = r then 2 * r - 1
      else q
  else
    let u := potentialZ r q
    if u % 2 = 0 then u
    else if r % 2 = 0 then r + 1 + u
    else r - 4 + u

set_option maxHeartbeats 10000000 in
lemma support_potential {r N q s : ℤ} (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (hq0 : 0 ≤ q) (hq : q < 2 * r) (hs0 : 0 ≤ s) (hs : s < 2 * r)
    (hnon : ¬ AdjQFZ r N (rowZ r N q) (colZ r s)) :
    q = s ∨ rankZ r s < rankZ r q := by
  by_contra hbad
  push Not at hbad
  apply hnon
  simp only [AdjQFZ, OffsetZ, rowZ, colZ, rankZ, potentialZ] at *
  split_ifs at * <;> omega

set_option maxHeartbeats 10000000 in
lemma diagonal_nonadj {r N q : ℤ} (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (hq0 : 0 ≤ q) (hq : q < 2 * r) :
    ¬ AdjQFZ r N (rowZ r N q) (colZ r q) := by
  simp only [AdjQFZ, OffsetZ, rowZ, colZ]
  split_ifs <;> omega

lemma direct_translate {r N i j : ℕ} (hij : i ≤ j)
    (heven : ((j : ℤ) - i) % 2 = 0) (hsmall : (j : ℤ) - i < 2 * r) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  have hevenN : (j - i) % 2 = 0 := by omega
  let a := (j - i) / 2
  have ha : a < r := by
    dsimp [a]
    omega
  left
  refine ⟨⟨a, ha⟩, ?_⟩
  have hj : j = i + 2 * a := by
    dsimp [a]
    omega
  simp only [cOffset]
  rw [hj]
  simp

lemma wrapped_translate {r N i j : ℕ} (hi : i < 2 * N) (hji : j < i)
    (heven : (((j + 2 * N : ℕ) : ℤ) - i) % 2 = 0)
    (hsmall : ((j + 2 * N : ℕ) : ℤ) - i < 2 * r) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  have hevenN : (j + 2 * N - i) % 2 = 0 := by omega
  let a := (j + 2 * N - i) / 2
  have ha : a < r := by
    dsimp [a]
    omega
  have heq : j + 2 * N = i + 2 * a := by
    dsimp [a]
    omega
  left
  refine ⟨⟨a, ha⟩, ?_⟩
  simp only [cOffset]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) heq
  simpa using hz

lemma direct_anti_regular {r N i j : ℕ}
    (hodd : (((j + i : ℕ) : ℤ) % 2) = 1)
    (hsmall : (j + i : ℤ) < 2 * r - 1) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  have hoddN : (j + i) % 2 = 1 := by omega
  let b := (j + i - 1) / 2
  have hb : b + 1 < r := by
    dsimp [b]
    omega
  have hsum : j + i = 2 * b + 1 := by
    dsimp [b]
    omega
  right
  refine ⟨⟨b, by omega⟩, ?_⟩
  have hif : ¬ b + 1 = r := by omega
  simp only [dOffset, hif, if_false, Nat.add_zero]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) hsum
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
  linear_combination hz

lemma direct_anti_special {r N i j : ℕ} (hr : 1 ≤ r)
    (hsum : j + i = 2 * r + 1) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  right
  let d : Fin r := ⟨r - 1, by omega⟩
  refine ⟨d, ?_⟩
  have hd : d.val + 1 = r := by
    dsimp [d]
    omega
  simp only [dOffset, hd, if_true]
  dsimp [d]
  have hoff : 2 * (r - 1) + 1 + 2 = 2 * r + 1 := by omega
  rw [hoff]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) hsum
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
  linear_combination hz

lemma wrapped_anti_regular {r N i j : ℕ} (hle : 2 * N ≤ j + i)
    (hodd : (((j + i : ℕ) : ℤ) - 2 * N) % 2 = 1)
    (hsmall : ((j + i : ℕ) : ℤ) - 2 * N < 2 * r - 1) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  have hoddN : (j + i - 2 * N) % 2 = 1 := by omega
  let b := (j + i - 2 * N - 1) / 2
  have hb : b + 1 < r := by
    dsimp [b]
    omega
  have hsum : j + i = 2 * b + 1 + 2 * N := by
    dsimp [b]
    omega
  right
  refine ⟨⟨b, by omega⟩, ?_⟩
  have hif : ¬ b + 1 = r := by omega
  simp only [dOffset, hif, if_false, Nat.add_zero]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) hsum
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
  have hn : (2 : ZMod (2 * N)) * (N : ZMod (2 * N)) = 0 := by
    have hzmod : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := by simp
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hzmod
  linear_combination hz + hn

lemma wrapped_anti_special {r N i j : ℕ} (hr : 1 ≤ r)
    (hsum : j + i = 2 * r + 1 + 2 * N) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  right
  let d : Fin r := ⟨r - 1, by omega⟩
  refine ⟨d, ?_⟩
  have hd : d.val + 1 = r := by
    dsimp [d]
    omega
  simp only [dOffset, hd, if_true]
  dsimp [d]
  have hoff : 2 * (r - 1) + 1 + 2 = 2 * r + 1 := by omega
  rw [hoff]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) hsum
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
  have hn : (2 : ZMod (2 * N)) * (N : ZMod (2 * N)) = 0 := by
    have hzmod : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := by simp
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hzmod
  linear_combination hz + hn

lemma adjQF_crossAdj {r N i j : ℕ} (hr : 1 ≤ r) (hi : i < 2 * N)
    (h : AdjQFZ r N i j) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  simp only [AdjQFZ, OffsetZ, Int.natCast_add, Int.natCast_mul] at h
  rcases h with h | h | h | h
  · exact direct_translate (by omega) h.2.1 h.2.2
  · exact wrapped_translate hi (by omega) h.2.1 h.2.2
  · rcases h with h | h
    · exact direct_anti_regular h.1 h.2.2
    · exact direct_anti_special hr (by omega)
  · rcases h with h | h
    · apply wrapped_anti_regular (by omega) h.1
      omega
    · exact wrapped_anti_special hr (by omega)

lemma crossAdj_adjQF {r N i j : ℕ} (hr : 1 ≤ r) (hN : r + 2 ≤ N)
    (hi : i < 2 * N) (hj : j < 2 * N)
    (h : CrossAdj (r := r) (N := N)
      (i : ZMod (2 * N)) (j : ZMod (2 * N))) :
    AdjQFZ r N i j := by
  rcases h with ⟨c, hc⟩ | ⟨d, hd⟩
  · have heq : (j : ZMod (2 * N)) = ((i + 2 * c.val : ℕ) : ZMod (2 * N)) := by
      simpa only [cOffset, Nat.cast_add] using hc
    have hmod := (ZMod.natCast_eq_natCast_iff' j (i + 2 * c.val) (2 * N)).mp heq
    have hc_lt : c.val < r := c.isLt
    simp only [AdjQFZ, OffsetZ]
    by_cases hw : i + 2 * c.val < 2 * N
    · left
      have hj_eq : j = i + 2 * c.val := by
        rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hw] at hmod
        exact hmod
      omega
    · right; left
      have hsum : i + 2 * c.val < 2 * (2 * N) := by omega
      have hj_eq : j + 2 * N = i + 2 * c.val := by
        rw [Nat.mod_eq_of_lt hj] at hmod
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hw)] at hmod
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
      omega
  · have hsumz :
        (j + i : ZMod (2 * N)) = dOffset (r := r) (N := N) d := by
      linear_combination hd
    let off : ℕ := 2 * d.val + 1 + if d.val + 1 = r then 2 else 0
    have heq : ((j + i : ℕ) : ZMod (2 * N)) = (off : ZMod (2 * N)) := by
      simpa only [off, dOffset, Nat.cast_add] using hsumz
    have hmod := (ZMod.natCast_eq_natCast_iff' (j + i) off (2 * N)).mp heq
    have hd_lt : d.val < r := d.isLt
    have hoff_lt : off < 2 * N := by
      simp only [off]
      split_ifs <;> omega
    have hoff_shape :
        (off % 2 = 1 ∧ off < 2 * r - 1) ∨ off = 2 * r + 1 := by
      simp only [off]
      split_ifs <;> omega
    simp only [AdjQFZ, OffsetZ]
    right; right
    by_cases hw : j + i < 2 * N
    · left
      have hji : j + i = off := by
        rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hoff_lt] at hmod
        exact hmod
      rcases hoff_shape with hs | hs
      · left; omega
      · right; omega
    · right
      have hsum : j + i < 2 * (2 * N) := by omega
      have hji : j + i = off + 2 * N := by
        rw [Nat.mod_eq_of_lt hoff_lt] at hmod
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hw)] at hmod
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
      rcases hoff_shape with hs | hs
      · left; omega
      · right; omega

def rowN (r N q : ℕ) : ℕ :=
  if q < r + 2 then q
  else if q - (r + 2) < 3 then 2 * N - r + 2 * (q - (r + 2))
  else 2 * N - r + (q - (r + 2)) + 2

def colN (r q : ℕ) : ℕ :=
  if q < r then 2 * r - 1 - q
  else if q = r then r - 4
  else if q = r + 1 then r - 2
  else if q - (r + 2) < 3 then r - 1 - 2 * (q - (r + 2))
  else r - (q - (r + 2)) - 3

lemma rowN_lt {r N q : ℕ} (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (hq : q < 2 * r) : rowN r N q < 2 * N := by
  simp only [rowN]
  split_ifs <;> omega

lemma colN_lt {r q : ℕ} (hr : 4 ≤ r) (hq : q < 2 * r) :
    colN r q < 2 * r := by
  simp only [colN]
  split_ifs <;> omega

lemma rowN_cast {r N q : ℕ} (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (hq : q < 2 * r) :
    (rowN r N q : ℤ) = rowZ r N q := by
  simp only [rowN, rowZ]
  split_ifs <;> omega

lemma colN_cast {r q : ℕ} (hr : 4 ≤ r) (hq : q < 2 * r) :
    (colN r q : ℤ) = colZ r q := by
  simp only [colN, colZ]
  split_ifs <;> omega

noncomputable def cuspMatrix (r N : ℕ) (h : NeZero (2 * N)) :
    Matrix (Fin (2 * r)) (Fin (2 * r)) ℂ := fun q s =>
  cuspProduct (r := r) h
    (rowN r N q.val : ZMod (2 * N))
    (colN r s.val : ZMod (2 * N))

lemma det_ne_zero_of_unique_matching {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (σ : Equiv.Perm n)
    (hσ : ∀ i, M (σ i) i ≠ 0)
    (hunique : ∀ τ : Equiv.Perm n, τ ≠ σ → ∃ i, M (τ i) i = 0) :
    M.det ≠ 0 := by
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_single σ]
  · apply (smul_ne_zero_iff_ne _).2
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hσ i)
  · intro τ hτ hne
    obtain ⟨i, hi⟩ := hunique τ hne
    have hp : ∏ j, M (τ j) j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hp, smul_zero]
  · simp

lemma det_ne_zero_of_potential {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (p : n → ℤ)
    (hdiag : ∀ i, M i i ≠ 0)
    (hoff : ∀ i j, M i j ≠ 0 → i = j ∨ p j < p i) :
    M.det ≠ 0 := by
  apply det_ne_zero_of_unique_matching M 1 hdiag
  intro τ hτ
  by_contra hall
  push Not at hall
  have hcases : ∀ i, τ i = i ∨ p i < p (τ i) := by
    intro i
    rcases hoff (τ i) i (hall i) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hle : ∀ i ∈ Finset.univ, p i ≤ p (τ i) := by
    intro i hi
    rcases hcases i with h | h
    · simp [h]
    · exact h.le
  have hstrict : ∃ i ∈ Finset.univ, p i < p (τ i) := by
    by_contra h
    push Not at h
    apply hτ
    ext i
    rcases hcases i with hi | hi
    · exact hi
    · exact False.elim (not_le_of_gt hi (h i (Finset.mem_univ i)))
  have hsum : ∑ i, p i < ∑ i, p (τ i) :=
    Finset.sum_lt_sum hle hstrict
  rw [← Equiv.sum_comp τ] at hsum
  exact (lt_irrefl _ hsum)

theorem proof (r N : ℕ) (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (h : NeZero (2 * N)) : (cuspMatrix r N h).det ≠ 0 := by
  apply det_ne_zero_of_potential (cuspMatrix r N h)
    (fun q => rankZ r q.val)
  · intro q hzero
    have hadj := (zeroPattern r N h
      (rowN r N q.val : ZMod (2 * N))
      (colN r q.val : ZMod (2 * N))).mp hzero
    have hqf := crossAdj_adjQF (by omega) hN
      (rowN_lt hr hN q.isLt)
      ((colN_lt hr q.isLt).trans (by omega)) hadj
    rw [rowN_cast hr hN q.isLt, colN_cast hr q.isLt] at hqf
    exact diagonal_nonadj (by exact_mod_cast hr) (by exact_mod_cast hN)
      (by positivity) (by exact_mod_cast q.isLt) hqf
  · intro q s hnz
    by_cases hqs : q = s
    · exact Or.inl hqs
    right
    have hnotcross : ¬ CrossAdj (r := r) (N := N)
        (rowN r N q.val : ZMod (2 * N))
        (colN r s.val : ZMod (2 * N)) := by
      intro hadj
      apply hnz
      exact (zeroPattern r N h _ _).mpr hadj
    have hnotqf : ¬ AdjQFZ r N (rowN r N q.val) (colN r s.val) := by
      intro hqf
      apply hnotcross
      exact adjQF_crossAdj (by omega) (rowN_lt hr hN q.isLt) hqf
    rw [rowN_cast hr hN q.isLt, colN_cast hr s.isLt] at hnotqf
    rcases support_potential (by exact_mod_cast hr) (by exact_mod_cast hN)
      (by positivity) (by exact_mod_cast q.isLt)
      (by positivity) (by exact_mod_cast s.isLt) hnotqf with h | h
    · exact False.elim (hqs (Fin.ext (by exact_mod_cast h)))
    · exact h


def row2 (q : Fin 4) : ℕ := q.val

def col2 (q : Fin 4) : ℕ := ![3, 2, 0, 4] q

def pot2 (q : Fin 4) : ℤ := ![2, 0, 0, 1] q

noncomputable def matrix2 (N : ℕ) (h : NeZero (2 * N)) :
    Matrix (Fin 4) (Fin 4) ℂ := fun q s =>
  cuspProduct (r := 2) h
    (row2 q : ZMod (2 * N)) (col2 s : ZMod (2 * N))

lemma row2_lt {N : ℕ} (hN : 4 ≤ N) (q : Fin 4) : row2 q < 2 * N := by
  simp [row2]
  omega

lemma col2_lt {N : ℕ} (hN : 4 ≤ N) (q : Fin 4) : col2 q < 2 * N := by
  fin_cases q <;> simp [col2] <;> omega

lemma diag2 {N : ℕ} (hN : 4 ≤ N) (q : Fin 4) :
    ¬ AdjQFZ 2 N (row2 q) (col2 q) := by
  fin_cases q <;> simp [AdjQFZ, OffsetZ, row2, col2] <;> omega

lemma support2 {N : ℕ} (hN : 4 ≤ N) (q s : Fin 4)
    (hnon : ¬ AdjQFZ 2 N (row2 q) (col2 s)) :
    q = s ∨ pot2 s < pot2 q := by
  fin_cases q <;> fin_cases s <;>
    simp [AdjQFZ, OffsetZ, row2, col2, pot2] at hnon ⊢ <;> omega

theorem minor2 (N : ℕ) (hN : 4 ≤ N) (h : NeZero (2 * N)) :
    (matrix2 N h).det ≠ 0 := by
  apply det_ne_zero_of_potential (matrix2 N h) pot2
  · intro q hzero
    have hadj := (zeroPattern 2 N h
      (row2 q : ZMod (2 * N)) (col2 q : ZMod (2 * N))).mp hzero
    have hqf := crossAdj_adjQF (r := 2) (N := N) (by omega) (by omega)
      (row2_lt hN q) (col2_lt hN q) hadj
    exact diag2 hN q hqf
  · intro q s hnz
    have hnotqf : ¬ AdjQFZ 2 N (row2 q) (col2 s) := by
      intro hqf
      apply hnz
      apply (zeroPattern 2 N h _ _).mpr
      exact adjQF_crossAdj (r := 2) (N := N) (by omega)
        (row2_lt hN q) hqf
    exact support2 hN q s hnotqf

def row3small (q : Fin 6) : ℕ := ![0, 1, 2, 3, 4, 7] q

def col3small (q : Fin 6) : ℕ := ![5, 4, 7, 1, 0, 2] q

def pot3small (q : Fin 6) : ℤ := ![0, 5, 4, 2, 3, 1] q

noncomputable def matrix3small (h : NeZero 10) :
    Matrix (Fin 6) (Fin 6) ℂ := fun q s =>
  cuspProduct (r := 3) (N := 5) h
    (row3small q : ZMod 10) (col3small s : ZMod 10)

lemma diag3small (q : Fin 6) :
    ¬ AdjQFZ 3 5 (row3small q) (col3small q) := by
  fin_cases q <;> simp [AdjQFZ, OffsetZ, row3small, col3small]

lemma support3small (q s : Fin 6)
    (hnon : ¬ AdjQFZ 3 5 (row3small q) (col3small s)) :
    q = s ∨ pot3small s < pot3small q := by
  fin_cases q <;> fin_cases s <;>
    simp [AdjQFZ, OffsetZ, row3small, col3small, pot3small] at hnon ⊢

theorem minor3small (h : NeZero 10) : (matrix3small h).det ≠ 0 := by
  apply det_ne_zero_of_potential (matrix3small h) pot3small
  · intro q hzero
    have hadj := (zeroPattern 3 5 h
      (row3small q : ZMod 10) (col3small q : ZMod 10)).mp hzero
    have hqf := crossAdj_adjQF (r := 3) (N := 5) (by omega) (by omega)
      (by fin_cases q <;> simp [row3small])
      (by fin_cases q <;> simp [col3small]) hadj
    exact diag3small q hqf
  · intro q s hnz
    have hnotqf : ¬ AdjQFZ 3 5 (row3small q) (col3small s) := by
      intro hqf
      apply hnz
      apply (zeroPattern 3 5 h _ _).mpr
      exact adjQF_crossAdj (r := 3) (N := 5) (by omega)
        (by fin_cases q <;> simp [row3small]) hqf
    exact support3small q s hnotqf

def row3large (N : ℕ) (q : Fin 6) : ℕ := ![0, 1, 2, 3, 4, 2 * N - 2] q

def col3large (q : Fin 6) : ℕ := ![5, 4, 3, 2, 0, 1] q

def pot3large (q : Fin 6) : ℤ := ![0, 0, 4, 2, 3, 1] q

noncomputable def matrix3large (N : ℕ) (h : NeZero (2 * N)) :
    Matrix (Fin 6) (Fin 6) ℂ := fun q s =>
  cuspProduct (r := 3) h
    (row3large N q : ZMod (2 * N)) (col3large s : ZMod (2 * N))

lemma row3large_lt {N : ℕ} (hN : 6 ≤ N) (q : Fin 6) :
    row3large N q < 2 * N := by
  fin_cases q <;> simp [row3large] <;> omega

lemma col3large_lt {N : ℕ} (hN : 6 ≤ N) (q : Fin 6) :
    col3large q < 2 * N := by
  fin_cases q <;> simp [col3large] <;> omega

lemma diag3large {N : ℕ} (hN : 6 ≤ N) (q : Fin 6) :
    ¬ AdjQFZ 3 N (row3large N q) (col3large q) := by
  fin_cases q <;> simp [AdjQFZ, OffsetZ, row3large, col3large] <;> omega

lemma support3large {N : ℕ} (hN : 6 ≤ N) (q s : Fin 6)
    (hnon : ¬ AdjQFZ 3 N (row3large N q) (col3large s)) :
    q = s ∨ pot3large s < pot3large q := by
  fin_cases q <;> fin_cases s <;>
    simp [AdjQFZ, OffsetZ, row3large, col3large, pot3large] at hnon ⊢ <;> omega

theorem minor3large (N : ℕ) (hN : 6 ≤ N) (h : NeZero (2 * N)) :
    (matrix3large N h).det ≠ 0 := by
  apply det_ne_zero_of_potential (matrix3large N h) pot3large
  · intro q hzero
    have hadj := (zeroPattern 3 N h
      (row3large N q : ZMod (2 * N))
      (col3large q : ZMod (2 * N))).mp hzero
    have hqf := crossAdj_adjQF (r := 3) (N := N) (by omega) (by omega)
      (row3large_lt hN q) (col3large_lt hN q) hadj
    exact diag3large hN q hqf
  · intro q s hnz
    have hnotqf : ¬ AdjQFZ 3 N (row3large N q) (col3large s) := by
      intro hqf
      apply hnz
      apply (zeroPattern 3 N h _ _).mpr
      exact adjQF_crossAdj (r := 3) (N := N) (by omega)
        (row3large_lt hN q) hqf
    exact support3large hN q s hnotqf

theorem allRank (r N : ℕ) (hr : 2 ≤ r) (hN : r + 2 ≤ N)
    (h : NeZero (2 * N)) :
    ∃ row col : Fin (2 * r) → ℕ,
      (∀ q, row q < 2 * N ∧ col q < 2 * N) ∧
      (Matrix.of fun q s => cuspProduct (r := r) h
        (row q : ZMod (2 * N)) (col s : ZMod (2 * N))).det ≠ 0 := by
  by_cases hr2 : r = 2
  · subst r
    refine ⟨row2, col2, ?_, ?_⟩
    · intro q
      exact ⟨row2_lt hN q, col2_lt hN q⟩
    · exact minor2 N hN h
  by_cases hr3 : r = 3
  · subst r
    by_cases hN5 : N = 5
    · subst N
      refine ⟨row3small, col3small, ?_, ?_⟩
      · intro q
        fin_cases q <;> simp [row3small, col3small]
      · exact minor3small h
    · have hN6 : 6 ≤ N := by omega
      refine ⟨row3large N, col3large, ?_, ?_⟩
      · intro q
        exact ⟨row3large_lt hN6 q, col3large_lt hN6 q⟩
      · exact minor3large N hN6 h
  · have hr4 : 4 ≤ r := by omega
    refine ⟨fun q => rowN r N q.val, fun q => colN r q.val, ?_, ?_⟩
    · intro q
      exact ⟨rowN_lt hr4 hN q.isLt,
        (colN_lt hr4 q.isLt).trans (by omega)⟩
    · exact proof r N hr4 hN h


end Submissions.CuspAllRankMinor.Explicit

