import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
Proof of Jig p14 s55 from the explicit cusp, with no elliptic specialization assumption.
Reuses woshuajolk's kernel-checked s63, s65, s70, s75, s79, s80, s81 proofs.
New work assembles invertible cusp factors, pure ranks, generic mixed ranks and the
canonical Hermitian seed family for every r>=2 and N>=r+2.
-/

namespace Submissions.EllipticBipartiteSeedFamily.CuspAssembly

/- Component: cusp_assembly/Reused.lean -/

/- Reuses the kernel-checked Jig p14 proofs s75, s79, s80 and s81 by woshuajolk.
   Original verifier checkout: 2f467d409773c4471b81e08d26ed25c870836aa0.
   Only namespaces and imports of the reused source are changed. -/


namespace Pure.CuspAllRankMinor

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


end Pure.CuspAllRankMinor



namespace Pure.CuspBiClutchedFactorization

open Polynomial
open scoped BigOperators

noncomputable def clutch (k : ℕ) (tau z : ℂ) : Fin k → ℂ := fun q =>
  if q.val = 0 then 1 + tau * z ^ k else z ^ q.val

lemma polynomial_eq_folded {k : ℕ} (hk : 1 ≤ k) (tau : ℂ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ k) (htop : P.coeff k = tau * P.coeff 0) :
    P = Polynomial.ofFn k (fun q => P.coeff q.val) +
      Polynomial.C (tau * P.coeff 0) * Polynomial.X ^ k := by
  ext m
  by_cases hm : m < k
  · rw [Polynomial.coeff_add, Polynomial.ofFn_coeff_eq_val_of_lt _ hm,
      Polynomial.coeff_C_mul_X_pow]
    simp [Nat.ne_of_lt hm]
  · have hkm : k ≤ m := Nat.le_of_not_gt hm
    rw [Polynomial.coeff_add, Polynomial.ofFn_coeff_eq_zero_of_ge _ hkm,
      zero_add, Polynomial.coeff_C_mul_X_pow]
    by_cases hmk : m = k
    · subst m
      simp [htop]
    · have hzero : P.coeff m = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [hmk, hzero]

lemma eval_eq_clutch_sum {k : ℕ} (hk : 1 ≤ k) (tau z : ℂ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ k) (htop : P.coeff k = tau * P.coeff 0) :
    P.eval z = ∑ q : Fin k, P.coeff q.val * clutch k tau z q := by
  have hP := polynomial_eq_folded hk tau P hdeg htop
  conv_lhs => rw [hP]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, clutch]
  let q0 : Fin k := ⟨0, hk⟩
  have hsplit (f : Fin k → ℂ) :
      ∑ q, f q = f q0 + ∑ q ∈ Finset.univ.erase q0, f q := by
    exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ q0)).symm
  rw [hsplit (fun q => P.coeff q.val * z ^ q.val),
    hsplit (fun q => P.coeff q.val *
      (if q.val = 0 then 1 + tau * z ^ k else z ^ q.val))]
  simp only [q0, pow_zero, mul_one, if_pos]
  have hrest :
      ∑ q ∈ Finset.univ.erase q0, P.coeff q.val * z ^ q.val =
        ∑ q ∈ Finset.univ.erase q0,
          P.coeff q.val *
            (if q.val = 0 then 1 + tau * z ^ k else z ^ q.val) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : q ≠ q0 := by simpa using hq
    have hqv : q.val ≠ 0 := fun h => hq0 (Fin.ext (by simpa [q0] using h))
    simp [hqv]
  rw [← hrest]
  ring

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) := (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

noncomputable def cuspProduct {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) : ℂ := by
  letI := h
  exact
    (∏ c : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c))) *
      (∏ d : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)))

noncomputable def directPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar j) -
    C (ZMod.stdAddChar (cOffset (r := r) (N := N) c)) * X

noncomputable def antiPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar j) * X -
    C (ZMod.stdAddChar (dOffset (r := r) (N := N) d))

noncomputable def cuspPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) : ℂ[X] :=
  (∏ c : Fin r, directPoly (r := r) (N := N) j c) *
    (∏ d : Fin r, antiPoly (r := r) (N := N) j d)

lemma anti_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (d : Fin r) :
    (antiPoly j d).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar i *
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)) := by
  simp only [antiPoly, eval_sub, eval_mul, eval_C, eval_X]
  rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  have hi : ZMod.stdAddChar i ≠ 0 := by simp [ZMod.stdAddChar_apply]
  field_simp

lemma direct_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (c : Fin r) :
    (directPoly j c).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c) := by
  simp [directPoly, AddChar.map_add_eq_mul]
  ring

lemma cuspPoly_eval {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j := by
  letI := h
  simp only [cuspPoly, eval_mul, eval_prod, direct_eval, anti_eval, cuspProduct]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma char_ne_zero {N : ℕ} [NeZero N] (i : ZMod N) :
    ZMod.stdAddChar i ≠ 0 := by
  simp [ZMod.stdAddChar_apply]

lemma direct_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) : (directPoly j c).natDegree = 1 := by
  have hc : ZMod.stdAddChar (cOffset (r := r) (N := N) c) ≠ 0 :=
    char_ne_zero _
  have hterm :
      (C (ZMod.stdAddChar (cOffset (r := r) (N := N) c)) * X).natDegree = 1 := by
    rw [natDegree_mul]
    · simp
    · exact C_ne_zero.mpr hc
    · exact (X_ne_zero : (X : ℂ[X]) ≠ 0)
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans (by simp [directPoly, hterm])
  · simp [directPoly, char_ne_zero]

lemma anti_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) : (antiPoly j d).natDegree = 1 := by
  simp [antiPoly, char_ne_zero]

lemma direct_leadingCoeff {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) :
    (directPoly j c).leadingCoeff =
      -ZMod.stdAddChar (cOffset (r := r) (N := N) c) := by
  rw [← coeff_natDegree, direct_natDegree]
  simp [directPoly]

lemma anti_leadingCoeff {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) :
    (antiPoly j d).leadingCoeff = ZMod.stdAddChar j := by
  rw [← coeff_natDegree, anti_natDegree]
  simp [antiPoly]

lemma cuspPoly_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) : (cuspPoly (r := r) j).natDegree = 2 * r := by
  have hc (c : Fin r) : directPoly j c ≠ 0 := by
    intro hz
    have hdeg := direct_natDegree j c
    simp [hz] at hdeg
  have hd (d : Fin r) : antiPoly j d ≠ 0 := by
    intro hz
    have hdeg := anti_natDegree j d
    simp [hz] at hdeg
  have hcprod : (∏ c : Fin r, directPoly j c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => hc c)
  have hdprod : (∏ d : Fin r, antiPoly j d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun d _ => hd d)
  simp only [cuspPoly]
  rw [natDegree_mul hcprod hdprod,
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun c : Fin r => directPoly j c) (fun c _ => hc c),
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun d : Fin r => antiPoly j d) (fun d _ => hd d)]
  simp [direct_natDegree, anti_natDegree]
  omega

noncomputable def cLead (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  ∏ c : Fin r, -ZMod.stdAddChar (cOffset (N := N) c)

noncomputable def dConst (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  ∏ d : Fin r, -ZMod.stdAddChar (dOffset (N := N) d)

noncomputable def tauZ (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  cLead r N / dConst r N

lemma cLead_ne_zero (r N : ℕ) [NeZero (2 * N)] : cLead r N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro c hc
  simp [char_ne_zero]

lemma dConst_ne_zero (r N : ℕ) [NeZero (2 * N)] : dConst r N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro d hd
  simp [char_ne_zero]

lemma cuspPoly_coeff_zero {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff 0 = ZMod.stdAddChar j ^ r * dConst r N := by
  rw [coeff_zero_eq_eval_zero]
  simp only [cuspPoly, eval_mul, eval_prod, directPoly, antiPoly,
    eval_sub, eval_C, eval_mul, eval_X, mul_zero, sub_zero, zero_mul, zero_sub]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma cuspPoly_coeff_top {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff (2 * r) = cLead r N * ZMod.stdAddChar j ^ r := by
  rw [← cuspPoly_natDegree j, coeff_natDegree]
  simp only [cuspPoly, leadingCoeff_mul, Polynomial.leadingCoeff_prod,
    direct_leadingCoeff, anti_leadingCoeff, cLead]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma cuspPoly_boundary {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff (2 * r) =
      tauZ r N * (cuspPoly (r := r) j).coeff 0 := by
  rw [cuspPoly_coeff_top, cuspPoly_coeff_zero]
  unfold tauZ
  field_simp [dConst_ne_zero]

theorem cusp_left_clutch {r N : ℕ} (hr : 1 ≤ r) (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
      ∑ q : Fin (2 * r),
        (cuspPoly (r := r) j).coeff q.val *
          clutch (2 * r) (tauZ r N)
            (ZMod.stdAddChar i) q := by
  letI := h
  rw [← cuspPoly_eval h i j]
  apply eval_eq_clutch_sum
  · omega
  · rw [cuspPoly_natDegree]
  · exact cuspPoly_boundary j

noncomputable def rightDirect {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (c : Fin r) : ℂ[X] :=
  X - C (ZMod.stdAddChar (cOffset (r := r) (N := N) c) * ZMod.stdAddChar i)

noncomputable def rightAnti {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (d : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar i) * X -
    C (ZMod.stdAddChar (dOffset (r := r) (N := N) d))

noncomputable def rightPoly {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) : ℂ[X] :=
  (∏ c : Fin r, rightDirect (r := r) (N := N) i c) *
    (∏ d : Fin r, rightAnti (r := r) (N := N) i d)

lemma rightDirect_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (c : Fin r) :
    (rightDirect i c).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c) := by
  simp [rightDirect, AddChar.map_add_eq_mul]
  ring

lemma rightAnti_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (d : Fin r) :
    (rightAnti i d).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar i *
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)) := by
  simp only [rightAnti, eval_sub, eval_mul, eval_C, eval_X]
  rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  have hi : ZMod.stdAddChar i ≠ 0 := char_ne_zero i
  field_simp

lemma rightPoly_eval {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    (rightPoly (r := r) i).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j := by
  letI := h
  simp only [rightPoly, eval_mul, eval_prod, rightDirect_eval, rightAnti_eval,
    cuspProduct]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma rightDirect_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (c : Fin r) : (rightDirect i c).natDegree = 1 := by
  simpa only [rightDirect] using
    (natDegree_X_sub_C
      (ZMod.stdAddChar (cOffset (r := r) (N := N) c) * ZMod.stdAddChar i))

lemma rightAnti_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (d : Fin r) : (rightAnti i d).natDegree = 1 := by
  simp [rightAnti, char_ne_zero]

lemma rightPoly_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) : (rightPoly (r := r) i).natDegree = 2 * r := by
  have hc (c : Fin r) : rightDirect i c ≠ 0 := by
    intro hz
    have hdeg := rightDirect_natDegree i c
    simp [hz] at hdeg
  have hd (d : Fin r) : rightAnti i d ≠ 0 := by
    intro hz
    have hdeg := rightAnti_natDegree i d
    simp [hz] at hdeg
  have hcprod : (∏ c : Fin r, rightDirect i c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => hc c)
  have hdprod : (∏ d : Fin r, rightAnti i d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun d _ => hd d)
  simp only [rightPoly]
  rw [natDegree_mul hcprod hdprod,
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun c : Fin r => rightDirect i c) (fun c _ => hc c),
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun d : Fin r => rightAnti i d) (fun d _ => hd d)]
  simp [rightDirect_natDegree, rightAnti_natDegree]
  omega

noncomputable def tauX (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  (cLead r N * dConst r N)⁻¹

lemma rightPoly_coeff_zero {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff 0 =
      cLead r N * dConst r N * ZMod.stdAddChar i ^ r := by
  rw [coeff_zero_eq_eval_zero]
  simp only [rightPoly, eval_mul, eval_prod, rightDirect, rightAnti,
    eval_sub, eval_X, eval_C, zero_mul, zero_sub, mul_zero, cLead, dConst]
  simp_rw [show ∀ c : Fin r,
    -(ZMod.stdAddChar (cOffset (N := N) c) * ZMod.stdAddChar i) =
      (-ZMod.stdAddChar (cOffset (N := N) c)) * ZMod.stdAddChar i by
        intro c; ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma rightPoly_coeff_top {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff (2 * r) = ZMod.stdAddChar i ^ r := by
  rw [← rightPoly_natDegree i, coeff_natDegree]
  simp only [rightPoly, leadingCoeff_mul, Polynomial.leadingCoeff_prod]
  have hc : ∀ c : Fin r, (rightDirect i c).leadingCoeff = 1 := by
    intro c
    rw [← coeff_natDegree, rightDirect_natDegree]
    simp [rightDirect]
  have hd : ∀ d : Fin r, (rightAnti i d).leadingCoeff = ZMod.stdAddChar i := by
    intro d
    rw [← coeff_natDegree, rightAnti_natDegree]
    simp [rightAnti]
  simp_rw [hc, hd]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp

lemma rightPoly_boundary {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff (2 * r) =
      tauX r N * (rightPoly (r := r) i).coeff 0 := by
  rw [rightPoly_coeff_top, rightPoly_coeff_zero]
  unfold tauX
  field_simp [cLead_ne_zero r N, dConst_ne_zero r N]

theorem cusp_right_clutch {r N : ℕ} (hr : 1 ≤ r) (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
      ∑ q : Fin (2 * r),
        (rightPoly (r := r) i).coeff q.val *
          clutch (2 * r) (tauX r N)
            (ZMod.stdAddChar j) q := by
  letI := h
  rw [← rightPoly_eval h i j]
  apply eval_eq_clutch_sum
  · omega
  · rw [rightPoly_natDegree]
  · exact rightPoly_boundary i

theorem proof :
    ∀ (r N : ℕ), 1 ≤ r → ∀ h : NeZero (2 * N),
      ∃ (tauL tauR : ℂ)
        (L R : ZMod (2 * N) → Fin (2 * r) → ℂ),
        tauL ≠ 0 ∧ tauR ≠ 0 ∧
        ∀ i j : ZMod (2 * N),
          (ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
            ∑ q, L j q * clutch (2 * r) tauL (ZMod.stdAddChar i) q) ∧
          (ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
            ∑ q, R i q * clutch (2 * r) tauR (ZMod.stdAddChar j) q) := by
  intro r N hr h
  letI := h
  refine ⟨tauZ r N, tauX r N,
    fun j q => (cuspPoly (r := r) j).coeff q.val,
    fun i q => (rightPoly (r := r) i).coeff q.val, ?_, ?_, ?_⟩
  · exact div_ne_zero (cLead_ne_zero r N) (dConst_ne_zero r N)
  · exact inv_ne_zero (mul_ne_zero (cLead_ne_zero r N) (dConst_ne_zero r N))
  · intro i j
    exact ⟨cusp_left_clutch hr h i j, cusp_right_clutch hr h i j⟩

end Pure.CuspBiClutchedFactorization


namespace Pure.ClutchedVandermondeRanks

open Matrix

noncomputable def clutch (k : ℕ) (tau z : ℂ) : Fin k → ℂ := fun q =>
  if q.val = 0 then 1 + tau * z ^ k else z ^ q.val

lemma clutch_kminus1_independent {k n : ℕ} (hk : 2 ≤ k)
    (tau : ℂ) (z : Fin n → ℂ) (hz : Function.Injective z)
    (hnz : ∀ i, z i ≠ 0) (f : Fin (k - 1) → Fin n)
    (hf : Function.Injective f) :
    LinearIndependent ℂ (fun i => clutch k tau (z (f i))) := by
  let D : (Fin k → ℂ) →ₗ[ℂ] (Fin (k - 1) → ℂ) :=
    LinearMap.pi (fun q => LinearMap.proj (R := ℂ)
      (⟨q.val + 1, by omega⟩ : Fin k))
  let A : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ :=
    fun i q => z (f i) ^ (q.val + 1)
  have hA : A = Matrix.diagonal (fun i => z (f i)) *
      Matrix.vandermonde (z ∘ f) := by
    ext i q
    simp [A, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vandermonde_apply,
      pow_succ']
  have hdet : A.det ≠ 0 := by
    rw [hA, Matrix.det_mul, Matrix.det_diagonal]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hnz (f i))
    · exact Matrix.det_vandermonde_ne_zero_iff.mpr (hz.comp hf)
  have hrows : LinearIndependent ℂ (fun i => A i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  apply LinearIndependent.of_comp D
  have hDA : (fun i => D (clutch k tau (z (f i)))) = fun i => A i := by
    funext i q
    simp [D, A, clutch]
  change LinearIndependent ℂ (fun i => D (clutch k tau (z (f i))))
  rw [hDA]
  exact hrows

lemma clutch_kplus1_spanning {k n : ℕ} (hk : 2 ≤ k)
    (tau : ℂ) (z : Fin n → ℂ) (hz : Function.Injective z)
    (f : Fin (k + 1) → Fin n) (hf : Function.Injective f) :
    Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) = ⊤ := by
  classical
  by_contra htop
  have hlt : Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) < ⊤ :=
    lt_top_iff_ne_top.mpr htop
  obtain ⟨phi, hphi, hker⟩ :=
    (Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i)))).exists_le_ker_of_lt_top hlt
  let b : Module.Basis (Fin k) ℂ (Fin k → ℂ) := Pi.basisFun ℂ (Fin k)
  let term : Fin k → _root_.Polynomial ℂ := fun q =>
    Polynomial.C (phi (b q)) *
      if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
      else Polynomial.X ^ q.val
  let P : _root_.Polynomial ℂ := ∑ q, term q
  have hphi_clutch (w : ℂ) :
      phi (clutch k tau w) = ∑ q, clutch k tau w q * phi (b q) := by
    conv_lhs => rw [← b.sum_repr (clutch k tau w)]
    simp [b, Pi.basisFun_repr]
  have hPeval (w : ℂ) : P.eval w = phi (clutch k tau w) := by
    rw [hphi_clutch]
    change Polynomial.eval w (∑ q, term q) = _
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [term, Polynomial.eval_mul, Polynomial.eval_C]
    by_cases hq0 : q.val = 0
    · rw [if_pos hq0]
      simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [show clutch k tau w q = 1 + tau * w ^ k by simp [clutch, hq0]]
      ring
    · rw [if_neg hq0]
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      rw [show clutch k tau w q = w ^ q.val by simp [clutch, hq0]]
      ring
  have hPdeg : P.natDegree ≤ k := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q hq
    simp only [term]
    by_cases hq0 : q.val = 0
    · rw [if_pos hq0]
      calc
        (Polynomial.C (phi (b q)) *
            (1 + Polynomial.C tau * Polynomial.X ^ k)).natDegree
            ≤ (Polynomial.C (phi (b q))).natDegree +
              (1 + Polynomial.C tau * Polynomial.X ^ k).natDegree :=
                Polynomial.natDegree_mul_le
        _ ≤ 0 + k := by
          apply Nat.add_le_add
          · simp
          · apply Polynomial.natDegree_add_le_of_degree_le
            · simp
            · exact Polynomial.natDegree_mul_le.trans (by simp)
        _ = k := Nat.zero_add k
    · rw [if_neg hq0]
      calc
        (Polynomial.C (phi (b q)) * Polynomial.X ^ q.val).natDegree
            ≤ (Polynomial.C (phi (b q))).natDegree +
              (Polynomial.X ^ q.val).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + q.val := by simp
        _ ≤ k := by omega
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (hz.comp hf)
    · intro i
      rw [hPeval]
      apply LinearMap.mem_ker.mp
      apply hker
      exact Submodule.subset_span (Set.mem_range_self i)
    · simpa using Nat.lt_succ_of_le hPdeg
  apply hphi
  apply b.ext
  intro q
  have hcoeff : P.coeff q.val = phi (b q) := by
    change (∑ s, term s).coeff q.val = phi (b q)
    rw [Polynomial.finsetSum_coeff]
    calc
      ∑ s, (term s).coeff q.val = (term q).coeff q.val := by
        apply Finset.sum_eq_single q
        · intro s hs hsq
          have hsqval : s.val ≠ q.val := fun h => hsq (Fin.ext h)
          by_cases hs0 : s.val = 0
          · have hq0 : q.val ≠ 0 := fun h => hsq (Fin.ext (hs0.trans h.symm))
            have hqk : q.val ≠ k := Nat.ne_of_lt q.isLt
            change (Polynomial.C (phi (b s)) *
              (if s.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
                else Polynomial.X ^ s.val)).coeff q.val = 0
            rw [if_pos hs0, Polynomial.coeff_C_mul, Polynomial.coeff_add,
              Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow]
            simp [hq0, hqk]
          · change (Polynomial.C (phi (b s)) *
              (if s.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
                else Polynomial.X ^ s.val)).coeff q.val = 0
            rw [if_neg hs0, Polynomial.coeff_C_mul_X_pow]
            simp [Ne.symm hsqval]
        · simp
      _ = phi (b q) := by
        by_cases hq0 : q.val = 0
        · have hk0 : k ≠ 0 := by omega
          change (Polynomial.C (phi (b q)) *
            (if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
              else Polynomial.X ^ q.val)).coeff q.val = phi (b q)
          rw [if_pos hq0, Polynomial.coeff_C_mul, Polynomial.coeff_add,
            Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow]
          simp [hq0, hk0, Ne.symm hk0]
        · change (Polynomial.C (phi (b q)) *
            (if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
              else Polynomial.X ^ q.val)).coeff q.val = phi (b q)
          rw [if_neg hq0, Polynomial.coeff_C_mul_X_pow]
          simp
  rw [hPzero] at hcoeff
  simpa using hcoeff.symm

theorem proof :
  ∀ (k n : ℕ), 2 ≤ k → ∀ (tau : ℂ) (z : Fin n → ℂ),
    Function.Injective z →
      ((∀ (_hnz : ∀ i, z i ≠ 0) (f : Fin (k - 1) → Fin n),
          Function.Injective f →
            LinearIndependent ℂ (fun i => clutch k tau (z (f i)))) ∧
       (∀ (f : Fin (k + 1) → Fin n), Function.Injective f →
          Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) = ⊤)) := by
  intro k n hk tau z hz
  constructor
  · intro hnz f hf
    exact clutch_kminus1_independent hk tau z hz hnz f hf
  · intro f hf
    exact clutch_kplus1_spanning hk tau z hz f hf

end Pure.ClutchedVandermondeRanks


namespace Pure.BifactorizationGlue

open scoped BigOperators

universe u v w

theorem proof
    {ι : Type u} {κ : Type v} {ϕ : Type w}
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ϕ ℂ)
    (D : Matrix ι κ ℂ) (X : Matrix κ ϕ ℂ)
    (C : Matrix ι ϕ ℂ)
    (f : κ → ι) (g : κ → ϕ)
    (hAB : C = A * B) (hDX : C = D * X)
    (hdet : (C.submatrix f g).det ≠ 0) :
    ∃ G : Matrix κ κ ℂ, G.det ≠ 0 ∧ C = A * (G * X) := by
  let Ar : Matrix κ κ ℂ := A.submatrix f id
  let Bs : Matrix κ κ ℂ := B.submatrix id g
  let Dr : Matrix κ κ ℂ := D.submatrix f id
  let Xs : Matrix κ κ ℂ := X.submatrix id g
  have hCselAB : C.submatrix f g = Ar * Bs := by
    rw [hAB]
    ext a b
    simp [Ar, Bs, Matrix.mul_apply]
  have hCselDX : C.submatrix f g = Dr * Xs := by
    rw [hDX]
    ext a b
    simp [Dr, Xs, Matrix.mul_apply]
  have hprodAB : Ar.det * Bs.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hCselAB]
    exact hdet
  have hprodDX : Dr.det * Xs.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hCselDX]
    exact hdet
  have hAr : IsUnit Ar.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodAB).1
  have hBs : IsUnit Bs.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodAB).2
  have hXs : IsUnit Xs.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodDX).2
  have hrows : Ar * B = Dr * X := by
    ext a j
    have hij := congrArg (fun M : Matrix ι ϕ ℂ => M (f a) j)
      (hAB.symm.trans hDX)
    simpa [Ar, Dr, Matrix.mul_apply] using hij
  have hselected : Ar * Bs = Dr * Xs := hCselAB.symm.trans hCselDX
  let G : Matrix κ κ ℂ := Bs * Xs⁻¹
  have hArG : Ar * G = Dr := by
    calc
      Ar * G = (Ar * Bs) * Xs⁻¹ := by simp [G, Matrix.mul_assoc]
      _ = (Dr * Xs) * Xs⁻¹ := by rw [hselected]
      _ = Dr := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Xs hXs, Matrix.mul_one]
  have hArEq : Ar * (G * X) = Ar * B := by
    calc
      Ar * (G * X) = (Ar * G) * X := (Matrix.mul_assoc Ar G X).symm
      _ = Dr * X := by rw [hArG]
      _ = Ar * B := hrows.symm
  have hB : G * X = B := by
    have hmul := congrArg (fun M : Matrix κ ϕ ℂ => Ar⁻¹ * M) hArEq
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Ar hAr] using hmul
  have hGunit : IsUnit G.det := by
    change IsUnit (Bs * Xs⁻¹).det
    rw [Matrix.det_mul]
    exact hBs.mul (Matrix.isUnit_nonsing_inv_det Xs hXs)
  refine ⟨G, isUnit_iff_ne_zero.mp hGunit, ?_⟩
  calc
    C = A * B := hAB
    _ = A * (G * X) := congrArg (fun Y : Matrix κ ϕ ℂ => A * Y) hB.symm

end Pure.BifactorizationGlue


/- Component: cusp_assembly/AssemblyBody.lean -/
namespace Pure

open scoped BigOperators

noncomputable section

theorem cusp_factorization (r N : ℕ) (hr : 2 ≤ r) (hN : r + 2 ≤ N)
    (h : NeZero (2 * N)) :
    ∃ (tauL tauR : ℂ) (G : Matrix (Fin (2 * r)) (Fin (2 * r)) ℂ),
      tauL ≠ 0 ∧ tauR ≠ 0 ∧ G.det ≠ 0 ∧
      ∀ i j : ZMod (2 * N),
        ZMod.stdAddChar i ^ r * CuspAllRankMinor.cuspProduct (r := r) h i j =
          ∑ q, ClutchedVandermondeRanks.clutch (2 * r) tauL (ZMod.stdAddChar i) q *
            (G.mulVec (ClutchedVandermondeRanks.clutch (2 * r) tauR
              (ZMod.stdAddChar j))) q := by
  letI := h
  obtain ⟨tauL, tauR, L, R, htL, htR, hfactor⟩ :=
    CuspBiClutchedFactorization.proof r N (by omega) h
  obtain ⟨row, col, hbounds, hminor⟩ := CuspAllRankMinor.allRank r N hr hN h
  let A : Matrix (ZMod (2 * N)) (Fin (2 * r)) ℂ :=
    fun i q => ClutchedVandermondeRanks.clutch (2 * r) tauL (ZMod.stdAddChar i) q
  let X : Matrix (Fin (2 * r)) (ZMod (2 * N)) ℂ :=
    fun q j => ClutchedVandermondeRanks.clutch (2 * r) tauR (ZMod.stdAddChar j) q
  let B : Matrix (Fin (2 * r)) (ZMod (2 * N)) ℂ := fun q j => L j q
  let D : Matrix (ZMod (2 * N)) (Fin (2 * r)) ℂ := Matrix.of R
  let C : Matrix (ZMod (2 * N)) (ZMod (2 * N)) ℂ :=
    fun i j => ZMod.stdAddChar i ^ r * CuspAllRankMinor.cuspProduct (r := r) h i j
  let f : Fin (2 * r) → ZMod (2 * N) := fun q => (row q : ZMod (2 * N))
  let g : Fin (2 * r) → ZMod (2 * N) := fun q => (col q : ZMod (2 * N))
  have hAB : C = A * B := by
    ext i j
    change C i j = ∑ q, A i q * B q j
    simpa [C, A, B, mul_comm,
      CuspAllRankMinor.cuspProduct, CuspAllRankMinor.cOffset, CuspAllRankMinor.dOffset,
      CuspBiClutchedFactorization.cuspProduct, CuspBiClutchedFactorization.cOffset,
      CuspBiClutchedFactorization.dOffset,
      ClutchedVandermondeRanks.clutch, CuspBiClutchedFactorization.clutch]
      using (hfactor i j).1
  have hRX : C = D * X := by
    ext i j
    change C i j = ∑ q, D i q * X q j
    simpa [C, D, X, Matrix.of_apply,
      CuspAllRankMinor.cuspProduct, CuspAllRankMinor.cOffset, CuspAllRankMinor.dOffset,
      CuspBiClutchedFactorization.cuspProduct, CuspBiClutchedFactorization.cOffset,
      CuspBiClutchedFactorization.dOffset,
      ClutchedVandermondeRanks.clutch, CuspBiClutchedFactorization.clutch]
      using (hfactor i j).2
  have hdet : (C.submatrix f g).det ≠ 0 := by
    have heq : C.submatrix f g =
        Matrix.diagonal (fun q => ZMod.stdAddChar (f q) ^ r) *
          (Matrix.of fun q s => CuspAllRankMinor.cuspProduct (r := r) h (f q) (g s)) := by
      ext q s
      rw [Matrix.diagonal_mul]
      rfl
    rw [heq, Matrix.det_mul, Matrix.det_diagonal]
    apply mul_ne_zero _ hminor
    apply Finset.prod_ne_zero_iff.mpr
    intro q _
    exact pow_ne_zero _ (CuspBiClutchedFactorization.char_ne_zero (f q))
  obtain ⟨G, hG, hC⟩ := BifactorizationGlue.proof A B D X C f g hAB hRX hdet
  refine ⟨tauL, tauR, G, htL, htR, hG, ?_⟩
  intro i j
  have hij := congrArg (fun M => M i j) hC
  change C i j = ∑ q, A i q * (∑ s, G q s * X s j) at hij
  simpa only [C, A, X, Matrix.mulVec, dotProduct] using hij

theorem conjugate_independent {k n : ℕ} {v : Fin n → Fin k → ℂ}
    (hv : LinearIndependent ℂ v) : LinearIndependent ℂ (fun i => star (v i)) := by
  let e := (starLinearEquiv ℂ : (Fin k → ℂ) ≃ₗ⋆[ℂ] (Fin k → ℂ))
  exact hv.map_of_surjective_injective (star : ℂ → ℂ) e.toAddEquiv.toAddMonoidHom
    (star_involutive.surjective) (by intro x hx; exact e.injective (by simpa using hx))
    (by intro c x; simp [e])

theorem conjugate_spanning {k n : ℕ} {v : Fin n → Fin k → ℂ}
    (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => star (v i)) = ⊤ := by
  let e := (starLinearEquiv ℂ : (Fin k → ℂ) ≃ₗ⋆[ℂ] (Fin k → ℂ))
  change Submodule.span ℂ (Set.range (e.toLinearMap ∘ v)) = ⊤
  rw [Set.range_comp, Submodule.span_image, hv]
  exact (Submodule.map_eq_top_iff (e := e)).mpr rfl

theorem matrix_spanning {k n : ℕ} {v : Fin n → Fin k → ℂ}
    (G : Matrix (Fin k) (Fin k) ℂ) (hG : G.det ≠ 0)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => G.mulVec (v i)) = ⊤ := by
  change Submodule.span ℂ (Set.range (G.mulVecLin ∘ v)) = ⊤
  rw [Set.range_comp, Submodule.span_image, hv, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    (Matrix.mulVec_surjective_iff_isUnit.mpr
      (G.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hG)))

/-- The cusp construction already supplies both pure rank conditions in all parameters.
The remaining seed obligation is the simultaneous rank condition on mixed subsets. -/
theorem proof (r N : ℕ) (hr : 2 ≤ r) (hN : r + 2 ≤ N) :
    ∃ x y : Fin (2 * N) → Fin (2 * r) → ℂ,
      (∀ i, x i ≠ 0 ∧ y i ≠ 0) ∧
      (∀ i j, (∑ q, star (x i q) * y j q) = 0 ↔
        CuspAllRankMinor.CrossAdj (r := r) (N := N)
          (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N))) ∧
      (∀ f : Fin (2 * r - 1) → Fin (2 * N), Function.Injective f →
        LinearIndependent ℂ (x ∘ f) ∧ LinearIndependent ℂ (y ∘ f)) ∧
      (∀ f : Fin (2 * r + 1) → Fin (2 * N), Function.Injective f →
        Submodule.span ℂ (Set.range (x ∘ f)) = ⊤ ∧
          Submodule.span ℂ (Set.range (y ∘ f)) = ⊤) := by
  have hN0 : 2 * N ≠ 0 := by omega
  letI : NeZero (2 * N) := ⟨hN0⟩
  obtain ⟨tauL, tauR, G, htL, htR, hG, hf⟩ := cusp_factorization r N hr hN inferInstance
  let z : Fin (2 * N) → ℂ := fun i => ZMod.stdAddChar (i.val : ZMod (2 * N))
  have hz : Function.Injective z := by
    intro a b hab
    apply Fin.ext
    have heq := ZMod.injective_stdAddChar hab
    have hv := congrArg ZMod.val heq
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hv
  have hnz : ∀ i, z i ≠ 0 := by
    intro i
    exact CuspBiClutchedFactorization.char_ne_zero _
  let u := fun i => ClutchedVandermondeRanks.clutch (2 * r) tauL (z i)
  let v := fun i => ClutchedVandermondeRanks.clutch (2 * r) tauR (z i)
  let x := fun i => star (u i)
  let y := fun i => G.mulVec (v i)
  have hu0 (i) : u i ≠ 0 := by
    intro hi
    have hcoord := congrFun hi (⟨1, by omega⟩ : Fin (2 * r))
    exact hnz i (by simpa [u, ClutchedVandermondeRanks.clutch] using hcoord)
  have hv0 (i) : v i ≠ 0 := by
    intro hi
    have hcoord := congrFun hi (⟨1, by omega⟩ : Fin (2 * r))
    exact hnz i (by simpa [v, ClutchedVandermondeRanks.clutch] using hcoord)
  have hGinj : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (G.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hG))
  refine ⟨x, y, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · simpa [x] using hu0 i
    · intro hzero
      apply hv0 i
      exact hGinj (by simpa [y] using hzero)
  · intro i j
    have heq := hf (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N))
    have hpair : (∑ q, star (x i q) * y j q) =
        z i ^ r * CuspAllRankMinor.cuspProduct (r := r) inferInstance
          (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N)) := by
      simpa [x, y, u, v, z] using heq.symm
    rw [hpair, mul_eq_zero]
    simp only [pow_ne_zero r (hnz i), false_or]
    exact CuspAllRankMinor.zeroPattern r N inferInstance _ _
  · intro f hfinj
    constructor
    · exact conjugate_independent
        (ClutchedVandermondeRanks.clutch_kminus1_independent (by omega) tauL z hz hnz f hfinj)
    · exact (ClutchedVandermondeRanks.clutch_kminus1_independent
        (by omega) tauR z hz hnz f hfinj).map' G.mulVecLin
          (LinearMap.ker_eq_bot.mpr hGinj)
  · intro f hfinj
    exact ⟨conjugate_spanning
      (ClutchedVandermondeRanks.clutch_kplus1_spanning (by omega) tauL z hz f hfinj),
      matrix_spanning G hG
        (ClutchedVandermondeRanks.clutch_kplus1_spanning (by omega) tauR z hz f hfinj)⟩

end
end Pure

/- Component: literature/Maximal.lean -/

namespace Maximal

open Submodule

noncomputable section

lemma exists_submodule_finrank_eq_of_le
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (d : ℕ) (hd : d ≤ Module.finrank ℂ U) :
    ∃ D : Submodule ℂ V, D ≤ U ∧ Module.finrank ℂ D = d := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hd
  let g : Fin d → V := fun i => (f i : V)
  have hg : LinearIndependent ℂ g :=
    hf.map' U.subtype U.ker_subtype
  refine ⟨Submodule.span ℂ (Set.range g), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).property
  · simpa [g] using (finrank_span_eq_card hg)

lemma exists_target_subspace
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Submodule ℂ V) (b : ℕ) (hbV : b ≤ Module.finrank ℂ V) :
    ∃ W' : Submodule ℂ V,
      Module.finrank ℂ W' = b ∧
      Module.finrank ℂ (U ⊔ W' : Submodule ℂ V) =
        min (Module.finrank ℂ V) (Module.finrank ℂ U + b) := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  have hdim : Module.finrank ℂ U + Module.finrank ℂ C = Module.finrank ℂ V :=
    Submodule.finrank_add_eq_of_isCompl hC
  by_cases hbC : b ≤ Module.finrank ℂ C
  · obtain ⟨D, hDC, hD⟩ := exists_submodule_finrank_eq_of_le C b hbC
    have hUD : Disjoint U D := hC.disjoint.mono_right hDC
    refine ⟨D, hD, ?_⟩
    have hsum : Module.finrank ℂ (U ⊔ D : Submodule ℂ V) =
        Module.finrank ℂ U + b := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq U D
      rw [hUD.eq_bot, finrank_bot, add_zero, hD] at h
      exact h
    rw [hsum, Nat.min_eq_right]
    omega
  · have hCb : Module.finrank ℂ C < b := Nat.lt_of_not_ge hbC
    have hsub : b - Module.finrank ℂ C ≤ Module.finrank ℂ U := by omega
    obtain ⟨A, hAU, hA⟩ :=
      exists_submodule_finrank_eq_of_le U (b - Module.finrank ℂ C) hsub
    have hCA : Disjoint C A := hC.symm.disjoint.mono_right hAU
    refine ⟨C ⊔ A, ?_, ?_⟩
    · have h := Submodule.finrank_sup_add_finrank_inf_eq C A
      rw [hCA.eq_bot, finrank_bot, add_zero, hA] at h
      omega
    · have htop : U ⊔ (C ⊔ A) = ⊤ := by
        simp [← sup_assoc, hC.codisjoint.eq_top]
      rw [htop, finrank_top, Nat.min_eq_left]
      omega

lemma exists_linearEquiv_map_eq_of_finrank_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W W' : Submodule ℂ V)
    (hrank : Module.finrank ℂ W = Module.finrank ℂ W') :
    ∃ g : V ≃ₗ[ℂ] V, W.map g.toLinearMap = W' := by
  let f : W ≃ₗ[ℂ] W' :=
    Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hfx : (f ⟨x, hx⟩ : V) ∈ W' := (f ⟨x, hx⟩).property
    simpa [hg ⟨x, hx⟩] using hfx
  · rw [g.finrank_map_eq, hrank]

theorem proof :
    ∀ k : ℕ, ∀ U W : Submodule ℂ (Fin k → ℂ),
      ∃ g : (Fin k → ℂ) ≃ₗ[ℂ] (Fin k → ℂ),
        Module.finrank ℂ
            (U ⊔ W.map g.toLinearMap : Submodule ℂ (Fin k → ℂ)) =
          min k (Module.finrank ℂ U + Module.finrank ℂ W) := by
  intro k U W
  have hVk : Module.finrank ℂ (Fin k → ℂ) = k := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hWk : Module.finrank ℂ W ≤ Module.finrank ℂ (Fin k → ℂ) :=
    Submodule.finrank_le W
  obtain ⟨W', hW', hUW'⟩ :=
    exists_target_subspace U (Module.finrank ℂ W) hWk
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' hW'.symm
  refine ⟨g, ?_⟩
  rw [hg, hUW', hVk]

end

end Maximal

/- Component: elliptic_audit/HermitianAssembly.lean -/


/-! Reused, attributed kernel-green Jig p14 lemmas s63 and s70.
The s63 Gram construction is retained before its positive-definite wrapper,
so its already-constructed invertible factor need not be recovered by CFC.sqrt.
The unused s63 coordinate-minor/subspace helpers are omitted; s70 is retained. -/


/-!
# Finite positive-Hermitian genericity

This file gives an algebraic replacement for the informal assertion that the
positive-definite Hermitian cone is Zariski dense.  The key construction pulls
a polynomial in a matrix `K` back along `K = star L * L`, writes the entries of
`L` in independent real and imaginary coordinates, and proves that this
pullback is injective by an explicit polynomial retraction.

No measure theory, classical Zariski topology, or unproved density statement is
used.
-/

namespace P14Hermitian.GreenGenericity

open Matrix MvPolynomial
open scoped Matrix ComplexConjugate

noncomputable section

abbrev MatVar (k : ℕ) := Fin k × Fin k

/-- Real and imaginary coordinate variables for a complex matrix. -/
abbrev GramVar (k : ℕ) := Bool × Fin k × Fin k

private def delta {k : ℕ} (i j : Fin k) : ℂ :=
  if i = j then 1 else 0

/-- The polynomial matrix `L = A + iB`. -/
def lPoly {k : ℕ} (i j : Fin k) : MvPolynomial (GramVar k) ℂ :=
  X (false, i, j) + C Complex.I * X (true, i, j)

/-- The entrywise conjugate polynomial matrix `A - iB`. -/
def lBarPoly {k : ℕ} (i j : Fin k) : MvPolynomial (GramVar k) ℂ :=
  X (false, i, j) - C Complex.I * X (true, i, j)

/-- The universal Gram-matrix entry `(LᴴL)ᵢⱼ`. -/
def gramEntry {k : ℕ} (ij : MatVar k) : MvPolynomial (GramVar k) ℂ :=
  ∑ r : Fin k, lBarPoly r ij.1 * lPoly r ij.2

/-- Pullback of matrix polynomials along `K = LᴴL`. -/
def gramPull {k : ℕ} :
    MvPolynomial (MatVar k) ℂ →ₐ[ℂ] MvPolynomial (GramVar k) ℂ :=
  bind₁ gramEntry

/-- Polynomial substitution used as a left inverse of `gramPull`.

It imposes `A + iB = X` and `A - iB = 1`.
-/
def gramRetractCoord {k : ℕ} (v : GramVar k) :
    MvPolynomial (MatVar k) ℂ :=
  if v.1 then
    C ((2 * Complex.I)⁻¹) *
      (X (v.2.1, v.2.2) - C (delta v.2.1 v.2.2))
  else
    C ((2 : ℂ)⁻¹) *
      (X (v.2.1, v.2.2) + C (delta v.2.1 v.2.2))

def gramRetract {k : ℕ} :
    MvPolynomial (GramVar k) ℂ →ₐ[ℂ] MvPolynomial (MatVar k) ℂ :=
  bind₁ gramRetractCoord

lemma gramRetract_lPoly {k : ℕ} (i j : Fin k) :
    gramRetract (lPoly i j) = X (i, j) := by
  simp only [gramRetract, lPoly, map_add, map_mul, bind₁_X_right,
    gramRetractCoord, Bool.false_eq_true, if_false, if_true, map_C]
  rw [show (2 * Complex.I : ℂ)⁻¹ = -Complex.I / 2 by
    field_simp [Complex.I_ne_zero]
    simpa [pow_two] using congrArg Neg.neg Complex.I_mul_I]
  norm_num
  have hI :
      (C Complex.I : MvPolynomial (MatVar k) ℂ) *
          C (-Complex.I / 2) = C (1 / 2) := by
    rw [← map_mul]
    apply congrArg C
    calc
      Complex.I * (-Complex.I / 2) =
          -(Complex.I * Complex.I) / 2 := by ring
      _ = 1 / 2 := by rw [Complex.I_mul_I]; ring
  rw [← mul_assoc (C Complex.I), hI]
  ring_nf
  calc
    C (1 / 2 : ℂ) * X (i, j) * 2 =
        (C (1 / 2 : ℂ) * C (2 : ℂ)) * X (i, j) := by
          rw [show (2 : MvPolynomial (MatVar k) ℂ) = C (2 : ℂ) from
            (map_ofNat C 2).symm]
          ring
    _ = X (i, j) := by rw [← map_mul]; norm_num

lemma gramRetract_lBarPoly {k : ℕ} (i j : Fin k) :
    gramRetract (lBarPoly i j) = C (delta i j) := by
  simp only [gramRetract, lBarPoly, map_sub, map_mul, bind₁_X_right,
    gramRetractCoord, Bool.false_eq_true, if_false, if_true, map_C]
  rw [show (2 * Complex.I : ℂ)⁻¹ = -Complex.I / 2 by
    field_simp [Complex.I_ne_zero]
    simpa [pow_two] using congrArg Neg.neg Complex.I_mul_I]
  norm_num
  have hI :
      (C Complex.I : MvPolynomial (MatVar k) ℂ) *
          C (-Complex.I / 2) = C (1 / 2) := by
    rw [← map_mul]
    apply congrArg C
    calc
      Complex.I * (-Complex.I / 2) =
          -(Complex.I * Complex.I) / 2 := by ring
      _ = 1 / 2 := by rw [Complex.I_mul_I]; ring
  rw [← mul_assoc (C Complex.I), hI]
  ring_nf
  calc
    C (1 / 2 : ℂ) * C (delta i j) * 2 =
        (C (1 / 2 : ℂ) * C (2 : ℂ)) * C (delta i j) := by
          rw [show (2 : MvPolynomial (MatVar k) ℂ) = C (2 : ℂ) from
            (map_ofNat C 2).symm]
          ring
    _ = C (delta i j) := by rw [← map_mul]; norm_num

/-- The explicit polynomial retraction sends a universal Gram entry back to
the corresponding universal matrix variable. -/
lemma gramRetract_gramEntry {k : ℕ} (ij : MatVar k) :
    gramRetract (gramEntry ij) = X ij := by
  rcases ij with ⟨i, j⟩
  simp only [gramEntry, map_sum, map_mul, gramRetract_lBarPoly,
    gramRetract_lPoly]
  simp [delta, X]

/-- Missing local lemma 1: the Hermitian Gram pullback on matrix polynomials is
injective. -/
lemma gramPull_injective {k : ℕ} : Function.Injective (gramPull (k := k)) := by
  intro p q hpq
  have h := congrArg (fun f => gramRetract (k := k) f) hpq
  rw [gramPull, gramRetract, bind₁_bind₁, bind₁_bind₁] at h
  have hc :
      (fun i : MatVar k => (bind₁ gramRetractCoord) (gramEntry i)) =
        (X : MatVar k → MvPolynomial (MatVar k) ℂ) := by
    funext i
    exact gramRetract_gramEntry i
  rw [hc] at h
  simpa only [bind₁_X_left, AlgHom.id_apply] using h

/-- The determinant of the polynomial matrix `L`. -/
def lDetPoly {k : ℕ} : MvPolynomial (GramVar k) ℂ :=
  Matrix.det (Matrix.of fun i j : Fin k => lPoly i j)

private def identityGramEval {k : ℕ} : GramVar k → ℂ
  | (false, i, j) => delta i j
  | (true, _, _) => 0

lemma eval_lPoly_identity {k : ℕ} (i j : Fin k) :
    eval (identityGramEval (k := k)) (lPoly i j) = delta i j := by
  simp [lPoly, identityGramEval]

lemma lDetPoly_ne_zero {k : ℕ} : lDetPoly (k := k) ≠ 0 := by
  intro h
  have hz : eval (identityGramEval (k := k)) (lDetPoly (k := k)) = 0 := by
    simp [h]
  have ho : eval (identityGramEval (k := k)) (lDetPoly (k := k)) = 1 := by
    unfold lDetPoly
    rw [(eval (identityGramEval (k := k))).map_det]
    convert Matrix.det_one (n := Fin k)
    ext i j
    simp [eval_lPoly_identity, delta, Matrix.one_apply]
  exact one_ne_zero (ho.symm.trans hz)

/-- A valuation of all Gram coordinates by embedded real numbers. -/
def IsRealValuation {k : ℕ} (z : GramVar k → ℂ) : Prop :=
  z ∈ Set.pi Set.univ (fun _ => Set.range ((↑) : ℝ → ℂ))

lemma exists_real_eval_ne_zero {k : ℕ}
    (p : MvPolynomial (GramVar k) ℂ) (hp : p ≠ 0) :
    ∃ z : GramVar k → ℂ, IsRealValuation z ∧ eval z p ≠ 0 := by
  by_contra h
  push_neg at h
  apply hp
  apply funext_set (fun _ : GramVar k => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  simpa [h z hz]

private def realPartOfValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (v : GramVar k) : ℝ :=
  Classical.choose (hz v (Set.mem_univ v))

private lemma ofReal_realPartOfValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (v : GramVar k) :
    (realPartOfValuation z hz v : ℂ) = z v :=
  Classical.choose_spec (hz v (Set.mem_univ v))

def matrixEntryOfRealValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) : ℂ :=
    (realPartOfValuation z hz (false, i, j) : ℂ) +
      Complex.I * (realPartOfValuation z hz (true, i, j) : ℂ)

def matrixOfRealValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of (matrixEntryOfRealValuation z hz)

/-- Entrywise formula for `LᴴL`, avoiding any dependence on matrix notation. -/
def gramOf {k : ℕ} (L : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun i j => ∑ r : Fin k, star (L r i) * L r j

lemma gramOf_eq_conjTranspose_mul {k : ℕ}
    (L : Matrix (Fin k) (Fin k) ℂ) :
    gramOf L = L.conjTranspose * L := by
  ext i j
  simp [gramOf, Matrix.mul_apply, conjTranspose_apply]

lemma eval_lPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (lPoly i j) =
      matrixEntryOfRealValuation z hz i j := by
  rw [show eval z (lPoly i j) =
      z (false, i, j) + Complex.I * z (true, i, j) by
    simp [lPoly]]
  rw [← ofReal_realPartOfValuation z hz (false, i, j),
    ← ofReal_realPartOfValuation z hz (true, i, j)]
  rfl

lemma eval_lBarPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (lBarPoly i j) =
      star (matrixEntryOfRealValuation z hz i j) := by
  rw [show eval z (lBarPoly i j) =
      z (false, i, j) - Complex.I * z (true, i, j) by
    simp [lBarPoly]]
  rw [← ofReal_realPartOfValuation z hz (false, i, j),
    ← ofReal_realPartOfValuation z hz (true, i, j)]
  unfold matrixEntryOfRealValuation
  rw [sub_eq_add_neg]
  change _ = conj
    ((realPartOfValuation z hz (false, i, j) : ℂ) +
      Complex.I * (realPartOfValuation z hz (true, i, j) : ℂ))
  simp

lemma eval_gramEntry_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (gramEntry (i, j)) =
      ∑ r : Fin k,
        star (matrixEntryOfRealValuation z hz r i) *
          matrixEntryOfRealValuation z hz r j := by
  rw [gramEntry, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_mul, eval_lPoly_realValuation, eval_lBarPoly_realValuation]

lemma eval_gramPull_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (p : MvPolynomial (MatVar k) ℂ) :
    eval z (gramPull p) =
      eval (fun ij =>
        ∑ r : Fin k,
          star (matrixEntryOfRealValuation z hz r ij.1) *
            matrixEntryOfRealValuation z hz r ij.2) p := by
  rw [gramPull]
  change aeval z (bind₁ gramEntry p) = _
  rw [aeval_bind₁]
  apply congrArg (fun f => eval f p)
  funext ij
  exact eval_gramEntry_realValuation z hz ij.1 ij.2

lemma eval_lDetPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) :
    eval z (lDetPoly (k := k)) =
      (matrixOfRealValuation (k := k) z hz).det := by
  unfold lDetPoly
  rw [(eval z).map_det]
  apply congrArg Matrix.det
  ext i j
  simpa [matrixOfRealValuation] using eval_lPoly_realValuation z hz i j

/-- The published s63 construction already supplies an invertible Gram factor.
Retaining it avoids subsequently recovering the factor by a matrix square root. -/
theorem exists_gram_eval_ne_zero {k : ℕ}
    (p : MvPolynomial (MatVar k) ℂ) (hp : p ≠ 0) :
    ∃ L : Matrix (Fin k) (Fin k) ℂ, IsUnit L ∧
      eval (fun ij => (L.conjTranspose * L) ij.1 ij.2) p ≠ 0 := by
  have hgp : gramPull p ≠ 0 := (gramPull_injective (k := k)).ne hp
  have hprod : gramPull p * lDetPoly (k := k) ≠ 0 :=
    mul_ne_zero hgp lDetPoly_ne_zero
  obtain ⟨z, hz, hzeval⟩ := exists_real_eval_ne_zero
    (gramPull p * lDetPoly (k := k)) hprod
  let L := matrixOfRealValuation z hz
  have hsplit :
      eval z (gramPull p) * eval z (lDetPoly (k := k)) ≠ 0 := by
    simpa [map_mul] using hzeval
  have hgram : eval z (gramPull p) ≠ 0 :=
    fun h => hsplit (by simp [h])
  have hdetEval : eval z (lDetPoly (k := k)) ≠ 0 :=
    fun h => hsplit (by simp [h])
  have hdet : L.det ≠ 0 := by
    rw [eval_lDetPoly_realValuation z hz] at hdetEval
    exact hdetEval
  have hL : IsUnit L :=
    (Matrix.isUnit_iff_isUnit_det L).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨L, hL, ?_⟩
  rw [eval_gramPull_realValuation z hz] at hgram
  simpa only [← gramOf_eq_conjTranspose_mul, L, gramOf, matrixOfRealValuation, Matrix.of_apply] using hgram

theorem finite_gram_genericity {k : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial (MatVar k) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ L : Matrix (Fin k) (Fin k) ℂ, IsUnit L ∧
      ∀ i, eval (fun ij => (L.conjTranspose * L) ij.1 ij.2) (p i) ≠ 0 := by
  classical
  obtain ⟨L, hL, hprod⟩ := exists_gram_eval_ne_zero (∏ i, p i)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  refine ⟨L, hL, ?_⟩
  rw [map_prod] at hprod
  exact fun i => Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)

end

end P14Hermitian.GreenGenericity


namespace P14Hermitian.GreenMixedMinor

open Matrix MvPolynomial

noncomputable section

abbrev MatVar (k : ℕ) := Fin k × Fin k

def universalMat {k : ℕ} :
    Matrix (Fin k) (Fin k) (MvPolynomial (MatVar k) ℂ) :=
  fun i j => X (i, j)

def mixedPolyVec {k d : ℕ} (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ) (q : Fin d) :
    Fin k → MvPolynomial (MatVar k) ℂ :=
  if move q then
    (universalMat (k := k)).adjugate.mulVec (fun i => C (v q i))
  else fun i => C (v q i)

lemma eval_universalMat (k : ℕ) (H : Matrix (Fin k) (Fin k) ℂ) :
    (eval (fun ij => H ij.1 ij.2)).mapMatrix (universalMat (k := k)) = H := by
  ext i j
  simp [universalMat]

lemma eval_mixedPolyVec {k d : ℕ} (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ) (q : Fin d)
    (H : Matrix (Fin k) (Fin k) ℂ) :
    (fun i => eval (fun ij => H ij.1 ij.2) (mixedPolyVec move v q i)) =
      if move q then H.adjugate.mulVec (v q) else v q := by
  funext i
  by_cases hq : move q
  · simp only [mixedPolyVec, hq, if_true]
    let z : MatVar k → ℂ := fun ij => H ij.1 ij.2
    have hmat :
        (eval z).mapMatrix (universalMat (k := k)).adjugate = H.adjugate := by
      rw [RingHom.map_adjugate, eval_universalMat]
    calc
      eval z ((universalMat (k := k)).adjugate.mulVec
          (fun j => C (v q j)) i) =
          (((eval z).mapMatrix (universalMat (k := k)).adjugate).mulVec
            (fun j => eval z (C (v q j)))) i := by
              exact RingHom.map_mulVec (eval z) _ _ i
      _ = (H.adjugate.mulVec (v q)) i := by rw [hmat]; simp
  · simp [mixedPolyVec, hq]

lemma adjugate_realizes_invertible {k : ℕ}
    (G : Matrix (Fin k) (Fin k) ℂ) (hG : IsUnit G.det) :
    ∃ (H : Matrix (Fin k) (Fin k) ℂ) (c : ℂ),
      IsUnit H.det ∧ c ≠ 0 ∧ H.adjugate = c • G := by
  let H : Matrix (Fin k) (Fin k) ℂ := G⁻¹
  have hH : IsUnit H.det := G.isUnit_nonsing_inv_det hG
  refine ⟨H, H.det, hH, isUnit_iff_ne_zero.mp hH, ?_⟩
  calc
    H.adjugate = 1 * H.adjugate := by rw [Matrix.one_mul]
    _ = (G * H) * H.adjugate := by
      rw [show G * H = 1 by exact G.mul_nonsing_inv hG]
    _ = G * (H * H.adjugate) := by rw [Matrix.mul_assoc]
    _ = G * (H.det • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
      rw [H.mul_adjugate]
    _ = H.det • G := by rw [Matrix.mul_smul, Matrix.mul_one]

lemma exists_adjugate_rank_witness {k d : ℕ}
    (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ)
    (G : Matrix (Fin k) (Fin k) ℂ) (hG : IsUnit G.det)
    (hli : LinearIndependent ℂ
      (fun q => if move q then G.mulVec (v q) else v q)) :
    ∃ H : Matrix (Fin k) (Fin k) ℂ, IsUnit H.det ∧
      LinearIndependent ℂ
        (fun q => if move q then H.adjugate.mulVec (v q) else v q) := by
  obtain ⟨H, c, hH, hc, hAdj⟩ := adjugate_realizes_invertible G hG
  let base : Fin d → (Fin k → ℂ) :=
    fun q => if move q then G.mulVec (v q) else v q
  let hcUnit : IsUnit c := isUnit_iff_ne_zero.mpr hc
  let scale : Fin d → ℂˣ := fun q => if move q then hcUnit.unit else 1
  have hs : LinearIndependent ℂ (scale • base) := by
    exact hli.units_smul scale
  refine ⟨H, hH, ?_⟩
  convert hs using 1
  funext q i
  by_cases hq : move q
  · simp only [Pi.smul_apply', scale, base, hq, if_true]
    rw [hAdj, Matrix.smul_mulVec]
    simp
  · simp [scale, base, hq]

lemma exists_nonzero_coord_minor {k d : ℕ} (A : Fin d → Fin k → ℂ)
    (hA : LinearIndependent ℂ A) :
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      (Matrix.of fun p q => A q (e p)).det ≠ 0 := by
  classical
  let rows : Fin k → (Fin d → ℂ) := fun i q => A q i
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ rows
  have : Finite κ := LinearIndependent.finite (R := ℂ) (M := Fin d → ℂ) hli
  let : Fintype κ := Fintype.ofFinite κ
  let M : Matrix (Fin d) (Fin k) ℂ := A
  have hfinrank_rows :
      Module.finrank ℂ (Submodule.span ℂ (Set.range rows)) = d := by
    have hA' : LinearIndependent ℂ M.row := hA
    have hr : M.rank = d := by
      simpa [Fintype.card_fin] using (LinearIndependent.rank_matrix (M := M) hA')
    have hrows : rows = M.col := by
      funext i q
      rfl
    rw [hrows, ← rank_eq_finrank_span_cols, hr]
  have hcard : Fintype.card κ = d := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)).mp hli
    rw [Set.finrank] at h
    rw [h, hspan, hfinrank_rows]
  let e : Fin d → Fin k :=
    fun i => a ((Fintype.equivFin κ).symm (Fin.cast hcard.symm i))
  have he : Function.Injective e :=
    ha.comp <| (Fintype.equivFin κ).symm.injective.comp
      (Fin.cast_injective hcard.symm)
  have hli_e : LinearIndependent ℂ (fun i : Fin d => rows (e i)) :=
    hli.comp _ <| (Fintype.equivFin κ).symm.injective.comp
      (Fin.cast_injective hcard.symm)
  refine ⟨e, he, ?_⟩
  let B : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun p q => A q (e p)
  have hrow : LinearIndependent ℂ B.row := by
    have : B.row = fun p : Fin d => rows (e p) := by
      funext p q
      rfl
    simpa [this] using hli_e
  exact (nonsingular_iff_det_ne_zero (R := ℂ)).mp
    (Nonsingular.of_linearIndependent_row hrow)

lemma polynomial_minor_from_eval {k d : ℕ} {σ : Type}
    (w : Fin d → Fin k → MvPolynomial σ ℂ) (ξ : σ → ℂ)
    (hli : LinearIndependent ℂ (fun q i => eval ξ (w q i))) :
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      Matrix.det (Matrix.of fun p q => w q (e p)) ≠ 0 := by
  obtain ⟨e, he, hdet⟩ := exists_nonzero_coord_minor
    (fun q i => eval ξ (w q i)) hli
  refine ⟨e, he, ?_⟩
  intro hp
  have hev : eval ξ (Matrix.det (Matrix.of fun p q => w q (e p))) = 0 := by
    simp [hp]
  rw [(eval ξ).map_det] at hev
  exact hdet hev

/-- An invertible mixed-rank witness produces a nonzero coordinate-minor
polynomial for the universal adjugate family. -/
theorem proof :
    ∀ (k d : ℕ) (move : Fin d → Prop) [DecidablePred move]
      (v : Fin d → Fin k → ℂ) (G : Matrix (Fin k) (Fin k) ℂ),
      IsUnit G.det →
      LinearIndependent ℂ
        (fun q => if move q then G.mulVec (v q) else v q) →
      ∃ e : Fin d → Fin k, Function.Injective e ∧
        Matrix.det (Matrix.of fun p q => mixedPolyVec move v q (e p)) ≠ 0 := by
  intro k d move _ v G hG hli
  obtain ⟨H, _hH, hliH⟩ := exists_adjugate_rank_witness move v G hG hli
  apply polynomial_minor_from_eval (mixedPolyVec move v) (fun ij => H ij.1 ij.2)
  have heval :
      (fun q i => eval (fun ij => H ij.1 ij.2) (mixedPolyVec move v q i)) =
        (fun q => if move q then H.adjugate.mulVec (v q) else v q) := by
    funext q
    exact eval_mixedPolyVec move v q H
  rw [heval]
  exact hliH

end

end P14Hermitian.GreenMixedMinor




namespace P14Hermitian

open Matrix MvPolynomial
open scoped Matrix ComplexConjugate BigOperators

noncomputable section

abbrev Vec (k : ℕ) := Fin k → ℂ
abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℂ
abbrev MatVar (k : ℕ) := Fin k × Fin k

/-- Pairing polynomials use unconstrained complex matrix entries. -/
def pairPoly {k : ℕ} (x y : Vec k) : MvPolynomial (MatVar k) ℂ :=
  dotProduct (fun i => C (star (x i)))
    ((GreenMixedMinor.universalMat (k := k)).mulVec (fun i => C (y i)))

def adjPairPoly {k : ℕ} (x y : Vec k) : MvPolynomial (MatVar k) ℂ :=
  dotProduct (fun i => C (star (x i)))
    ((GreenMixedMinor.universalMat (k := k)).adjugate.mulVec (fun i => C (y i)))

lemma eval_pairPoly {k : ℕ} (x y : Vec k) (H : Mat k) :
    eval (fun ij => H ij.1 ij.2) (pairPoly x y) =
      dotProduct (star x) (H.mulVec y) := by
  simp [pairPoly, dotProduct, Matrix.mulVec, GreenMixedMinor.universalMat]

lemma eval_adjPairPoly {k : ℕ} (x y : Vec k) (H : Mat k) :
    eval (fun ij => H ij.1 ij.2) (adjPairPoly x y) =
      dotProduct (star x) (H.adjugate.mulVec y) := by
  let z : MatVar k → ℂ := fun ij => H ij.1 ij.2
  have hmat :
      (eval z).mapMatrix (GreenMixedMinor.universalMat (k := k)).adjugate =
        H.adjugate := by
    rw [RingHom.map_adjugate, GreenMixedMinor.eval_universalMat]
  simp only [adjPairPoly, dotProduct, map_sum, map_mul, eval_C]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  calc
    eval z ((GreenMixedMinor.universalMat (k := k)).adjugate.mulVec
        (fun j => C (y j)) i) =
        (((eval z).mapMatrix (GreenMixedMinor.universalMat (k := k)).adjugate).mulVec
          (fun j => eval z (C (y j)))) i := by
            exact RingHom.map_mulVec (eval z) _ _ i
    _ = (H.adjugate.mulVec y) i := by rw [hmat]; simp

lemma pairPoly_ne_zero {k : ℕ} (x y : Vec k) (hx : x ≠ 0) (hy : y ≠ 0) :
    pairPoly x y ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  let E : Mat k := fun a b => if a = i then if b = j then 1 else 0 else 0
  intro hp
  have hev := eval_pairPoly x y E
  have hzero : dotProduct (star x) (E.mulVec y) = 0 := by
    rw [hp, map_zero] at hev
    exact hev.symm
  have hval : dotProduct (star x) (E.mulVec y) = star (x i) * y j := by
    simp [E, dotProduct, Matrix.mulVec]
  rw [hval] at hzero
  exact (mul_ne_zero (star_ne_zero.mpr hi) hj) hzero

/-- Adjugate pairings are nonzero polynomials too.  The already-proved
positive-cone lemma supplies one invertible witness for the linear pairing. -/
lemma adjPairPoly_ne_zero {k : ℕ} (x y : Vec k) (hx : x ≠ 0) (hy : y ≠ 0) :
    adjPairPoly x y ≠ 0 := by
  obtain ⟨L, hL, hpK⟩ := GreenGenericity.exists_gram_eval_ne_zero
    (pairPoly x y) (pairPoly_ne_zero x y hx hy)
  let K : Mat k := L.conjTranspose * L
  have hK : IsUnit K := ((Matrix.isUnit_conjTranspose L).mpr hL).mul hL
  have hKd : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK
  obtain ⟨H, c, _, hc, hAdj⟩ :=
    GreenMixedMinor.adjugate_realizes_invertible K hKd
  rw [eval_pairPoly] at hpK
  intro hp
  have hev := eval_adjPairPoly x y H
  rw [hp, map_zero] at hev
  have hval : dotProduct (star x) (H.adjugate.mulVec y) =
      c * dotProduct (star x) (K.mulVec y) := by
    rw [hAdj, Matrix.smul_mulVec]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hval] at hev
  exact (mul_ne_zero hc hpK) hev.symm

def right {n : ℕ} : Fin n ⊕ Fin n → Prop
  | .inl _ => False
  | .inr _ => True

instance {n : ℕ} (q : Fin n ⊕ Fin n) : Decidable (right q) := by
  cases q <;> unfold right <;> infer_instance

/-- The common algebraic action on a selected mixed vector. -/
def mixed {k n : ℕ} (x y : Fin n → Vec k) (G : Mat k) :
    Fin n ⊕ Fin n → Vec k := Sum.elim x (fun j => G.mulVec (y j))

lemma mixed_as_if {k n : ℕ} (x y : Fin n → Vec k) (G : Mat k)
    (q : Fin n ⊕ Fin n) :
    mixed x y G q = if right q then G.mulVec (Sum.elim x y q) else Sum.elim x y q := by
  cases q <;> simp [mixed, right]

/-- Finite Hermitian placement for any finite collection of independent
mixed-subfamily tests with separate invertible witnesses. -/
theorem finite_gram_placement {k n : ℕ} {T : Type*} [Fintype T]
    (x y : Fin n → Vec k) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (d : T → ℕ) (f : (t : T) → Fin (d t) → Fin n ⊕ Fin n)
    (hw : ∀ t, ∃ G : Mat k, IsUnit G.det ∧
      LinearIndependent ℂ (fun q => mixed x y G (f t q))) :
    ∃ L : Mat k, IsUnit L ∧
      let K := L.conjTranspose * L
      (∀ t, LinearIndependent ℂ (fun q => mixed x y K.adjugate (f t q))) ∧
      (∀ i j, dotProduct (star (x i)) (K.mulVec (x j)) ≠ 0) ∧
      (∀ i j, dotProduct (star (y i)) (K.adjugate.mulVec (y j)) ≠ 0) := by
  classical
  let base (t : T) : Fin (d t) → Vec k := fun q => Sum.elim x y (f t q)
  let move (t : T) : Fin (d t) → Prop := fun q => right (f t q)
  have hminor : ∀ t, ∃ e : Fin (d t) → Fin k, Function.Injective e ∧
      Matrix.det (Matrix.of fun p q =>
        GreenMixedMinor.mixedPolyVec (move t) (base t) q (e p)) ≠ 0 := by
    intro t
    obtain ⟨G, hG, hli⟩ := hw t
    apply GreenMixedMinor.proof k (d t) (move t) (base t) G hG
    simpa only [base, move, mixed_as_if] using hli
  choose e he hpoly using hminor
  let poly : T ⊕ ((Fin n × Fin n) ⊕ (Fin n × Fin n)) →
      MvPolynomial (MatVar k) ℂ := fun t => match t with
    | .inl t => Matrix.det (Matrix.of fun p q =>
        GreenMixedMinor.mixedPolyVec (move t) (base t) q (e t p))
    | .inr (.inl ij) => pairPoly (x ij.1) (x ij.2)
    | .inr (.inr ij) => adjPairPoly (y ij.1) (y ij.2)
  have hp : ∀ t, poly t ≠ 0 := by
    rintro (t | (ij | ij))
    · exact hpoly t
    · exact pairPoly_ne_zero _ _ (hx ij.1) (hx ij.2)
    · exact adjPairPoly_ne_zero _ _ (hy ij.1) (hy ij.2)
  obtain ⟨L, hL, havoid⟩ := GreenGenericity.finite_gram_genericity poly hp
  let K : Mat k := L.conjTranspose * L
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro t
    have hdet : (Matrix.of fun p q => mixed x y K.adjugate (f t q) (e t p)).det ≠ 0 := by
      have h := havoid (.inl t)
      change eval (fun ij => K ij.1 ij.2)
        (Matrix.det (Matrix.of fun p q =>
          GreenMixedMinor.mixedPolyVec (move t) (base t) q (e t p))) ≠ 0 at h
      rw [(eval (fun ij : MatVar k => K ij.1 ij.2)).map_det] at h
      convert h using 1
      congr 1
      ext p q
      change mixed x y K.adjugate (f t q) (e t p) =
        eval (fun ij => K ij.1 ij.2)
          (GreenMixedMinor.mixedPolyVec (move t) (base t) q (e t p))
      have heval := congrFun
        (GreenMixedMinor.eval_mixedPolyVec (move t) (base t) q K) (e t p)
      simpa only [base, move, mixed_as_if] using heval.symm
    let D : Vec k →ₗ[ℂ] (Fin (d t) → ℂ) :=
      LinearMap.pi (fun p => LinearMap.proj (R := ℂ) (e t p))
    apply LinearIndependent.of_comp D
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  · intro i j
    have h := havoid (.inr (.inl (i, j)))
    simpa only [poly, eval_pairPoly] using h
  · intro i j
    have h := havoid (.inr (.inr (i, j)))
    simpa only [poly, eval_adjPairPoly] using h

/-- Hermitian realization of a finite family of mixed-rank constraints.
The cross pairing is preserved up to one nonzero scalar, hence its zero
pattern is preserved exactly. -/
theorem finite_hermitian_placement {k n : ℕ} {T : Type*} [Fintype T]
    (x y : Fin n → Vec k) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (d : T → ℕ) (f : (t : T) → Fin (d t) → Fin n ⊕ Fin n)
    (hw : ∀ t, ∃ G : Mat k, IsUnit G.det ∧
      LinearIndependent ℂ (fun q => mixed x y G (f t q))) :
    ∃ a b : Fin n → EuclideanSpace ℂ (Fin k),
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (∀ i j, inner ℂ (a i) (b j) = 0 ↔ dotProduct (star (x i)) (y j) = 0) ∧
      (∀ i j, inner ℂ (a i) (a j) ≠ 0 ∧ inner ℂ (b i) (b j) ≠ 0) ∧
      (∀ t, LinearIndependent ℂ (fun q => Sum.elim a b (f t q))) := by
  classical
  obtain ⟨L, hL, hLI, hXX, hYY⟩ := finite_gram_placement x y hx hy d f hw
  let K : Mat k := L.conjTranspose * L
  have hK : IsUnit K := ((Matrix.isUnit_conjTranspose L).mpr hL).mul hL
  have hGram : K = L.conjTranspose * L := rfl
  have hHerm : K.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self L
  let E : Vec k ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) :=
    (WithLp.linearEquiv 2 ℂ (Vec k)).symm
  let F : Vec k →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := E.toLinearMap.comp L.mulVecLin
  have hF : Function.Injective F :=
    E.injective.comp (Matrix.mulVec_injective_iff_isUnit.mpr hL)
  have hinner (u v : Vec k) :
      inner ℂ (F u) (F v) = dotProduct (star u) (K.mulVec v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change dotProduct (star (L.mulVec u)) (L.mulVec v) = _
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hGram]
  let a : Fin n → EuclideanSpace ℂ (Fin k) := fun i => F (x i)
  let b : Fin n → EuclideanSpace ℂ (Fin k) := fun j => F (K.adjugate.mulVec (y j))
  have hdet : K.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det K).mp hK)
  have haa (i j : Fin n) : inner ℂ (a i) (a j) ≠ 0 := by
    change inner ℂ (F (x i)) (F (x j)) ≠ 0
    rw [hinner]
    exact hXX i j
  have hbb (i j : Fin n) : inner ℂ (b i) (b j) ≠ 0 := by
    change inner ℂ (F (K.adjugate.mulVec (y i)))
      (F (K.adjugate.mulVec (y j))) ≠ 0
    rw [hinner, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hHerm.adjugate.eq]
    exact mul_ne_zero hdet (hYY i j)
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · intro hz
      exact haa i i (by simp [hz])
    · intro hz
      exact hbb i i (by simp [hz])
  · intro i j
    change inner ℂ (F (x i)) (F (K.adjugate.mulVec (y j))) = 0 ↔ _
    rw [hinner, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_eq_zero.trans (or_iff_right hdet)
  · intro i j
    exact ⟨haa i j, hbb i j⟩
  · intro t
    have h := (hLI t).map' F (LinearMap.ker_eq_bot.mpr hF)
    have heq : (fun q => Sum.elim a b (f t q)) =
        F ∘ (fun q => mixed x y (L.conjTranspose * L).adjugate (f t q)) := by
      funext q
      cases hf : f t q <;> simp [Function.comp_apply, hf, mixed, a, b, K]
    rw [heq]
    exact h

end
end P14Hermitian

/- Component: literature/MixedRanks.lean -/

/-! Rank witnesses used by the mixed Hermitian seed construction.
The imported transversality proof is the existing Jig s65 submission,
copied unchanged into this private preflight directory. -/

noncomputable section

open Submodule Function

namespace P14MixedRanks

abbrev Vec (k : ℕ) := Fin k → ℂ

lemma map_span_range {k : ℕ} {ι : Type*} (x : ι → Vec k)
    (g : Vec k ≃ₗ[ℂ] Vec k) :
    (span ℂ (Set.range x)).map g.toLinearMap =
      span ℂ (Set.range (g ∘ x)) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma span_sum_elim {k : ℕ} {ι κ : Type*} (x : ι → Vec k) (y : κ → Vec k) :
    span ℂ (Set.range (Sum.elim x y)) =
      span ℂ (Set.range x) ⊔ span ℂ (Set.range y) := by
  rw [Set.Sum.elim_range, Submodule.span_union]

theorem exists_equiv_sum_independent {k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Vec k) (y : κ → Vec k)
    (hx : LinearIndependent ℂ x) (hy : LinearIndependent ℂ y)
    (hsize : Fintype.card ι + Fintype.card κ ≤ k) :
    ∃ g : Vec k ≃ₗ[ℂ] Vec k,
      LinearIndependent ℂ (Sum.elim x (g ∘ y)) := by
  let U := span ℂ (Set.range x)
  let W := span ℂ (Set.range y)
  obtain ⟨g, hg⟩ := Maximal.proof k U W
  have hU : Module.finrank ℂ U = Fintype.card ι := finrank_span_eq_card hx
  have hW : Module.finrank ℂ W = Fintype.card κ := finrank_span_eq_card hy
  rw [hU, hW, Nat.min_eq_right hsize] at hg
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U (W.map g.toLinearMap)
  rw [hg, hU, g.finrank_map_eq, hW] at hdim
  have hdis : Disjoint U (W.map g.toLinearMap) := by
    rw [disjoint_iff, ← Submodule.finrank_eq_zero]
    omega
  refine ⟨g, hx.sum_type (hy.map' g.toLinearMap g.ker) ?_⟩
  simpa only [U, W, map_span_range] using hdis

theorem exists_equiv_sum_spanning {k : ℕ} {ι κ : Type*}
    (x : ι → Vec k) (y : κ → Vec k)
    (hrank : k ≤ Module.finrank ℂ (span ℂ (Set.range x)) +
      Module.finrank ℂ (span ℂ (Set.range y))) :
    ∃ g : Vec k ≃ₗ[ℂ] Vec k,
      span ℂ (Set.range (Sum.elim x (g ∘ y))) = ⊤ := by
  obtain ⟨g, hg⟩ := Maximal.proof
    k (span ℂ (Set.range x)) (span ℂ (Set.range y))
  refine ⟨g, Submodule.eq_top_of_finrank_eq ?_⟩
  rw [span_sum_elim, ← map_span_range, hg, Nat.min_eq_left hrank]
  simp [Vec]

lemma matrix_isUnit_det {k : ℕ} (g : Vec k ≃ₗ[ℂ] Vec k) :
    IsUnit (LinearMap.toMatrix' g.toLinearMap).det := by
  apply Matrix.isUnit_det_of_left_inverse
    (B := LinearMap.toMatrix' g.symm.toLinearMap)
  rw [← LinearMap.toMatrix'_comp]
  have h : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact g.symm_apply_apply v
  rw [h, LinearMap.toMatrix'_id]

theorem exists_matrix_sum_independent {k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Vec k) (y : κ → Vec k)
    (hx : LinearIndependent ℂ x) (hy : LinearIndependent ℂ y)
    (hsize : Fintype.card ι + Fintype.card κ ≤ k) :
    ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      LinearIndependent ℂ (Sum.elim x (fun j => G.mulVec (y j))) := by
  obtain ⟨g, hg⟩ := exists_equiv_sum_independent x y hx hy hsize
  refine ⟨LinearMap.toMatrix' g.toLinearMap, matrix_isUnit_det g, ?_⟩
  simpa [Function.comp_def] using hg

theorem exists_matrix_sum_spanning {k : ℕ} {ι κ : Type*}
    (x : ι → Vec k) (y : κ → Vec k)
    (hrank : k ≤ Module.finrank ℂ (span ℂ (Set.range x)) +
      Module.finrank ℂ (span ℂ (Set.range y))) :
    ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      span ℂ (Set.range (Sum.elim x (fun j => G.mulVec (y j)))) = ⊤ := by
  obtain ⟨g, hg⟩ := exists_equiv_sum_spanning x y hrank
  refine ⟨LinearMap.toMatrix' g.toLinearMap, matrix_isUnit_det g, ?_⟩
  simpa [Function.comp_def] using hg

theorem independent_subfamily_of_spanning {k : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → Vec k) (hv : span ℂ (Set.range v) = ⊤) :
    ∃ e : Fin k → ι, Function.Injective e ∧ LinearIndependent ℂ (v ∘ e) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hspan, hv]
    simp [Vec]
  let eκ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨a ∘ eκ, ha.comp eκ.injective, hli.comp eκ eκ.injective⟩

def SmallSelections {k n : ℕ} (x : Fin n → Vec k) : Prop :=
  ∀ d : ℕ, d < k → ∀ f : Fin d → Fin n, Injective f →
    LinearIndependent ℂ (x ∘ f)

def LargeSelections {k n : ℕ} (x : Fin n → Vec k) : Prop :=
  ∀ f : Fin (k + 1) → Fin n, Injective f →
    span ℂ (Set.range (x ∘ f)) = ⊤

theorem smallSelections_of_exact {k n : ℕ} (x : Fin n → Vec k) (hn : k - 1 ≤ n)
    (hx : ∀ f : Fin (k - 1) → Fin n, Injective f → LinearIndependent ℂ (x ∘ f)) :
    SmallSelections x := by
  intro d hd f hf
  have hdk : d ≤ k - 1 := by omega
  have hdn : d ≤ n := hdk.trans hn
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE hdn) f (Fin.castLE_injective _) hf
  have hli := hx (σ ∘ Fin.castLE hn) (σ.injective.comp (Fin.castLE_injective _))
  have hres := hli.comp (Fin.castLE hdk) (Fin.castLE_injective _)
  have heq : (x ∘ (σ ∘ Fin.castLE hn)) ∘ Fin.castLE hdk = x ∘ f := by
    funext i
    exact congrArg x (hσ i)
  rwa [heq] at hres

lemma independent_small {k n : ℕ} {ι : Type*} [Fintype ι]
    (x : Fin n → Vec k) (hx : SmallSelections x)
    (f : ι → Fin n) (hf : Injective f) (hsize : Fintype.card ι < k) :
    LinearIndependent ℂ (x ∘ f) := by
  let e := Fintype.equivFin ι
  have h := hx _ hsize (f ∘ e.symm) (hf.comp e.symm.injective)
  simpa [Function.comp_def] using h.comp e e.injective

lemma spanning_large {k n : ℕ} {ι : Type*} [Fintype ι]
    (x : Fin n → Vec k) (hx : LargeSelections x)
    (f : ι → Fin n) (hf : Injective f) (hsize : Fintype.card ι = k + 1) :
    span ℂ (Set.range (x ∘ f)) = ⊤ := by
  let e : Fin (k + 1) ≃ ι := (Fintype.equivFinOfCardEq hsize).symm
  have h := hx (f ∘ e) (hf.comp e.injective)
  simpa only [← Function.comp_assoc, e.surjective.range_comp] using h

lemma pure_rank_lower {k n : ℕ} {ι : Type*} [Fintype ι]
    (hk : 0 < k) (x : Fin n → Vec k) (hx : SmallSelections x)
    (f : ι → Fin n) (hf : Injective f) :
    min (Fintype.card ι) (k - 1) ≤ Module.finrank ℂ (span ℂ (Set.range (x ∘ f))) := by
  let d := min (Fintype.card ι) (k - 1)
  have hd : d < k := lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
  let e : Fin d → ι := fun i => (Fintype.equivFin ι).symm
    (Fin.castLE (Nat.min_le_left _ _) i)
  have he : Injective e := (Fintype.equivFin ι).symm.injective.comp (Fin.castLE_injective _)
  have hli := hx d hd (f ∘ e) (hf.comp he)
  have hs : span ℂ (Set.range (x ∘ (f ∘ e))) ≤ span ℂ (Set.range (x ∘ f)) := by
    apply Submodule.span_mono
    rintro z ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  have hdim : Module.finrank ℂ (span ℂ (Set.range (x ∘ (f ∘ e)))) = d := by
    simpa using finrank_span_eq_card hli
  have hmono := Submodule.finrank_mono hs
  rw [hdim] at hmono
  exact hmono

def leftIndex {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n)
    (i : {i // (f i).isLeft}) : Fin n := (f i.val).getLeft i.property

def rightIndex {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n)
    (i : {i // ¬ (f i).isLeft}) : Fin n :=
  (f i.val).getRight (by simpa using i.property)

lemma leftIndex_injective {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n) (hf : Injective f) :
    Injective (leftIndex f) := by
  intro i j hij
  apply Subtype.ext
  apply hf
  simpa only [leftIndex, Sum.inl_getLeft] using congrArg (Sum.inl : Fin n → Fin n ⊕ Fin n) hij

lemma rightIndex_injective {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n) (hf : Injective f) :
    Injective (rightIndex f) := by
  intro i j hij
  apply Subtype.ext
  apply hf
  simpa only [rightIndex, Sum.inr_getRight] using congrArg (Sum.inr : Fin n → Fin n ⊕ Fin n) hij

lemma partition_card {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n) :
    Fintype.card {i // (f i).isLeft} + Fintype.card {i // ¬ (f i).isLeft} = d := by
  classical
  simpa using Fintype.card_congr (Equiv.sumCompl (fun i => (f i).isLeft))

lemma partition_family {k d n : ℕ} (x y : Fin n → Vec k)
    (f : Fin d → Fin n ⊕ Fin n) (G : Matrix (Fin k) (Fin k) ℂ) :
    Sum.elim (x ∘ leftIndex f) (fun j => G.mulVec (y (rightIndex f j))) =
      (Sum.elim x (fun j => G.mulVec (y j))) ∘ f ∘
        (Equiv.sumCompl (fun i => (f i).isLeft)) := by
  classical
  funext i
  cases i with
  | inl i =>
    change x ((f i.val).getLeft i.property) = Sum.elim x _ (f i.val)
    conv_rhs => rw [← Sum.inl_getLeft (f i.val) i.property]
    rfl
  | inr i =>
    change G.mulVec (y ((f i.val).getRight _)) = Sum.elim x _ (f i.val)
    conv_rhs => rw [← Sum.inr_getRight (f i.val) (by simpa using i.property)]
    rfl

theorem small_selection_gl {k n d : ℕ} (x y : Fin n → Vec k)
    (hx : SmallSelections x) (hy : SmallSelections y)
    (hd : d < k) (f : Fin d → Fin n ⊕ Fin n) (hf : Injective f) :
    ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      LinearIndependent ℂ (fun q => Sum.elim x (fun j => G.mulVec (y j)) (f q)) := by
  classical
  have hc := partition_card f
  have hl := independent_small x hx (leftIndex f) (leftIndex_injective f hf) (by omega)
  have hr := independent_small y hy (rightIndex f) (rightIndex_injective f hf) (by omega)
  obtain ⟨G, hG, hli⟩ := exists_matrix_sum_independent
    (x ∘ leftIndex f) (y ∘ rightIndex f) hl hr (by omega)
  refine ⟨G, hG, ?_⟩
  change LinearIndependent ℂ (Sum.elim (x ∘ leftIndex f)
    (fun j => G.mulVec (y (rightIndex f j)))) at hli
  rw [partition_family x y f G] at hli
  simpa [Function.comp_def] using
    hli.comp (Equiv.sumCompl (fun i => (f i).isLeft)).symm
      (Equiv.sumCompl (fun i => (f i).isLeft)).symm.injective

theorem large_selection_gl_spanning {k n : ℕ} (hk : 2 ≤ k)
    (x y : Fin n → Vec k)
    (hx : SmallSelections x) (hy : SmallSelections y)
    (hx' : LargeSelections x) (hy' : LargeSelections y)
    (f : Fin (k + 1) → Fin n ⊕ Fin n) (hf : Injective f) :
    ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      span ℂ (Set.range (fun q => Sum.elim x (fun j => G.mulVec (y j)) (f q))) = ⊤ := by
  classical
  have hc := partition_card f
  have hrank : k ≤
      Module.finrank ℂ (span ℂ (Set.range (x ∘ leftIndex f))) +
      Module.finrank ℂ (span ℂ (Set.range (y ∘ rightIndex f))) := by
    by_cases hl : Fintype.card {i // (f i).isLeft} = 0
    · have hs := spanning_large y hy' (rightIndex f) (rightIndex_injective f hf) (by omega)
      rw [hs]
      simp [Vec]
    by_cases hr : Fintype.card {i // ¬ (f i).isLeft} = 0
    · have hs := spanning_large x hx' (leftIndex f) (leftIndex_injective f hf) (by omega)
      rw [hs]
      simp [Vec]
    have hxl := pure_rank_lower (by omega) x hx (leftIndex f) (leftIndex_injective f hf)
    have hyl := pure_rank_lower (by omega) y hy (rightIndex f) (rightIndex_injective f hf)
    omega
  obtain ⟨G, hG, hs⟩ := exists_matrix_sum_spanning
    (x ∘ leftIndex f) (y ∘ rightIndex f) hrank
  refine ⟨G, hG, ?_⟩
  change span ℂ (Set.range (Sum.elim (x ∘ leftIndex f)
    (fun j => G.mulVec (y (rightIndex f j))))) = ⊤ at hs
  rw [partition_family x y f G] at hs
  change span ℂ (Set.range (((Sum.elim x (fun j => G.mulVec (y j))) ∘ f) ∘
    (Equiv.sumCompl (fun i => (f i).isLeft)))) = ⊤ at hs
  rw [(Equiv.sumCompl (fun i => (f i).isLeft)).surjective.range_comp] at hs
  exact hs

theorem large_selection_gl {k n : ℕ} (hk : 2 ≤ k)
    (x y : Fin n → Vec k)
    (hx : SmallSelections x) (hy : SmallSelections y)
    (hx' : LargeSelections x) (hy' : LargeSelections y)
    (f : Fin (k + 1) → Fin n ⊕ Fin n) (hf : Injective f) :
    ∃ e : Fin k → Fin (k + 1), Injective e ∧
      ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
        LinearIndependent ℂ
          (fun q => Sum.elim x (fun j => G.mulVec (y j)) (f (e q))) := by
  obtain ⟨G, hG, hs⟩ := large_selection_gl_spanning hk x y hx hy hx' hy' f hf
  obtain ⟨e, he, hli⟩ := independent_subfamily_of_spanning
    (fun q => Sum.elim x (fun j => G.mulVec (y j)) (f q)) hs
  exact ⟨e, he, G, hG, hli⟩

end P14MixedRanks
end


/- Component: literature/SeedAssembly.lean -/

/-! Assemble all finite mixed rank tests into one Hermitian seed family. -/

noncomputable section

open Function Submodule

namespace P14SeedAssembly

abbrev Vec (k : ℕ) := Fin k → ℂ

/-- Pure rank conditions suffice for the mixed Hermitian seed conditions. -/
theorem seed_of_pure_ranks {k n : ℕ} (hk : 2 ≤ k) (hn : k - 1 ≤ n)
    (x y : Fin n → Vec k)
    (hx0 : ∀ i, x i ≠ 0) (hy0 : ∀ i, y i ≠ 0)
    (hx : ∀ f : Fin (k - 1) → Fin n, Injective f →
      LinearIndependent ℂ (x ∘ f))
    (hy : ∀ f : Fin (k - 1) → Fin n, Injective f →
      LinearIndependent ℂ (y ∘ f))
    (hx' : ∀ f : Fin (k + 1) → Fin n, Injective f →
      span ℂ (Set.range (x ∘ f)) = ⊤)
    (hy' : ∀ f : Fin (k + 1) → Fin n, Injective f →
      span ℂ (Set.range (y ∘ f)) = ⊤) :
    ∃ a b : Fin n → EuclideanSpace ℂ (Fin k),
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (∀ i j, inner ℂ (a i) (b j) = 0 ↔ dotProduct (star (x i)) (y j) = 0) ∧
      (∀ i j, inner ℂ (a i) (a j) ≠ 0 ∧ inner ℂ (b i) (b j) ≠ 0) ∧
      (∀ S : Finset (Fin n ⊕ Fin n), S.card + 1 ≤ k →
        LinearIndependent ℂ (fun i : (S : Set (Fin n ⊕ Fin n)) =>
          Sum.elim a b i.1)) ∧
      (∀ S : Finset (Fin n ⊕ Fin n), S.card = k + 1 →
        span ℂ (Set.range (fun i : (S : Set (Fin n ⊕ Fin n)) =>
          Sum.elim a b i.1)) = ⊤) := by
  classical
  have hxs := P14MixedRanks.smallSelections_of_exact x hn hx
  have hys := P14MixedRanks.smallSelections_of_exact y hn hy
  let Small := Σ d : Fin k,
    {f : Fin d.val → Fin n ⊕ Fin n // Injective f}
  let Big := {f : Fin (k + 1) → Fin n ⊕ Fin n // Injective f}
  have hb (f : Big) : ∃ e : Fin k → Fin (k + 1), Injective e ∧
      ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
        LinearIndependent ℂ (fun q =>
          P14Hermitian.mixed x y G (f.val (e q))) := by
    exact P14MixedRanks.large_selection_gl hk x y hxs hys hx' hy' f.val f.property
  choose pick hpick hwbig using hb
  let T := Small ⊕ Big
  let d : T → ℕ := Sum.elim (fun t => t.1.val) (fun _ => k)
  let f : (t : T) → Fin (d t) → Fin n ⊕ Fin n := fun t =>
    match t with
    | .inl t => t.2.val
    | .inr t => t.val ∘ pick t
  have hw (t : T) : ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      LinearIndependent ℂ (fun q => P14Hermitian.mixed x y G (f t q)) := by
    cases t with
    | inl t =>
      exact P14MixedRanks.small_selection_gl x y hxs hys t.1.isLt t.2.val t.2.property
    | inr t => exact hwbig t
  obtain ⟨a, b, hnz, hcross, hsame, htest⟩ :=
    P14Hermitian.finite_hermitian_placement x y hx0 hy0 d f hw
  refine ⟨a, b, hnz, hcross, hsame, ?_, ?_⟩
  · intro S hS
    let e : (S : Set (Fin n ⊕ Fin n)) ≃ Fin S.card :=
      Fintype.equivFinOfCardEq (by simp)
    let s : Fin S.card → Fin n ⊕ Fin n := fun q => (e.symm q).val
    have hs : Injective s := Subtype.val_injective.comp e.symm.injective
    let t : T := .inl ⟨⟨S.card, by omega⟩, ⟨s, hs⟩⟩
    have ht := (htest t).comp e e.injective
    change LinearIndependent ℂ
      (fun i : (S : Set (Fin n ⊕ Fin n)) =>
        Sum.elim a b (e.symm (e i)).val) at ht
    simpa using ht
  · intro S hS
    let e : (S : Set (Fin n ⊕ Fin n)) ≃ Fin (k + 1) :=
      Fintype.equivFinOfCardEq (by simpa using hS)
    let s : Fin (k + 1) → Fin n ⊕ Fin n := fun q => (e.symm q).val
    have hs : Injective s := Subtype.val_injective.comp e.symm.injective
    let t : Big := ⟨s, hs⟩
    have ht := htest (.inr t)
    let w : Fin k → EuclideanSpace ℂ (Fin k) :=
      fun q => Sum.elim a b (s (pick t q))
    have hli : LinearIndependent ℂ w := ht
    have htop : span ℂ (Set.range w) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hli]
      simp
    have hsub : span ℂ (Set.range w) ≤
        span ℂ (Set.range (fun i : (S : Set (Fin n ⊕ Fin n)) =>
          Sum.elim a b i.1)) := by
      apply span_mono
      rintro v ⟨q, rfl⟩
      exact ⟨e.symm (pick t q), rfl⟩
    rw [htop] at hsub
    exact top_unique hsub

end P14SeedAssembly
end


/- Component: cusp_assembly/SeedFinalLocal.lean -/




/-- The even translate offsets. -/
def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

/-- The odd anti-translate offsets
`1,3,...,2r-3,2r+1`. -/
def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

/-- Balanced translate/anti-translate incidence. -/
def CrossAdj {r N : ℕ} (i j : ZMod (2 * N)) : Prop :=
  (∃ c : Fin r, j = i + cOffset c) ∨
  (∃ d : Fin r, j = -i + dOffset d)

/-- Finite-index version of the cyclic incidence relation. -/
def CrossAdjFin {r N : ℕ} (i j : Fin (2 * N)) : Prop :=
  CrossAdj (r := r) (N := N) (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N))

def Tight {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ S : Finset ι, S.card + 1 ≤ k →
    LinearIndependent ℂ fun i : (S : Set ι) => v i.1

def KPlusOneSpanning {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ S : Finset ι, S.card = k + 1 →
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i.1) = ⊤

/-- The elliptic normal curve seed family. -/
abbrev statement : Prop :=
  ∀ r N : ℕ, 2 ≤ r → r + 2 ≤ N →
    let k := 2 * r
    let n := 2 * N
    ∃ a b : Fin n → EuclideanSpace ℂ (Fin k),
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (∀ i j, inner ℂ (a i) (b j) = 0 ↔
        CrossAdjFin (r := r) (N := N) i j) ∧
      (∀ i j, i ≠ j →
        inner ℂ (a i) (a j) ≠ 0 ∧ inner ℂ (b i) (b j) ≠ 0) ∧
      Tight (Sum.elim a b) ∧
      KPlusOneSpanning (Sum.elim a b)


theorem proof : statement := by
  intro r N hr hN
  obtain ⟨x, y, h0, hcross, hsmall, hlarge⟩ :=
    Pure.proof r N hr hN
  obtain ⟨a, b, hab0, hab, hsame, htight, hspan⟩ :=
    P14SeedAssembly.seed_of_pure_ranks (by omega) (by omega) x y
      (fun i => (h0 i).1) (fun i => (h0 i).2)
      (fun f hf => (hsmall f hf).1) (fun f hf => (hsmall f hf).2)
      (fun f hf => (hlarge f hf).1) (fun f hf => (hlarge f hf).2)
  refine ⟨a, b, hab0, ?_, ?_, htight, hspan⟩
  · intro i j
    rw [hab]
    simpa only [dotProduct, Pi.star_apply, CrossAdjFin, CrossAdj, cOffset, dOffset,
      Pure.CuspAllRankMinor.CrossAdj,
      Pure.CuspAllRankMinor.cOffset,
      Pure.CuspAllRankMinor.dOffset]
      using hcross i j
  · intro i j _
    exact hsame i j


end Submissions.EllipticBipartiteSeedFamily.CuspAssembly
