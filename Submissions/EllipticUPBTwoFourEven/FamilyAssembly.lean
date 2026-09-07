import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fintype
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace Submissions.EllipticUPBTwoFourEven.FamilyAssembly

/- Source: cusp_assembly/CuspAssembly.lean. Reused authorship is retained in the source comments and artifact citations. -/
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


/- Source: cusp_assembly/CliqueRows.lean. Reused authorship is retained in the source comments and artifact citations. -/
namespace P14CliqueRows.Reused

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

abbrev vand (k : ℕ) (s : ℂ) : Fin k → ℂ := fun r => s ^ (r : ℕ)

abbrev statement : Prop :=
  ∀ (k n : ℕ), 2 ≤ k →
    ∀ t : Fin n → ℂ, Function.Injective t →
      (∀ i j : Fin n,
          pair (vand k (t i)) (vand k (t j)) = 0 ↔
            ((star (t i) * t j) ^ k = 1 ∧ star (t i) * t j ≠ 1)) ∧
      (∀ b : Fin k → Fin n, Function.Injective b →
          LinearIndependent ℂ fun p => vand k (t (b p))) ∧
      (∀ b : Fin (k + 1) → Fin n, Function.Injective b →
          Submodule.span ℂ (Set.range fun p => vand k (t (b p))) = ⊤)

lemma pairing_formula (k : ℕ) (s s' : ℂ) :
    pair (vand k s) (vand k s') =
      ∑ r : Fin k, (star s * s') ^ (r : ℕ) := by
  simp only [pair, vand]
  apply Finset.sum_congr rfl
  intro r hr
  rw [star_pow, mul_pow]

lemma geometric_sum_zero_iff (k : ℕ) (hk : 2 ≤ k) (ρ : ℂ) :
    (∑ r ∈ Finset.range k, ρ ^ r) = 0 ↔
      (ρ ^ k = 1 ∧ ρ ≠ 1) := by
  by_cases hρ : ρ = 1
  · subst ρ
    have hk0 : (k : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hk))
    simp [hk0]
  · have hsub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ
    constructor
    · intro hs
      have hfac : (∑ r ∈ Finset.range k, ρ ^ r) * (ρ - 1) =
          ρ ^ k - 1 := geom_sum_mul ρ k
      have hz : ρ ^ k - 1 = 0 := by
        rw [← hfac]
        simp [hs]
      exact ⟨sub_eq_zero.mp hz, hρ⟩
    · rintro ⟨hp, -⟩
      have hfac : (∑ r ∈ Finset.range k, ρ ^ r) * (ρ - 1) =
          ρ ^ k - 1 := geom_sum_mul ρ k
      have hz : (∑ r ∈ Finset.range k, ρ ^ r) * (ρ - 1) = 0 := by
        rw [hfac, hp]
        simp
      exact (mul_eq_zero.mp hz).resolve_right hsub

lemma vandermonde_rows_li {k n : ℕ} (t : Fin n → ℂ)
    (ht : Function.Injective t) (b : Fin k → Fin n)
    (hb : Function.Injective b) :
    LinearIndependent ℂ (fun p => vand k (t (b p))) := by
  let A : Matrix (Fin k) (Fin k) ℂ :=
    fun p q => (t (b p)) ^ (q : ℕ)
  have hnode : Function.Injective (t ∘ b) := ht.comp hb
  have hA : A = Matrix.vandermonde (t ∘ b) := by
    ext p q
    simp [A, Matrix.vandermonde_apply, Function.comp_apply]
  have hdet : A.det ≠ 0 := by
    rw [hA]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hnode
  have hrows : LinearIndependent ℂ (fun p => A p) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  simpa [A, vand] using hrows

theorem target : statement := by
  intro k n hk t ht
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [pairing_formula]
    rw [Fin.sum_univ_eq_sum_range]
    rw [geometric_sum_zero_iff k hk (star (t i) * t j)]
  · intro b hb
    exact vandermonde_rows_li t ht b hb
  · intro b hb
    let b₀ : Fin k → Fin (k + 1) := fun p => ⟨p.1, by omega⟩
    have hb₀ : Function.Injective b₀ := by
      intro p q hpq
      apply Fin.ext
      simpa [b₀] using congrArg Fin.val hpq
    have hli : LinearIndependent ℂ
        (fun p => vand k (t (b (b₀ p)))) :=
      vandermonde_rows_li t ht (b ∘ b₀) (hb.comp hb₀)
    letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    have hspan :
        Submodule.span ℂ (Set.range (fun p => vand k (t (b (b₀ p))))) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simp)
    have hsub :
        Set.range (fun p => vand k (t (b (b₀ p)))) ⊆
          Set.range (fun p => vand k (t (b p))) := by
      rintro v ⟨p, rfl⟩
      exact ⟨b₀ p, rfl⟩
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono hsub

end
end P14CliqueRows.Reused

namespace P14CliqueRows
set_option maxHeartbeats 2000000
noncomputable section
open Complex

def node {c k : ℕ} (ζ : ℂ) (i : Fin c × Fin k) : ℂ :=
  ζ ^ (i.1.val + c * i.2.val)

lemma node_injective {c k : ℕ} (hc : 0 < c) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (c * k)) : Function.Injective (node (c := c) (k := k) ζ) := by
  intro i j hij
  have hi : i.1.val + c * i.2.val < c * k := by
    nlinarith [i.1.isLt, i.2.isLt]
  have hj : j.1.val + c * j.2.val < c * k := by
    nlinarith [j.1.isLt, j.2.isLt]
  have he := hζ.pow_inj hi hj hij
  have hm := congrArg (fun z => z % c) he
  have hd := congrArg (fun z => z / c) he
  simp [Nat.add_mod, Nat.mod_eq_of_lt i.1.isLt, Nat.mod_eq_of_lt j.1.isLt] at hm
  have hsecond : i.2.val = j.2.val := by nlinarith
  exact Prod.ext (Fin.ext hm) (Fin.ext hsecond)

lemma node_norm {c k : ℕ} (hc : 0 < c) (hk : 0 < k) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (c * k)) (i : Fin c × Fin k) : ‖node ζ i‖ = 1 := by
  simp [node, norm_pow, hζ.norm'_eq_one (Nat.mul_ne_zero (by omega) (by omega))]

lemma node_pow {c k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (c * k))
    (i : Fin c × Fin k) : node ζ i ^ k = ζ ^ (i.1.val * k) := by
  simp only [node, ← pow_mul]
  rw [Nat.add_mul, pow_add]
  have h : c * i.2.val * k = (c * k) * i.2.val := by ring
  rw [h, pow_mul ζ (c*k) _, hζ.pow_eq_one]
  simp

lemma unit_star_mul {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  change (starRingEnd ℂ) z * z = 1
  rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hz]
  norm_num

lemma clique_pair {c k : ℕ} (hc : 0 < c) (hk : 2 ≤ k) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (c * k)) (i : Fin c) (a b : Fin k) (hab : a ≠ b) :
    Reused.pair (Reused.vand k (node ζ (i,a))) (Reused.vand k (node ζ (i,b))) = 0 := by
  have hn := node_injective hc hζ
  let t : Fin (c*k) → ℂ := fun j => ζ ^ j.val
  rw [Reused.pairing_formula, Fin.sum_univ_eq_sum_range,
    Reused.geometric_sum_zero_iff k hk]
  constructor
  · rw [mul_pow, ← star_pow, node_pow hζ, node_pow hζ]
    apply unit_star_mul
    simp [norm_pow, hζ.norm'_eq_one (Nat.mul_ne_zero (by omega) (by omega))]
  · intro he
    have hnrm := unit_star_mul (node_norm hc (by omega) hζ (i,a))
    have hz : star (node ζ (i,a)) ≠ 0 := by
      intro h; rw [h, zero_mul] at hnrm; exact zero_ne_one hnrm
    have heq : node ζ (i,a) = node ζ (i,b) :=
      mul_left_cancel₀ hz (hnrm.trans he.symm)
    have h := congrArg Prod.snd (hn heq)
    exact hab h

/-- Any number of mutually orthogonal k-tuples, with every k rows independent. -/
theorem clique_rows (c k : ℕ) (hc : 0 < c) (hk : 2 ≤ k) :
    ∃ v : Fin c × Fin k → EuclideanSpace ℂ (Fin k),
      (∀ i, v i ≠ 0) ∧
      (∀ i a b, a ≠ b → inner ℂ (v (i,a)) (v (i,b)) = 0) ∧
      (∀ b : Fin k → Fin c × Fin k, Function.Injective b →
        LinearIndependent ℂ (fun j => v (b j))) ∧
      (∀ S : Finset (Fin c × Fin k), S.card = k →
        Submodule.span ℂ (Set.range fun i : (S : Set (Fin c × Fin k)) => v i.val) = ⊤) := by
  let ζ : ℂ := exp (2 * Real.pi * I / (c*k))
  have hck : c*k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hζ : IsPrimitiveRoot ζ (c*k) := by
    simpa [ζ, Nat.cast_mul] using Complex.isPrimitiveRoot_exp (c*k) hck
  let e : (Fin k → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) :=
    (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).symm
  let v : Fin c × Fin k → EuclideanSpace ℂ (Fin k) :=
    fun i => e (Reused.vand k (node ζ i))
  have hn := node_injective hc hζ
  have hli : ∀ b : Fin k → Fin c × Fin k, Function.Injective b →
      LinearIndependent ℂ (fun j => v (b j)) := by
    intro b hb
    let A : Matrix (Fin k) (Fin k) ℂ := Matrix.vandermonde (fun j => node ζ (b j))
    have hdet : A.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr (hn.comp hb)
    have h := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    exact h.map' e.toLinearMap (by simp)
  refine ⟨v, ?_, ?_, hli, ?_⟩
  · intro i hi
    have he : Reused.vand k (node ζ i) = 0 := e.injective (hi.trans (map_zero e).symm)
    have hz := congrFun he ⟨0, by omega⟩
    simpa [Reused.vand] using hz
  · intro i a b hab
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change (∑ j, star ((Reused.vand k (node ζ (i,a))) j) *
      (Reused.vand k (node ζ (i,b))) j) = 0
    exact clique_pair hc hk hζ i a b hab
  · intro S hS
    let f : (S : Set (Fin c × Fin k)) ≃ Fin k :=
      Fintype.equivFinOfCardEq (by simpa using hS)
    let b : Fin k → Fin c × Fin k := fun j => (f.symm j).val
    have hb : Function.Injective b := Subtype.val_injective.comp f.symm.injective
    have h := (hli b hb).comp f f.injective
    have h' : LinearIndependent ℂ (fun i : (S : Set (Fin c × Fin k)) => v i.val) := by
      simpa [b, Function.comp_def] using h
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card h']
    simpa using hS

end
end P14CliqueRows


/- Source: literature/GadgetFactor.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-
  GadgetComplementOneFactorization: the complement of c disjoint copies of the
  gadget graph G_k in K_{2kc} has an explicit 1-factorization into 2kc - k - 1
  factors, for all k ≥ 2, c ≥ 1.

  Construction:
  * Half 1 (k-1 factors): within each copy, K_{k,k} minus a perfect matching is
    1-factorized by shifts d = 1, ..., k-1 in ZMod k.
  * Half 2 ((2c-2)·k factors): a round-robin 1-factorization of K_{2c} on the
    super-vertices (copy, side), labeled by Option (ZMod (2c-1)); each round-robin
    factor is refined by a shift β in ZMod k using an orientation of its edges.
-/







namespace Submissions.GadgetComplementOneFactorization.GadgetFactor

/-- Vertices: a copy, a side, and a position. -/
abbrev V (c k : ℕ) : Type := Fin c × Fin 2 × Fin k

/-- `K_m` minus the degenerate class. -/
def compl (c k : ℕ) : SimpleGraph (V c k) :=
  SimpleGraph.fromRel fun v w =>
    v.1 ≠ w.1 ∨ (v.1 = w.1 ∧ v.2.1 ≠ w.2.1 ∧ v.2.2 ≠ w.2.2)

/-- The adjacency of `compl` in usable form. -/
lemma adj_iff {c k : ℕ} (v w : V c k) :
    (compl c k).Adj v w ↔ (v.1 ≠ w.1 ∨ (v.2.1 ≠ w.2.1 ∧ v.2.2 ≠ w.2.2)) := by
  rw [compl, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with h1 | ⟨_, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h2, h3⟩
    · rcases h with h1 | ⟨_, h2, h3⟩
      · exact Or.inl (Ne.symm h1)
      · exact Or.inr ⟨Ne.symm h2, Ne.symm h3⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h with h1 | ⟨h2, _⟩
      · exact fun he => h1 (congrArg Prod.fst he)
      · exact fun he => h2 (congrArg (fun x => x.2.1) he)
    · rcases h with h1 | ⟨h2, h3⟩
      · exact Or.inl (Or.inl h1)
      · by_cases hcc : v.1 = w.1
        · exact Or.inl (Or.inr ⟨hcc, h2, h3⟩)
        · exact Or.inl (Or.inl hcc)

/-! ### Core: round-robin partner map on `Option (ZMod (2c-1))` -/

section Core

variable {c : ℕ}

/-- Round-robin partner map for round `a` on labels `Option (ZMod (2c-1))`. -/
def pim (a : ZMod (2 * c - 1)) : Option (ZMod (2 * c - 1)) → Option (ZMod (2 * c - 1))
  | none => some a
  | some x => if x = a then none else some (2 * a - x)

/-- (F0) `2 * c = 1` in `ZMod (2c-1)`. -/
lemma two_mul_c (hc : 1 ≤ c) : (2 : ZMod (2 * c - 1)) * (c : ZMod (2 * c - 1)) = 1 := by
  have he : 2 * c = (2 * c - 1) + 1 := by omega
  calc (2 : ZMod (2 * c - 1)) * (c : ZMod (2 * c - 1))
      = ((2 * c : ℕ) : ZMod (2 * c - 1)) := by push_cast; ring
    _ = (((2 * c - 1) + 1 : ℕ) : ZMod (2 * c - 1)) := by rw [← he]
    _ = 1 := by rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]

/-- Cancellation of 2 in `ZMod (2c-1)`. -/
lemma two_cancel (hc : 1 ≤ c) {x y : ZMod (2 * c - 1)} (h : 2 * x = 2 * y) : x = y := by
  have h1 := two_mul_c hc
  calc x = ((2 : ZMod (2 * c - 1)) * c) * x := by rw [h1, one_mul]
    _ = (c : ZMod (2 * c - 1)) * (2 * x) := by ring
    _ = (c : ZMod (2 * c - 1)) * (2 * y) := by rw [h]
    _ = ((2 : ZMod (2 * c - 1)) * c) * y := by ring
    _ = y := by rw [h1, one_mul]

/-- (F1) `pim a` is an involution. -/
lemma pim_invol (a : ZMod (2 * c - 1)) (P : Option (ZMod (2 * c - 1))) :
    pim a (pim a P) = P := by
  match P with
  | none =>
    simp [pim]
  | some x =>
    by_cases hx : x = a
    · simp [pim, hx]
    · have hne : 2 * a - x ≠ a := by
        intro h
        apply hx
        have h' : a = x := by linear_combination h
        exact h'.symm
      simp only [pim, if_neg hx, if_neg hne]
      congr 1
      ring

/-- (F2) `pim a` has no fixed point. -/
lemma pim_ne (hc : 1 ≤ c) (a : ZMod (2 * c - 1)) (P : Option (ZMod (2 * c - 1))) :
    pim a P ≠ P := by
  match P with
  | none => simp [pim]
  | some x =>
    by_cases hx : x = a
    · simp [pim, hx]
    · simp only [pim, if_neg hx, ne_eq, Option.some.injEq]
      intro h
      apply hx
      apply two_cancel hc
      linear_combination -h

/-- (F3, uniqueness) the round `a` is determined by one matched pair. -/
lemma pim_arg_inj (hc : 1 ≤ c) {a b : ZMod (2 * c - 1)}
    (X : Option (ZMod (2 * c - 1))) (h : pim a X = pim b X) : a = b := by
  match X with
  | none => simpa [pim] using h
  | some x =>
    by_cases hxa : x = a <;> by_cases hxb : x = b
    · rw [← hxa, ← hxb]
    · rw [pim, pim, if_pos hxa, if_neg hxb] at h
      exact absurd h (by simp)
    · rw [pim, pim, if_neg hxa, if_pos hxb] at h
      exact absurd h (by simp)
    · rw [pim, pim, if_neg hxa, if_neg hxb, Option.some.injEq] at h
      apply two_cancel hc
      linear_combination h

/-- (F3, existence) a round matching `X` to `Y`. -/
def solveA : Option (ZMod (2 * c - 1)) → Option (ZMod (2 * c - 1)) → ZMod (2 * c - 1)
  | none, some y => y
  | some x, none => x
  | some x, some y => (c : ZMod (2 * c - 1)) * (x + y)
  | none, none => 0

lemma pim_solveA (hc : 1 ≤ c) {X Y : Option (ZMod (2 * c - 1))} (hXY : X ≠ Y) :
    pim (solveA X Y) X = Y := by
  match X, Y with
  | none, none => exact absurd rfl hXY
  | none, some y => simp [pim, solveA]
  | some x, none => simp [pim, solveA]
  | some x, some y =>
    have hxy : x ≠ y := by
      intro h; exact hXY (by rw [h])
    have h2 : 2 * ((c : ZMod (2 * c - 1)) * (x + y)) = x + y := by
      calc 2 * ((c : ZMod (2 * c - 1)) * (x + y))
          = ((2 : ZMod (2 * c - 1)) * c) * (x + y) := by ring
        _ = x + y := by rw [two_mul_c hc, one_mul]
    have hxa : x ≠ (c : ZMod (2 * c - 1)) * (x + y) := by
      intro h
      apply hxy
      have h3 : 2 * x = x + y := by
        calc 2 * x = 2 * ((c : ZMod (2 * c - 1)) * (x + y)) := by rw [← h]
          _ = x + y := h2
      linear_combination h3
    rw [show solveA (some x) (some y) = (c : ZMod (2 * c - 1)) * (x + y) from rfl]
    simp only [pim]
    rw [if_neg hxa]
    congr 1
    linear_combination h2

/-- (F4) orientation of the round-`a` matching. -/
def orient (a : ZMod (2 * c - 1)) : Option (ZMod (2 * c - 1)) → Bool
  | none => false
  | some x => if x = a then true else decide (c ≤ (x - a).val)

/-- (F4) flip law: the partner has the opposite orientation. -/
lemma orient_pim (hc : 1 ≤ c) (a : ZMod (2 * c - 1)) (P : Option (ZMod (2 * c - 1))) :
    orient a (pim a P) = ! orient a P := by
  have : NeZero (2 * c - 1) := ⟨by omega⟩
  match P with
  | none => simp [pim, orient]
  | some x =>
    by_cases hx : x = a
    · simp [pim, orient, hx]
    · have hne : 2 * a - x ≠ a := by
        intro h
        apply hx
        have h' : a = x := by linear_combination h
        exact h'.symm
      simp only [pim, orient, if_neg hx, if_neg hne]
      have hz : x - a ≠ 0 := sub_ne_zero_of_ne hx
      have hz' : (2 * a - x) - a = -(x - a) := by ring
      rw [hz', ZMod.neg_val, if_neg hz]
      have hv1 : 1 ≤ (x - a).val := by
        rcases Nat.eq_zero_or_pos (x - a).val with h0 | h0
        · exact absurd ((ZMod.val_eq_zero _).mp h0) hz
        · exact h0
      have hv2 : (x - a).val < 2 * c - 1 := ZMod.val_lt _
      rw [← decide_not]
      apply decide_eq_decide.mpr
      omega

end Core

/-! ### Sides: `Fin 2` helpers -/

/-- The side flip. -/
def flip2 (s : Fin 2) : Fin 2 := ⟨1 - s.val, by omega⟩

lemma flip2_flip2 (s : Fin 2) : flip2 (flip2 s) = s := by
  have hs := s.isLt
  apply Fin.ext
  show 1 - (1 - s.val) = s.val
  omega

lemma flip2_ne (s : Fin 2) : flip2 s ≠ s := by
  intro h
  have hv := congrArg Fin.val h
  have hs := s.isLt
  simp only [flip2] at hv
  omega

lemma fin2_eq_or_flip (s s' : Fin 2) : s' = s ∨ s' = flip2 s := by
  have h1 := s.isLt
  have h2 := s'.isLt
  by_cases h : s'.val = s.val
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (show s'.val = 1 - s.val by omega))

/-- The side as a Boolean direction. -/
def sideBool (s : Fin 2) : Bool := decide (s.val = 1)

lemma sideBool_flip2 (s : Fin 2) : sideBool (flip2 s) = ! sideBool s := by
  have hs := s.isLt
  by_cases h : s.val = 1
  · simp [sideBool, flip2, h]
  · have h0 : s.val = 0 := by omega
    simp [sideBool, flip2, h0]

/-! ### The label bijection `Fin c × Fin 2 ≃ Option (ZMod (2c-1))` -/

section Lab

variable {c : ℕ}

/-- The labeling of super-vertices (copy, side) by round-robin labels. -/
def lab (P : Fin c × Fin 2) : Option (ZMod (2 * c - 1)) :=
  if P.2.val = 0 then
    (if P.1.val = 0 then none else some ((P.1.val : ℕ) : ZMod (2 * c - 1)))
  else some (-((P.1.val : ℕ) : ZMod (2 * c - 1)))

/-- The inverse labeling. -/
def labInv (hc : 1 ≤ c) (Q : Option (ZMod (2 * c - 1))) : Fin c × Fin 2 :=
  match Q with
  | none => (⟨0, hc⟩, ⟨0, by omega⟩)
  | some x =>
    if h : x.val < c then
      (⟨x.val, h⟩, if x = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩)
    else
      (⟨2 * c - 1 - x.val, by omega⟩, ⟨1, by omega⟩)

lemma copy_val_lt (hc : 1 ≤ c) (u : Fin c) : u.val < 2 * c - 1 := by
  have := u.isLt
  omega

lemma cast_copy_val (hc : 1 ≤ c) (u : Fin c) :
    ((u.val : ℕ) : ZMod (2 * c - 1)).val = u.val :=
  ZMod.val_cast_of_lt (copy_val_lt hc u)

lemma cast_copy_ne_zero (hc : 1 ≤ c) {u : Fin c} (hu : u.val ≠ 0) :
    ((u.val : ℕ) : ZMod (2 * c - 1)) ≠ 0 := by
  intro h
  apply hu
  rw [← cast_copy_val hc u]
  exact (ZMod.val_eq_zero _).mpr h

/-! Evaluation lemmas for `lab`, `labInv`, `pim`. -/

lemma lab_s0_u0 {u : Fin c} {s : Fin 2} (hs : s.val = 0) (hu : u.val = 0) :
    lab (u, s) = none := by
  simp only [lab]
  rw [if_pos hs, if_pos hu]

lemma lab_s0_u1 {u : Fin c} {s : Fin 2} (hs : s.val = 0) (hu : u.val ≠ 0) :
    lab (u, s) = some ((u.val : ℕ) : ZMod (2 * c - 1)) := by
  simp only [lab]
  rw [if_pos hs, if_neg hu]

lemma lab_s1 {u : Fin c} {s : Fin 2} (hs : s.val ≠ 0) :
    lab (u, s) = some (-((u.val : ℕ) : ZMod (2 * c - 1))) := by
  simp only [lab]
  rw [if_neg hs]

lemma pim_none (a : ZMod (2 * c - 1)) : pim a none = some a := rfl

lemma pim_some_eq {a x : ZMod (2 * c - 1)} (h : x = a) : pim a (some x) = none := by
  simp only [pim]
  rw [if_pos h]

lemma pim_some_ne {a x : ZMod (2 * c - 1)} (h : x ≠ a) :
    pim a (some x) = some (2 * a - x) := by
  simp only [pim]
  rw [if_neg h]

lemma labInv_none (hc : 1 ≤ c) : labInv hc none = (⟨0, hc⟩, ⟨0, by omega⟩) := rfl

lemma labInv_some_lt (hc : 1 ≤ c) {x : ZMod (2 * c - 1)} (h : x.val < c) (hx : x ≠ 0) :
    labInv hc (some x) = (⟨x.val, h⟩, ⟨0, by omega⟩) := by
  simp only [labInv]
  rw [dif_pos h, if_neg hx]

lemma labInv_some_zero (hc : 1 ≤ c) :
    labInv hc (some (0 : ZMod (2 * c - 1))) = (⟨0, hc⟩, ⟨1, by omega⟩) := by
  have hv : (0 : ZMod (2 * c - 1)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
  have h0 : (0 : ZMod (2 * c - 1)).val < c := by omega
  simp only [labInv]
  rw [dif_pos h0]
  simp only [if_true]
  refine congrArg₂ Prod.mk (Fin.ext ?_) rfl
  exact hv

lemma labInv_some_ge (hc : 1 ≤ c) {x : ZMod (2 * c - 1)} (h : ¬ x.val < c) :
    labInv hc (some x) = (⟨2 * c - 1 - x.val, by omega⟩, ⟨1, by omega⟩) := by
  simp only [labInv]
  rw [dif_neg h]

/-! Round trips. -/

lemma labInv_lab (hc : 1 ≤ c) (P : Fin c × Fin 2) :
    labInv hc (lab P) = P := by
  have hnz : NeZero (2 * c - 1) := ⟨by omega⟩
  obtain ⟨u, s⟩ := P
  have hs2 := s.isLt
  by_cases hs0 : s.val = 0
  · by_cases hu0 : u.val = 0
    · rw [lab_s0_u0 hs0 hu0, labInv_none hc]
      exact congrArg₂ Prod.mk (Fin.ext (by simpa using hu0.symm))
        (Fin.ext (by simpa using hs0.symm))
    · rw [lab_s0_u1 hs0 hu0]
      have hval : ((u.val : ℕ) : ZMod (2 * c - 1)).val = u.val := cast_copy_val hc u
      have hlt : ((u.val : ℕ) : ZMod (2 * c - 1)).val < c := by
        rw [hval]; exact u.isLt
      rw [labInv_some_lt hc hlt (cast_copy_ne_zero hc hu0)]
      exact congrArg₂ Prod.mk (Fin.ext (by simpa using hval))
        (Fin.ext (by simpa using hs0.symm))
  · by_cases hu0 : u.val = 0
    · have hcast : ((u.val : ℕ) : ZMod (2 * c - 1)) = 0 := by
        rw [hu0]; exact Nat.cast_zero
      rw [lab_s1 hs0, hcast, neg_zero, labInv_some_zero hc]
      exact congrArg₂ Prod.mk (Fin.ext (by simpa using hu0.symm))
        (Fin.ext (by simpa using (show s.val = 1 by omega).symm))
    · rw [lab_s1 hs0]
      have hval : ((u.val : ℕ) : ZMod (2 * c - 1)).val = u.val := cast_copy_val hc u
      have hnegval : (-((u.val : ℕ) : ZMod (2 * c - 1))).val = 2 * c - 1 - u.val := by
        rw [ZMod.neg_val, if_neg (cast_copy_ne_zero hc hu0), hval]
      have hnlt : ¬ (-((u.val : ℕ) : ZMod (2 * c - 1))).val < c := by
        rw [hnegval]
        have := u.isLt
        omega
      rw [labInv_some_ge hc hnlt]
      refine congrArg₂ Prod.mk (Fin.ext ?_) (Fin.ext (by simpa using (show s.val = 1 by omega).symm))
      show 2 * c - 1 - (-((u.val : ℕ) : ZMod (2 * c - 1))).val = u.val
      rw [hnegval]
      have := u.isLt
      omega

lemma lab_inj (hc : 1 ≤ c) {P P' : Fin c × Fin 2} (h : lab P = lab P') : P = P' := by
  rw [← labInv_lab hc P, ← labInv_lab hc P', h]

lemma lab_labInv (hc : 1 ≤ c) (Q : Option (ZMod (2 * c - 1))) :
    lab (labInv hc Q) = Q := by
  have hnz : NeZero (2 * c - 1) := ⟨by omega⟩
  have hbij : Function.Bijective (lab (c := c)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun P P' h => lab_inj hc h, ?_⟩
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_option, ZMod.card]
    omega
  obtain ⟨P, hP⟩ := hbij.2 Q
  rw [← hP, labInv_lab hc]

/-- Crux: the round-0 partner of a label is the label of the *same copy*, other side. -/
lemma pim_zero_lab (hc : 1 ≤ c) (u : Fin c) (s : Fin 2) :
    pim 0 (lab (u, s)) = lab (u, flip2 s) := by
  have hs2 := s.isLt
  by_cases hs0 : s.val = 0
  · have hflip : (flip2 s).val ≠ 0 := by simp only [flip2]; omega
    by_cases hu0 : u.val = 0
    · rw [lab_s0_u0 hs0 hu0, lab_s1 hflip, pim_none]
      have hcast : ((u.val : ℕ) : ZMod (2 * c - 1)) = 0 := by
        rw [hu0]; exact Nat.cast_zero
      rw [hcast, neg_zero]
    · have hx0 : ((u.val : ℕ) : ZMod (2 * c - 1)) ≠ 0 := cast_copy_ne_zero hc hu0
      rw [lab_s0_u1 hs0 hu0, lab_s1 hflip, pim_some_ne hx0]
      congr 1
      ring
  · have hflip0 : (flip2 s).val = 0 := by simp only [flip2]; omega
    by_cases hu0 : u.val = 0
    · have hcast : ((u.val : ℕ) : ZMod (2 * c - 1)) = 0 := by
        rw [hu0]; exact Nat.cast_zero
      rw [lab_s1 hs0, hcast, neg_zero, lab_s0_u0 hflip0 hu0, pim_some_eq rfl]
    · have hx0 : ((u.val : ℕ) : ZMod (2 * c - 1)) ≠ 0 := cast_copy_ne_zero hc hu0
      have hnx0 : -((u.val : ℕ) : ZMod (2 * c - 1)) ≠ 0 := by simpa using hx0
      rw [lab_s1 hs0, lab_s0_u1 hflip0 hu0, pim_some_ne hnx0]
      congr 1
      ring

/-- For a nonzero round, the partner super-vertex lies in a different copy. -/
lemma cross_copy_ne (hc : 1 ≤ c) {a : ZMod (2 * c - 1)} (ha : a ≠ 0)
    (u : Fin c) (s : Fin 2) :
    (labInv hc (pim a (lab (u, s)))).1 ≠ u := by
  intro hEq
  have hlabP' : lab (labInv hc (pim a (lab (u, s)))) = pim a (lab (u, s)) :=
    lab_labInv hc _
  have hP'eq : labInv hc (pim a (lab (u, s)))
      = (u, (labInv hc (pim a (lab (u, s)))).2) := by
    exact Prod.ext hEq rfl
  rcases fin2_eq_or_flip s (labInv hc (pim a (lab (u, s)))).2 with h1 | h1
  · have hcontra : pim a (lab (u, s)) = lab (u, s) := by
      rw [← hlabP', hP'eq, h1]
    exact pim_ne hc a _ hcontra
  · have hcontra : pim a (lab (u, s)) = pim 0 (lab (u, s)) := by
      rw [← hlabP', hP'eq, h1, ← pim_zero_lab hc]
    exact ha (pim_arg_inj hc _ hcontra)

/-- Coverage: for distinct copies there is a nonzero round matching the labels. -/
lemma cross_exists (hc : 1 ≤ c) {u u' : Fin c} (hne : u ≠ u') (s s' : Fin 2) :
    ∃ a : ZMod (2 * c - 1), a ≠ 0 ∧ pim a (lab (u, s)) = lab (u', s') := by
  have hXY : lab (u, s) ≠ lab (u', s') := by
    intro h
    exact hne (congrArg Prod.fst (lab_inj hc h))
  refine ⟨solveA (lab (u, s)) (lab (u', s')), ?_, pim_solveA hc hXY⟩
  intro h0
  have h1 : lab (u', s') = lab (u, flip2 s) := by
    rw [← pim_zero_lab hc, ← h0, pim_solveA hc hXY]
  exact hne (congrArg Prod.fst (lab_inj hc h1)).symm

end Lab

/-! ### Positions: shifts in `ZMod k` -/

section Pos

variable {k : ℕ}

/-- Convert `ZMod k` back to `Fin k`. -/
def toF (hk : 0 < k) (z : ZMod k) : Fin k :=
  ⟨z.val, by have : NeZero k := ⟨by omega⟩; exact ZMod.val_lt z⟩

lemma toF_val_cast (hk : 0 < k) (i : Fin k) : toF hk ((i.val : ℕ) : ZMod k) = i :=
  Fin.ext (ZMod.val_cast_of_lt i.isLt)

lemma cast_toF (hk : 0 < k) (z : ZMod k) : (((toF hk z).val : ℕ) : ZMod k) = z := by
  have : NeZero k := ⟨by omega⟩
  exact ZMod.natCast_zmod_val z

lemma toF_inj (hk : 0 < k) {z z' : ZMod k} (h : toF hk z = toF hk z') : z = z' := by
  rw [← cast_toF hk z, ← cast_toF hk z', h]

/-- Shift a position by `β`, in the direction given by `b`. -/
def move (hk : 0 < k) : Bool → ZMod k → Fin k → Fin k
  | false, β, i => toF hk ((i.val : ZMod k) + β)
  | true, β, i => toF hk ((i.val : ZMod k) - β)

lemma move_move (hk : 0 < k) (b : Bool) (β : ZMod k) (i : Fin k) :
    move hk (!b) β (move hk b β i) = i := by
  cases b
  · show toF hk (((toF hk ((i.val : ZMod k) + β)).val : ZMod k) - β) = i
    rw [cast_toF, show ((i.val : ZMod k) + β) - β = ((i.val : ℕ) : ZMod k) from by ring,
      toF_val_cast]
  · show toF hk (((toF hk ((i.val : ZMod k) - β)).val : ZMod k) + β) = i
    rw [cast_toF, show ((i.val : ZMod k) - β) + β = ((i.val : ℕ) : ZMod k) from by ring,
      toF_val_cast]

lemma move_ne (hk : 0 < k) {β : ZMod k} (hβ : β ≠ 0) (b : Bool) (i : Fin k) :
    move hk b β i ≠ i := by
  intro h
  apply hβ
  cases b
  · have h' : toF hk ((i.val : ZMod k) + β) = toF hk ((i.val : ℕ) : ZMod k) := by
      rw [toF_val_cast]; exact h
    have := toF_inj hk h'
    linear_combination this
  · have h' : toF hk ((i.val : ZMod k) - β) = toF hk ((i.val : ℕ) : ZMod k) := by
      rw [toF_val_cast]; exact h
    have := toF_inj hk h'
    linear_combination -this

lemma move_inj (hk : 0 < k) (b : Bool) {β β' : ZMod k} (i : Fin k)
    (h : move hk b β i = move hk b β' i) : β = β' := by
  cases b
  · have := toF_inj hk (z := (i.val : ZMod k) + β) (z' := (i.val : ZMod k) + β') h
    linear_combination this
  · have := toF_inj hk (z := (i.val : ZMod k) - β) (z' := (i.val : ZMod k) - β') h
    linear_combination -this

/-- The shift needed to move `i` to `j` in direction `b`. -/
def moveSolve (b : Bool) (i j : Fin k) : ZMod k :=
  if b then (i.val : ZMod k) - (j.val : ZMod k) else (j.val : ZMod k) - (i.val : ZMod k)

lemma move_moveSolve (hk : 0 < k) (b : Bool) (i j : Fin k) :
    move hk b (moveSolve b i j) i = j := by
  cases b
  · show toF hk ((i.val : ZMod k) + ((j.val : ZMod k) - (i.val : ZMod k))) = j
    rw [show (i.val : ZMod k) + ((j.val : ZMod k) - (i.val : ZMod k))
        = ((j.val : ℕ) : ZMod k) from by ring, toF_val_cast]
  · show toF hk ((i.val : ZMod k) - ((i.val : ZMod k) - (j.val : ZMod k))) = j
    rw [show (i.val : ZMod k) - ((i.val : ZMod k) - (j.val : ZMod k))
        = ((j.val : ℕ) : ZMod k) from by ring, toF_val_cast]

lemma moveSolve_ne_zero (hk : 0 < k) (b : Bool) {i j : Fin k} (hij : i ≠ j) :
    moveSolve b i j ≠ 0 := by
  have hcast : ((i.val : ℕ) : ZMod k) ≠ ((j.val : ℕ) : ZMod k) := by
    intro h
    exact hij (by rw [← toF_val_cast hk i, ← toF_val_cast hk j, h])
  cases b
  · show (j.val : ZMod k) - (i.val : ZMod k) ≠ 0
    exact fun h => hcast (by linear_combination -h)
  · show (i.val : ZMod k) - (j.val : ZMod k) ≠ 0
    exact fun h => hcast (by linear_combination h)

end Pos

/-! ### The two factor families -/

section Factors

variable {c k : ℕ}

/-- Within-copy factor with shift `d`: flip the side, shift the position. -/
def withinF (hk : 0 < k) (d : ZMod k) (v : V c k) : V c k :=
  (v.1, flip2 v.2.1, move hk (sideBool v.2.1) d v.2.2)

/-- Cross-copy factor for round `a` and shift `β`: move to the round-robin partner
super-vertex, shifting the position in the direction given by the orientation. -/
def crossF (hc : 1 ≤ c) (hk : 0 < k) (a : ZMod (2 * c - 1)) (β : ZMod k) (v : V c k) :
    V c k :=
  ((labInv hc (pim a (lab (v.1, v.2.1)))).1,
   (labInv hc (pim a (lab (v.1, v.2.1)))).2,
   move hk (orient a (lab (v.1, v.2.1))) β v.2.2)

lemma withinF_invol (hk : 0 < k) (d : ZMod k) (v : V c k) :
    withinF hk d (withinF hk d v) = v := by
  obtain ⟨u, s, i⟩ := v
  simp only [withinF]
  rw [sideBool_flip2, move_move, flip2_flip2]

lemma withinF_adj (hk : 0 < k) {d : ZMod k} (hd : d ≠ 0) (v : V c k) :
    (compl c k).Adj v (withinF hk d v) := by
  rw [adj_iff]
  right
  exact ⟨fun h => flip2_ne v.2.1 h.symm, fun h => move_ne hk hd (sideBool v.2.1) v.2.2 h.symm⟩

lemma withinF_inj_d (hk : 0 < k) {d d' : ZMod k} (v : V c k)
    (h : withinF hk d v = withinF hk d' v) : d = d' := by
  have h3 : move hk (sideBool v.2.1) d v.2.2 = move hk (sideBool v.2.1) d' v.2.2 :=
    congrArg (fun z : V c k => z.2.2) h
  exact move_inj hk _ v.2.2 h3

lemma crossF_invol (hc : 1 ≤ c) (hk : 0 < k) (a : ZMod (2 * c - 1)) (β : ZMod k)
    (v : V c k) : crossF hc hk a β (crossF hc hk a β v) = v := by
  obtain ⟨u, s, i⟩ := v
  simp only [crossF, Prod.mk.eta]
  rw [lab_labInv hc, pim_invol, orient_pim hc, move_move, labInv_lab hc]

lemma crossF_adj (hc : 1 ≤ c) (hk : 0 < k) {a : ZMod (2 * c - 1)} (ha : a ≠ 0)
    (β : ZMod k) (v : V c k) : (compl c k).Adj v (crossF hc hk a β v) := by
  rw [adj_iff]
  left
  exact fun h => cross_copy_ne hc ha v.1 v.2.1 h.symm

lemma crossF_inj_params (hc : 1 ≤ c) (hk : 0 < k) {a a' : ZMod (2 * c - 1)}
    {β β' : ZMod k} (v : V c k)
    (h : crossF hc hk a β v = crossF hc hk a' β' v) : a = a' ∧ β = β' := by
  have h1 : (labInv hc (pim a (lab (v.1, v.2.1)))).1
      = (labInv hc (pim a' (lab (v.1, v.2.1)))).1 := congrArg (fun z : V c k => z.1) h
  have h2 : (labInv hc (pim a (lab (v.1, v.2.1)))).2
      = (labInv hc (pim a' (lab (v.1, v.2.1)))).2 := congrArg (fun z : V c k => z.2.1) h
  have hP : labInv hc (pim a (lab (v.1, v.2.1))) = labInv hc (pim a' (lab (v.1, v.2.1))) :=
    Prod.ext h1 h2
  have hpim : pim a (lab (v.1, v.2.1)) = pim a' (lab (v.1, v.2.1)) := by
    rw [← lab_labInv hc (pim a (lab (v.1, v.2.1))),
      ← lab_labInv hc (pim a' (lab (v.1, v.2.1))), hP]
  have ha : a = a' := pim_arg_inj hc _ hpim
  subst ha
  have h3 : move hk (orient a (lab (v.1, v.2.1))) β v.2.2
      = move hk (orient a (lab (v.1, v.2.1))) β' v.2.2 :=
    congrArg (fun z : V c k => z.2.2) h
  exact ⟨rfl, move_inj hk _ v.2.2 h3⟩

end Factors

/-! ### Index packing and the full family -/

section Assemble

variable {c k : ℕ}

lemma N_split (hk : 2 ≤ k) (hc : 1 ≤ c) :
    2 * k * c - k - 1 = (k - 1) + (2 * c - 2) * k := by
  have e1 : 2 * k * c = 2 * (k * c) := by ring
  have e2 : (2 * c - 2) * k = 2 * (k * c) - 2 * k := by
    rw [Nat.sub_mul]
    congr 1
    ring
  have e3 : k ≤ k * c := Nat.le_mul_of_pos_right k (by omega)
  omega

/-- The packed family of factors. -/
def bigF (hc : 1 ≤ c) (hk : 0 < k) (t : Fin (2 * k * c - k - 1)) : V c k → V c k :=
  if t.val < k - 1 then withinF hk ((t.val + 1 : ℕ) : ZMod k)
  else crossF hc hk (((t.val - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
    (((t.val - (k - 1)) % k : ℕ) : ZMod k)

lemma bigF_lt (hc : 1 ≤ c) (hk : 0 < k) {t : Fin (2 * k * c - k - 1)}
    (ht : t.val < k - 1) :
    bigF hc hk t = withinF hk ((t.val + 1 : ℕ) : ZMod k) := by
  simp only [bigF]
  rw [if_pos ht]

lemma bigF_ge (hc : 1 ≤ c) (hk : 0 < k) {t : Fin (2 * k * c - k - 1)}
    (ht : ¬ t.val < k - 1) :
    bigF hc hk t = crossF hc hk (((t.val - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
      (((t.val - (k - 1)) % k : ℕ) : ZMod k) := by
  simp only [bigF]
  rw [if_neg ht]

/-- Decoding facts for a cross index. -/
lemma decode_cross (hk2 : 2 ≤ k) (hc : 1 ≤ c) {t : ℕ}
    (ht1 : ¬ t < k - 1) (ht2 : t < 2 * k * c - k - 1) :
    ((((t - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1)).val = (t - (k - 1)) / k + 1)
    ∧ ((((t - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1)) ≠ 0)
    ∧ ((((t - (k - 1)) % k : ℕ) : ZMod k).val = (t - (k - 1)) % k) := by
  have hN := N_split hk2 hc
  have hq : t - (k - 1) < (2 * c - 2) * k := by omega
  have hdiv : (t - (k - 1)) / k < 2 * c - 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
  have hlt : (t - (k - 1)) / k + 1 < 2 * c - 1 := by
    calc (t - (k - 1)) / k + 1 < (2 * c - 2) + 1 := Nat.add_lt_add_right hdiv 1
      _ ≤ 2 * c - 1 := by omega
  refine ⟨ZMod.val_cast_of_lt hlt, ?_, ZMod.val_cast_of_lt (Nat.mod_lt _ (by omega))⟩
  intro h0
  have hval := (ZMod.val_eq_zero _).mpr h0
  rw [ZMod.val_cast_of_lt hlt] at hval
  exact Nat.succ_ne_zero _ hval

end Assemble

/-! ### The main theorem -/

theorem proof :
    ∀ k c : ℕ, 2 ≤ k → 1 ≤ c →
      ∃ F : Fin (2 * k * c - k - 1) → V c k → V c k,
        (∀ t v, (compl c k).Adj v (F t v)) ∧
        (∀ t v, F t (F t v) = v) ∧
        (∀ v w, (compl c k).Adj v w → ∃! t, F t v = w) := by
  intro k c hk hc
  have hk0 : 0 < k := by omega
  have hnzk : NeZero k := ⟨by omega⟩
  have hnzc : NeZero (2 * c - 1) := ⟨by omega⟩
  have hN := N_split (c := c) hk hc
  refine ⟨bigF hc hk0, ?_, ?_, ?_⟩
  · -- adjacency
    intro t v
    by_cases ht : t.val < k - 1
    · rw [bigF_lt hc hk0 ht]
      apply withinF_adj hk0 _ v
      intro h0
      have hval : (((t.val + 1 : ℕ) : ZMod k)).val = 0 := (ZMod.val_eq_zero _).mpr h0
      rw [ZMod.val_cast_of_lt (show t.val + 1 < k by omega)] at hval
      omega
    · rw [bigF_ge hc hk0 ht]
      obtain ⟨hva, ha0, hvb⟩ := decode_cross hk hc ht t.isLt
      exact crossF_adj hc hk0 ha0 _ v
  · -- involution
    intro t v
    by_cases ht : t.val < k - 1
    · rw [bigF_lt hc hk0 ht]
      exact withinF_invol hk0 _ v
    · rw [bigF_ge hc hk0 ht]
      exact crossF_invol hc hk0 _ _ v
  · -- uniqueness
    intro v w hadj
    rw [adj_iff] at hadj
    by_cases hcopy : v.1 = w.1
    · -- within-copy edge
      obtain ⟨hss, hii⟩ : v.2.1 ≠ w.2.1 ∧ v.2.2 ≠ w.2.2 := by
        rcases hadj with h | h
        · exact absurd hcopy h
        · exact h
      set d := moveSolve (sideBool v.2.1) v.2.2 w.2.2 with hddef
      have hd0 : d ≠ 0 := moveSolve_ne_zero hk0 _ hii
      have hdval1 : 1 ≤ d.val := by
        rcases Nat.eq_zero_or_pos d.val with h0 | h0
        · exact absurd ((ZMod.val_eq_zero _).mp h0) hd0
        · exact h0
      have hdvalk : d.val < k := ZMod.val_lt d
      have hwd : withinF hk0 d v = w := by
        have hflip : flip2 v.2.1 = w.2.1 := by
          rcases fin2_eq_or_flip v.2.1 w.2.1 with h | h
          · exact absurd h.symm hss
          · exact h.symm
        exact Prod.ext hcopy (Prod.ext hflip (move_moveSolve hk0 _ _ _))
      have htv : d.val - 1 < 2 * k * c - k - 1 := by omega
      refine ⟨⟨d.val - 1, htv⟩, ?_, ?_⟩
      · show bigF hc hk0 ⟨d.val - 1, htv⟩ v = w
        have htlt' : (⟨d.val - 1, htv⟩ : Fin (2 * k * c - k - 1)).val < k - 1 := by
          show d.val - 1 < k - 1
          omega
        rw [bigF_lt hc hk0 htlt']
        have hcast : ((((⟨d.val - 1, htv⟩ : Fin (2 * k * c - k - 1)).val + 1 : ℕ))
            : ZMod k) = d := by
          show (((d.val - 1) + 1 : ℕ) : ZMod k) = d
          rw [show d.val - 1 + 1 = d.val from by omega, ZMod.natCast_zmod_val]
        rw [hcast]
        exact hwd
      · intro t' ht'
        by_cases ht'lt : t'.val < k - 1
        · rw [bigF_lt hc hk0 ht'lt] at ht'
          have hdd : ((t'.val + 1 : ℕ) : ZMod k) = d :=
            withinF_inj_d hk0 v (ht'.trans hwd.symm)
          have hval := congrArg ZMod.val hdd
          rw [ZMod.val_cast_of_lt (show t'.val + 1 < k by omega)] at hval
          apply Fin.ext
          show t'.val = d.val - 1
          omega
        · rw [bigF_ge hc hk0 ht'lt] at ht'
          obtain ⟨hva', ha0', hvb'⟩ := decode_cross hk hc ht'lt t'.isLt
          have h1 : (crossF hc hk0 (((t'.val - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
              (((t'.val - (k - 1)) % k : ℕ) : ZMod k) v).1 = w.1 :=
            congrArg Prod.fst ht'
          exact absurd (h1.trans hcopy.symm) (cross_copy_ne hc ha0' v.1 v.2.1)
    · -- cross-copy edge
      have hc2 : 2 ≤ c := by
        have h1 := v.1.isLt
        have h2 := w.1.isLt
        by_contra hcon
        exact hcopy (Fin.ext (by omega))
      obtain ⟨a, ha0, hpa⟩ := cross_exists hc hcopy v.2.1 w.2.1
      obtain ⟨β, hβmove⟩ :
          ∃ β, move hk0 (orient a (lab (v.1, v.2.1))) β v.2.2 = w.2.2 :=
        ⟨moveSolve _ _ _, move_moveSolve hk0 _ _ _⟩
      have hcross : crossF hc hk0 a β v = w := by
        show ((labInv hc (pim a (lab (v.1, v.2.1)))).1,
              (labInv hc (pim a (lab (v.1, v.2.1)))).2,
              move hk0 (orient a (lab (v.1, v.2.1))) β v.2.2) = w
        rw [hpa, labInv_lab hc]
        exact Prod.ext rfl (Prod.ext rfl hβmove)
      have hav1 : 1 ≤ a.val := by
        rcases Nat.eq_zero_or_pos a.val with h0 | h0
        · exact absurd ((ZMod.val_eq_zero _).mp h0) ha0
        · exact h0
      have hav2 : a.val < 2 * c - 1 := ZMod.val_lt a
      have hβv : β.val < k := ZMod.val_lt β
      set tq := β.val + (a.val - 1) * k with htq
      have hdiv : tq / k = a.val - 1 := by
        rw [htq, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt hβv, Nat.zero_add]
      have hmod : tq % k = β.val := by
        rw [htq, Nat.add_mul_mod_self_right β.val (a.val - 1) k, Nat.mod_eq_of_lt hβv]
      have hacast : ((tq / k + 1 : ℕ) : ZMod (2 * c - 1)) = a := by
        rw [hdiv, show a.val - 1 + 1 = a.val from by omega, ZMod.natCast_zmod_val]
      have hbcast : ((tq % k : ℕ) : ZMod k) = β := by
        rw [hmod, ZMod.natCast_zmod_val]
      have hbound1 : (a.val - 1) * k ≤ (2 * c - 3) * k :=
        Nat.mul_le_mul_right k (by omega)
      have hbound2 : (2 * c - 3) * k + k = (2 * c - 2) * k := by
        rw [show 2 * c - 2 = (2 * c - 3) + 1 from by omega, Nat.add_mul, Nat.one_mul]
      have htlt : (k - 1) + tq < 2 * k * c - k - 1 := by omega
      refine ⟨⟨(k - 1) + tq, htlt⟩, ?_, ?_⟩
      · show bigF hc hk0 ⟨(k - 1) + tq, htlt⟩ v = w
        have htge : ¬ ((⟨(k - 1) + tq, htlt⟩ : Fin (2 * k * c - k - 1)).val < k - 1) := by
          show ¬ ((k - 1) + tq < k - 1)
          omega
        rw [bigF_ge hc hk0 htge]
        show crossF hc hk0 ((((k - 1) + tq - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
          ((((k - 1) + tq - (k - 1)) % k : ℕ) : ZMod k) v = w
        rw [show (k - 1) + tq - (k - 1) = tq from by omega, hacast, hbcast]
        exact hcross
      · intro t' ht'
        by_cases ht'lt : t'.val < k - 1
        · rw [bigF_lt hc hk0 ht'lt] at ht'
          have h1 : (withinF hk0 ((t'.val + 1 : ℕ) : ZMod k) v).1 = w.1 :=
            congrArg Prod.fst ht'
          exact absurd h1 hcopy
        · rw [bigF_ge hc hk0 ht'lt] at ht'
          obtain ⟨hva', ha0', hvb'⟩ := decode_cross hk hc ht'lt t'.isLt
          have heq : crossF hc hk0
              (((t'.val - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
              (((t'.val - (k - 1)) % k : ℕ) : ZMod k) v = crossF hc hk0 a β v :=
            ht'.trans hcross.symm
          obtain ⟨haa, hbb⟩ := crossF_inj_params hc hk0 v heq
          have hva2 : (t'.val - (k - 1)) / k + 1 = a.val := by
            have hh := congrArg ZMod.val haa
            rw [hva'] at hh
            exact hh
          have hvb2 : (t'.val - (k - 1)) % k = β.val := by
            have hh := congrArg ZMod.val hbb
            rw [hvb'] at hh
            exact hh
          have hq'k : (t'.val - (k - 1)) / k = a.val - 1 := Nat.eq_sub_of_add_eq hva2
          have hdm : k * ((t'.val - (k - 1)) / k) + (t'.val - (k - 1)) % k
              = t'.val - (k - 1) := Nat.div_add_mod _ k
          have e5 : t'.val - (k - 1) = tq := by
            rw [← hdm, hq'k, hvb2, htq]
            ring
          apply Fin.ext
          show t'.val = (k - 1) + tq
          omega

end Submissions.GadgetComplementOneFactorization.GadgetFactor


/- Source: literature/CliqueComplement.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Extract the complete multipartite part of the existing gadget factorization.
For k=2 its parts have size four, exactly what the K4-block assembly needs. -/

noncomputable section

namespace P14CliqueComplement

open Submissions.GadgetComplementOneFactorization.GadgetFactor

/-- The complement of disjoint cliques of size `2*k` has an explicit
factorization. Each factor is a fixed-point-free involution changing the block. -/
theorem clique_complement_factors {c k : ℕ} (hc : 1 ≤ c) (hk : 0 < k) :
    ∃ F : Fin ((2 * c - 2) * k) → V c k → V c k,
      (∀ t v, (F t v).1 ≠ v.1) ∧
      (∀ t v, F t (F t v) = v) ∧
      (∀ v w, v.1 ≠ w.1 ↔ ∃! t, F t v = w) := by
  classical
  have : NeZero (2 * c - 1) := ⟨by omega⟩
  have : NeZero k := ⟨by omega⟩
  let T := {a : ZMod (2 * c - 1) // a ≠ 0} × ZMod k
  let F : T → V c k → V c k := fun t => crossF hc hk t.1.val t.2
  have hcard : Fintype.card T = (2 * c - 2) * k := by
    simp [T, Fintype.card_subtype_compl, ZMod.card, Nat.sub_sub]
  have hne (t : T) (v : V c k) : (F t v).1 ≠ v.1 :=
    cross_copy_ne hc t.1.property v.1 v.2.1
  have huniq (v w : V c k) : v.1 ≠ w.1 ↔ ∃! t : T, F t v = w := by
    constructor
    · intro hvw
      obtain ⟨a, ha, hpa⟩ := cross_exists hc hvw v.2.1 w.2.1
      let β := moveSolve (orient a (lab (v.1, v.2.1))) v.2.2 w.2.2
      have hβ : move hk (orient a (lab (v.1, v.2.1))) β v.2.2 = w.2.2 :=
        move_moveSolve hk _ _ _
      have hf : F (⟨a, ha⟩, β) v = w := by
        change ((labInv hc (pim a (lab (v.1, v.2.1)))).1,
          (labInv hc (pim a (lab (v.1, v.2.1)))).2,
          move hk (orient a (lab (v.1, v.2.1))) β v.2.2) = w
        rw [hpa, labInv_lab hc]
        exact Prod.ext rfl (Prod.ext rfl hβ)
      refine ⟨(⟨a, ha⟩, β), hf, ?_⟩
      intro t ht
      obtain ⟨h₁, h₂⟩ := crossF_inj_params hc hk v (ht.trans hf.symm)
      exact Prod.ext (Subtype.ext h₁) h₂
    · rintro ⟨t, ht, _⟩ hsame
      exact hne t v (congrArg Prod.fst ht |>.trans hsame.symm)
  let e : Fin ((2 * c - 2) * k) ≃ T :=
    (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun t => F (e t), fun t v => hne (e t) v, ?_, ?_⟩
  · intro t v
    exact crossF_invol hc hk (e t).1.val (e t).2 v
  · intro v w
    rw [huniq]
    exact e.existsUnique_congr_right.symm

end P14CliqueComplement
end


/- Source: literature/CrossComplement.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Direct factorization of the complement of the elliptic cross graph.
The parity argument extends the existing s60 proof to all even and odd offsets.
No graph matching existence theorem is needed. -/

noncomputable section
open Function

namespace P14CrossComplement

abbrev Class (N : ℕ) := Fin N ⊕ Fin N
abbrev Vertex (N : ℕ) := ZMod (2 * N) ⊕ ZMod (2 * N)

def peer {N : ℕ} : Class N → ZMod (2 * N) → ZMod (2 * N)
  | .inl c, i => i + (2 * c.val : ℕ)
  | .inr d, i => -i + (2 * d.val + 1 : ℕ)

def back {N : ℕ} : Class N → ZMod (2 * N) → ZMod (2 * N)
  | .inl c, j => j - (2 * c.val : ℕ)
  | .inr d, j => -j + (2 * d.val + 1 : ℕ)

lemma back_peer {N : ℕ} (a : Class N) (i : ZMod (2 * N)) :
    back a (peer a i) = i := by
  cases a <;> dsimp only [back, peer] <;> ring

lemma peer_back {N : ℕ} (a : Class N) (i : ZMod (2 * N)) :
    peer a (back a i) = i := by
  cases a <;> dsimp only [back, peer] <;> ring

lemma peer_cross_ne {N : ℕ} (hN : 0 < N)
    (i : ZMod (2 * N)) (c d : Fin N) :
    peer (.inl c) i ≠ peer (.inr d) i := by
  have : NeZero (2 * N) := ⟨by omega⟩
  intro h
  have h' : i + i + (2 * c.val : ℕ) = (2 * d.val + 1 : ℕ) := by
    change i + (2 * c.val : ℕ) = -i + (2 * d.val + 1 : ℕ) at h
    linear_combination h
  rw [← ZMod.natCast_zmod_val i] at h'
  have hcast : ((2 * i.val + 2 * c.val : ℕ) : ZMod (2 * N)) =
      (2 * d.val + 1 : ℕ) := by
    simpa [Nat.cast_add, Nat.cast_mul, two_mul] using h'
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hm2 := hm.of_dvd (by omega : 2 ∣ 2 * N)
  simp [Nat.ModEq] at hm2

theorem peer_injective {N : ℕ} (hN : 0 < N) (i : ZMod (2 * N)) :
    Injective (fun a : Class N => peer a i) := by
  intro a b hab
  cases a with
  | inl c =>
    cases b with
    | inl c' =>
      have he : ((2 * c.val : ℕ) : ZMod (2 * N)) = (2 * c'.val : ℕ) :=
        add_left_cancel hab
      have hm := (ZMod.natCast_eq_natCast_iff (2 * c.val) (2 * c'.val) (2 * N)).mp
        he
      have hv := hm.eq_of_lt_of_lt (by omega) (by omega)
      exact congrArg Sum.inl (Fin.ext (by omega))
    | inr d => exact False.elim (peer_cross_ne hN i c d hab)
  | inr d =>
    cases b with
    | inl c => exact False.elim (peer_cross_ne hN i c d hab.symm)
    | inr d' =>
      have he : ((2 * d.val + 1 : ℕ) : ZMod (2 * N)) = (2 * d'.val + 1 : ℕ) :=
        add_left_cancel hab
      have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
      have hv := hm.eq_of_lt_of_lt (by omega) (by omega)
      exact congrArg Sum.inr (Fin.ext (by omega))

theorem peer_bijective {N : ℕ} (hN : 0 < N) (i : ZMod (2 * N)) :
    Bijective (fun a : Class N => peer a i) := by
  have : NeZero (2 * N) := ⟨by omega⟩
  refine ⟨peer_injective hN i, ?_⟩
  by_contra h
  have hc := Fintype.card_lt_of_injective_not_surjective _ (peer_injective hN i) h
  simp only [Class, Fintype.card_sum, Fintype.card_fin, ZMod.card] at hc
  omega

def matchVertex {N : ℕ} (a : Class N) : Vertex N → Vertex N
  | .inl i => .inr (peer a i)
  | .inr j => .inl (back a j)

theorem matchVertex_involutive {N : ℕ} (a : Class N) :
    Involutive (matchVertex a) := by
  intro v
  cases v <;> simp [matchVertex, peer_back, back_peer]

theorem matchVertex_ne {N : ℕ} (a : Class N) (v : Vertex N) :
    matchVertex a v ≠ v := by cases v <;> simp [matchVertex]

def selected {r N : ℕ} (hN : r + 2 ≤ N) : Class r → Class N
  | .inl c => .inl ⟨c.val, by omega⟩
  | .inr d => .inr ⟨d.val + if d.val + 1 = r then 1 else 0, by split <;> omega⟩

theorem selected_injective {r N : ℕ} (hN : r + 2 ≤ N) :
    Injective (selected hN) := by
  intro a b hab
  cases a with
  | inl c =>
    cases b with
    | inl c' =>
      have h := congrArg Fin.val (Sum.inl.inj hab)
      exact congrArg Sum.inl (Fin.ext h)
    | inr d => cases hab
  | inr d =>
    cases b with
    | inl c => cases hab
    | inr d' =>
      have h := congrArg Fin.val (Sum.inr.inj hab)
      change d.val + (if d.val + 1 = r then 1 else 0) =
        d'.val + (if d'.val + 1 = r then 1 else 0) at h
      exact congrArg Sum.inr (Fin.ext (by split_ifs at h <;> omega))

def CrossAdj {r N : ℕ} (i j : ZMod (2 * N)) : Prop :=
  (∃ c : Fin r, j = i + (2 * c.val : ℕ)) ∨
  (∃ d : Fin r, j = -i + (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ))

theorem crossAdj_iff_selected {r N : ℕ} (hN : r + 2 ≤ N)
    (i j : ZMod (2 * N)) :
    CrossAdj (r := r) i j ↔ ∃ a : Class r, peer (selected hN a) i = j := by
  constructor
  · rintro (⟨c, hc⟩ | ⟨d, hd⟩)
    · exact ⟨.inl c, hc.symm⟩
    · refine ⟨.inr d, ?_⟩
      simp only [peer, selected]
      rw [hd]
      congr 1
      split_ifs <;> norm_num
      all_goals ring
  · rintro ⟨a, ha⟩
    cases a with
    | inl c => exact Or.inl ⟨c, ha.symm⟩
    | inr d =>
      refine Or.inr ⟨d, ?_⟩
      rw [← ha]
      simp only [peer, selected]
      congr 1
      split_ifs <;> norm_num
      all_goals ring

abbrev Unused {r N : ℕ} (hN : r + 2 ≤ N) :=
  {a : Class N // a ∉ Set.range (selected hN)}

theorem unused_card {r N : ℕ} (hN : r + 2 ≤ N) :
    Fintype.card (Unused hN) = 2 * N - 2 * r := by
  classical
  have hcard : Fintype.card (Set.range (selected hN)) = 2 * r := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ (selected_injective hN))]
    simp [Class, two_mul]
  change Fintype.card {a : Class N // ¬ a ∈ Set.range (selected hN)} = _
  rw [Fintype.card_subtype_compl, hcard]
  simp [Class, two_mul]

/-- Every non-seed cross edge belongs to exactly one unused matching. -/
theorem complement_unique {r N : ℕ} (hN : r + 2 ≤ N)
    (i j : ZMod (2 * N)) :
    ¬ CrossAdj (r := r) i j ↔ ∃! a : Unused hN, peer a.val i = j := by
  classical
  have hpos : 0 < N := by omega
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (peer_bijective hpos i).surjective j
    have hn : a ∉ Set.range (selected hN) := by
      rintro ⟨b, hb⟩
      apply h
      rw [crossAdj_iff_selected hN]
      exact ⟨b, hb ▸ ha⟩
    refine ⟨⟨a, hn⟩, ha, ?_⟩
    intro b hb
    exact Subtype.ext (peer_injective hpos i (hb.trans ha.symm))
  · rintro ⟨a, ha, _⟩ hadj
    obtain ⟨b, hb⟩ := (crossAdj_iff_selected hN i j).mp hadj
    apply a.property
    exact ⟨b, peer_injective hpos i (hb.trans ha.symm)⟩

def peerEquiv {N : ℕ} (a : Class N) : Equiv.Perm (ZMod (2 * N)) where
  toFun := peer a
  invFun := back a
  left_inv := back_peer a
  right_inv := peer_back a

/-- A finite-indexed family of permutations, one for each unused matching.
Every cross edge outside the seed occurs in exactly one of these matchings. -/
theorem complement_permutations {r N : ℕ} (hN : r + 2 ≤ N) :
    ∃ F : Fin (2 * N - 2 * r) → Equiv.Perm (ZMod (2 * N)),
      ∀ i j, ¬ CrossAdj (r := r) i j ↔ ∃! t, F t i = j := by
  classical
  let e : Fin (2 * N - 2 * r) ≃ Unused hN :=
    (Fintype.equivFinOfCardEq (unused_card hN)).symm
  refine ⟨fun t => peerEquiv (e t).val, ?_⟩
  intro i j
  rw [complement_unique hN]
  exact e.existsUnique_congr_right.symm

end P14CrossComplement
end


/- Source: grouping_audit/QubitMatching.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Explicit qubit vectors for any perfect matching on `Fin m`.
The integer determinant/elimination argument is adapted from the verified
Jig p14 `MinUPB2244/Circulant.lean` construction, now uniformly in the matching.
-/

namespace P14QubitMatching

noncomputable section

def vectorsZ {m : ℕ} (F : Fin m → Fin m) (i : Fin m) : Fin 2 → ℤ :=
  if i < F i then ![1, (i.val : ℤ) + 1]
  else ![-((F i).val : ℤ) - 1, 1]

def vectors {m : ℕ} (F : Fin m → Fin m) (i : Fin m) :
    EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun r => (vectorsZ F i r : ℂ))

def det2Z (x y : Fin 2 → ℤ) : ℤ := x 0 * y 1 - x 1 * y 0

lemma nonzero {m : ℕ} (F : Fin m → Fin m) (i : Fin m) : vectors F i ≠ 0 := by
  intro h
  by_cases hi : i < F i
  · have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 0) h
    simp [vectors, vectorsZ, hi] at h0
  · have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) h
    simp [vectors, vectorsZ, hi] at h1

lemma matching_dotZ {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Involutive F) (hfix : ∀ i, F i ≠ i) (i : Fin m) :
    vectorsZ F i 0 * vectorsZ F (F i) 0 +
      vectorsZ F i 1 * vectorsZ F (F i) 1 = 0 := by
  by_cases hi : i < F i
  · have hj : ¬ F i < i := not_lt_of_gt hi
    simp [vectorsZ, hi, hj, hF i]
  · have hj : F i < i := lt_of_le_of_ne (le_of_not_gt hi) (hfix i)
    simp [vectorsZ, hi, hj, hF i]

lemma matching_orthogonal {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Involutive F) (hfix : ∀ i, F i ≠ i) (i : Fin m) :
    inner ℂ (vectors F i) (vectors F (F i)) = 0 := by
  have h := matching_dotZ F hF hfix i
  have hc : (vectorsZ F i 0 : ℂ) * (vectorsZ F (F i) 0 : ℂ) +
      (vectorsZ F i 1 : ℂ) * (vectorsZ F (F i) 1 : ℂ) = 0 := by
    exact_mod_cast h
  simpa [vectors, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, star_intCast, mul_comm] using hc

lemma determinant_ne_zero {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {i j : Fin m} (hij : i ≠ j) :
    det2Z (vectorsZ F i) (vectorsZ F j) ≠ 0 := by
  have hv : (i.val : ℤ) ≠ (j.val : ℤ) := by
    intro h
    apply hij
    apply Fin.ext
    exact_mod_cast h
  have hw : ((F i).val : ℤ) ≠ ((F j).val : ℤ) := by
    intro h
    apply hij
    apply hF
    apply Fin.ext
    exact_mod_cast h
  by_cases hi : i < F i <;> by_cases hj : j < F j
  · simp [vectorsZ, det2Z, hi, hj]
    omega
  · have hp : 0 ≤ (i.val : ℤ) * (F j).val := mul_nonneg (by positivity) (by positivity)
    simp only [vectorsZ, hi, hj, if_true, if_false, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, det2Z]
    nlinarith
  · have hp : 0 ≤ ((F i).val : ℤ) * j.val := mul_nonneg (by positivity) (by positivity)
    simp only [vectorsZ, hi, hj, if_true, if_false, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, det2Z]
    nlinarith
  · simp [vectorsZ, det2Z, hi, hj]
    omega

lemma determinant_complex_ne_zero {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {i j : Fin m} (hij : i ≠ j) :
    vectors F i 0 * vectors F j 1 - vectors F i 1 * vectors F j 0 ≠ 0 := by
  have h := determinant_ne_zero F hF hij
  change (vectorsZ F i 0 : ℂ) * (vectorsZ F j 1 : ℂ) -
    (vectorsZ F i 1 : ℂ) * (vectorsZ F j 0 : ℂ) ≠ 0
  exact_mod_cast h

lemma pair_independent {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {i j : Fin m} (hij : i ≠ j) :
    LinearIndependent ℂ ![vectors F i, vectors F j] := by
  rw [linearIndependent_fin2]
  refine ⟨nonzero F j, ?_⟩
  intro c hc
  have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 0) hc
  have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) hc
  change c * vectors F j 0 = vectors F i 0 at h0
  change c * vectors F j 1 = vectors F i 1 at h1
  apply determinant_complex_ne_zero F hF hij
  rw [← h0, ← h1]
  ring

lemma exact_independent {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) (f : Fin 2 → Fin m) (hf : Function.Injective f) :
    LinearIndependent ℂ (fun q => vectors F (f q)) := by
  have h := pair_independent F hF (hf.ne (by decide : (0 : Fin 2) ≠ 1))
  convert h using 1
  ext q
  fin_cases q <;> rfl

/-- The exact finite-set spanning interface used by `P14UPBAssembly.SpansEvery`. -/
lemma spans_every_two {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) (S : Finset (Fin m)) (hS : S.card = 2) :
    Submodule.span ℂ (Set.range fun i : (S : Set (Fin m)) => vectors F i.1) = ⊤ := by
  let e : (S : Set (Fin m)) ≃ Fin 2 := Fintype.equivFinOfCardEq (by simpa using hS)
  let f : Fin 2 → Fin m := fun q => (e.symm q).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hli := (exact_independent F hF f hf).comp e e.injective
  have hs : LinearIndependent ℂ (fun i : (S : Set (Fin m)) => vectors F i.1) := by
    simpa [f, Function.comp_def] using hli
  apply hs.span_eq_top_of_card_eq_finrank'
  simpa [finrank_euclideanSpace_fin] using hS

lemma killed_pair_zero {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {i j : Fin m} (hij : i ≠ j)
    {a : EuclideanSpace ℂ (Fin 2)}
    (hi : inner ℂ (vectors F i) a = 0)
    (hj : inner ℂ (vectors F j) a = 0) : a = 0 := by
  have h0 : vectors F i 0 * a 0 + vectors F i 1 * a 1 = 0 := by
    simpa [vectors, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, star_intCast, mul_comm] using hi
  have h1 : vectors F j 0 * a 0 + vectors F j 1 * a 1 = 0 := by
    simpa [vectors, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, star_intCast, mul_comm] using hj
  have hd := determinant_complex_ne_zero F hF hij
  ext r
  fin_cases r
  · apply (mul_eq_zero.mp ?_).resolve_left hd
    calc
      (vectors F i 0 * vectors F j 1 - vectors F i 1 * vectors F j 0) * a 0 =
          vectors F j 1 * (vectors F i 0 * a 0 + vectors F i 1 * a 1) -
            vectors F i 1 * (vectors F j 0 * a 0 + vectors F j 1 * a 1) := by ring
      _ = 0 := by rw [h0, h1]; ring
  · apply (mul_eq_zero.mp ?_).resolve_left hd
    calc
      (vectors F i 0 * vectors F j 1 - vectors F i 1 * vectors F j 0) * a 1 =
          vectors F i 0 * (vectors F j 0 * a 0 + vectors F j 1 * a 1) -
            vectors F j 0 * (vectors F i 0 * a 0 + vectors F i 1 * a 1) := by ring
      _ = 0 := by rw [h0, h1]; ring

lemma killing_bound {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {a : EuclideanSpace ℂ (Fin 2)} (ha : a ≠ 0)
    (S : Finset (Fin m)) (hS : ∀ i ∈ S, inner ℂ (vectors F i) a = 0) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  by_contra hij
  exact ha (killed_pair_zero F hF hij (hS i hi) (hS j hj))

/-- Uniform qubit realization with the properties used in the UPB assembly. -/
theorem realization {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Involutive F) (hfix : ∀ i, F i ≠ i) :
    ∃ z : Fin m → EuclideanSpace ℂ (Fin 2),
      (∀ i, z i ≠ 0) ∧
      (∀ i, inner ℂ (z i) (z (F i)) = 0) ∧
      (∀ i j, i ≠ j → LinearIndependent ℂ ![z i, z j]) ∧
      (∀ a, a ≠ 0 → ∀ S : Finset (Fin m),
        (∀ i ∈ S, inner ℂ (z i) a = 0) → S.card ≤ 1) := by
  exact ⟨vectors F, nonzero F, matching_orthogonal F hF hfix,
    fun _ _ h => pair_independent F hF.injective h,
    fun _ h S hS => killing_bound F hF.injective h S hS⟩

end

end P14QubitMatching


/- Source: elliptic_audit/UPBAssembly.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-!
Reusable final gluing for the problem-14 UPB constructions.

The finite budget argument is adapted from the existing green submission
`Submissions/UPBFromDegreeBudget/Budget.lean` (s3), and span induction from
`Submissions/UPBIffNoDeficientCover/DeficientCover.lean` (s52).
This file supplies a Euclidean spanning-to-budget interface and the s56 specialization.
It does not assert the missing graph decomposition or local vector existence.
-/

noncomputable section
open scoped BigOperators

namespace P14UPBAssembly

abbrev Space (k : ℕ) := EuclideanSpace ℂ (Fin k)

/-- Every subfamily with exactly `s` members spans the ambient space. -/
def SpansEvery {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (v : V → Space k) (s : ℕ) : Prop :=
  ∀ S : Finset V, S.card = s →
    Submodule.span ℂ (Set.range fun i : (S : Set V) => v i.1) = ⊤

/-- The span-induction argument already used by the green deficient-cover theorem. -/
lemma span_inner_right_eq_zero {k : ℕ} {s : Set (Space k)} {a x : Space k}
    (hgen : ∀ y ∈ s, inner ℂ y a = 0)
    (hx : x ∈ Submodule.span ℂ s) : inner ℂ x a = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | smul c x _ hx => simp [inner_smul_left, hx]

/-- A nonzero vector kills at most `c` members of a `(c+1)`-spanning family. -/
theorem killing_bound {V : Type*} [Fintype V] [DecidableEq V] {k c : ℕ}
    (v : V → Space k) (hspan : SpansEvery v (c + 1))
    (a : Space k) (ha : a ≠ 0) (S : Finset V)
    (hkill : ∀ i ∈ S, inner ℂ (v i) a = 0) : S.card ≤ c := by
  by_contra hbad
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (show c + 1 ≤ S.card by omega)
  have haSpan : a ∈ Submodule.span ℂ
      (Set.range fun i : (T : Set V) => v i.1) := by
    rw [hspan T hT]
    exact Submodule.mem_top
  have hself : inner ℂ a a = 0 := span_inner_right_eq_zero (by
    rintro _ ⟨i, rfl⟩
    exact hkill i.1 (hTS i.2)) haSpan
  exact ha (inner_self_eq_zero.mp hself)

/-- Dimension-sized independent subfamilies give the required spanning interface. -/
theorem spansEvery_of_independent {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (v : V → Space k)
    (h : ∀ S : Finset V, S.card = k →
      LinearIndependent ℂ (fun i : (S : Set V) => v i.1)) : SpansEvery v k := by
  intro S hS
  apply (h S hS).span_eq_top_of_card_eq_finrank'
  simpa [finrank_euclideanSpace_fin] using hS

/-- Existing s3 finite budget argument, generalized to arbitrary finite index types. -/
theorem finite_budget {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (d c : J → ℕ) (v : V → (j : J) → Space (d j))
    (hbudget : (∑ j, c j) < Fintype.card V)
    (hkill : ∀ j (a : Space (d j)), a ≠ 0 →
      ∀ S : Finset V, (∀ i ∈ S, inner ℂ (v i j) a = 0) → S.card ≤ c j) :
    ∀ a : (j : J) → Space (d j), (∀ j, a j ≠ 0) →
      ∃ i, ∀ j, inner ℂ (v i j) (a j) ≠ 0 := by
  classical
  intro a ha
  by_contra hsurvivor
  push Not at hsurvivor
  choose f hf using hsurvivor
  let S : J → Finset V := fun j => Finset.univ.filter (fun i => f i = j)
  have hScap : ∀ j, (S j).card ≤ c j := by
    intro j
    apply hkill j (a j) (ha j)
    intro i hi
    have hfi : f i = j := (Finset.mem_filter.mp hi).2
    rw [← hfi]
    exact hf i
  have hcard : Fintype.card V = ∑ j, (S j).card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := f)
      (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset J))
      (fun _ _ => Finset.mem_univ _)
    simpa [S] using h
  have hle : Fintype.card V ≤ ∑ j, c j := by
    calc
      Fintype.card V = ∑ j, (S j).card := hcard
      _ ≤ ∑ j, c j := Finset.sum_le_sum (fun j _ => hScap j)
  exact (Nat.not_lt_of_ge hle) hbudget

theorem survivor_of_spanning {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (d c : J → ℕ) (v : V → (j : J) → Space (d j))
    (hbudget : (∑ j, c j) < Fintype.card V)
    (hspan : ∀ j, SpansEvery (fun i => v i j) (c j + 1)) :
    ∀ a : (j : J) → Space (d j), (∀ j, a j ≠ 0) →
      ∃ i, ∀ j, inner ℂ (v i j) (a j) ≠ 0 :=
  finite_budget d c v hbudget (fun j a ha S hS =>
    killing_bound (fun i => v i j) (hspan j) a ha S hS)

/-- Convenient input form for matrix and Vandermonde constructions. -/
theorem spansEvery_of_exact_independent {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (v : V → Space k)
    (h : ∀ f : Fin k → V, Function.Injective f →
      LinearIndependent ℂ (fun q => v (f q))) : SpansEvery v k := by
  apply spansEvery_of_independent
  intro S hS
  let e : (S : Set V) ≃ Fin k := Fintype.equivFinOfCardEq (by simpa using hS)
  let f : Fin k → V := fun q => (e.symm q).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hli := (h f hf).comp e e.injective
  simpa [f, Function.comp_def] using hli

theorem exact_independent_of_spansEvery {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (v : V → Space k) (h : SpansEvery v k)
    (f : Fin k → V) (hf : Function.Injective f) :
    LinearIndependent ℂ (fun q => v (f q)) := by
  classical
  let S : Finset V := Finset.univ.image f
  have hS : S.card = k := by simp [S, Finset.card_image_of_injective _ hf]
  have hs := h S hS
  have heq : Set.range (fun i : (S : Set V) => v i.1) = Set.range (fun q => v (f q)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp i.2
      exact ⟨q, congrArg v hq⟩
    · rintro ⟨q, rfl⟩
      exact ⟨⟨f q, Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩⟩, rfl⟩
  rw [heq] at hs
  apply linearIndependent_of_top_le_span_of_card_le_finrank hs.ge
  simp

theorem spansEvery_pullback {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {k : ℕ} (v : V → Space k)
    (h : SpansEvery v k) (f : W → V) (hf : Function.Injective f) :
    SpansEvery (fun w => v (f w)) k := by
  apply spansEvery_of_exact_independent
  intro g hg
  exact exact_independent_of_spansEvery v h (f ∘ g) (hf.comp hg)

/-- The survivor clause of s56: budget `t + 3 + k < t + k + 4`. -/
theorem two_four_survivor {V : Type*} [Fintype V] [DecidableEq V] {k t : ℕ}
    (z : V → Fin t → Space 2) (y : V → Space 4) (x : V → Space k)
    (hcard : Fintype.card V = t + k + 4)
    (hz : ∀ q, SpansEvery (fun i => z i q) 2)
    (hy : SpansEvery y 4) (hx : SpansEvery x (k + 1)) :
    ∀ az : Fin t → Space 2, ∀ ay : Space 4, ∀ ax : Space k,
      (∀ q, az q ≠ 0) → ay ≠ 0 → ax ≠ 0 →
      ∃ i, (∀ q, inner ℂ (z i q) (az q) ≠ 0) ∧
        inner ℂ (y i) ay ≠ 0 ∧ inner ℂ (x i) ax ≠ 0 := by
  classical
  intro az ay ax haz hay hax
  let J := (Fin t ⊕ Unit) ⊕ Unit
  let d : J → ℕ := Sum.elim (Sum.elim (fun _ => 2) (fun _ => 4)) (fun _ => k)
  let c : J → ℕ := Sum.elim (Sum.elim (fun _ => 1) (fun _ => 3)) (fun _ => k)
  let v : V → (j : J) → Space (d j) := fun i j => match j with
    | .inl (.inl q) => z i q
    | .inl (.inr _) => y i
    | .inr _ => x i
  let a : (j : J) → Space (d j) := fun j => match j with
    | .inl (.inl q) => az q
    | .inl (.inr _) => ay
    | .inr _ => ax
  have hb : (∑ j, c j) < Fintype.card V := by
    simp [c, J, Fintype.sum_sum_type, hcard]
    omega
  have hs : ∀ j, SpansEvery (fun i => v i j) (c j + 1) := by
    rintro ((q | u) | u)
    · exact hz q
    · exact hy
    · exact hx
  have ha : ∀ j, a j ≠ 0 := by
    rintro ((q | u) | u)
    · exact haz q
    · exact hay
    · exact hax
  obtain ⟨i, hi⟩ := survivor_of_spanning d c v hb hs a ha
  exact ⟨i, fun q => hi (.inl (.inl q)), hi (.inl (.inr ())), hi (.inr ())⟩

end P14UPBAssembly
end


/- Source: elliptic_audit/UnitaryReused.lean. Reused authorship is retained in the source comments and artifact citations. -/
/- Attributed reuse of the existing green s19 proof. The only mathematical interface
change removes its two unused hypotheses Tight and Spanning. Its proof introduced
these as _tight and _spanning and never used them. No new genericity argument is claimed. -/
/-
Submission for `Statements.CopiesUnitaryGenericity`.

For every `k ≥ 2` and every family of nonzero vectors `v : Fin n → Fin k → ℂ` that is
tight and `(k+1)`-spanning, some unitary `U` makes the two-block family `(v, U·v)`
cross-nonorthogonal and transversal.

Proof strategy (real-polynomial genericity on the unitary group):
* LAYER W (witnesses): for each single condition (a cross pairing `(i,j)`, or a
  subset pair `(S,T)` demanding `rk = min k (rk S + rk T)`), construct one unitary
  achieving it, via orthonormal-basis surgery on `EuclideanSpace ℂ (Fin k)`.
* LAYER P (parameterization): the Cayley transform `x ↦ (1 - S x) * (1 + S x)⁻¹`
  parameterizes (almost all of) the unitary group by real parameters
  `x : Fin k × Fin k → ℝ`, with `S x` skew-Hermitian. Each condition, composed with
  the Cayley map and cleared of denominators, is (the nonvanishing of) a polynomial
  in `MvPolynomial (Fin k × Fin k) ℂ`. Each witness (adjusted by a unimodular phase
  so that `1 + W` is invertible) yields a real point where the condition polynomial
  does not vanish, so each polynomial is nonzero; their product is nonzero, and a
  nonzero polynomial over `ℂ` does not vanish at some *real* point (one-variable
  induction + finiteness of roots).  Evaluating the Cayley map there gives one
  unitary satisfying all conditions simultaneously.
* LAYER T (minors): the rank conditions are caught polynomially by `det (P * C U)`
  where `C U` is a `k × r` matrix of chosen columns of the combined family and `P`
  a fixed `r × k` matrix (the conjugate-transpose of the witness columns), using
  positive-definiteness of the Hermitian Gram matrix.
-/
















namespace P14UnitaryReused

open Matrix

variable {k : ℕ}

/-- Hermitian pairing, conjugate-linear in the first slot. -/
abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

noncomputable abbrev rk {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i))

abbrev Tight {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card ≤ k - 1 → LinearIndependent ℂ fun i : (S : Set ι) => v i

abbrev Spanning {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card = k + 1 →
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i) = ⊤

abbrev Transversal {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ) :
    Prop :=
  ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
    rk (Sum.elim u w) (S.disjSum T) = min k (rk u S + rk w T)

/-- A matrix is unitary when `U * star U = 1`. -/
abbrev IsUnitary (U : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  U * star U = 1

/-- Apply a `k × k` matrix to a coordinate vector. -/
abbrev applyMat (U : Matrix (Fin k) (Fin k) ℂ) (x : Fin k → ℂ) : Fin k → ℂ :=
  U.mulVec x

noncomputable section

/-! ### Section A: generalities on the pairing -/

lemma pair_comm_star {m : ℕ} (x y : Fin m → ℂ) : star (pair x y) = pair y x := by
  rw [star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [star_mul', star_star]
  ring

lemma pair_smul_right {m : ℕ} (c : ℂ) (x y : Fin m → ℂ) :
    pair x (c • y) = c * pair x y := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma pair_add_right {m : ℕ} (x y z : Fin m → ℂ) :
    pair x (y + z) = pair x y + pair x z := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [mul_add]

lemma pair_neg_right {m : ℕ} (x y : Fin m → ℂ) : pair x (-y) = -pair x y := by
  rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun r _ => ?_
  simp

lemma pair_zero_right {m : ℕ} (x : Fin m → ℂ) : pair x 0 = 0 := by
  refine Finset.sum_eq_zero fun r _ => ?_
  simp

lemma pair_self_real {m : ℕ} (x : Fin m → ℂ) :
    pair x x = ((∑ r, Complex.normSq (x r) : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj]

lemma pair_self_eq_zero {m : ℕ} {x : Fin m → ℂ} (h : pair x x = 0) : x = 0 := by
  rw [pair_self_real] at h
  have h0 : (∑ r, Complex.normSq (x r) : ℝ) = 0 := by exact_mod_cast h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (r : Fin m) _ => Complex.normSq_nonneg (x r))).mp h0
  funext r
  exact Complex.normSq_eq_zero.mp (hz r (Finset.mem_univ r))

lemma pair_self_ne_zero {m : ℕ} {x : Fin m → ℂ} (hx : x ≠ 0) : pair x x ≠ 0 :=
  fun h => hx (pair_self_eq_zero h)

/-- The rectangular adjoint identity for the pairing. -/
lemma pair_mulVec_left {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℂ) (a : Fin r → ℂ)
    (b : Fin m → ℂ) : pair (M.mulVec a) b = pair a (Mᴴ.mulVec b) := by
  calc pair (M.mulVec a) b
      = ∑ i, ∑ t, star (M i t) * star (a t) * b i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_apply_eq_sum, star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [star_mul']
    _ = ∑ t, ∑ i, star (M i t) * star (a t) * b i := Finset.sum_comm
    _ = pair a (Mᴴ.mulVec b) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.conjTranspose_apply]
        ring

/-! ### Section B: the unit circle and phase adjustment -/

/-- The set of unimodular complex numbers is infinite. -/
lemma unimodular_infinite : {z : ℂ | star z * z = 1}.Infinite := by
  have key : ∀ x : ℝ, ((x : ℂ) + Complex.I) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp at hi
  have hconj : ∀ x : ℝ, (starRingEnd ℂ) ((x : ℂ) + Complex.I) = (x : ℂ) - Complex.I := by
    intro x
    rw [map_add, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have hconj0 : ∀ x : ℝ, (starRingEnd ℂ) ((x : ℂ) + Complex.I) ≠ 0 := by
    intro x h
    rw [hconj] at h
    have hi := congrArg Complex.im h
    simp at hi
  refine Set.infinite_of_injective_forall_mem
    (f := fun x : ℝ => (starRingEnd ℂ) ((x : ℂ) + Complex.I) / ((x : ℂ) + Complex.I)) ?_ ?_
  · intro x y h
    simp only at h
    rw [div_eq_div_iff (key x) (key y), hconj, hconj] at h
    have hxy : ((x : ℂ) - y) = 0 := by
      have h2 : (2 : ℂ) * Complex.I * ((x : ℂ) - y) = 0 := by linear_combination h
      have h3 : ((2 : ℂ) * Complex.I) ≠ 0 := by
        simp [Complex.I_ne_zero]
      exact (mul_eq_zero.mp h2).resolve_left h3
    exact_mod_cast sub_eq_zero.mp hxy
  · intro x
    show (starRingEnd ℂ) _ / _ ∈ {z : ℂ | star z * z = 1}
    simp only [Set.mem_ofPred_eq, Complex.star_def]
    rw [map_div₀, Complex.conj_conj, div_mul_div_comm,
      mul_comm ((starRingEnd ℂ) ((x : ℂ) + Complex.I)) ((x : ℂ) + Complex.I)]
    exact div_self (mul_ne_zero (key x) (hconj0 x))

lemma unimodular_ne_zero {c : ℂ} (hc : star c * c = 1) : c ≠ 0 := by
  intro h
  rw [h, mul_zero] at hc
  exact zero_ne_one hc

/-- Any matrix admits a unimodular phase `c` such that `1 + c • M` is nonsingular. -/
lemma exists_phase_det {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    ∃ c : ℂ, star c * c = 1 ∧ ((1 : Matrix (Fin m) (Fin m) ℂ) + c • M).det ≠ 0 := by
  classical
  set Mat : Matrix (Fin m) (Fin m) (Polynomial ℂ) :=
    (1 : Matrix (Fin m) (Fin m) (Polynomial ℂ)) +
      (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C with hMat
  set Q : Polynomial ℂ := Mat.det with hQ
  have hev : ∀ z : ℂ, Q.eval z = ((1 : Matrix (Fin m) (Fin m) ℂ) + z • M).det := by
    intro z
    have h1 : (Polynomial.evalRingHom z) Q
        = (((Polynomial.evalRingHom z)).mapMatrix Mat).det := RingHom.map_det _ _
    have h2 : ((Polynomial.evalRingHom z)).mapMatrix Mat
        = (1 : Matrix (Fin m) (Fin m) ℂ) + z • M := by
      rw [hMat, map_add, map_one]
      congr 1
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    simpa [h2] using h1
  have hQ0 : Q ≠ 0 := by
    intro h
    have h0 := hev 0
    rw [h] at h0
    simp at h0
  obtain ⟨c, hc⟩ :=
    (unimodular_infinite.sdiff (Polynomial.finite_setOfPred_isRoot hQ0)).nonempty
  refine ⟨c, hc.1, ?_⟩
  rw [← hev]
  exact fun h => hc.2 h

/-! ### Section C: a nonzero polynomial does not vanish at some real point -/

lemma exists_real_eval_ne_zero : ∀ {m : ℕ} (p : MvPolynomial (Fin m) ℂ), p ≠ 0 →
    ∃ x : Fin m → ℝ, MvPolynomial.eval (fun i => (x i : ℂ)) p ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro p hp
    obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (Fin 0) p
    refine ⟨fun i => i.elim0, ?_⟩
    rw [MvPolynomial.eval_C]
    intro h
    exact hp (by rw [h, map_zero])
  | succ m ih =>
    intro p hp
    set q := MvPolynomial.finSuccEquiv ℂ m p with hqdef
    have hq0 : q ≠ 0 := by
      intro h
      apply hp
      have h2 := congrArg (MvPolynomial.finSuccEquiv ℂ m).symm h
      rwa [hqdef, AlgEquiv.symm_apply_apply, map_zero] at h2
    obtain ⟨d, hd⟩ : ∃ d, q.coeff d ≠ 0 := by
      by_contra h
      exact hq0 (Polynomial.ext fun d => by
        rw [Polynomial.coeff_zero]
        by_contra hne
        exact h ⟨d, hne⟩)
    obtain ⟨x, hx⟩ := ih _ hd
    set Q : Polynomial ℂ := q.map (MvPolynomial.eval (fun i => (x i : ℂ))) with hQdef
    have hQ0 : Q ≠ 0 := by
      intro h
      apply hx
      have hc : Q.coeff d = 0 := by rw [h]; simp
      rwa [hQdef, Polynomial.coeff_map] at hc
    have hinf : (Set.range ((↑) : ℝ → ℂ)).Infinite :=
      Set.infinite_range_of_injective Complex.ofReal_injective
    obtain ⟨z, hz⟩ := (hinf.sdiff (Polynomial.finite_setOfPred_isRoot hQ0)).nonempty
    obtain ⟨t, rfl⟩ := hz.1
    refine ⟨Fin.cons t x, ?_⟩
    have hcons : (fun i => ((Fin.cons t x : Fin (m+1) → ℝ) i : ℂ))
        = Fin.cons (t : ℂ) (fun i => (x i : ℂ)) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    rw [hcons, MvPolynomial.eval_eq_eval_mv_eval']
    exact fun h => hz.2 h

/-- The version over the index type `Fin k × Fin k` used by the Cayley parameters. -/
lemma exists_real_eval_ne_zero' {m : ℕ} (p : MvPolynomial (Fin m × Fin m) ℂ)
    (hp : p ≠ 0) :
    ∃ x : Fin m × Fin m → ℝ, MvPolynomial.eval (fun s => (x s : ℂ)) p ≠ 0 := by
  have hren : MvPolynomial.rename (⇑(finProdFinEquiv : Fin m × Fin m ≃ Fin (m * m))) p ≠ 0 := by
    intro h
    apply hp
    apply MvPolynomial.rename_injective _ finProdFinEquiv.injective
    simpa using h
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero _ hren
  refine ⟨fun s => x (finProdFinEquiv s), ?_⟩
  have : (fun s : Fin m × Fin m => ((x (finProdFinEquiv s) : ℝ) : ℂ))
      = (fun i => (x i : ℂ)) ∘ ⇑finProdFinEquiv := rfl
  rw [this, ← MvPolynomial.eval_rename]
  exact hx

/-! ### Section D: the Cayley transform -/

/-- The skew-Hermitian matrix built from real parameters. -/
def sMat {m : ℕ} (x : Fin m × Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun p q =>
    if p = q then Complex.I * (x (p, p) : ℂ)
    else if p < q then (x (p, q) : ℂ) + Complex.I * (x (q, p) : ℂ)
    else -(x (q, p) : ℂ) + Complex.I * (x (p, q) : ℂ)

lemma sMat_skew {m : ℕ} (x : Fin m × Fin m → ℝ) : (sMat x)ᴴ = -(sMat x) := by
  ext p q
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
  simp only [sMat, Matrix.of_apply]
  rcases lt_trichotomy p q with h | h | h
  · rw [if_neg h.ne', if_neg (asymm h), if_neg h.ne, if_pos h]
    simp only [Complex.star_def, map_add, map_neg, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  · subst h
    rw [if_pos rfl]
    simp only [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  · rw [if_neg h.ne, if_pos h, if_neg h.ne', if_neg (asymm h)]
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

/-- `1 + S` is nonsingular for skew-Hermitian `S`. -/
lemma det_one_add_skew_ne_zero {m : ℕ} {S : Matrix (Fin m) (Fin m) ℂ}
    (hS : Sᴴ = -S) : ((1 : Matrix (Fin m) (Fin m) ℂ) + S).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have h1 : w + S.mulVec w = 0 := by
    calc w + S.mulVec w = (1 + S).mulVec w := by rw [Matrix.add_mulVec, Matrix.one_mulVec]
      _ = 0 := hw
  have h2 : pair w w + pair w (S.mulVec w) = 0 := by
    have h3 := congrArg (fun z => pair w z) h1
    simpa [pair_add_right, pair_zero_right] using h3
  set z := pair w (S.mulVec w) with hzdef
  have h3 : star z = -z := by
    rw [hzdef, pair_comm_star, pair_mulVec_left S w w, hS, Matrix.neg_mulVec, pair_neg_right]
  have hz2 : z = -pair w w := eq_neg_of_add_eq_zero_right h2
  have h4 : star z = z := by
    rw [hz2, pair_self_real, star_neg]
    simp [Complex.conj_ofReal]
  rw [h4] at h3
  have hz0 : z = 0 := by
    have h6 : (2 : ℂ) * z = 0 := by linear_combination h3
    exact (mul_eq_zero.mp h6).resolve_left two_ne_zero
  have hww : pair w w = 0 := by
    rw [hz0] at h2
    simpa using h2
  exact hw0 (pair_self_eq_zero hww)

/-- The Cayley transform of the real parameter point `x`. -/
def cayley {m : ℕ} (x : Fin m × Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 - sMat x) * (1 + sMat x)⁻¹

lemma cayley_unitary_aux {m : ℕ} {S : Matrix (Fin m) (Fin m) ℂ} (hS : Sᴴ = -S) :
    ((1 - S) * (1 + S)⁻¹) * ((1 - S) * (1 + S)⁻¹)ᴴ = 1 := by
  classical
  set A := (1 : Matrix (Fin m) (Fin m) ℂ) + S with hA
  set B := (1 : Matrix (Fin m) (Fin m) ℂ) - S with hB
  have hdetA : A.det ≠ 0 := det_one_add_skew_ne_zero hS
  have hAH : Aᴴ = B := by
    rw [hA, hB, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hS, sub_eq_add_neg]
  have hBH : Bᴴ = A := by
    rw [hB, hA, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hS, sub_neg_eq_add]
  have hdetB : B.det ≠ 0 := by
    rw [← hAH, Matrix.det_conjTranspose, star_ne_zero]
    exact hdetA
  have hUA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdetA
  have hUB : IsUnit B.det := isUnit_iff_ne_zero.mpr hdetB
  have hcomm : A * B = B * A := by
    rw [hA, hB]
    noncomm_ring
  have hinvH : (A⁻¹)ᴴ = B⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hAH]
  have hswap : A⁻¹ * B⁻¹ = B⁻¹ * A⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hcomm]
  calc (B * A⁻¹) * (B * A⁻¹)ᴴ
      = B * A⁻¹ * ((A⁻¹)ᴴ * Bᴴ) := by rw [Matrix.conjTranspose_mul]
    _ = B * (A⁻¹ * B⁻¹) * A := by rw [hinvH, hBH]; simp [Matrix.mul_assoc]
    _ = B * (B⁻¹ * A⁻¹) * A := by rw [hswap]
    _ = (B * B⁻¹) * (A⁻¹ * A) := by simp [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hUB, Matrix.nonsing_inv_mul _ hUA, one_mul]

lemma cayley_unitary {m : ℕ} (x : Fin m × Fin m → ℝ) :
    cayley x * (cayley x)ᴴ = 1 :=
  cayley_unitary_aux (sMat_skew x)

/-- Every skew-Hermitian matrix arises from real parameters. -/
lemma skew_reaches {m : ℕ} {S₀ : Matrix (Fin m) (Fin m) ℂ} (hS : S₀ᴴ = -S₀) :
    ∃ x : Fin m × Fin m → ℝ, sMat x = S₀ := by
  classical
  have hskew : ∀ p q, star (S₀ q p) = -(S₀ p q) := by
    intro p q
    have h1 : S₀ᴴ p q = (-S₀) p q := by rw [hS]
    rwa [Matrix.conjTranspose_apply, Matrix.neg_apply] at h1
  set f : Fin m × Fin m → ℝ := fun pq => if pq.1 = pq.2 then (S₀ pq.1 pq.1).im
    else if pq.1 < pq.2 then (S₀ pq.1 pq.2).re else (S₀ pq.2 pq.1).im with hf
  have hf1 : ∀ p, f (p, p) = (S₀ p p).im := fun p => by simp [hf]
  have hf2 : ∀ p q : Fin m, p < q → f (p, q) = (S₀ p q).re := fun p q h => by
    simp [hf, h.ne, h]
  have hf3 : ∀ p q : Fin m, q < p → f (p, q) = (S₀ q p).im := fun p q h => by
    simp [hf, h.ne', asymm h]
  refine ⟨f, ?_⟩
  ext p q
  simp only [sMat, Matrix.of_apply]
  rcases lt_trichotomy p q with h | h | h
  · rw [if_neg h.ne, if_pos h, hf2 p q h, hf3 q p h]
    apply Complex.ext <;> simp
  · subst h
    rw [if_pos rfl, hf1 p]
    have hre : (S₀ p p).re = 0 := by
      have h1 := congrArg Complex.re (hskew p p)
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h1
      linarith
    apply Complex.ext <;> simp [hre]
  · rw [if_neg h.ne', if_neg (asymm h), hf2 q p h, hf3 p q h]
    have hval : S₀ p q = -star (S₀ q p) := by
      have h1 := hskew p q
      linear_combination h1
    rw [hval]
    apply Complex.ext <;> simp

/-- Unimodular scalar multiples of unitaries are unitary. -/
lemma smul_unitary {m : ℕ} {c : ℂ} {W : Matrix (Fin m) (Fin m) ℂ}
    (hc : star c * c = 1) (hW : W * Wᴴ = 1) : (c • W) * (c • W)ᴴ = 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW,
    show c * star c = 1 from by rw [mul_comm]; exact hc]
  simp

/-- Any unitary `W` with `1 + W` nonsingular is in the image of the Cayley map. -/
lemma cayley_reaches {m : ℕ} {W : Matrix (Fin m) (Fin m) ℂ}
    (hW : W * Wᴴ = 1) (hdet : ((1 : Matrix (Fin m) (Fin m) ℂ) + W).det ≠ 0) :
    ∃ x : Fin m × Fin m → ℝ, cayley x = W := by
  classical
  set A := (1 : Matrix (Fin m) (Fin m) ℂ) + W with hA
  have hUA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  set S₀ := (1 - W) * A⁻¹ with hS0
  have hWH : Wᴴ * W = 1 := mul_eq_one_comm.mp hW
  have hAH : Aᴴ = 1 + Wᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  have hdetAH : (Aᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose, star_ne_zero]
    exact hdet
  have hUAH : IsUnit (Aᴴ).det := isUnit_iff_ne_zero.mpr hdetAH
  have hkey : (1 - Wᴴ) * A = -(Aᴴ * (1 - W)) := by
    rw [hA, hAH]
    have e1 : ((1 : Matrix (Fin m) (Fin m) ℂ) - Wᴴ) * (1 + W)
        = 1 + W - Wᴴ - Wᴴ * W := by noncomm_ring
    have e2 : ((1 : Matrix (Fin m) (Fin m) ℂ) + Wᴴ) * (1 - W)
        = 1 - W + Wᴴ - Wᴴ * W := by noncomm_ring
    rw [e1, e2, hWH]
    abel
  have hskew : S₀ᴴ = -S₀ := by
    rw [hS0, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    have h2 : (Aᴴ)⁻¹ * ((1 - Wᴴ) * A) * A⁻¹ = (Aᴴ)⁻¹ * (-(Aᴴ * (1 - W))) * A⁻¹ := by
      rw [hkey]
    calc (Aᴴ)⁻¹ * (1 - Wᴴ)
        = (Aᴴ)⁻¹ * ((1 - Wᴴ) * A) * A⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUA,
            Matrix.mul_one]
      _ = (Aᴴ)⁻¹ * (-(Aᴴ * (1 - W))) * A⁻¹ := h2
      _ = -((Aᴴ)⁻¹ * Aᴴ * (1 - W) * A⁻¹) := by
          simp [Matrix.mul_assoc]
      _ = -((1 - W) * A⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hUAH, Matrix.one_mul]
  obtain ⟨x, hx⟩ := skew_reaches hskew
  refine ⟨x, ?_⟩
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUA
  have hsum : A + (1 - W) = (2 : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    rw [hA, two_smul]
    abel
  have hdiff : A - (1 - W) = (2 : ℂ) • W := by
    rw [hA, two_smul]
    abel
  have h1pS : 1 + S₀ = (2 : ℂ) • A⁻¹ := by
    rw [hS0]
    calc (1 : Matrix (Fin m) (Fin m) ℂ) + (1 - W) * A⁻¹
        = A * A⁻¹ + (1 - W) * A⁻¹ := by rw [hAA]
      _ = (A + (1 - W)) * A⁻¹ := (Matrix.add_mul _ _ _).symm
      _ = ((2 : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) * A⁻¹ := by rw [hsum]
      _ = (2 : ℂ) • A⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have h1mS : 1 - S₀ = (2 : ℂ) • (W * A⁻¹) := by
    rw [hS0]
    calc (1 : Matrix (Fin m) (Fin m) ℂ) - (1 - W) * A⁻¹
        = A * A⁻¹ - (1 - W) * A⁻¹ := by rw [hAA]
      _ = (A - (1 - W)) * A⁻¹ := (Matrix.sub_mul _ _ _).symm
      _ = ((2 : ℂ) • W) * A⁻¹ := by rw [hdiff]
      _ = (2 : ℂ) • (W * A⁻¹) := Matrix.smul_mul _ _ _
  have hinv : (1 + S₀)⁻¹ = (2⁻¹ : ℂ) • A := by
    apply Matrix.inv_eq_right_inv
    rw [h1pS, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hUA]
    norm_num
  show (1 - sMat x) * (1 + sMat x)⁻¹ = W
  rw [hx]
  rw [h1mS, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hUA, Matrix.mul_one]
  norm_num

/-! ### Section E: matrices over the polynomial ring and evaluation bridges -/

/-- The generic skew-Hermitian matrix over the polynomial ring. -/
def Spoly (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  Matrix.of fun p q =>
    if p = q then MvPolynomial.C Complex.I * MvPolynomial.X (p, p)
    else if p < q then
      MvPolynomial.X (p, q) + MvPolynomial.C Complex.I * MvPolynomial.X (q, p)
    else -MvPolynomial.X (q, p) + MvPolynomial.C Complex.I * MvPolynomial.X (p, q)

/-- Evaluation at a real parameter point, as a ring hom. -/
def evalx {m : ℕ} (x : Fin m × Fin m → ℝ) :
    MvPolynomial (Fin m × Fin m) ℂ →+* ℂ :=
  MvPolynomial.eval (fun pq => (x pq : ℂ))

lemma evalx_mat_Spoly {m : ℕ} (x : Fin m × Fin m → ℝ) :
    (Spoly m).map (evalx x) = sMat x := by
  ext p q
  rw [Matrix.map_apply]
  simp only [Spoly, sMat, Matrix.of_apply]
  rcases lt_trichotomy p q with h | h | h
  · rw [if_neg h.ne, if_pos h, if_neg h.ne, if_pos h]
    simp [evalx]
  · subst h
    rw [if_pos rfl, if_pos rfl]
    simp [evalx]
  · rw [if_neg h.ne', if_neg (asymm h), if_neg h.ne', if_neg (asymm h)]
    simp [evalx]

/-- `1 + S` over the polynomial ring. -/
def Apoly (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  1 + Spoly m

/-- The numerator matrix `(1 - S) * adjugate (1 + S)` over the polynomial ring. -/
def Npoly (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  (1 - Spoly m) * (Apoly m).adjugate

/-- The denominator polynomial `det (1 + S)`. -/
def Dpoly (m : ℕ) : MvPolynomial (Fin m × Fin m) ℂ := (Apoly m).det

lemma evalx_mat_Apoly {m : ℕ} (x : Fin m × Fin m → ℝ) :
    (evalx x).mapMatrix (Apoly m) = 1 + sMat x := by
  rw [Apoly, map_add, map_one, RingHom.mapMatrix_apply, evalx_mat_Spoly]

lemma evalx_Dpoly {m : ℕ} (x : Fin m × Fin m → ℝ) :
    evalx x (Dpoly m) = (1 + sMat x).det := by
  rw [Dpoly, RingHom.map_det, evalx_mat_Apoly]

lemma evalx_Dpoly_ne_zero {m : ℕ} (x : Fin m × Fin m → ℝ) :
    evalx x (Dpoly m) ≠ 0 := by
  rw [evalx_Dpoly]
  exact det_one_add_skew_ne_zero (sMat_skew x)

lemma evalx_mat_Npoly {m : ℕ} (x : Fin m × Fin m → ℝ) :
    (Npoly m).map (evalx x) = ((1 + sMat x).det) • cayley x := by
  have h : (evalx x).mapMatrix (Npoly m)
      = ((1 : Matrix (Fin m) (Fin m) ℂ) - sMat x) * (1 + sMat x).adjugate := by
    rw [Npoly, map_mul, map_sub, map_one, RingHom.map_adjugate, evalx_mat_Apoly,
      RingHom.mapMatrix_apply, evalx_mat_Spoly]
  rw [← RingHom.mapMatrix_apply, h]
  have hdet : (1 + sMat x).det ≠ 0 := det_one_add_skew_ne_zero (sMat_skew x)
  have hadj : (1 + sMat x).adjugate = (1 + sMat x).det • (1 + sMat x)⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hdet, one_smul]
  rw [hadj, Matrix.mul_smul, cayley]

lemma evalx_mulVec {m r : ℕ} (x : Fin m × Fin m → ℝ)
    (M : Matrix (Fin m) (Fin r) (MvPolynomial (Fin m × Fin m) ℂ))
    (c : Fin r → MvPolynomial (Fin m × Fin m) ℂ) (i : Fin m) :
    evalx x ((M.mulVec c) i) = ((M.map (evalx x)).mulVec (fun t => evalx x (c t))) i := by
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, Matrix.map_apply]

/-! ### Section F: witnesses via orthonormal bases on Euclidean space -/

open scoped InnerProductSpace

lemma pair_eq_inner {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) :
    pair (WithLp.ofLp x) (WithLp.ofLp y) = inner ℂ x y := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [RCLike.inner_apply, Complex.star_def]
  ring

lemma euclid_decomp {m : ℕ} (x : EuclideanSpace ℂ (Fin m)) :
    x = ∑ i, x i • EuclideanSpace.single i (1 : ℂ) := by
  classical
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℂ).sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]

/-- The matrix of a linear isometry equivalence of Euclidean space. -/
def matOf {m : ℕ}
    (g : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => g (EuclideanSpace.single j 1) i

lemma matOf_mulVec {m : ℕ}
    (g : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (y : Fin m → ℂ) :
    (matOf g).mulVec y = WithLp.ofLp (g (WithLp.toLp 2 y)) := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  conv_rhs => rw [euclid_decomp (WithLp.toLp 2 y)]
  rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, matOf, Matrix.of_apply]
  ring

lemma matOf_unitary {m : ℕ}
    (g : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    (matOf g) * (matOf g)ᴴ = 1 := by
  classical
  rw [← mul_eq_one_comm]
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h1 : ∑ r, ((matOf g)ᴴ) i r * (matOf g) r j
      = pair (WithLp.ofLp (g (EuclideanSpace.single i 1)))
          (WithLp.ofLp (g (EuclideanSpace.single j 1))) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.conjTranspose_apply, matOf, Matrix.of_apply, Matrix.of_apply]
  rw [h1, pair_eq_inner, LinearIsometryEquiv.inner_map_map,
    EuclideanSpace.inner_single_left]
  simp

/-- Any orthonormal family indexed by `Fin r` extends to an orthonormal basis whose
first `r` vectors are the given family. -/
lemma exists_adapted_onb {m r : ℕ} (hr : r ≤ m)
    (w : Fin r → EuclideanSpace ℂ (Fin m)) (hw : Orthonormal ℂ w) :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      ∀ t : Fin r, b (Fin.castLE hr t) = w t := by
  classical
  set v₀ : Fin m → EuclideanSpace ℂ (Fin m) := fun i =>
    if h : (i : ℕ) < r then w ⟨i, h⟩ else 0 with hv₀
  set s : Set (Fin m) := {i : Fin m | (i : ℕ) < r} with hs
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  have hv : ∀ (i : Fin m) (h : (i : ℕ) < r), v₀ i = w ⟨i, h⟩ := by
    intro i h
    simp only [hv₀]
    rw [dif_pos h]
  have hres : Orthonormal ℂ (s.domRestrict v₀) := by
    have hcomp : s.domRestrict v₀ = w ∘ (fun i : s => (⟨(i : Fin m), i.2⟩ : Fin r)) := by
      funext i
      exact hv (i : Fin m) i.2
    rw [hcomp]
    refine hw.comp _ ?_
    intro a b hab
    have h2 : (⟨(a : Fin m), a.2⟩ : Fin r) = (⟨(b : Fin m), b.2⟩ : Fin r) := hab
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin r => (z : ℕ)) h2
  obtain ⟨b, hb⟩ := hres.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨b, fun t => ?_⟩
  have ht : ((Fin.castLE hr t : Fin m) : ℕ) < r := t.2
  have hmem : (Fin.castLE hr t : Fin m) ∈ s := ht
  rw [hb _ hmem, hv _ ht]
  congr 1

/-- Every subspace of Euclidean space has an orthonormal spanning family indexed by
`Fin (finrank A)`. -/
lemma subspace_onb {m : ℕ} (A : Submodule ℂ (EuclideanSpace ℂ (Fin m))) :
    ∃ w : Fin (Module.finrank ℂ A) → EuclideanSpace ℂ (Fin m),
      Orthonormal ℂ w ∧ Submodule.span ℂ (Set.range w) = A := by
  refine ⟨fun t => ((stdOrthonormalBasis ℂ A) t : EuclideanSpace ℂ (Fin m)), ?_, ?_⟩
  · exact (A.subtypeₗᵢ.orthonormal_comp_iff).mpr (stdOrthonormalBasis ℂ A).orthonormal
  · have h1 : Set.range (fun t => ((stdOrthonormalBasis ℂ A) t : EuclideanSpace ℂ (Fin m)))
        = A.subtype '' (Set.range (stdOrthonormalBasis ℂ A)) := by
      rw [← Set.range_comp]
      rfl
    have h2 : Submodule.span ℂ (Set.range (⇑(stdOrthonormalBasis ℂ A))) = ⊤ := by
      rw [← OrthonormalBasis.coe_toBasis]
      exact Module.Basis.span_eq _
    rw [h1, Submodule.span_image, h2, Submodule.map_top, Submodule.range_subtype]

/-- The normalized nonzero vector as an orthonormal singleton family. -/
lemma orthonormal_normalize {m : ℕ} {x : EuclideanSpace ℂ (Fin m)} (hx : x ≠ 0) :
    Orthonormal ℂ (fun _ : Fin 1 => ((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  rw [if_pos rfl, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.conj_ofReal]
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm' : ((‖x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm
  push_cast
  field_simp
  norm_cast

/-- W1': some unitary makes the cross pairing of two nonzero vectors nonzero. -/
lemma exists_unitary_pair_ne_zero {m : ℕ} (hm : 0 < m) {x y : Fin m → ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ W : Matrix (Fin m) (Fin m) ℂ, W * Wᴴ = 1 ∧ pair x (W.mulVec y) ≠ 0 := by
  classical
  set xE : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 x with hxE
  set yE : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 y with hyE
  have hxE0 : xE ≠ 0 := fun h => hx (congrArg WithLp.ofLp h)
  have hyE0 : yE ≠ 0 := fun h => hy (congrArg WithLp.ofLp h)
  have h1m : 1 ≤ m := hm
  obtain ⟨bx, hbx⟩ := exists_adapted_onb h1m _ (orthonormal_normalize hxE0)
  obtain ⟨by', hby⟩ := exists_adapted_onb h1m _ (orthonormal_normalize hyE0)
  set g := by'.equiv bx (Equiv.refl (Fin m)) with hg
  refine ⟨matOf g, matOf_unitary g, ?_⟩
  rw [matOf_mulVec]
  have hgy : g yE = (‖yE‖ : ℂ) • (((‖xE‖⁻¹ : ℝ) : ℂ) • xE) := by
    have hyy : yE = (‖yE‖ : ℂ) • (((‖yE‖⁻¹ : ℝ) : ℂ) • yE) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hyE0),
        Complex.ofReal_one, one_smul]
    conv_lhs => rw [hyy]
    rw [map_smul]
    congr 1
    have h0 : (((‖yE‖⁻¹ : ℝ) : ℂ) • yE) = by' (Fin.castLE h1m 0) := (hby 0).symm
    rw [h0, hg, OrthonormalBasis.equiv_apply_basis]
    simpa using hbx 0
  rw [hgy, WithLp.ofLp_smul, WithLp.ofLp_smul, pair_smul_right, pair_smul_right]
  have hox : WithLp.ofLp xE = x := rfl
  rw [hox]
  apply mul_ne_zero
  · rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hyE0
  apply mul_ne_zero
  · rw [Complex.ofReal_ne_zero]
    exact inv_ne_zero (norm_ne_zero_iff.mpr hxE0)
  · exact pair_self_ne_zero hx

/-- The index bookkeeping for W2: the first `a` indices together with the rotation
by `a` of the first `b` indices make up exactly the first `min m (a+b)` indices. -/
lemma index_union {m a b : ℕ} [NeZero m] (hm : 0 < m) (ha : a ≤ m) (hb : b ≤ m) :
    {i : Fin m | (i : ℕ) < a} ∪ (⇑(Equiv.addLeft (Fin.ofNat m a)) '' {i : Fin m | (i : ℕ) < b})
      = {i : Fin m | (i : ℕ) < min m (a + b)} := by
  have hσval : ∀ j : Fin m, ((Fin.ofNat m a + j : Fin m) : ℕ) = ((a % m) + (j : ℕ)) % m := by
    intro j
    rw [Fin.val_add, Fin.val_ofNat]
  ext i
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image, Equiv.coe_addLeft]
  constructor
  · rintro (h | ⟨j, hj, rfl⟩)
    · exact lt_of_lt_of_le h (le_min ha (Nat.le_add_right a b))
    · rw [hσval j, lt_min_iff]
      have hjm : (j : ℕ) < m := j.isLt
      by_cases ham : a < m
      · rw [Nat.mod_eq_of_lt ham]
        by_cases hsum : a + (j : ℕ) < m
        · rw [Nat.mod_eq_of_lt hsum]
          omega
        · have h2 : (a + (j : ℕ)) % m = a + (j : ℕ) - m := by
            rw [Nat.mod_eq_sub_mod (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h2]
          omega
      · have ham' : a = m := le_antisymm ha (le_of_not_gt ham)
        have hlt : ((a % m) + (j : ℕ)) % m < m := Nat.mod_lt _ hm
        omega
  · intro hi
    rw [lt_min_iff] at hi
    by_cases hia : (i : ℕ) < a
    · exact Or.inl hia
    · right
      have ham : a < m := lt_of_le_of_lt (le_of_not_gt hia) hi.1
      refine ⟨⟨(i : ℕ) - a, by omega⟩, ?_, ?_⟩
      · show (i : ℕ) - a < b
        omega
      · apply Fin.ext
        rw [hσval]
        show ((a % m) + ((i : ℕ) - a)) % m = (i : ℕ)
        rw [Nat.mod_eq_of_lt ham]
        have h3 : a + ((i : ℕ) - a) = (i : ℕ) := by omega
        rw [h3, Nat.mod_eq_of_lt hi.1]

/-- W2: some unitary puts `B` in generic position relative to `A`: the sup of `A`
with the image of `B` has the maximal possible rank `min m (finrank A + finrank B)`. -/
lemma exists_unitary_sup_finrank {m : ℕ} (hm : 0 < m)
    (A B : Submodule ℂ (Fin m → ℂ)) :
    ∃ W : Matrix (Fin m) (Fin m) ℂ, W * Wᴴ = 1 ∧
      Module.finrank ℂ (A ⊔ Submodule.map (Matrix.mulVecLin W) B :
          Submodule ℂ (Fin m → ℂ))
        = min m (Module.finrank ℂ A + Module.finrank ℂ B) := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  set eL : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (Fin m → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).toLinearMap with heL
  set eLi : (Fin m → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).symm.toLinearMap with heLi
  set A' : Submodule ℂ (EuclideanSpace ℂ (Fin m)) := Submodule.map eLi A with hA'def
  set B' : Submodule ℂ (EuclideanSpace ℂ (Fin m)) := Submodule.map eLi B with hB'def
  have hmapback : ∀ X : Submodule ℂ (Fin m → ℂ),
      Submodule.map eL (Submodule.map eLi X) = X := by
    intro X
    ext z
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      simpa [heL, heLi] using hu
    · intro hz
      exact ⟨eLi z, ⟨z, hz, rfl⟩, by simp [heL, heLi]⟩
  have hfinL : ∀ X : Submodule ℂ (EuclideanSpace ℂ (Fin m)),
      Module.finrank ℂ (Submodule.map eL X) = Module.finrank ℂ X := by
    intro X
    exact LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)) X
  have hfinA : Module.finrank ℂ A' = Module.finrank ℂ A := by
    rw [hA'def]
    exact LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).symm A
  have hfinB : Module.finrank ℂ B' = Module.finrank ℂ B := by
    rw [hB'def]
    exact LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).symm B
  set a := Module.finrank ℂ A' with hadef
  set b := Module.finrank ℂ B' with hbdef
  have hEfin : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := finrank_euclideanSpace_fin
  have haM : a ≤ m := by
    rw [hadef]
    calc Module.finrank ℂ A' ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) := A'.finrank_le
      _ = m := hEfin
  have hbM : b ≤ m := by
    rw [hbdef]
    calc Module.finrank ℂ B' ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) := B'.finrank_le
      _ = m := hEfin
  obtain ⟨wA, hwA_on, hwA_span⟩ := subspace_onb A'
  obtain ⟨wB, hwB_on, hwB_span⟩ := subspace_onb B'
  obtain ⟨eA, heA⟩ := exists_adapted_onb haM wA hwA_on
  obtain ⟨eB, heB⟩ := exists_adapted_onb hbM wB hwB_on
  set σ : Equiv.Perm (Fin m) := Equiv.addLeft (Fin.ofNat m a) with hσ
  set g := eB.equiv eA σ with hg
  set gmap : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    g.toLinearEquiv.toLinearMap with hgmap
  refine ⟨matOf g, matOf_unitary g, ?_⟩
  have hAA' : Submodule.map eL A' = A := by
    rw [hA'def]
    exact hmapback A
  have hbridge : Submodule.map (Matrix.mulVecLin (matOf g)) B
      = Submodule.map eL (Submodule.map gmap B') := by
    rw [hB'def]
    ext z
    simp only [Submodule.mem_map, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨gmap (eLi y), ⟨eLi y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
      rw [matOf_mulVec]
      rfl
    · rintro ⟨w, ⟨u, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      rw [matOf_mulVec]
      rfl
  have hA'span : A' = Submodule.span ℂ (Set.range fun t : Fin a => eA (Fin.castLE haM t)) := by
    rw [← hwA_span]
    congr 1
    rw [show (fun t : Fin a => eA (Fin.castLE haM t)) = wA from funext heA]
  have hB'span : B' = Submodule.span ℂ (Set.range fun t : Fin b => eB (Fin.castLE hbM t)) := by
    rw [← hwB_span]
    congr 1
    rw [show (fun t : Fin b => eB (Fin.castLE hbM t)) = wB from funext heB]
  have hmapg : Submodule.map gmap B'
      = Submodule.span ℂ (Set.range fun t : Fin b => eA (σ (Fin.castLE hbM t))) := by
    rw [hB'span, Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    congr 1
    funext t
    simp only [Function.comp_apply, hgmap, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [hg]
    exact OrthonormalBasis.equiv_apply_basis eB eA σ _
  have hmnM : min m (a + b) ≤ m := min_le_left _ _
  have hidx := index_union (a := a) (b := b) hm haM hbM
  have hsup : A' ⊔ Submodule.map gmap B'
      = Submodule.span ℂ (Set.range fun t : Fin (min m (a + b)) => eA (Fin.castLE hmnM t)) := by
    rw [hA'span, hmapg, ← Submodule.span_union]
    congr 1
    have h1 : (Set.range fun t : Fin a => eA (Fin.castLE haM t))
        = ⇑eA '' {i : Fin m | (i : ℕ) < a} := by
      rw [← Fin.range_castLE haM, ← Set.range_comp]
      rfl
    have h2 : (Set.range fun t : Fin b => eA (σ (Fin.castLE hbM t)))
        = ⇑eA '' (⇑σ '' {i : Fin m | (i : ℕ) < b}) := by
      rw [← Fin.range_castLE hbM, ← Set.range_comp, ← Set.range_comp]
      rfl
    have h3 : (Set.range fun t : Fin (min m (a + b)) => eA (Fin.castLE hmnM t))
        = ⇑eA '' {i : Fin m | (i : ℕ) < min m (a + b)} := by
      rw [← Fin.range_castLE hmnM, ← Set.range_comp]
      rfl
    rw [h1, h2, h3, ← Set.image_union, hσ, hidx]
  have hrank : Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun t : Fin (min m (a + b)) => eA (Fin.castLE hmnM t)))
      = min m (a + b) := by
    have hli : LinearIndependent ℂ (fun t : Fin (min m (a + b)) => eA (Fin.castLE hmnM t)) :=
      (eA.orthonormal.linearIndependent).comp _ (Fin.castLE_injective hmnM)
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  calc Module.finrank ℂ (A ⊔ Submodule.map (Matrix.mulVecLin (matOf g)) B :
          Submodule ℂ (Fin m → ℂ))
      = Module.finrank ℂ (Submodule.map eL A' ⊔ Submodule.map eL (Submodule.map gmap B') :
          Submodule ℂ (Fin m → ℂ)) := by rw [hAA', hbridge]
    _ = Module.finrank ℂ (Submodule.map eL (A' ⊔ Submodule.map gmap B')) := by
        rw [Submodule.map_sup]
    _ = Module.finrank ℂ (A' ⊔ Submodule.map gmap B' :
          Submodule ℂ (EuclideanSpace ℂ (Fin m))) := hfinL _
    _ = min m (a + b) := by rw [hsup, hrank]
    _ = min m (Module.finrank ℂ A + Module.finrank ℂ B) := by rw [hfinA, hfinB]

/-! ### Section G: rank bookkeeping for the combined family -/

lemma span_restrict_eq {m : ℕ} {ι : Type} (v : ι → Fin m → ℂ) (S : Finset ι) :
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i)
      = Submodule.span ℂ (v '' (S : Set ι)) := by
  rw [Set.image_eq_range]

lemma rk_eq_span_image {m : ℕ} {ι : Type} (v : ι → Fin m → ℂ) (S : Finset ι) :
    rk v S = Module.finrank ℂ (Submodule.span ℂ (v '' (S : Set ι))) := by
  rw [rk, span_restrict_eq]

lemma coe_disjSum_set {n₁ n₂ : ℕ} (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set (Fin n₁ ⊕ Fin n₂))
      = Sum.inl '' (S : Set (Fin n₁)) ∪ Sum.inr '' (T : Set (Fin n₂)) := by
  ext x
  simp only [Finset.mem_coe, Finset.mem_disjSum, Set.mem_union, Set.mem_image]

lemma span_disjSum {m n₁ n₂ : ℕ} (u : Fin n₁ → Fin m → ℂ) (w : Fin n₂ → Fin m → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    Submodule.span ℂ
        (Set.range fun i : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set (Fin n₁ ⊕ Fin n₂)) =>
          Sum.elim u w i)
      = Submodule.span ℂ (u '' (S : Set (Fin n₁))) ⊔ Submodule.span ℂ (w '' (T : Set (Fin n₂))) := by
  rw [span_restrict_eq, coe_disjSum_set, Set.image_union, ← Submodule.span_union]
  congr 2
  · rw [Set.image_image]
    exact Set.image_congr fun a _ => rfl
  · rw [Set.image_image]
    exact Set.image_congr fun a _ => rfl

lemma rk_disjSum_eq {m n₁ n₂ : ℕ} (u : Fin n₁ → Fin m → ℂ) (w : Fin n₂ → Fin m → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    rk (Sum.elim u w) (S.disjSum T)
      = Module.finrank ℂ
          (Submodule.span ℂ (u '' (S : Set (Fin n₁))) ⊔ Submodule.span ℂ (w '' (T : Set (Fin n₂))) :
            Submodule ℂ (Fin m → ℂ)) := by
  rw [rk, span_disjSum]

lemma finrank_sup_le {m : ℕ} (X Y : Submodule ℂ (Fin m → ℂ)) :
    Module.finrank ℂ (X ⊔ Y : Submodule ℂ (Fin m → ℂ))
      ≤ min m (Module.finrank ℂ X + Module.finrank ℂ Y) := by
  rw [le_min_iff]
  constructor
  · calc Module.finrank ℂ (X ⊔ Y : Submodule ℂ (Fin m → ℂ))
        ≤ Module.finrank ℂ (Fin m → ℂ) := Submodule.finrank_le _
      _ = m := by rw [Module.finrank_pi, Fintype.card_fin]
  · have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
    omega

/-- The `≤` half of transversality, valid for arbitrary second block. -/
lemma rk_disjSum_le {m n₁ n₂ : ℕ} (u : Fin n₁ → Fin m → ℂ) (w : Fin n₂ → Fin m → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    rk (Sum.elim u w) (S.disjSum T) ≤ min m (rk u S + rk w T) := by
  rw [rk_disjSum_eq, rk_eq_span_image u S, rk_eq_span_image w T]
  exact finrank_sup_le _ _

/-- Rank is invariant under an invertible (e.g. unitary) matrix acting on the family. -/
lemma finrank_map_matrix {m : ℕ} {W : Matrix (Fin m) (Fin m) ℂ} (hW : W * Wᴴ = 1)
    (X : Submodule ℂ (Fin m → ℂ)) :
    Module.finrank ℂ (Submodule.map (Matrix.mulVecLin W) X) = Module.finrank ℂ X := by
  classical
  have h1 : Wᴴ * W = 1 := mul_eq_one_comm.mp hW
  set e : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) := LinearEquiv.ofLinearMap
    (Matrix.mulVecLin W) (Matrix.mulVecLin Wᴴ)
    (by rw [← Matrix.mulVecLin_mul, hW, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, h1, Matrix.mulVecLin_one]) with he
  have hcoe : (e : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = Matrix.mulVecLin W := by
    rw [he]
    exact LinearEquiv.toLinearMap_ofLinearMap _ _ _ _
  rw [← hcoe]
  exact LinearEquiv.finrank_map_eq e X

lemma span_image_mulVecLin {m n₂ : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (w : Fin n₂ → Fin m → ℂ) (T : Finset (Fin n₂)) :
    Submodule.span ℂ ((fun j => U.mulVec (w j)) '' (T : Set (Fin n₂)))
      = Submodule.map (Matrix.mulVecLin U) (Submodule.span ℂ (w '' (T : Set (Fin n₂)))) := by
  rw [Submodule.map_span]
  congr 1
  rw [Set.image_image]
  exact Set.image_congr fun a _ => rfl

/-- Unitary invariance of the rank of a block. -/
lemma rk_image_unitary {m n₂ : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U * Uᴴ = 1)
    (w : Fin n₂ → Fin m → ℂ) (T : Finset (Fin n₂)) :
    rk (fun j => U.mulVec (w j)) T = rk w T := by
  rw [rk_eq_span_image, rk_eq_span_image, span_image_mulVecLin, finrank_map_matrix hU]

/-- The lower bound on the combined rank from independent columns inside the family. -/
lemma rk_ge_of_cols {m n₁ n₂ r : ℕ} (u : Fin n₁ → Fin m → ℂ) (w : Fin n₂ → Fin m → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) (col : Fin r → Fin m → ℂ)
    (hmem : ∀ t, col t ∈ (u '' (S : Set (Fin n₁)) ∪ w '' (T : Set (Fin n₂))))
    (hli : LinearIndependent ℂ col) :
    r ≤ rk (Sum.elim u w) (S.disjSum T) := by
  rw [rk_disjSum_eq]
  have h2 : Submodule.span ℂ (Set.range col)
      ≤ Submodule.span ℂ (u '' (S : Set (Fin n₁))) ⊔ Submodule.span ℂ (w '' (T : Set (Fin n₂))) := by
    rw [← Submodule.span_union]
    apply Submodule.span_mono
    rintro z ⟨t, rfl⟩
    exact hmem t
  calc r = Module.finrank ℂ (Submodule.span ℂ (Set.range col)) := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
    _ ≤ _ := Submodule.finrank_mono h2

/-- Scaling the matrix by a nonzero constant does not change the image submodule. -/
lemma map_smul_mulVecLin {m : ℕ} {c : ℂ} (hc : c ≠ 0) (W : Matrix (Fin m) (Fin m) ℂ)
    (B : Submodule ℂ (Fin m → ℂ)) :
    Submodule.map (Matrix.mulVecLin (c • W)) B = Submodule.map (Matrix.mulVecLin W) B := by
  ext z
  simp only [Submodule.mem_map, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨c • y, B.smul_mem c hy, ?_⟩
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨c⁻¹ • y, B.smul_mem c⁻¹ hy, ?_⟩
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-! ### Section H: Gram determinants and column independence -/

lemma mulVec_eq_sum_smul_cols {m r : ℕ} (C : Matrix (Fin m) (Fin r) ℂ) (lam : Fin r → ℂ) :
    C.mulVec lam = ∑ t, lam t • (fun i => C i t) := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [mul_comm]

lemma cols_ker {m r : ℕ} {C : Matrix (Fin m) (Fin r) ℂ}
    (h : LinearIndependent ℂ (fun t : Fin r => (fun i : Fin m => C i t)))
    {lam : Fin r → ℂ} (h0 : C.mulVec lam = 0) : lam = 0 := by
  have h1 := (Fintype.linearIndependent_iff.mp h) lam
    (by rw [← mulVec_eq_sum_smul_cols, h0])
  funext t
  exact h1 t

/-- Positive-definiteness of the Hermitian Gram matrix: injective columns give a
nonzero Gram determinant. -/
lemma det_gram_ne_zero {m r : ℕ} {C : Matrix (Fin m) (Fin r) ℂ}
    (h : ∀ lam : Fin r → ℂ, C.mulVec lam = 0 → lam = 0) : (Cᴴ * C).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨lam, hlam0, hlam⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : pair (C.mulVec lam) (C.mulVec lam) = 0 := by
    rw [pair_mulVec_left, Matrix.mulVec_mulVec, hlam, pair_zero_right]
  exact hlam0 (h lam (pair_self_eq_zero h1))

/-- A nonzero `det (P * C)` certifies that the columns of `C` are independent. -/
lemma cols_independent_of_det {m r : ℕ} {P : Matrix (Fin r) (Fin m) ℂ}
    {C : Matrix (Fin m) (Fin r) ℂ} (hdet : (P * C).det ≠ 0) :
    LinearIndependent ℂ (fun t : Fin r => (fun i : Fin m => C i t)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro lam hlam
  have hC : C.mulVec lam = 0 := by
    rw [mulVec_eq_sum_smul_cols]
    exact hlam
  have h2 : (P * C).mulVec lam = 0 := by
    rw [← Matrix.mulVec_mulVec, hC, Matrix.mulVec_zero]
  have h3 : lam = 0 := by
    by_contra hne
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨lam, hne, h2⟩)
  intro t
  rw [h3]
  rfl

/-! ### Section I: the condition polynomials -/

/-- The constant polynomial vector attached to `y`. -/
def vecPoly {m : ℕ} (y : Fin m → ℂ) : Fin m → MvPolynomial (Fin m × Fin m) ℂ :=
  fun s => MvPolynomial.C (y s)

/-- The polynomial column of the combined family: constants on the left block,
`Npoly ·  y` on the right block. -/
def wPoly {m n : ℕ} (v : Fin n → Fin m → ℂ) :
    Fin n ⊕ Fin n → Fin m → MvPolynomial (Fin m × Fin m) ℂ :=
  Sum.elim (fun i => vecPoly (v i)) (fun j => (Npoly m).mulVec (vecPoly (v j)))

lemma evalx_wPoly_inl {m n : ℕ} (v : Fin n → Fin m → ℂ) (x : Fin m × Fin m → ℝ)
    (i : Fin n) (r : Fin m) : evalx x (wPoly v (Sum.inl i) r) = v i r := by
  simp [wPoly, vecPoly, evalx]

lemma evalx_wPoly_inr {m n : ℕ} (v : Fin n → Fin m → ℂ) (x : Fin m × Fin m → ℝ)
    (j : Fin n) (r : Fin m) :
    evalx x (wPoly v (Sum.inr j) r)
      = evalx x (Dpoly m) * ((cayley x).mulVec (v j) r) := by
  have h1 : evalx x (wPoly v (Sum.inr j) r)
      = (((Npoly m).map (evalx x)).mulVec (fun s => evalx x (vecPoly (v j) s))) r := by
    rw [wPoly, Sum.elim_inr]
    exact evalx_mulVec x (Npoly m) (vecPoly (v j)) r
  have h2 : (fun s => evalx x (vecPoly (v j) s)) = v j := by
    funext s
    simp [vecPoly, evalx]
  rw [h1, h2, evalx_mat_Npoly, Matrix.smul_mulVec, evalx_Dpoly]
  rfl

/-- The pairing condition polynomial. -/
def gPair {m n : ℕ} (v : Fin n → Fin m → ℂ) (i j : Fin n) :
    MvPolynomial (Fin m × Fin m) ℂ :=
  ∑ r, MvPolynomial.C (star (v i r)) * wPoly v (Sum.inr j) r

lemma evalx_C {m : ℕ} (x : Fin m × Fin m → ℝ) (c : ℂ) :
    evalx x (MvPolynomial.C c) = c :=
  MvPolynomial.eval_C c

lemma evalx_gPair {m n : ℕ} (v : Fin n → Fin m → ℂ) (i j : Fin n)
    (x : Fin m × Fin m → ℝ) :
    evalx x (gPair v i j) = evalx x (Dpoly m) * pair (v i) ((cayley x).mulVec (v j)) := by
  rw [gPair, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, evalx_C, evalx_wPoly_inr]
  ring

/-- The matrix of chosen polynomial columns. -/
def colPolyMat {m n r : ℕ} (v : Fin n → Fin m → ℂ) (aIdx : Fin r → Fin n ⊕ Fin n) :
    Matrix (Fin m) (Fin r) (MvPolynomial (Fin m × Fin m) ℂ) :=
  Matrix.of fun i t => wPoly v (aIdx t) i

/-- The matrix of chosen scalar columns at a given matrix `U`. -/
def colMat {m n r : ℕ} (v : Fin n → Fin m → ℂ) (U : Matrix (Fin m) (Fin m) ℂ)
    (aIdx : Fin r → Fin n ⊕ Fin n) : Matrix (Fin m) (Fin r) ℂ :=
  Matrix.of fun i t => Sum.elim v (fun j => U.mulVec (v j)) (aIdx t) i

/-- The rank condition polynomial. -/
def gRank {m n r : ℕ} (v : Fin n → Fin m → ℂ) (P : Matrix (Fin r) (Fin m) ℂ)
    (aIdx : Fin r → Fin n ⊕ Fin n) : MvPolynomial (Fin m × Fin m) ℂ :=
  ((P.map MvPolynomial.C) * colPolyMat v aIdx).det

/-- The per-column denominator scaling factors. -/
def sclFac {m n : ℕ} (x : Fin m × Fin m → ℝ) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim (fun _ => (1 : ℂ)) (fun _ => evalx x (Dpoly m))

lemma sclFac_ne_zero {m n : ℕ} (x : Fin m × Fin m → ℝ) (a : Fin n ⊕ Fin n) :
    sclFac x a ≠ 0 := by
  rcases a with i | j
  · simp [sclFac]
  · simpa [sclFac] using evalx_Dpoly_ne_zero x

lemma evalx_gRank {m n r : ℕ} (v : Fin n → Fin m → ℂ) (P : Matrix (Fin r) (Fin m) ℂ)
    (aIdx : Fin r → Fin n ⊕ Fin n) (x : Fin m × Fin m → ℝ) :
    evalx x (gRank v P aIdx)
      = (∏ t, sclFac x (aIdx t)) * (P * colMat v (cayley x) aIdx).det := by
  rw [gRank, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
  have hP : (P.map MvPolynomial.C).map (evalx x) = P := by
    ext i j
    simp [Matrix.map_apply, evalx]
  have hC : (colPolyMat v aIdx).map (evalx x)
      = Matrix.of (fun i t => sclFac x (aIdx t) * colMat v (cayley x) aIdx i t) := by
    ext i t
    rw [Matrix.map_apply]
    cases haIdx : aIdx t with
    | inl i' =>
        rw [colPolyMat, Matrix.of_apply, haIdx, evalx_wPoly_inl, Matrix.of_apply,
          colMat, Matrix.of_apply, haIdx]
        simp [sclFac]
    | inr j =>
        rw [colPolyMat, Matrix.of_apply, haIdx, evalx_wPoly_inr, Matrix.of_apply,
          colMat, Matrix.of_apply, haIdx]
        simp [sclFac]
  rw [hP, hC]
  have hPC : P * Matrix.of (fun i t => sclFac x (aIdx t) * colMat v (cayley x) aIdx i t)
      = Matrix.of (fun s t => sclFac x (aIdx t) * (P * colMat v (cayley x) aIdx) s t) := by
    ext s t
    rw [Matrix.mul_apply, Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.of_apply]
    ring
  rw [hPC]
  exact Matrix.det_mul_row (fun t => sclFac x (aIdx t)) (P * colMat v (cayley x) aIdx)

/-! ### Section J: existence of nonvanishing points for each condition polynomial -/

/-- The pairing condition: its polynomial is nonzero at some real point and detects
nonorthogonality of the cross pairing. -/
lemma pair_condition {m n : ℕ} (hm : 0 < m) (v : Fin n → Fin m → ℂ)
    (i j : Fin n) (hvi : v i ≠ 0) (hvj : v j ≠ 0) :
    ∃ g : MvPolynomial (Fin m × Fin m) ℂ,
      (∃ x₀ : Fin m × Fin m → ℝ, evalx x₀ g ≠ 0) ∧
      ∀ x : Fin m × Fin m → ℝ, evalx x g ≠ 0 →
        pair (v i) ((cayley x).mulVec (v j)) ≠ 0 := by
  refine ⟨gPair v i j, ?_, ?_⟩
  · obtain ⟨W, hWu, hWp⟩ := exists_unitary_pair_ne_zero hm hvi hvj
    obtain ⟨c, hc, hcdet⟩ := exists_phase_det W
    have hc0 : c ≠ 0 := unimodular_ne_zero hc
    have hW'u : (c • W) * (c • W)ᴴ = 1 := smul_unitary hc hWu
    obtain ⟨x₀, hx₀⟩ := cayley_reaches hW'u hcdet
    refine ⟨x₀, ?_⟩
    rw [evalx_gPair, hx₀]
    apply mul_ne_zero (evalx_Dpoly_ne_zero x₀)
    rw [Matrix.smul_mulVec, pair_smul_right]
    exact mul_ne_zero hc0 hWp
  · intro x hx h0
    rw [evalx_gPair, h0, mul_zero] at hx
    exact hx rfl

/-- The rank condition for a subset pair: its polynomial is nonzero at some real point
and forces the combined family to reach the maximal rank. -/
lemma rank_condition {m n : ℕ} (hm : 0 < m) (v : Fin n → Fin m → ℂ)
    (S T : Finset (Fin n)) :
    ∃ g : MvPolynomial (Fin m × Fin m) ℂ,
      (∃ x₀ : Fin m × Fin m → ℝ, evalx x₀ g ≠ 0) ∧
      ∀ x : Fin m × Fin m → ℝ, evalx x g ≠ 0 →
        min m (rk v S + rk v T)
          ≤ rk (Sum.elim v fun j => (cayley x).mulVec (v j)) (S.disjSum T) := by
  classical
  obtain ⟨W, hWu, hWr⟩ := exists_unitary_sup_finrank hm
    (Submodule.span ℂ (v '' (S : Set (Fin n)))) (Submodule.span ℂ (v '' (T : Set (Fin n))))
  obtain ⟨c, hc, hcdet⟩ := exists_phase_det W
  have hc0 : c ≠ 0 := unimodular_ne_zero hc
  have hW'u : (c • W) * (c • W)ᴴ = 1 := smul_unitary hc hWu
  set W' := c • W with hW'def
  -- the combined span at `W'` has the maximal rank
  have hspan : Module.finrank ℂ (Submodule.span ℂ
        (v '' (S : Set (Fin n)) ∪ (fun j => W'.mulVec (v j)) '' (T : Set (Fin n))))
      = min m (rk v S + rk v T) := by
    rw [Submodule.span_union, span_image_mulVecLin, hW'def, map_smul_mulVecLin hc0, hWr,
      rk_eq_span_image, rk_eq_span_image]
  -- extract independent columns realizing the rank
  set Vset : Set (Fin m → ℂ) :=
    v '' (S : Set (Fin n)) ∪ (fun j => W'.mulVec (v j)) '' (T : Set (Fin n)) with hVset
  obtain ⟨sset, hsub, hsspan, hsli⟩ := exists_linearIndependent ℂ Vset
  have hfin : sset.Finite := hsli.setFinite
  have : Fintype ↥sset := hfin.fintype
  have hindep : LinearIndepOn ℂ id sset := hsli
  have hcard : Fintype.card ↥sset = min m (rk v S + rk v T) := by
    have h1 : Module.finrank ℂ (Submodule.span ℂ sset) = sset.toFinset.card :=
      finrank_span_set_eq_card hindep
    rw [hsspan, hspan] at h1
    rw [← Set.toFinset_card, ← h1]
  set e : Fin (min m (rk v S + rk v T)) ≃ ↥sset :=
    (Fintype.equivFinOfCardEq hcard).symm with he
  set col : Fin (min m (rk v S + rk v T)) → (Fin m → ℂ) := fun t => ((e t : ↥sset) : Fin m → ℂ)
    with hcol
  have hcol_li : LinearIndependent ℂ col := hsli.comp _ e.injective
  have hcol_mem : ∀ t, col t ∈ Vset := fun t => hsub (e t).2
  -- choose realizing indices
  have hidx : ∀ t, ∃ a : Fin n ⊕ Fin n,
      Sum.elim (fun i => i ∈ S) (fun j => j ∈ T) a ∧
      Sum.elim v (fun j => W'.mulVec (v j)) a = col t := by
    intro t
    rcases hcol_mem t with ⟨i, hiS, hvi⟩ | ⟨j, hjT, hvj⟩
    · exact ⟨Sum.inl i, hiS, hvi⟩
    · exact ⟨Sum.inr j, hjT, hvj⟩
  choose aIdx haIdx1 haIdx2 using hidx
  have hcolMat : ∀ t, (fun i => colMat v W' aIdx i t) = col t := by
    intro t
    funext i
    rw [colMat, Matrix.of_apply]
    exact congrFun (haIdx2 t) i
  set P : Matrix (Fin (min m (rk v S + rk v T))) (Fin m) ℂ := (colMat v W' aIdx)ᴴ with hP
  have hgram : (P * colMat v W' aIdx).det ≠ 0 := by
    rw [hP]
    apply det_gram_ne_zero
    intro lam h0
    apply cols_ker ?_ h0
    have hcols : (fun t => (fun i => colMat v W' aIdx i t)) = col := funext hcolMat
    rw [hcols]
    exact hcol_li
  refine ⟨gRank v P aIdx, ?_, ?_⟩
  · obtain ⟨x₀, hx₀⟩ := cayley_reaches hW'u hcdet
    refine ⟨x₀, ?_⟩
    rw [evalx_gRank, hx₀]
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      exact fun t _ => sclFac_ne_zero x₀ (aIdx t)
    · exact hgram
  · intro x hx
    rw [evalx_gRank] at hx
    have hdet : (P * colMat v (cayley x) aIdx).det ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hx
      exact hx rfl
    have hli := cols_independent_of_det hdet
    apply rk_ge_of_cols v (fun j => (cayley x).mulVec (v j)) S T
      (fun t => (fun i => colMat v (cayley x) aIdx i t)) ?_ hli
    intro t
    rcases haIdx3 : aIdx t with i | j
    · left
      refine ⟨i, ?_, ?_⟩
      · have := haIdx1 t
        rwa [haIdx3] at this
      · funext i'
        rw [colMat, Matrix.of_apply, haIdx3]
        rfl
    · right
      refine ⟨j, ?_, ?_⟩
      · have := haIdx1 t
        rwa [haIdx3] at this
      · funext i'
        rw [colMat, Matrix.of_apply, haIdx3]
        rfl

/-! ### Section K: assembly of the main theorem -/

theorem all_nonzero : ∀ (k n : ℕ), 2 ≤ k →
    ∀ (v : Fin n → Fin k → ℂ),
      (∀ i, v i ≠ 0) →
      ∃ U : Matrix (Fin k) (Fin k) ℂ,
        IsUnitary U ∧
        (∀ (i j : Fin n),
          pair (v i) (applyMat U (v j)) ≠ 0) ∧
        Transversal v (fun j => applyMat U (v j)) := by
  intro k n hk v hv0
  classical
  have hm : 0 < k := by omega
  have hpairs : ∀ ij : Fin n × Fin n, ∃ g : MvPolynomial (Fin k × Fin k) ℂ,
      (∃ x₀ : Fin k × Fin k → ℝ, evalx x₀ g ≠ 0) ∧
      ∀ x : Fin k × Fin k → ℝ, evalx x g ≠ 0 →
        pair (v ij.1) ((cayley x).mulVec (v ij.2)) ≠ 0 :=
    fun ij => pair_condition hm v ij.1 ij.2 (hv0 _) (hv0 _)
  have hranks : ∀ ST : Finset (Fin n) × Finset (Fin n),
      ∃ g : MvPolynomial (Fin k × Fin k) ℂ,
      (∃ x₀ : Fin k × Fin k → ℝ, evalx x₀ g ≠ 0) ∧
      ∀ x : Fin k × Fin k → ℝ, evalx x g ≠ 0 →
        min k (rk v ST.1 + rk v ST.2)
          ≤ rk (Sum.elim v fun j => (cayley x).mulVec (v j)) (ST.1.disjSum ST.2) :=
    fun ST => rank_condition hm v ST.1 ST.2
  choose gp hgp1 hgp2 using hpairs
  choose gr hgr1 hgr2 using hranks
  set G : MvPolynomial (Fin k × Fin k) ℂ :=
    (∏ ij : Fin n × Fin n, gp ij) * (∏ ST : Finset (Fin n) × Finset (Fin n), gr ST) with hG
  have hG0 : G ≠ 0 := by
    rw [hG]
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro ij _
      obtain ⟨x₀, hx₀⟩ := hgp1 ij
      intro h
      rw [h, map_zero] at hx₀
      exact hx₀ rfl
    · rw [Finset.prod_ne_zero_iff]
      intro ST _
      obtain ⟨x₀, hx₀⟩ := hgr1 ST
      intro h
      rw [h, map_zero] at hx₀
      exact hx₀ rfl
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero' G hG0
  have hxG : evalx x G ≠ 0 := hx
  have hfac_p : ∀ ij : Fin n × Fin n, evalx x (gp ij) ≠ 0 := by
    intro ij h0
    apply hxG
    rw [hG, map_mul]
    apply mul_eq_zero_of_left
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ij) h0
  have hfac_r : ∀ ST : Finset (Fin n) × Finset (Fin n), evalx x (gr ST) ≠ 0 := by
    intro ST h0
    apply hxG
    rw [hG, map_mul]
    apply mul_eq_zero_of_right
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ST) h0
  refine ⟨cayley x, ?_, ?_, ?_⟩
  · show cayley x * star (cayley x) = 1
    rw [Matrix.star_eq_conjTranspose]
    exact cayley_unitary x
  · intro i j
    exact hgp2 (i, j) x (hfac_p (i, j))
  · intro S T
    have hUu : cayley x * (cayley x)ᴴ = 1 := cayley_unitary x
    apply le_antisymm
    · exact rk_disjSum_le v (fun j => applyMat (cayley x) (v j)) S T
    · have h2 := hgr2 (S, T) x (hfac_r (S, T))
      have h3 : rk (fun j => (cayley x).mulVec (v j)) T = rk v T :=
        rk_image_unitary hUu v T
      calc min k (rk v S + rk (fun j => applyMat (cayley x) (v j)) T)
          = min k (rk v S + rk v T) := by rw [h3]
        _ ≤ _ := h2

end

end P14UnitaryReused


/- Source: elliptic_audit/GPBlockPlacement.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-!
Full general-position placement of two different finite blocks, preserving each
block's internal Hermitian pairings. The unitary genericity argument is the
attributed s19 reuse in UnitaryReused; its Tight/Spanning hypotheses were unused.
-/

noncomputable section
open Matrix

namespace P14GPBlockPlacement
open P14UnitaryReused

/-- Full general position, including small subfamilies when the whole block is small. -/
def FullSpark {k : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    (v : V → Fin k → ℂ) : Prop :=
  ∀ S : Finset V, S.card ≤ k → LinearIndependent ℂ (fun i : (S : Set V) => v i.1)

/-- Exact dimension-sized independence implies all smaller instances when enough rows exist.
The finite permutation extension is also used by the earlier MixedRanks helper. -/
theorem fullSpark_of_exact {k n : ℕ} (hn : k ≤ n) (v : Fin n → Fin k → ℂ)
    (h : ∀ f : Fin k → Fin n, Function.Injective f →
      LinearIndependent ℂ (fun q => v (f q))) : FullSpark v := by
  classical
  intro S hS
  let e : (S : Set (Fin n)) ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let f : Fin S.card → Fin n := fun q => (e.symm q).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hSn : S.card ≤ n := hS.trans hn
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE hSn) f (Fin.castLE_injective _) hf
  have hli := h (σ ∘ Fin.castLE hn) (σ.injective.comp (Fin.castLE_injective _))
  have hres := hli.comp (Fin.castLE hS) (Fin.castLE_injective _)
  have heq : (fun q => v ((σ ∘ Fin.castLE hn) q)) ∘ Fin.castLE hS =
      fun q => v (f q) := by
    funext i
    exact congrArg v (hσ i)
  rw [heq] at hres
  simpa [f, Function.comp_def] using hres.comp e e.injective

/-- Reindex the two desired blocks inside one larger family before invoking s19. -/
theorem two_family_unitary {k n₁ n₂ : ℕ} (hk : 2 ≤ k)
    (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ)
    (hu : ∀ i, u i ≠ 0) (hw : ∀ j, w j ≠ 0) :
    ∃ U : Matrix (Fin k) (Fin k) ℂ,
      U * Uᴴ = 1 ∧
      (∀ i j, pair (u i) (U.mulVec (w j)) ≠ 0) ∧
      Transversal u (fun j => U.mulVec (w j)) := by
  classical
  let e : Fin n₁ ⊕ Fin n₂ ≃ Fin (n₁ + n₂) := finSumFinEquiv
  let v : Fin (n₁ + n₂) → Fin k → ℂ := fun i => Sum.elim u w (e.symm i)
  let il : Fin n₁ → Fin (n₁ + n₂) := fun i => e (.inl i)
  let ir : Fin n₂ → Fin (n₁ + n₂) := fun j => e (.inr j)
  have hv : ∀ i, v i ≠ 0 := by
    intro i
    dsimp [v]
    cases e.symm i with
    | inl i => exact hu i
    | inr j => exact hw j
  obtain ⟨U, hU, hp, ht⟩ := all_nonzero k (n₁ + n₂) hk v hv
  refine ⟨U, by simpa [IsUnitary, Matrix.star_eq_conjTranspose] using hU, ?_, ?_⟩
  · intro i j
    simpa [v, il, ir] using hp (il i) (ir j)
  · intro S T
    have h := ht (S.image il) (T.image ir)
    rw [rk_disjSum_eq] at h ⊢
    simp only [rk_eq_span_image] at h ⊢
    have hL : v '' (↑(S.image il) : Set (Fin (n₁ + n₂))) = u '' (S : Set (Fin n₁)) := by
      rw [Finset.coe_image, Set.image_image]
      simp [v, il]
    have hR : (fun j => U.mulVec (v j)) '' (↑(T.image ir) : Set (Fin (n₁ + n₂))) =
        (fun j => U.mulVec (w j)) '' (T : Set (Fin n₂)) := by
      rw [Finset.coe_image, Set.image_image]
      simp [v, ir]
    change Module.finrank ℂ (Submodule.span ℂ (v '' (↑(S.image il) : Set _)) ⊔
        Submodule.span ℂ ((fun j => U.mulVec (v j)) '' (↑(T.image ir) : Set _)) :
          Submodule ℂ (Fin k → ℂ)) =
      min k (Module.finrank ℂ (Submodule.span ℂ (v '' (↑(S.image il) : Set _))) +
        Module.finrank ℂ (Submodule.span ℂ ((fun j => U.mulVec (v j)) ''
          (↑(T.image ir) : Set _)))) at h
    rwa [hL, hR] at h

lemma pair_unitary {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ} (hU : U * Uᴴ = 1)
    (a b : Fin k → ℂ) : pair (U.mulVec a) (U.mulVec b) = pair a b := by
  rw [pair_mulVec_left, Matrix.mulVec_mulVec, mul_eq_one_comm.mp hU, Matrix.one_mulVec]

lemma unitary_nonzero {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ} (hU : U * Uᴴ = 1)
    {a : Fin k → ℂ} (ha : a ≠ 0) : U.mulVec a ≠ 0 := by
  intro hz
  have h := congrArg Uᴴ.mulVec hz
  rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp hU, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  exact ha h

lemma rank_eq_card {k : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    {v : V → Fin k → ℂ} (hv : FullSpark v) (S : Finset V) (hS : S.card ≤ k) :
    rk v S = S.card := by
  rw [rk, finrank_span_eq_card (hv S hS)]
  simp

theorem fullSpark_union_of_transversal {k n₁ n₂ : ℕ}
    (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ)
    (hu : FullSpark u) (hw : FullSpark w)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U * Uᴴ = 1)
    (ht : Transversal u (fun j => U.mulVec (w j))) :
    FullSpark (Sum.elim u (fun j => U.mulVec (w j))) := by
  intro S hS
  have hl : S.toLeft.card ≤ k := Finset.card_toLeft_le.trans hS
  have hr : S.toRight.card ≤ k := Finset.card_toRight_le.trans hS
  have h := ht S.toLeft S.toRight
  rw [Finset.toLeft_disjSum_toRight, rk_image_unitary hU, rank_eq_card hu _ hl,
    rank_eq_card hw _ hr, Finset.card_toLeft_add_card_toRight, min_eq_right hS] at h
  apply (linearIndependent_iff_card_eq_finrank_span (R := ℂ)).mpr
  simpa [rk, Set.finrank] using h.symm

/-- Two full-general-position blocks admit simultaneous full general position,
with every internal pairing preserved and no new cross orthogonality. -/
theorem place_fullSpark_blocks {k n₁ n₂ : ℕ} (hk : 2 ≤ k)
    (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ)
    (hu0 : ∀ i, u i ≠ 0) (hw0 : ∀ j, w j ≠ 0)
    (hu : FullSpark u) (hw : FullSpark w) :
    ∃ w' : Fin n₂ → Fin k → ℂ,
      (∀ j, w' j ≠ 0) ∧
      (∀ i j, pair (w' i) (w' j) = pair (w i) (w j)) ∧
      (∀ i j, pair (u i) (w' j) ≠ 0) ∧
      FullSpark (Sum.elim u w') := by
  obtain ⟨U, hU, hp, ht⟩ := two_family_unitary hk u w hu0 hw0
  exact ⟨fun j => U.mulVec (w j), fun j => unitary_nonzero hU (hw0 j),
    fun i j => pair_unitary hU (w i) (w j), hp,
    fullSpark_union_of_transversal u w hu hw U hU ht⟩

/-- Direct interface for finite Euclidean prism/clique families.
Both input blocks have every `k` rows independent; the output union has the same property. -/
theorem place_euclidean_blocks {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {k : ℕ} (hk : 2 ≤ k)
    (hV : k ≤ Fintype.card V) (hW : k ≤ Fintype.card W)
    (u : V → P14UPBAssembly.Space k) (w : W → P14UPBAssembly.Space k)
    (hu0 : ∀ i, u i ≠ 0) (hw0 : ∀ j, w j ≠ 0)
    (hu : ∀ f : Fin k → V, Function.Injective f →
      LinearIndependent ℂ (fun q => u (f q)))
    (hw : ∀ f : Fin k → W, Function.Injective f →
      LinearIndependent ℂ (fun q => w (f q))) :
    ∃ w' : W → P14UPBAssembly.Space k,
      (∀ j, w' j ≠ 0) ∧
      (∀ i j, inner ℂ (w' i) (w' j) = inner ℂ (w i) (w j)) ∧
      (∀ i j, inner ℂ (u i) (w' j) ≠ 0) ∧
      P14UPBAssembly.SpansEvery (Sum.elim u w') k := by
  classical
  let eV := Fintype.equivFin V
  let eW := Fintype.equivFin W
  let eL : (Fin k → ℂ) ≃ₗ[ℂ] P14UPBAssembly.Space k :=
    (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).symm
  let u₀ : Fin (Fintype.card V) → Fin k → ℂ := fun i => eL.symm (u (eV.symm i))
  let w₀ : Fin (Fintype.card W) → Fin k → ℂ := fun j => eL.symm (w (eW.symm j))
  have hu₀ : ∀ i, u₀ i ≠ 0 := by
    intro i hi
    apply hu0 (eV.symm i)
    exact eL.symm.injective (hi.trans (map_zero eL.symm).symm)
  have hw₀ : ∀ j, w₀ j ≠ 0 := by
    intro j hj
    apply hw0 (eW.symm j)
    exact eL.symm.injective (hj.trans (map_zero eL.symm).symm)
  have huGP : FullSpark u₀ := by
    apply fullSpark_of_exact hV
    intro f hf
    have h := (hu (eV.symm ∘ f) (eV.symm.injective.comp hf)).map'
      eL.symm.toLinearMap (by simp)
    simpa [u₀, Function.comp_def] using h
  have hwGP : FullSpark w₀ := by
    apply fullSpark_of_exact hW
    intro f hf
    have h := (hw (eW.symm ∘ f) (eW.symm.injective.comp hf)).map'
      eL.symm.toLinearMap (by simp)
    simpa [w₀, Function.comp_def] using h
  obtain ⟨w₁, hw₁, hp, hc, hGP⟩ := place_fullSpark_blocks hk u₀ w₀ hu₀ hw₀ huGP hwGP
  let w' : W → P14UPBAssembly.Space k := fun j => eL (w₁ (eW j))
  have hinner (a b : Fin k → ℂ) : inner ℂ (eL a) (eL b) = pair a b := by
    exact (pair_eq_inner (eL a) (eL b)).symm
  refine ⟨w', ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact hw₁ (eW j) (eL.injective (hj.trans (map_zero eL).symm))
  · intro i j
    change inner ℂ (eL (w₁ (eW i))) (eL (w₁ (eW j))) = _
    rw [hinner, hp]
    simpa [w₀, eL] using (pair_eq_inner (w i) (w j))
  · intro i j
    have h := hc (eV i) (eW j)
    simpa [u₀, w', eL, pair_eq_inner] using h
  · apply P14UPBAssembly.spansEvery_of_independent
    intro S hS
    let E : V ⊕ W ≃ Fin (Fintype.card V) ⊕ Fin (Fintype.card W) :=
      Equiv.sumCongr eV eW
    let T := S.image E
    have hT : T.card ≤ k := by simp [T, Finset.card_image_of_injective _ E.injective, hS]
    let f : ↥(S : Set (V ⊕ W)) → ↥(T : Set (Fin (Fintype.card V) ⊕ Fin (Fintype.card W))) :=
      fun i => ⟨E i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Subtype.ext (E.injective (congrArg Subtype.val hij))
    have hli := ((hGP T hT).comp f hf).map' eL.toLinearMap (by simp)
    have heq : (fun i : (S : Set (V ⊕ W)) =>
        eL (Sum.elim u₀ w₁ (f i).val)) = fun i => Sum.elim u w' i.val := by
      funext i
      cases hi : i.val with
      | inl j => simp [f, E, u₀, hi]
      | inr j => simp [f, E, w', hi]
    change LinearIndependent ℂ (fun i : (S : Set (V ⊕ W)) =>
      eL (Sum.elim u₀ w₁ (f i).val)) at hli
    rwa [heq] at hli

end P14GPBlockPlacement
end


/- Source: elliptic_audit/PrismCliqueRows.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-!
Explicit GP4 prism, any number of K4 blocks, and two copies of the resulting half-family.
The prism's six integer rows were supplied and independently checked by the literature agent.
CliqueRows is root's attributed Vandermonde construction. GPBlockPlacement reuses s19.
-/

noncomputable section
open scoped BigOperators
open P14UPBAssembly P14GPBlockPlacement

namespace P14PrismCliqueRows

def prismZ : Fin 6 → Fin 4 → ℤ := ![
  ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0],
  ![0, 1, 1, 1], ![1, 0, 1, -1], ![1, -1, 0, 1]]

def PrismAdj (i j : Fin 6) : Prop :=
  i ≠ j ∧ (i.val / 3 = j.val / 3 ∨ i.val % 3 = j.val % 3)

instance (i j : Fin 6) : Decidable (PrismAdj i j) := inferInstanceAs (Decidable (_ ∧ _))

lemma prismZ_nonzero : ∀ i : Fin 6, ∃ r, prismZ i r ≠ 0 := by decide +kernel

lemma prismZ_orth : ∀ i j : Fin 6,
    (∑ r, prismZ i r * prismZ j r) = 0 ↔ PrismAdj i j := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prismZ_det : ∀ f : Fin 4 → Fin 6, Function.Injective f →
    Matrix.det (fun i j : Fin 4 => prismZ (f i) j) ≠ 0 := by decide +kernel

def prism (i : Fin 6) : Space 4 :=
  WithLp.toLp 2 (fun r => (prismZ i r : ℂ))

theorem prism_nonzero (i : Fin 6) : prism i ≠ 0 := by
  obtain ⟨r, hr⟩ := prismZ_nonzero i
  intro hz
  have h := congrArg (fun v : Space 4 => v r) hz
  have hc : (prismZ i r : ℂ) = 0 := h
  exact hr (by exact_mod_cast hc)

theorem prism_orth (i j : Fin 6) : inner ℂ (prism i) (prism j) = 0 ↔ PrismAdj i j := by
  rw [← P14UnitaryReused.pair_eq_inner]
  change (∑ r, star (prismZ i r : ℂ) * (prismZ j r : ℂ)) = 0 ↔ _
  have hcast : (∑ r, star (prismZ i r : ℂ) * (prismZ j r : ℂ)) =
      ((∑ r, prismZ i r * prismZ j r : ℤ) : ℂ) := by simp
  rw [hcast, Int.cast_eq_zero]
  exact prismZ_orth i j

theorem prism_independent (f : Fin 4 → Fin 6) (hf : Function.Injective f) :
    LinearIndependent ℂ (fun q => prism (f q)) := by
  let A : Matrix (Fin 4) (Fin 4) ℤ := fun i j => prismZ (f i) j
  have hd : (A.map (Int.castRingHom ℂ)).det ≠ 0 := by
    change ((Int.castRingHom ℂ).mapMatrix A).det ≠ 0
    rw [← RingHom.map_det]
    change (A.det : ℂ) ≠ 0
    have hz : A.det ≠ 0 := prismZ_det f hf
    exact_mod_cast hz
  have h := (Matrix.linearIndependent_rows_of_det_ne_zero hd).map'
    (WithLp.linearEquiv 2 ℂ (Fin 4 → ℂ)).symm.toLinearMap (by simp)
  change LinearIndependent ℂ (fun q => prism (f q)) at h
  exact h

theorem prism_spans : SpansEvery prism 4 := spansEvery_of_exact_independent prism prism_independent

abbrev HalfVertices (q : ℕ) := Fin 6 ⊕ (Fin q × Fin 4)

/-- Prism first, followed by `q` clique blocks. Includes the standalone prism at `q=0`. -/
theorem half_rows (q : ℕ) :
    ∃ v : HalfVertices q → Space 4,
      (∀ i, v i ≠ 0) ∧
      (∀ i j, inner ℂ (v (.inl i)) (v (.inl j)) = 0 ↔ PrismAdj i j) ∧
      (∀ c a b, a ≠ b → inner ℂ (v (.inr (c, a))) (v (.inr (c, b))) = 0) ∧
      (∀ f : Fin 4 → HalfVertices q, Function.Injective f →
        LinearIndependent ℂ (fun j => v (f j))) ∧
      SpansEvery v 4 := by
  classical
  by_cases hq : q = 0
  · subst q
    let e : HalfVertices 0 → Fin 6 := Sum.elim id (fun i => Fin.elim0 i.1)
    have he : Function.Injective e := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact congrArg Sum.inl hij
        | inr j => exact Fin.elim0 j.1
      | inr i => exact Fin.elim0 i.1
    let v : HalfVertices 0 → Space 4 := fun i => prism (e i)
    have hs : SpansEvery v 4 := spansEvery_pullback prism prism_spans e he
    refine ⟨v, fun i => prism_nonzero (e i), ?_, ?_,
      exact_independent_of_spansEvery v hs, hs⟩
    · exact prism_orth
    · intro c
      exact Fin.elim0 c
  · obtain ⟨w, hw0, horth, hli, -⟩ := P14CliqueRows.clique_rows q 4 (by omega) (by omega)
    obtain ⟨w', hw'0, hpair, -, hspan⟩ := place_euclidean_blocks (k := 4)
      (by omega) (by simp) (by simp; omega) prism w prism_nonzero hw0 prism_independent hli
    let v : HalfVertices q → Space 4 := Sum.elim prism w'
    refine ⟨v, ?_, prism_orth, ?_, exact_independent_of_spansEvery v hspan, hspan⟩
    · intro i
      cases i with
      | inl i => exact prism_nonzero i
      | inr i => exact hw'0 i
    · intro c a b hab
      change inner ℂ (w' (c, a)) (w' (c, b)) = 0
      rw [hpair]
      exact horth c a b hab

/-- Two halves on a common vertex set, suitable for the two sides of the bipartite seed. -/
theorem two_half_rows (q : ℕ) :
    ∃ a b : HalfVertices q → Space 4,
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (∀ i j, inner ℂ (a (.inl i)) (a (.inl j)) = 0 ↔ PrismAdj i j) ∧
      (∀ i j, inner ℂ (b (.inl i)) (b (.inl j)) = 0 ↔ PrismAdj i j) ∧
      (∀ c i j, i ≠ j → inner ℂ (a (.inr (c, i))) (a (.inr (c, j))) = 0 ∧
        inner ℂ (b (.inr (c, i))) (b (.inr (c, j))) = 0) ∧
      (∀ f : Fin 4 → HalfVertices q ⊕ HalfVertices q, Function.Injective f →
        LinearIndependent ℂ (fun j => Sum.elim a b (f j))) ∧
      SpansEvery (Sum.elim a b) 4 := by
  obtain ⟨a, ha0, hap, hac, haLI, -⟩ := half_rows q
  have hc : 4 ≤ Fintype.card (HalfVertices q) := by simp [HalfVertices]; omega
  obtain ⟨b, hb0, hbpair, -, hs⟩ := place_euclidean_blocks (by omega) hc hc
    a a ha0 ha0 haLI haLI
  refine ⟨a, b, fun i => ⟨ha0 i, hb0 i⟩, hap, ?_, ?_,
    exact_independent_of_spansEvery (Sum.elim a b) hs, hs⟩
  · intro i j
    rw [hbpair]
    exact hap i j
  · intro c i j hij
    exact ⟨hac c i j hij, by rw [hbpair]; exact hac c i j hij⟩

end P14PrismCliqueRows
end


/- Source: grouping_audit/EvenHalfUPB.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The `M = 8*c` subfamily of the two-qubits/quart/even-factor assembly.
This file combines locally kernel-checked components, and does not assert
the full `M % 4 = 0` statement. -/

noncomputable section
open Function

namespace P14EvenHalfUPB

open P14UPBAssembly

lemma spansEvery_comp {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {k s : ℕ} (v : W → Space k)
    (hv : SpansEvery v s) (f : V → W) (hf : Injective f) :
    SpansEvery (v ∘ f) s := by
  intro S hS
  let T := S.image f
  have hT : T.card = s := by simpa [T, Finset.card_image_of_injective S hf] using hS
  have hsub : (Set.range fun i : (T : Set W) => v i.val) ⊆
      Set.range (fun i : (S : Set V) => (v ∘ f) i.val) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp i.property
    exact ⟨⟨j, hj⟩, congrArg v he⟩
  apply top_unique
  rw [← hv T hT]
  exact Submodule.span_mono hsub

lemma matching_vectors {V : Type*} [Fintype V] [DecidableEq V]
    (F : V → V) (hF : Involutive F) (hfix : ∀ i, F i ≠ i) :
    ∃ z : V → Space 2,
      (∀ i, z i ≠ 0) ∧ (∀ i, inner ℂ (z i) (z (F i)) = 0) ∧ SpansEvery z 2 := by
  let e := Fintype.equivFin V
  let G : Fin (Fintype.card V) → Fin (Fintype.card V) := fun i => e (F (e.symm i))
  have hG : Involutive G := by
    intro i
    simp only [G, e.symm_apply_apply]
    rw [hF (e.symm i), e.apply_symm_apply]
  have hGn : ∀ i, G i ≠ i := by
    intro i hi
    apply hfix (e.symm i)
    exact e.injective (by simpa [G] using hi)
  refine ⟨fun i => P14QubitMatching.vectors G (e i),
    fun i => P14QubitMatching.nonzero G (e i), ?_, ?_⟩
  · intro i
    simpa [G] using P14QubitMatching.matching_orthogonal G hG hGn (e i)
  · exact spansEvery_comp _ (P14QubitMatching.spans_every_two G hG.injective) e e.injective

def sameMatch {V : Type*} (f : V → V) : V ⊕ V → V ⊕ V := Sum.map f f

lemma sameMatch_involutive {V : Type*} (f : V → V) (hf : Involutive f) :
    Involutive (sameMatch f) := by
  intro i
  cases i with
  | inl i => exact congrArg Sum.inl (hf i)
  | inr i => exact congrArg Sum.inr (hf i)

lemma sameMatch_ne {V : Type*} (f : V → V) (hf : ∀ i, f i ≠ i) :
    ∀ i, sameMatch f i ≠ i := by intro i; cases i <;> simpa [sameMatch] using hf _

def crossMatch {V : Type*} (f : Equiv.Perm V) : V ⊕ V → V ⊕ V
  | .inl i => .inr (f i)
  | .inr i => .inl (f.symm i)

lemma crossMatch_involutive {V : Type*} (f : Equiv.Perm V) :
    Involutive (crossMatch f) := by intro i; cases i <;> simp [crossMatch]

lemma crossMatch_ne {V : Type*} (f : Equiv.Perm V) :
    ∀ i, crossMatch f i ≠ i := by intro i; cases i <;> simp [crossMatch]

def finZEquiv (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun := fun i => (i.val : ZMod n)
  invFun := fun i => ⟨i.val, ZMod.val_lt i⟩
  left_inv := by intro i; apply Fin.ext; exact ZMod.val_natCast_of_lt i.isLt
  right_inv := ZMod.natCast_zmod_val

abbrev Block (c : ℕ) := Fin c × Fin 2 × Fin 2
abbrev Vertex (c : ℕ) := Block c ⊕ Block c

lemma vertex_card (c : ℕ) : Fintype.card (Vertex c) = 8*c := by
  simp [Vertex, Block]
  omega

/-- The complete nonzero, orthogonality, and product-survivor conclusion. -/
def HasUPB (V : Type*) (t k : ℕ) : Prop :=
  ∃ z : V → Fin t → Space 2, ∃ y : V → Space 4, ∃ x : V → Space k,
    (∀ i q, z i q ≠ 0) ∧ (∀ i, y i ≠ 0 ∧ x i ≠ 0) ∧
    (∀ i j, i ≠ j →
      (∃ q, inner ℂ (z i q) (z j q) = 0) ∨
      inner ℂ (y i) (y j) = 0 ∨ inner ℂ (x i) (x j) = 0) ∧
    (∀ az : Fin t → Space 2, ∀ ay : Space 4, ∀ ax : Space k,
      (∀ q, az q ≠ 0) → ay ≠ 0 → ax ≠ 0 →
      ∃ i, (∀ q, inner ℂ (z i q) (az q) ≠ 0) ∧
        inner ℂ (y i) ay ≠ 0 ∧ inner ℂ (x i) ax ≠ 0)

theorem on_vertices (c r : ℕ) (hr : 2 ≤ r) (hcr : r + 2 ≤ 2*c) :
    HasUPB (Vertex c) (8*c - 2*r - 4) (2*r) := by
  classical
  have hc : 0 < c := by omega
  let n := 2*(2*c)
  have hn : 0 < n := by dsimp [n]; omega
  let : NeZero n := ⟨by omega⟩
  let eB : Block c ≃ Fin n := Fintype.equivFinOfCardEq (by simp [Block, n]; omega)
  let eS : Vertex c ≃ Fin n ⊕ Fin n := Equiv.sumCongr eB eB
  let eZ : Block c ≃ ZMod n := eB.trans (finZEquiv n)
  obtain ⟨a,b,hab0,hab,_,_,hspan⟩ :=
    Submissions.EllipticBipartiteSeedFamily.CuspAssembly.proof r (2*c) hr hcr
  let x : Vertex c → Space (2*r) := (Sum.elim a b) ∘ eS
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i
    cases i with
    | inl i => exact (hab0 (eB i)).1
    | inr i => exact (hab0 (eB i)).2
  have hxspan : SpansEvery x (2*r+1) := spansEvery_comp _ hspan eS eS.injective
  have hxcross (i j : Block c) :
      inner ℂ (x (.inl i)) (x (.inr j)) = 0 ↔
        P14CrossComplement.CrossAdj (r := r) (eZ i) (eZ j) := by
    change inner ℂ (a (eB i)) (b (eB j)) = 0 ↔
      P14CrossComplement.CrossAdj (r := r) ((eB i).val : ZMod n) ((eB j).val : ZMod n)
    simpa only [
      Submissions.EllipticBipartiteSeedFamily.CuspAssembly.CrossAdjFin,
      Submissions.EllipticBipartiteSeedFamily.CuspAssembly.CrossAdj,
      Submissions.EllipticBipartiteSeedFamily.CuspAssembly.cOffset,
      Submissions.EllipticBipartiteSeedFamily.CuspAssembly.dOffset,
      P14CrossComplement.CrossAdj]
      using hab (eB i) (eB j)
  let eC : Fin c ⊕ Fin c ≃ Fin (2*c) :=
    Fintype.equivFinOfCardEq (by simp; omega)
  let e4 : Fin 2 × Fin 2 ≃ Fin 4 := Fintype.equivFinOfCardEq (by decide)
  let eY : Vertex c ≃ Fin (2*c) × Fin 4 :=
    (Equiv.sumProdDistrib (Fin c) (Fin c) (Fin 2 × Fin 2)).symm.trans
      (Equiv.prodCongr eC e4)
  obtain ⟨yy,hy0,hyorth,hyind,_⟩ := P14CliqueRows.clique_rows (2*c) 4 (by omega) (by decide)
  let y : Vertex c → Space 4 := yy ∘ eY
  have hyspan : SpansEvery y 4 := by
    apply spansEvery_of_exact_independent
    intro f hf
    exact hyind (eY ∘ f) (eY.injective.comp hf)
  have hya (i j : Block c) (hne : i ≠ j) (hblock : i.1 = j.1) :
      inner ℂ (y (.inl i)) (y (.inl j)) = 0 := by
    change inner ℂ (yy (eC (.inl i.1), e4 i.2)) (yy (eC (.inl j.1), e4 j.2)) = 0
    rw [hblock]
    apply hyorth
    intro h
    exact hne (Prod.ext hblock (e4.injective h))
  have hyb (i j : Block c) (hne : i ≠ j) (hblock : i.1 = j.1) :
      inner ℂ (y (.inr i)) (y (.inr j)) = 0 := by
    change inner ℂ (yy (eC (.inr i.1), e4 i.2)) (yy (eC (.inr j.1), e4 j.2)) = 0
    rw [hblock]
    apply hyorth
    intro h
    exact hne (Prod.ext hblock (e4.injective h))
  obtain ⟨I,hIblock,hIinv,hIcover⟩ :=
    P14CliqueComplement.clique_complement_factors (c := c) (k := 2) (by omega) (by decide)
  obtain ⟨C,hCcover⟩ := P14CrossComplement.complement_permutations hcr
  let J := Fin ((2*c-2)*2) ⊕ Fin (2*(2*c)-2*r)
  let Cp : Fin (2*(2*c)-2*r) → Equiv.Perm (Block c) :=
    fun q => eZ.trans ((C q).trans eZ.symm)
  let F : J → Vertex c → Vertex c :=
    Sum.elim (fun q => sameMatch (I q)) (fun q => crossMatch (Cp q))
  have hFinv : ∀ q, Involutive (F q) := by
    rintro (q | q)
    · exact sameMatch_involutive _ (hIinv q)
    · exact crossMatch_involutive _
  have hFfix : ∀ q i, F q i ≠ i := by
    rintro (q | q)
    · apply sameMatch_ne
      intro i he
      exact hIblock q i (congrArg Prod.fst he)
    · exact crossMatch_ne _
  choose zz hz0 hzorth hzspan using fun q => matching_vectors (F q) (hFinv q) (hFfix q)
  have hJ : Fintype.card J = 8*c-2*r-4 := by
    simp [J]
    omega
  let eJ : Fin (8*c-2*r-4) ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  let z : Vertex c → Fin (8*c-2*r-4) → Space 2 := fun i q => zz (eJ q) i
  have hmatch (q : J) (i j : Vertex c) (he : F q i = j) :
      ∃ p, inner ℂ (z i p) (z j p) = 0 := by
    refine ⟨eJ.symm q, ?_⟩
    simpa [z, ← he] using hzorth q i
  have hcoverage : ∀ i j : Vertex c, i ≠ j →
      (∃ q, inner ℂ (z i q) (z j q) = 0) ∨
      inner ℂ (y i) (y j) = 0 ∨ inner ℂ (x i) (x j) = 0 := by
    have hcross (i j : Block c) :
        (∃ q, inner ℂ (z (.inl i) q) (z (.inr j) q) = 0) ∨
        inner ℂ (x (.inl i)) (x (.inr j)) = 0 := by
      by_cases h : P14CrossComplement.CrossAdj (r := r) (eZ i) (eZ j)
      · exact Or.inr ((hxcross i j).mpr h)
      · obtain ⟨q,hq,_⟩ := (hCcover (eZ i) (eZ j)).mp h
        apply Or.inl
        apply hmatch (.inr q)
        change Sum.inr (Cp q i) = Sum.inr j
        congr 1
        change eZ.symm (C q (eZ i)) = j
        rw [hq, eZ.symm_apply_apply]
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        by_cases hb : i.1 = j.1
        · exact Or.inr (Or.inl (hya i j (fun h => hij (congrArg Sum.inl h)) hb))
        · obtain ⟨q,hq,_⟩ := (hIcover i j).mp hb
          exact Or.inl (hmatch (.inl q) _ _ (congrArg Sum.inl hq))
      | inr j =>
        exact (hcross i j).imp_right Or.inr
    | inr i =>
      cases j with
      | inl j =>
        rcases hcross j i with ⟨q,hq⟩ | hx
        · exact Or.inl ⟨q, inner_eq_zero_symm.mp hq⟩
        · exact Or.inr (Or.inr (inner_eq_zero_symm.mp hx))
      | inr j =>
        by_cases hb : i.1 = j.1
        · exact Or.inr (Or.inl (hyb i j (fun h => hij (congrArg Sum.inr h)) hb))
        · obtain ⟨q,hq,_⟩ := (hIcover i j).mp hb
          exact Or.inl (hmatch (.inl q) _ _ (congrArg Sum.inr hq))
  refine ⟨z,y,x,fun i q => hz0 (eJ q) i,
    fun i => ⟨hy0 (eY i), hx0 i⟩,hcoverage, ?_⟩
  apply two_four_survivor z y x
  · rw [vertex_card]
    omega
  · intro q
    exact hzspan (eJ q)
  · exact hyspan
  · exact hxspan

/-- Actual UPBs of size `8*c` on dimensions `(2^[8*c-2*r-4],4,2*r)`. -/
theorem proof (c r : ℕ) (hr : 2 ≤ r) (hcr : r+2 ≤ 2*c) :
    HasUPB (Fin (8*c)) (8*c-2*r-4) (2*r) := by
  obtain ⟨z,y,x,hz,hxy,horth,hsurv⟩ := on_vertices c r hr hcr
  let e : Fin (8*c) ≃ Vertex c := (Fintype.equivFinOfCardEq (vertex_card c)).symm
  refine ⟨fun i => z (e i), y ∘ e, x ∘ e, fun i q => hz (e i) q,
    fun i => hxy (e i), ?_, ?_⟩
  · intro i j hij
    exact horth (e i) (e j) (e.injective.ne hij)
  · intro az ay ax haz hay hax
    obtain ⟨i,hi⟩ := hsurv az ay ax haz hay hax
    exact ⟨e.symm i, by simpa using hi⟩

/-- The usual `(k,t)` parameterization, restricted to total order divisible by eight. -/
theorem canonical_subfamily (k t : ℕ) (hk : 4 ≤ k) (hkEven : Even k)
    (ht : k+4 ≤ t) (h8 : (t+k+4) % 8 = 0) :
    HasUPB (Fin (t+k+4)) t k := by
  obtain ⟨r,hr⟩ := hkEven
  obtain ⟨c,hc⟩ := Nat.dvd_of_mod_eq_zero h8
  have hkr : k = 2*r := by omega
  have hr2 : 2 ≤ r := by omega
  have hcr : r+2 ≤ 2*c := by omega
  have htr : t = 8*c-2*r-4 := by omega
  rw [hc, htr, hkr]
  exact proof c r hr2 hcr

end P14EvenHalfUPB
end


/- Source: grouping_audit/AbstractHalfUPB.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! General half-graph assembly. All even half-orders are allowed.
The required local input is a GP4 family and a perfect-matching cover of
its orthogonality complement. The seed and cross-complement are supplied
by the existing exact cusp construction. -/

noncomputable section
open Function P14UPBAssembly P14EvenHalfUPB

namespace P14AbstractHalfUPB

theorem from_global_quart {H : Type} [Fintype H] [DecidableEq H]
    (r N : ℕ) (hr : 2 ≤ r) (hN : r+2 ≤ N) (hcard : Fintype.card H = 2*N)
    (y : H ⊕ H → Space 4) (hy0 : ∀ i, y i ≠ 0) (hyspan : SpansEvery y 4)
    (I : Fin (2*N-4) → H → H) (hIinv : ∀ q, Involutive (I q))
    (hIfix : ∀ q i, I q i ≠ i)
    (hIcover : ∀ i j, i ≠ j →
      (inner ℂ (y (.inl i)) (y (.inl j)) = 0 ∧
       inner ℂ (y (.inr i)) (y (.inr j)) = 0) ∨ ∃ q, I q i = j) :
    HasUPB (H ⊕ H) (4*N-2*r-4) (2*r) := by
  classical
  let n := 2*N
  have hn : 0 < n := by dsimp [n]; omega
  let : NeZero n := ⟨by omega⟩
  let eB : H ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let eS : H ⊕ H ≃ Fin n ⊕ Fin n := Equiv.sumCongr eB eB
  let eZ : H ≃ ZMod n := eB.trans (finZEquiv n)
  obtain ⟨a,b,hab0,hab,_,_,hspan⟩ :=
    Submissions.EllipticBipartiteSeedFamily.CuspAssembly.proof r N hr hN
  let x : H ⊕ H → Space (2*r) := (Sum.elim a b) ∘ eS
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i
    cases i with
    | inl i => exact (hab0 (eB i)).1
    | inr i => exact (hab0 (eB i)).2
  have hxspan : SpansEvery x (2*r+1) := spansEvery_comp _ hspan eS eS.injective
  have hxcross (i j : H) :
      inner ℂ (x (.inl i)) (x (.inr j)) = 0 ↔
        P14CrossComplement.CrossAdj (r := r) (eZ i) (eZ j) := by
    change inner ℂ (a (eB i)) (b (eB j)) = 0 ↔
      P14CrossComplement.CrossAdj (r := r) ((eB i).val : ZMod n) ((eB j).val : ZMod n)
    simpa only [
      Submissions.EllipticBipartiteSeedFamily.CuspAssembly.CrossAdjFin,
      Submissions.EllipticBipartiteSeedFamily.CuspAssembly.CrossAdj,
      Submissions.EllipticBipartiteSeedFamily.CuspAssembly.cOffset,
      Submissions.EllipticBipartiteSeedFamily.CuspAssembly.dOffset,
      P14CrossComplement.CrossAdj]
      using hab (eB i) (eB j)
  obtain ⟨C,hCcover⟩ := P14CrossComplement.complement_permutations hN
  let J := Fin (2*N-4) ⊕ Fin (2*N-2*r)
  let Cp : Fin (2*N-2*r) → Equiv.Perm (H) :=
    fun q => eZ.trans ((C q).trans eZ.symm)
  let F : J → H ⊕ H → H ⊕ H :=
    Sum.elim (fun q => sameMatch (I q)) (fun q => crossMatch (Cp q))
  have hFinv : ∀ q, Involutive (F q) := by
    rintro (q | q)
    · exact sameMatch_involutive _ (hIinv q)
    · exact crossMatch_involutive _
  have hFfix : ∀ q i, F q i ≠ i := by
    rintro (q | q)
    · apply sameMatch_ne
      exact hIfix q
    · exact crossMatch_ne _
  choose zz hz0 hzorth hzspan using fun q => matching_vectors (F q) (hFinv q) (hFfix q)
  have hJ : Fintype.card J = 4*N-2*r-4 := by
    simp [J]
    omega
  let eJ : Fin (4*N-2*r-4) ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  let z : H ⊕ H → Fin (4*N-2*r-4) → Space 2 := fun i q => zz (eJ q) i
  have hmatch (q : J) (i j : H ⊕ H) (he : F q i = j) :
      ∃ p, inner ℂ (z i p) (z j p) = 0 := by
    refine ⟨eJ.symm q, ?_⟩
    simpa [z, ← he] using hzorth q i
  have hcoverage : ∀ i j : H ⊕ H, i ≠ j →
      (∃ q, inner ℂ (z i q) (z j q) = 0) ∨
      inner ℂ (y i) (y j) = 0 ∨ inner ℂ (x i) (x j) = 0 := by
    have hcross (i j : H) :
        (∃ q, inner ℂ (z (.inl i) q) (z (.inr j) q) = 0) ∨
        inner ℂ (x (.inl i)) (x (.inr j)) = 0 := by
      by_cases h : P14CrossComplement.CrossAdj (r := r) (eZ i) (eZ j)
      · exact Or.inr ((hxcross i j).mpr h)
      · obtain ⟨q,hq,_⟩ := (hCcover (eZ i) (eZ j)).mp h
        apply Or.inl
        apply hmatch (.inr q)
        change Sum.inr (Cp q i) = Sum.inr j
        congr 1
        change eZ.symm (C q (eZ i)) = j
        rw [hq, eZ.symm_apply_apply]
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        rcases hIcover i j (fun h => hij (congrArg Sum.inl h)) with hY | ⟨q,hq⟩
        · exact Or.inr (Or.inl hY.1)
        · exact Or.inl (hmatch (.inl q) _ _ (congrArg Sum.inl hq))
      | inr j =>
        exact (hcross i j).imp_right Or.inr
    | inr i =>
      cases j with
      | inl j =>
        rcases hcross j i with ⟨q,hq⟩ | hx
        · exact Or.inl ⟨q, inner_eq_zero_symm.mp hq⟩
        · exact Or.inr (Or.inr (inner_eq_zero_symm.mp hx))
      | inr j =>
        rcases hIcover i j (fun h => hij (congrArg Sum.inr h)) with hY | ⟨q,hq⟩
        · exact Or.inr (Or.inl hY.2)
        · exact Or.inl (hmatch (.inl q) _ _ (congrArg Sum.inr hq))
  refine ⟨z,y,x,fun i q => hz0 (eJ q) i,
    fun i => ⟨hy0 i, hx0 i⟩,hcoverage, ?_⟩
  apply two_four_survivor z y x
  · simp only [Fintype.card_sum, hcard]
    omega
  · intro q
    exact hzspan (eJ q)
  · exact hyspan
  · exact hxspan

/-- A single GP4 half-family and a matching cover of its complement suffice. -/
theorem from_half_rows {H : Type} [Fintype H] [DecidableEq H]
    (r N : ℕ) (hr : 2 ≤ r) (hN : r+2 ≤ N) (hcard : Fintype.card H = 2*N)
    (u : H → Space 4) (hu0 : ∀ i, u i ≠ 0) (huspan : SpansEvery u 4)
    (I : Fin (2*N-4) → H → H) (hIinv : ∀ q, Involutive (I q))
    (hIfix : ∀ q i, I q i ≠ i)
    (hIcover : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0 ∨ ∃ q, I q i = j) :
    HasUPB (Fin (4*N)) (4*N-2*r-4) (2*r) := by
  have hH : 4 ≤ Fintype.card H := by omega
  have hu := exact_independent_of_spansEvery u huspan
  obtain ⟨b,hb0,hbinner,_,hyspan⟩ :=
    P14GPBlockPlacement.place_euclidean_blocks (by decide : 2 ≤ 4) hH hH u u hu0 hu0 hu hu
  let y := Sum.elim u b
  have hy0 : ∀ i, y i ≠ 0 := by
    rintro (i | i)
    · exact hu0 i
    · exact hb0 i
  have hc : ∀ i j, i ≠ j →
      (inner ℂ (y (.inl i)) (y (.inl j)) = 0 ∧
       inner ℂ (y (.inr i)) (y (.inr j)) = 0) ∨ ∃ q, I q i = j := by
    intro i j hij
    rcases hIcover i j hij with h | h
    · exact Or.inl ⟨h, (hbinner i j).trans h⟩
    · exact Or.inr h
  obtain ⟨z,y',x,hz,hxy,horth,hsurv⟩ :=
    from_global_quart r N hr hN hcard y hy0 hyspan I hIinv hIfix hc
  let e : Fin (4*N) ≃ H ⊕ H :=
    (Fintype.equivFinOfCardEq (by simp [hcard]; omega)).symm
  refine ⟨fun i => z (e i), y' ∘ e, x ∘ e, fun i q => hz (e i) q,
    fun i => hxy (e i), ?_, ?_⟩
  · intro i j hij
    exact horth (e i) (e j) (e.injective.ne hij)
  · intro az ay ax haz hay hax
    obtain ⟨i,hi⟩ := hsurv az ay ax haz hay hax
    exact ⟨e.symm i, by simpa using hi⟩

/-- An abstract graph version: only edge-to-orthogonality and complement coverage are needed. -/
theorem from_half_graph {H : Type} [Fintype H] [DecidableEq H]
    (r N : ℕ) (hr : 2 ≤ r) (hN : r+2 ≤ N) (hcard : Fintype.card H = 2*N)
    (Edge : H → H → Prop)
    (u : H → Space 4) (hu0 : ∀ i, u i ≠ 0) (huspan : SpansEvery u 4)
    (huorth : ∀ i j, Edge i j → inner ℂ (u i) (u j) = 0)
    (I : Fin (2*N-4) → H → H) (hIinv : ∀ q, Involutive (I q))
    (hIfix : ∀ q i, I q i ≠ i)
    (hIcover : ∀ i j, i ≠ j → Edge i j ∨ ∃ q, I q i = j) :
    HasUPB (Fin (4*N)) (4*N-2*r-4) (2*r) := by
  apply from_half_rows r N hr hN hcard u hu0 huspan I hIinv hIfix
  intro i j hij
  exact (hIcover i j hij).imp_left (huorth i j)

end P14AbstractHalfUPB
end


/- Source: grouping_audit/PrismHalfTransport.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Label transport for the odd-half-order construction.
Positive `q` is required because `ZMod 0` is infinite. In the application
`N=3+2*q` and `r+2≤N`, the odd case always has `q≥1`. -/

noncomputable section
open P14UPBAssembly P14EvenHalfUPB Function

namespace P14PrismHalfTransport

abbrev Half (q : ℕ) := Fin 6 ⊕ ZMod (4*q)

def extEquiv (q : ℕ) (hq : 0 < q) : ZMod (4*q) ≃ Fin q × Fin 4 := by
  let : NeZero (4*q) := ⟨by omega⟩
  exact (finZEquiv (4*q)).symm.trans
    (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin 4) (Fin q)))

lemma extEquiv_first (q : ℕ) (hq : 0 < q) (x : ZMod (4*q)) :
    (extEquiv q hq x).1.val = x.val % q := rfl

def halfEquiv (q : ℕ) (hq : 0 < q) : Half q ≃ P14PrismCliqueRows.HalfVertices q :=
  Equiv.sumCongr (Equiv.refl _) (extEquiv q hq)

lemma half_card (q : ℕ) [NeZero (4*q)] : Fintype.card (Half q) = 6+4*q := by
  simp [Half, ZMod.card]

def Edge {q : ℕ} : Half q → Half q → Prop
  | .inl i, .inl j => P14PrismCliqueRows.PrismAdj i j
  | .inr i, .inr j => i ≠ j ∧ i.val % q = j.val % q
  | _, _ => False

lemma residue_eq_of_difference_multiple (q : ℕ) (hq : 0 < q)
    (x y a : ZMod (4*q)) (h : y-x = (q : ZMod (4*q))*a) :
    x.val % q = y.val % q := by
  let : NeZero (4*q) := ⟨by omega⟩
  have he : ((y.val : ℕ) : ZMod (4*q)) = (x.val+q*a.val : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    linear_combination h
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
  have hm' := hm.of_dvd (show q ∣ 4*q by exact dvd_mul_left q 4)
  simpa [Nat.ModEq, Nat.add_mod] using hm'.symm

theorem rows (q : ℕ) (hq : 0 < q) [NeZero (4*q)] :
    ∃ u : Half q → Space 4,
      (∀ i, u i ≠ 0) ∧ SpansEvery u 4 ∧
      (∀ i j, Edge i j → inner ℂ (u i) (u j) = 0) := by
  classical
  obtain ⟨v,hv0,hprism,hclique,_,hvspan⟩ := P14PrismCliqueRows.half_rows q
  let e := halfEquiv q hq
  let u : Half q → Space 4 := v ∘ e
  refine ⟨u,fun i => hv0 (e i),spansEvery_comp _ hvspan e e.injective, ?_⟩
  intro i j hEdge
  cases i with
  | inl i =>
    cases j with
    | inl j => exact (hprism i j).mpr hEdge
    | inr j => exact False.elim hEdge
  | inr i =>
    cases j with
    | inl j => exact False.elim hEdge
    | inr j =>
      rcases hEdge with ⟨hne,hmod⟩
      have hf : (extEquiv q hq i).1 = (extEquiv q hq j).1 := by
        apply Fin.ext
        simpa only [extEquiv_first] using hmod
      have hs : (extEquiv q hq i).2 ≠ (extEquiv q hq j).2 := by
        intro he
        exact hne ((extEquiv q hq).injective (Prod.ext hf he))
      change inner ℂ (v (.inr ((extEquiv q hq i).1, (extEquiv q hq i).2)))
        (v (.inr ((extEquiv q hq j).1, (extEquiv q hq j).2))) = 0
      rw [hf]
      exact hclique _ _ _ hs

/-- Same rows, with clique edges expressed as multiples of `q` in the cyclic group. -/
theorem rows_cosets (q : ℕ) (hq : 0 < q) [NeZero (4*q)] :
    ∃ u : Half q → Space 4,
      (∀ i, u i ≠ 0) ∧ SpansEvery u 4 ∧
      (∀ i j, P14PrismCliqueRows.PrismAdj i j →
        inner ℂ (u (.inl i)) (u (.inl j)) = 0) ∧
      (∀ i j : ZMod (4*q), i ≠ j →
        (∃ a : ZMod (4*q), j-i = (q : ZMod (4*q))*a) →
        inner ℂ (u (.inr i)) (u (.inr j)) = 0) := by
  obtain ⟨u,hu0,husp,huorth⟩ := rows q hq
  refine ⟨u,hu0,husp,fun i j h => huorth _ _ h, ?_⟩
  intro i j hij hcoset
  obtain ⟨a,ha⟩ := hcoset
  exact huorth _ _ ⟨hij,residue_eq_of_difference_multiple q hq i j a ha⟩

end P14PrismHalfTransport
end


/- Source: grouping_audit/PrismFiniteFactors.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Exact finite complement factors for the standalone prism and prism+K4.
All certificate checks below reduce in Lean's kernel. -/

namespace P14PrismFiniteFactors

open P14PrismCliqueRows

def factors0 : Fin 2 → Fin 6 → Fin 6 := ![
  ![4,5,3,2,0,1],
  ![5,3,4,1,2,0]]

theorem factors0_invol : ∀ t i, factors0 t (factors0 t i) = i := by decide +kernel
theorem factors0_ne : ∀ t i, factors0 t i ≠ i := by decide +kernel
theorem factors0_cover : ∀ i j : Fin 6, i ≠ j →
    PrismAdj i j ∨ ∃ t, factors0 t i = j := by decide +kernel

abbrev Half1 := Fin 6 ⊕ ZMod 4

def encode1 : Half1 → Fin 10
  | .inl i => ⟨i.val, by omega⟩
  | .inr i => ⟨6+i.val, by have := ZMod.val_lt i; omega⟩

def decode1 (i : Fin 10) : Half1 :=
  if h : i.val < 6 then .inl ⟨i.val,h⟩ else .inr ((i.val-6 : ℕ) : ZMod 4)

/-- Each row contains one consecutive edge of the prism-complement cycle
`0,4,2,3,1,5`, and the four remaining vertices are paired with the K4. -/
def partner1 : Fin 6 → Fin 10 → Fin 10 := ![
  ![4,8,6,7,0,9,2,3,1,5],
  ![9,7,4,6,2,8,3,1,5,0],
  ![8,6,3,2,9,7,1,5,0,4],
  ![7,3,9,1,8,6,5,0,4,2],
  ![6,5,8,9,7,1,0,4,2,3],
  ![5,9,7,8,6,0,4,2,3,1]]

def factors1 (t : Fin 6) (i : Half1) : Half1 := decode1 (partner1 t (encode1 i))

def Edge1 : Half1 → Half1 → Prop
  | .inl i, .inl j => PrismAdj i j
  | .inr i, .inr j => i ≠ j
  | _, _ => False

instance (i j : Half1) : Decidable (Edge1 i j) := by
  cases i <;> cases j <;> unfold Edge1 <;> infer_instance

theorem factors1_invol : ∀ t i, factors1 t (factors1 t i) = i := by decide +kernel
theorem factors1_ne : ∀ t i, factors1 t i ≠ i := by decide +kernel
theorem factors1_cover : ∀ i j : Half1, i ≠ j →
    Edge1 i j ∨ ∃ t, factors1 t i = j := by decide +kernel

theorem control0 : ∃ F : Fin 2 → Fin 6 → Fin 6,
    (∀ t, Function.Involutive (F t)) ∧ (∀ t i, F t i ≠ i) ∧
    (∀ i j, i ≠ j → PrismAdj i j ∨ ∃ t, F t i = j) :=
  ⟨factors0,factors0_invol,factors0_ne,factors0_cover⟩

theorem control1 : ∃ F : Fin 6 → Half1 → Half1,
    (∀ t, Function.Involutive (F t)) ∧ (∀ t i, F t i ≠ i) ∧
    (∀ i j, i ≠ j → Edge1 i j ∨ ∃ t, F t i = j) :=
  ⟨factors1,factors1_invol,factors1_ne,factors1_cover⟩

lemma edge1_transport (i j : Half1) (h : Edge1 i j) :
    P14PrismHalfTransport.Edge (q := 1) i j := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact h
    | inr j => exact False.elim h
  | inr i =>
    cases j with
    | inl j => exact False.elim h
    | inr j => exact ⟨h,by omega⟩

theorem control1_transport : ∃ F : Fin 6 → Half1 → Half1,
    (∀ t, Function.Involutive (F t)) ∧ (∀ t i, F t i ≠ i) ∧
    (∀ i j, i ≠ j → P14PrismHalfTransport.Edge (q := 1) i j ∨ ∃ t, F t i = j) := by
  refine ⟨factors1,factors1_invol,factors1_ne,?_⟩
  intro i j hij
  exact (factors1_cover i j hij).imp_left (edge1_transport i j)

end P14PrismFiniteFactors


/- Source: literature/ReflectionStarter.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section

namespace P14ReflectionStarter

abbrev Ext (q : ℕ) := ZMod (4 * q)

def delta {q : ℕ} (x : Ext q) : Ext q :=
  if x.val < 2 * q then 2 * (q : Ext q) - 1 - 2 * x
  else 6 * (q : Ext q) - 2 - 2 * x

def reflect {q : ℕ} (x : Ext q) : Ext q := x + delta x

lemma half_cancel {q : ℕ} (hq : 0 < q) (x y : Ext q)
    (hhalf : x.val < 2 * q ↔ y.val < 2 * q) (he : 2 * x = 2 * y) : x = y := by
  have : NeZero (4 * q) := ⟨by omega⟩
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hc : ((2 * x.val : ℕ) : Ext q) = (2 * y.val : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using he
  have hm : 2 * x.val ≡ 2 * y.val [MOD 2 * (2 * q)] := by
    simpa only [show 2 * (2 * q) = 4 * q by omega] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
  have hm' := Nat.ModEq.mul_left_cancel' (by decide : 2 ≠ 0) hm
  have hv : x.val = y.val := by
    by_cases hxl : x.val < 2 * q
    · exact hm'.eq_of_lt_of_lt hxl (hhalf.mp hxl)
    · have hyl : ¬ y.val < 2 * q := fun h => hxl (hhalf.mpr h)
      have hs := Nat.ModEq.sub (by omega : 2 * q ≤ x.val)
        (by omega : 2 * q ≤ y.val) hm' (Nat.ModEq.refl (2 * q))
      have heq := hs.eq_of_lt_of_lt (by omega) (by omega)
      omega
  exact ZMod.val_injective _ hv

lemma cross_half_ne {q : ℕ} (_hq : 0 < q) (x y : Ext q)
    (hx : x.val < 2 * q) (hy : ¬ y.val < 2 * q) : delta x ≠ delta y := by
  intro h
  have h2 := congrArg (ZMod.castHom (by omega : 2 ∣ 4 * q) (ZMod 2)) h
  simp only [delta, if_pos hx, if_neg hy, map_sub, map_mul, map_natCast] at h2
  have hcast2 : (ZMod.cast (2 : Ext q) : ZMod 2) = 0 := by
    change (ZMod.cast ((2 : ℕ) : Ext q) : ZMod 2) = 0
    rw [ZMod.cast_natCast (by omega : 2 ∣ 4 * q)]
    decide
  have hcast6 : (ZMod.cast (6 : Ext q) : ZMod 2) = 0 := by
    change (ZMod.cast ((6 : ℕ) : Ext q) : ZMod 2) = 0
    rw [ZMod.cast_natCast (by omega : 2 ∣ 4 * q)]
    decide
  norm_num [hcast2, hcast6, ZMod.cast_one (by omega : 2 ∣ 4 * q)] at h2

theorem delta_injective {q : ℕ} (hq : 0 < q) : Function.Injective (delta (q := q)) := by
  intro x y he
  by_cases hx : x.val < 2 * q <;> by_cases hy : y.val < 2 * q
  · apply half_cancel hq x y (by simp [hx, hy])
    simp only [delta, if_pos hx, if_pos hy] at he
    linear_combination -he
  · exact False.elim (cross_half_ne hq x y hx hy he)
  · exact False.elim (cross_half_ne hq y x hy hx he.symm)
  · apply half_cancel hq x y (by simp [hx, hy])
    simp only [delta, if_neg hx, if_neg hy] at he
    linear_combination -he

theorem delta_bijective {q : ℕ} (hq : 0 < q) : Function.Bijective (delta (q := q)) := by
  have : NeZero (4 * q) := ⟨by omega⟩
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨delta_injective hq, rfl⟩

lemma reflect_eq_lower {q : ℕ} (hq : 0 < q) (x : Ext q) (hx : x.val < 2 * q) :
    reflect x = ((2 * q - 1 - x.val : ℕ) : Ext q) := by
  have : NeZero (4 * q) := ⟨by omega⟩
  rw [Nat.cast_sub (by omega : x.val ≤ 2 * q - 1),
    Nat.cast_sub (by omega : 1 ≤ 2 * q)]
  simp only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val, reflect, delta, if_pos hx]
  ring

lemma reflect_eq_upper {q : ℕ} (hq : 0 < q) (x : Ext q) (hx : ¬x.val < 2 * q) :
    reflect x = ((6 * q - 2 - x.val : ℕ) : Ext q) := by
  have : NeZero (4 * q) := ⟨by omega⟩
  have hxb := ZMod.val_lt x
  rw [Nat.cast_sub (by omega : x.val ≤ 6 * q - 2),
    Nat.cast_sub (by omega : 2 ≤ 6 * q)]
  simp only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val, reflect, delta, if_neg hx]
  ring

lemma reflect_half {q : ℕ} (hq : 0 < q) (x : Ext q) (hlast : x.val ≠ 4 * q - 1) :
    (reflect x).val < 2 * q ↔ x.val < 2 * q := by
  have : NeZero (4 * q) := ⟨by omega⟩
  have hxb := ZMod.val_lt x
  by_cases hx : x.val < 2 * q
  · rw [reflect_eq_lower hq x hx, ZMod.val_cast_of_lt (by omega)]
    omega
  · rw [reflect_eq_upper hq x hx, ZMod.val_cast_of_lt (by omega)]
    omega

lemma reflect_invol {q : ℕ} (hq : 0 < q) (x : Ext q) (hlast : x.val ≠ 4 * q - 1) :
    reflect (reflect x) = x := by
  have hh := reflect_half hq x hlast
  by_cases hx : x.val < 2 * q
  · have hy := hh.mpr hx
    change reflect x + delta (reflect x) = x
    rw [delta, if_pos hy, reflect, delta, if_pos hx]
    ring
  · have hy : ¬ (reflect x).val < 2 * q := fun h => hx (hh.mp h)
    change reflect x + delta (reflect x) = x
    rw [delta, if_neg hy, reflect, delta, if_neg hx]
    ring

lemma delta_reflect {q : ℕ} (hq : 0 < q) (x : Ext q) (hlast : x.val ≠ 4 * q - 1) :
    delta (reflect x) = -delta x := by
  have h := reflect_invol hq x hlast
  unfold reflect at h
  change delta (x + delta x) = -delta x
  linear_combination h

lemma four_q_zero (q : ℕ) : (4 : Ext q) * q = 0 := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZMod.natCast_self (4 * q)

def badValue (q : ℕ) : Fin 6 → Ext q := ![0, 1, -1, q, -q, 2 * q]
def badNat (q : ℕ) : Fin 6 → ℕ := ![0, 1, 4 * q - 1, q, 3 * q, 2 * q]

lemma badValue_eq_nat {q : ℕ} (hq : 2 ≤ q) (i : Fin 6) :
    badValue q i = (badNat q i : Ext q) := by
  have hz := four_q_zero q
  fin_cases i <;> norm_num [badValue, badNat]
  · rw [Nat.cast_sub (by omega : 1 ≤ 4 * q)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    linear_combination -hz
  · linear_combination -hz

lemma badNat_lt {q : ℕ} (hq : 2 ≤ q) (i : Fin 6) : badNat q i < 4 * q := by
  fin_cases i <;> norm_num [badNat] <;> omega

lemma badNat_injective {q : ℕ} (hq : 2 ≤ q) : Function.Injective (badNat q) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals norm_num [badNat] at h
  all_goals first | rfl | omega

lemma badValue_injective {q : ℕ} (hq : 2 ≤ q) : Function.Injective (badValue q) := by
  intro i j h
  rw [badValue_eq_nat hq, badValue_eq_nat hq] at h
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  exact badNat_injective hq (he.eq_of_lt_of_lt (badNat_lt hq i) (badNat_lt hq j))

lemma badValue_neg {q : ℕ} (i : Fin 6) : ∃ j : Fin 6, -badValue q i = badValue q j := by
  have hz := four_q_zero q
  fin_cases i
  · exact ⟨0, by simp [badValue]⟩
  · exact ⟨2, rfl⟩
  · exact ⟨1, by simp [badValue]⟩
  · exact ⟨4, rfl⟩
  · exact ⟨3, by simp [badValue]⟩
  · refine ⟨5, ?_⟩
    change -(2 * (q : Ext q)) = 2 * q
    linear_combination -hz

def Good {q : ℕ} (x : Ext q) : Prop := ∀ i : Fin 6, delta x ≠ badValue q i

lemma delta_last {q : ℕ} (hq : 0 < q) (x : Ext q) (hx : x.val = 4 * q - 1) :
    delta x = 2 * q := by
  have : NeZero (4 * q) := ⟨by omega⟩
  have hz := four_q_zero q
  have he : x = -1 := by
    rw [← ZMod.natCast_zmod_val x, hx, Nat.cast_sub (by omega : 1 ≤ 4 * q)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hz, zero_sub]
  rw [delta, if_neg (by omega : ¬ x.val < 2 * q), he]
  linear_combination hz

lemma good_ne_last {q : ℕ} (hq : 0 < q) {x : Ext q} (hx : Good x) :
    x.val ≠ 4 * q - 1 := by
  intro h
  exact hx 5 (delta_last hq x h)

lemma reflect_good {q : ℕ} (hq : 0 < q) {x : Ext q} (hx : Good x) : Good (reflect x) := by
  intro i hi
  obtain ⟨j, hj⟩ := badValue_neg (q := q) i
  apply hx j
  rw [delta_reflect hq x (good_ne_last hq hx)] at hi
  rw [← hj, ← hi, neg_neg]

def hole {q : ℕ} (hq : 2 ≤ q) (i : Fin 6) : Ext q :=
  (Equiv.ofBijective delta (delta_bijective (by omega : 0 < q))).symm (badValue q i)

lemma delta_hole {q : ℕ} (hq : 2 ≤ q) (i : Fin 6) :
    delta (hole hq i) = badValue q i :=
  (Equiv.ofBijective delta (delta_bijective (by omega : 0 < q))).apply_symm_apply _

lemma hole_injective {q : ℕ} (hq : 2 ≤ q) : Function.Injective (hole hq) := by
  intro i j h
  apply badValue_injective hq
  rw [← delta_hole hq i, ← delta_hole hq j, h]

lemma not_good_iff_hole {q : ℕ} (hq : 2 ≤ q) (x : Ext q) :
    ¬ Good x ↔ ∃ i : Fin 6, hole hq i = x := by
  classical
  simp only [Good, not_forall, not_not]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, delta_injective (by omega : 0 < q) ((delta_hole hq i).trans hi.symm)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, hi ▸ delta_hole hq i⟩

end P14ReflectionStarter
end


/- Source: literature/PrismFactors.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
open P14ReflectionStarter
namespace P14PrismFactors

abbrev V (q : ℕ) := Fin 6 ⊕ Ext q

def badIndex {q : ℕ} (hq : 2 ≤ q) (x : Ext q) (hx : ¬ Good x) : Fin 6 :=
  ((not_good_iff_hole hq x).mp hx).choose

lemma hole_badIndex {q : ℕ} (hq : 2 ≤ q) (x : Ext q) (hx : ¬ Good x) :
    hole hq (badIndex hq x hx) = x := ((not_good_iff_hole hq x).mp hx).choose_spec

lemma hole_not_good {q : ℕ} (hq : 2 ≤ q) (i : Fin 6) : ¬ Good (hole hq i) := by
  exact (not_good_iff_hole hq _).mpr ⟨i, rfl⟩

lemma badIndex_hole {q : ℕ} (hq : 2 ≤ q) (i : Fin 6) (h : ¬ Good (hole hq i)) :
    badIndex hq (hole hq i) h = i := hole_injective hq (hole_badIndex hq _ h)

def base {q : ℕ} (hq : 2 ≤ q) : V q → V q := by
  classical
  exact Sum.elim (fun i => .inr (hole hq i))
    (fun x => if h : Good x then .inr (reflect x) else .inl (badIndex hq x h))

lemma base_invol {q : ℕ} (hq : 2 ≤ q) : Function.Involutive (base hq) := by
  classical
  intro v
  rcases v with i | x
  · simp only [base, Sum.elim_inl, Sum.elim_inr, dif_neg (hole_not_good hq i),
      badIndex_hole]
  · by_cases h : Good x
    · simp only [base, Sum.elim_inr, dif_pos h, dif_pos (reflect_good (by omega) h),
        reflect_invol (by omega) x (good_ne_last (by omega) h)]
    · simp only [base, Sum.elim_inr, dif_neg h, Sum.elim_inl, hole_badIndex]

lemma base_ne {q : ℕ} (hq : 2 ≤ q) (v : V q) : base hq v ≠ v := by
  classical
  rcases v with i | x
  · simp [base]
  · by_cases h : Good x
    · simp only [base, Sum.elim_inr, dif_pos h, ne_eq, Sum.inr.injEq]
      intro he
      apply h 0
      change delta x = 0
      change x + delta x = x at he
      exact add_left_cancel (he.trans (add_zero x).symm)
    · simp [base, h]

def shift {q : ℕ} (t : Ext q) : V q ≃ V q :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.addRight t)

def mainFactor {q : ℕ} (hq : 2 ≤ q) (t : Ext q) (v : V q) : V q :=
  shift t (base hq ((shift t).symm v))

lemma mainFactor_invol {q : ℕ} (hq : 2 ≤ q) (t : Ext q) :
    Function.Involutive (mainFactor hq t) := by
  intro v
  simp only [mainFactor, Equiv.symm_apply_apply]
  rw [base_invol hq]
  exact (shift t).apply_symm_apply v

lemma mainFactor_ne {q : ℕ} (hq : 2 ≤ q) (t : Ext q) (v : V q) :
    mainFactor hq t v ≠ v := by
  intro h
  apply base_ne hq ((shift t).symm v)
  have he := congrArg (shift t).symm h
  simpa only [mainFactor, Equiv.symm_apply_apply] using he

lemma mainFactor_cross {q : ℕ} (hq : 2 ≤ q) (i : Fin 6) (x : Ext q) :
    mainFactor hq (x - hole hq i) (.inl i) = .inr x := by
  simp [mainFactor, shift, base]

lemma mainFactor_external {q : ℕ} (hq : 2 ≤ q) (x y : Ext q)
    (h : ∀ i : Fin 6, y - x ≠ badValue q i) :
    ∃ t : Ext q, mainFactor hq t (.inr x) = .inr y := by
  classical
  obtain ⟨a, ha⟩ := (delta_bijective (by omega : 0 < q)).surjective (y - x)
  have hag : Good a := fun i hi => h i (ha.symm.trans hi)
  refine ⟨x - a, ?_⟩
  simp only [mainFactor, shift, Equiv.sumCongr_symm, Equiv.refl_symm,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.addRight_symm_apply]
  have hxa : x + -(x - a) = a := by ring
  rw [hxa]
  simp only [base, Sum.elim_inr, dif_pos hag, Sum.map_inr,
    Sum.inr.injEq]
  change reflect a + (x - a) = y
  rw [reflect, ha]
  ring

end P14PrismFactors
end


/- Source: literature/CycleFactors.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
open P14ReflectionStarter
namespace P14CycleFactors

def parity {q : ℕ} : Ext q →+* ZMod 2 := ZMod.castHom (by omega : 2 ∣ 4 * q) _

lemma mod2_sub_one {a b : ZMod 2} (h : a ≠ b) : a - 1 = b := by
  revert a b
  decide +kernel

lemma mod2_add_one_ne (a : ZMod 2) : a + 1 ≠ a := by
  revert a
  decide +kernel

lemma one_ne_zero_ext {q : ℕ} (hq : 0 < q) : (1 : Ext q) ≠ 0 := by
  intro h
  have hd : 4 * q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 (4 * q)).mp (by simpa using h)
  have := Nat.le_of_dvd (by omega : 0 < 1) hd
  omega

def cycle {q : ℕ} (s : ZMod 2) (x : Ext q) : Ext q :=
  if parity x = s then x + 1 else x - 1

lemma cycle_invol {q : ℕ} (s : ZMod 2) : Function.Involutive (cycle (q := q) s) := by
  intro x
  by_cases hx : parity x = s
  · have hp : parity (x + 1) ≠ s := by
      rw [map_add, map_one, hx]
      exact mod2_add_one_ne s
    simp only [cycle, if_pos hx, if_neg hp]
    ring
  · have hp : parity (x - 1) = s := by
      rw [map_sub, map_one]
      exact mod2_sub_one hx
    simp only [cycle, if_neg hx, if_pos hp]
    ring

lemma cycle_ne {q : ℕ} (hq : 0 < q) (s : ZMod 2) (x : Ext q) : cycle s x ≠ x := by
  intro h
  apply one_ne_zero_ext hq
  by_cases hx : parity x = s
  · simp only [cycle, if_pos hx] at h
    exact add_left_cancel (h.trans (add_zero x).symm)
  · simp only [cycle, if_neg hx] at h
    linear_combination -h

lemma cycle_plus {q : ℕ} (x : Ext q) : cycle (parity x) x = x + 1 := by simp [cycle]
lemma cycle_minus {q : ℕ} (x : Ext q) : cycle (parity x + 1) x = x - 1 := by
  simp only [cycle, if_neg (Ne.symm (mod2_add_one_ne _))]

def prismCycle : Fin 2 → Fin 6 → Fin 6 := ![![4, 5, 3, 2, 0, 1], ![5, 3, 4, 1, 2, 0]]

def PrismAdj (i j : Fin 6) : Prop :=
  i ≠ j ∧ (i.val / 3 = j.val / 3 ∨ i.val % 3 = j.val % 3)
instance (i j : Fin 6) : Decidable (PrismAdj i j) := inferInstanceAs (Decidable (_ ∧ _))

lemma prismCycle_invol : ∀ s : Fin 2, Function.Involutive (prismCycle s) := by
  change ∀ s i, prismCycle s (prismCycle s i) = i
  decide +kernel
lemma prismCycle_ne : ∀ s i, prismCycle s i ≠ i := by decide +kernel
lemma prismCycle_cover : ∀ i j, i ≠ j → PrismAdj i j ∨ ∃ s, prismCycle s i = j := by decide +kernel

def special {q : ℕ} (s : Fin 2) : Fin 6 ⊕ Ext q → Fin 6 ⊕ Ext q :=
  Sum.map (prismCycle s) (cycle s.val)

lemma special_invol {q : ℕ} (s : Fin 2) : Function.Involutive (special (q := q) s) := by
  rintro (i | x)
  · exact congrArg Sum.inl (prismCycle_invol s i)
  · exact congrArg Sum.inr (cycle_invol (s.val : ZMod 2) x)

lemma special_ne {q : ℕ} (hq : 0 < q) (s : Fin 2) (v : Fin 6 ⊕ Ext q) : special s v ≠ v := by
  rcases v with i | x
  · exact fun h => prismCycle_ne s i (Sum.inl.inj h)
  · exact fun h => cycle_ne hq _ x (Sum.inr.inj h)

lemma special_plus {q : ℕ} (x : Ext q) :
    ∃ s : Fin 2, special s (.inr x : Fin 6 ⊕ Ext q) = .inr (x + 1) := by
  refine ⟨⟨(parity x).val, ZMod.val_lt _⟩, ?_⟩
  change Sum.inr (cycle ((parity x).val : ZMod 2) x) = _
  rw [ZMod.natCast_zmod_val, cycle_plus]

lemma special_minus {q : ℕ} (x : Ext q) :
    ∃ s : Fin 2, special s (.inr x : Fin 6 ⊕ Ext q) = .inr (x - 1) := by
  refine ⟨⟨(parity x + 1).val, ZMod.val_lt _⟩, ?_⟩
  change Sum.inr (cycle ((parity x + 1).val : ZMod 2) x) = _
  rw [ZMod.natCast_zmod_val, cycle_minus]

end P14CycleFactors
end


/- Source: literature/PrismComplement.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
open P14ReflectionStarter P14PrismFactors P14CycleFactors
namespace P14PrismComplement

def Edge {q : ℕ} : V q → V q → Prop
  | .inl i, .inl j => PrismAdj i j
  | .inr x, .inr y => x ≠ y ∧ ∃ a : Ext q, y - x = q * a
  | _, _ => False

def factor {q : ℕ} (hq : 2 ≤ q) (t : Ext q ⊕ Fin 2) : V q → V q :=
  Sum.elim (mainFactor hq) special t

lemma factor_invol {q : ℕ} (hq : 2 ≤ q) (t : Ext q ⊕ Fin 2) :
    Function.Involutive (factor hq t) := by
  rcases t with t | s
  · exact mainFactor_invol hq t
  · exact special_invol s

lemma factor_ne {q : ℕ} (hq : 2 ≤ q) (t : Ext q ⊕ Fin 2) (v : V q) :
    factor hq t v ≠ v := by
  rcases t with t | s
  · exact mainFactor_ne hq t v
  · exact special_ne (by omega) s v

lemma factor_cover {q : ℕ} (hq : 2 ≤ q) (v w : V q) (hvw : v ≠ w) :
    Edge v w ∨ ∃ t, factor hq t v = w := by
  classical
  rcases v with i | x <;> rcases w with j | y
  · have hij : i ≠ j := fun h => hvw (congrArg Sum.inl h)
    rcases prismCycle_cover i j hij with h | ⟨s, hs⟩
    · exact Or.inl h
    · exact Or.inr ⟨.inr s, congrArg Sum.inl hs⟩
  · exact Or.inr ⟨.inl (y - hole hq i), mainFactor_cross hq i y⟩
  · refine Or.inr ⟨.inl (x - hole hq j), ?_⟩
    have h := mainFactor_cross hq j x
    have hh := congrArg (mainFactor hq (x - hole hq j)) h
    rw [mainFactor_invol hq _ (.inl j)] at hh
    exact hh.symm
  · have hxy : x ≠ y := fun h => hvw (congrArg Sum.inr h)
    by_cases h : ∀ i : Fin 6, y - x ≠ badValue q i
    · obtain ⟨t, ht⟩ := mainFactor_external hq x y h
      exact Or.inr ⟨.inl t, ht⟩
    · push Not at h
      obtain ⟨i, hi⟩ := h
      fin_cases i
      · change y - x = 0 at hi
        exact False.elim (hxy (sub_eq_zero.mp hi).symm)
      · change y - x = 1 at hi
        have hy : y = x + 1 := by linear_combination hi
        obtain ⟨s, hs⟩ := special_plus x
        exact Or.inr ⟨.inr s, hy ▸ hs⟩
      · change y - x = -1 at hi
        have hy : y = x - 1 := by linear_combination hi
        obtain ⟨s, hs⟩ := special_minus x
        exact Or.inr ⟨.inr s, hy ▸ hs⟩
      · change y - x = q at hi
        exact Or.inl ⟨hxy, 1, by simpa using hi⟩
      · change y - x = -(q : Ext q) at hi
        exact Or.inl ⟨hxy, -1, by simpa using hi⟩
      · change y - x = 2 * (q : Ext q) at hi
        exact Or.inl ⟨hxy, 2, by simpa only [mul_comm] using hi⟩

/-- Explicit complement matching cover of a prism and `q` disjoint K4 blocks, for `q ≥ 2`.
The external blocks are the cosets of `q` in `ZMod (4*q)`. -/
theorem complement_factors {q : ℕ} (hq : 2 ≤ q) :
    ∃ F : Fin (4 * q + 2) → V q → V q,
      (∀ t, Function.Involutive (F t)) ∧
      (∀ t v, F t v ≠ v) ∧
      (∀ v w, v ≠ w → Edge v w ∨ ∃ t, F t v = w) := by
  classical
  have : NeZero (4 * q) := ⟨by omega⟩
  let e : Fin (4 * q + 2) ≃ Ext q ⊕ Fin 2 :=
    (Fintype.equivFinOfCardEq (by simp [Ext])).symm
  refine ⟨fun t => factor hq (e t), fun t => factor_invol hq (e t),
    fun t v => factor_ne hq (e t) v, ?_⟩
  intro v w hvw
  rcases factor_cover hq v w hvw with h | ⟨t, ht⟩
  · exact Or.inl h
  · exact Or.inr ⟨e.symm t, by simpa using ht⟩

end P14PrismComplement
end


/- Source: grouping_audit/AllHalfUPB.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Complete `(r,N)` parameter family: clique halves for even N, and
prism-plus-clique halves for odd N. -/

noncomputable section
open P14UPBAssembly P14EvenHalfUPB P14AbstractHalfUPB

namespace P14AllHalfUPB

theorem proof (r N : ℕ) (hr : 2 ≤ r) (hN : r+2 ≤ N) :
    HasUPB (Fin (4*N)) (4*N-2*r-4) (2*r) := by
  classical
  rcases Nat.even_or_odd N with heven | hodd
  · obtain ⟨c,hc⟩ := heven
    have hm : 4*N = 8*c := by omega
    rw [hm]
    exact P14EvenHalfUPB.proof c r hr (by omega)
  · obtain ⟨d,hd⟩ := hodd
    let q := d-1
    have hq : 0 < q := by dsimp [q]; omega
    have hNq : N = 3+2*q := by dsimp [q]; omega
    let : NeZero (4*q) := ⟨by omega⟩
    by_cases hq1 : q = 1
    · have hN5 : N = 5 := by omega
      rw [hN5]
      obtain ⟨u,hu0,husp,huorth⟩ := P14PrismHalfTransport.rows 1 (by decide)
      obtain ⟨F,hFinv,hFfix,hFcover⟩ := P14PrismFiniteFactors.control1_transport
      apply from_half_graph r 5 hr (by omega) (by decide) P14PrismHalfTransport.Edge
        u hu0 husp huorth F hFinv hFfix hFcover
    · have hq2 : 2 ≤ q := by omega
      obtain ⟨u,hu0,husp,huprism,huclique⟩ := P14PrismHalfTransport.rows_cosets q hq
      obtain ⟨F,hFinv,hFfix,hFcover⟩ := P14PrismComplement.complement_factors hq2
      have hcard : Fintype.card (P14PrismHalfTransport.Half q) = 2*N := by
        rw [P14PrismHalfTransport.half_card]
        omega
      have horth : ∀ i j, P14PrismComplement.Edge i j → inner ℂ (u i) (u j) = 0 := by
        intro i j h
        cases i with
        | inl i =>
          cases j with
          | inl j => exact huprism i j h
          | inr j => exact False.elim h
        | inr i =>
          cases j with
          | inl j => exact False.elim h
          | inr j => exact huclique i j h.1 h.2
      have hcount : 2*N-4 = 4*q+2 := by omega
      let I : Fin (2*N-4) → P14PrismHalfTransport.Half q → P14PrismHalfTransport.Half q :=
        fun t => F (Fin.cast hcount t)
      apply from_half_graph r N hr hN hcard P14PrismComplement.Edge
        u hu0 husp horth I
      · intro t
        exact hFinv (Fin.cast hcount t)
      · intro t i
        exact hFfix (Fin.cast hcount t) i
      · intro i j hij
        rcases hFcover i j hij with h | ⟨t,ht⟩
        · exact Or.inl h
        · exact Or.inr ⟨Fin.cast hcount.symm t,by simpa [I] using ht⟩

end P14AllHalfUPB
end


/- Source: cusp_assembly/Final56Local.lean. Reused authorship is retained in the source comments and artifact citations. -/
namespace P14Final56
open P14EvenHalfUPB

abbrev statement : Prop :=
  ∀ k t : ℕ, 4 ≤ k → Even k → k + 4 ≤ t → (t + k) % 4 = 0 →
    let M := t + k + 4
    ∃ z : Fin M → Fin t → EuclideanSpace ℂ (Fin 2),
    ∃ y : Fin M → EuclideanSpace ℂ (Fin 4),
    ∃ x : Fin M → EuclideanSpace ℂ (Fin k),
      (∀ i q, z i q ≠ 0) ∧ (∀ i, y i ≠ 0 ∧ x i ≠ 0) ∧
      (∀ i i', i ≠ i' →
        (∃ q, inner ℂ (z i q) (z i' q) = 0) ∨
        inner ℂ (y i) (y i') = 0 ∨
        inner ℂ (x i) (x i') = 0) ∧
      (∀ az : Fin t → EuclideanSpace ℂ (Fin 2),
        ∀ ay : EuclideanSpace ℂ (Fin 4),
        ∀ ax : EuclideanSpace ℂ (Fin k),
        (∀ q, az q ≠ 0) → ay ≠ 0 → ax ≠ 0 →
        ∃ i,
          (∀ q, inner ℂ (z i q) (az q) ≠ 0) ∧
          inner ℂ (y i) ay ≠ 0 ∧
          inner ℂ (x i) ax ≠ 0)


/-- Translate the complete (r,N) family to the exact canonical k,t variables. -/
theorem canonical_from_parameters
    (hfamily : ∀ r N : ℕ, 2 ≤ r → r + 2 ≤ N →
      HasUPB (Fin (4*N)) (4*N-2*r-4) (2*r)) : statement := by
  intro k t hk hke htk hmod
  obtain ⟨r, hr⟩ := hke
  have hk2 : k = 2*r := by omega
  have hr2 : 2 ≤ r := by omega
  have hm : (t+k+4) % 4 = 0 := by omega
  let N := (t+k+4)/4
  have hM : 4*N = t+k+4 := by dsimp [N]; omega
  have hN : r+2 ≤ N := by omega
  have ht : 4*N-2*r-4 = t := by omega
  have h := hfamily r N hr2 hN
  rw [ht, hM, ← hk2] at h
  exact h

end P14Final56

theorem proof : P14Final56.statement :=
  P14Final56.canonical_from_parameters P14AllHalfUPB.proof

end Submissions.EllipticUPBTwoFourEven.FamilyAssembly
