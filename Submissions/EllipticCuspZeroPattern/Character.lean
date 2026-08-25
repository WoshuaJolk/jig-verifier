import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic

namespace Submissions.EllipticCuspZeroPattern.Character

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

theorem proof :
  ∀ (r N : ℕ) (h : NeZero (2 * N)) (i j : ZMod (2 * N)),
      cuspProduct (r := r) h i j = 0 ↔ CrossAdj (r := r) i j := by
  intro r N h i j
  letI := h
  simp only [cuspProduct, CrossAdj, mul_eq_zero, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero]
  simp only [ZMod.injective_stdAddChar.eq_iff]

end Submissions.EllipticCuspZeroPattern.Character
