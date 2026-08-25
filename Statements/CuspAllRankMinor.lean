import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic

/-!
# CuspAllRankMinor

The Tate-cusp evaluation kernel has a nonsingular inner-size square minor
in every even rank used by the elliptic seed construction.
-/

namespace Statements.CuspAllRankMinor

open scoped BigOperators

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

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

abbrev statement : Prop :=
  ∀ (r N : ℕ), 2 ≤ r → r + 2 ≤ N → ∀ h : NeZero (2 * N),
    ∃ row col : Fin (2 * r) → ℕ,
      (∀ q, row q < 2 * N ∧ col q < 2 * N) ∧
      (Matrix.of fun q s => cuspProduct (r := r) h
        (row q : ZMod (2 * N)) (col s : ZMod (2 * N))).det ≠ 0

theorem target : statement := sorry

end Statements.CuspAllRankMinor
