import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic

/-!
# CuspTriangularMinor

The explicit cusp evaluation grid has a nonsingular square minor in every
even rank at least eight.  This is the uniform nondegeneracy certificate for
the elliptic bipartite seed construction.
-/

namespace Statements.CuspTriangularMinor

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

def rowIndex (r N q : ℕ) : ℕ :=
  if q < r + 2 then q
  else if q - (r + 2) < 3 then 2 * N - r + 2 * (q - (r + 2))
  else 2 * N - r + (q - (r + 2)) + 2

def colIndex (r q : ℕ) : ℕ :=
  if q < r then 2 * r - 1 - q
  else if q = r then r - 4
  else if q = r + 1 then r - 2
  else if q - (r + 2) < 3 then r - 1 - 2 * (q - (r + 2))
  else r - (q - (r + 2)) - 3

noncomputable def cuspMinor (r N : ℕ) (h : NeZero (2 * N)) :
    Matrix (Fin (2 * r)) (Fin (2 * r)) ℂ := fun q s =>
  cuspProduct (r := r) h
    (rowIndex r N q.val : ZMod (2 * N))
    (colIndex r s.val : ZMod (2 * N))

abbrev statement : Prop :=
  ∀ (r N : ℕ), 4 ≤ r → r + 2 ≤ N → ∀ h : NeZero (2 * N),
    (cuspMinor r N h).det ≠ 0

theorem target : statement := sorry

end Statements.CuspTriangularMinor
