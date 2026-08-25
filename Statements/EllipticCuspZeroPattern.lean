import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic

/-!
# EllipticCuspZeroPattern

The Tate-cusp product has exactly the balanced translate/anti-translate zero
pattern used by the elliptic seed family.  This is the uniform incidence layer:
injectivity of the standard character of `ZMod (2*N)` rules out every
unintended zero.
-/

namespace Statements.EllipticCuspZeroPattern

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

abbrev statement : Prop :=
  ∀ (r N : ℕ) (h : NeZero (2 * N)) (i j : ZMod (2 * N)),
    cuspProduct (r := r) h i j = 0 ↔ CrossAdj (r := r) i j

theorem target : statement := sorry

end Statements.EllipticCuspZeroPattern
