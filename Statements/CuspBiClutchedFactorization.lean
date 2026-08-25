import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic

/-!
# CuspBiClutchedFactorization

The scaled Tate-cusp kernel lies simultaneously in fixed clutched
Vandermonde spaces in each variable.
-/

namespace Statements.CuspBiClutchedFactorization

open scoped BigOperators

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

noncomputable def clutch (k : ℕ) (tau z : ℂ) : Fin k → ℂ := fun q =>
  if q.val = 0 then 1 + tau * z ^ k else z ^ q.val

abbrev statement : Prop :=
  ∀ (r N : ℕ), 1 ≤ r → ∀ h : NeZero (2 * N),
    ∃ (tauL tauR : ℂ)
      (L R : ZMod (2 * N) → Fin (2 * r) → ℂ),
      tauL ≠ 0 ∧ tauR ≠ 0 ∧
      ∀ i j : ZMod (2 * N),
        (ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
          ∑ q, L j q * clutch (2 * r) tauL (ZMod.stdAddChar i) q) ∧
        (ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
          ∑ q, R i q * clutch (2 * r) tauR (ZMod.stdAddChar j) q)

theorem target : statement := sorry

end Statements.CuspBiClutchedFactorization
