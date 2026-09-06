import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-
A numerical barrier to the modular orbit / dyadic-spanning inference proposed
in Duran-Ballester, Zenodo22019344, 'System increment arithmetic', part(a).
This statement concerns finite arithmetic spectra only. It neither gives a
graph counterexample to Erdos64 nor refutes all extra residual hypotheses of
that paper's full lemma. Its arbitrary parameterB excludes repair by any
fixed frequency threshold or fixed end trimming.
-/
namespace Statements.ErdosGyarfasOrbitSpanningBarrier

def InSpectrum (d y : ℕ) : Prop :=
  ∃ t ≤ 8 * d, ∃ r ≤ 12, y = 17 * (12 * d + t) + r

abbrev statement : Prop :=
  (2 ^ 8 % 17 = 1 ∧
    (∀ k ∈ Finset.Icc 1 7, 2 ^ k % 17 ≠ 1) ∧
    8 > 17 - 13 ∧ (∃ k : ℕ, 2 ^ k % 17 ≤ 12)) ∧
  ∀ B : ℕ, ∃ d k : ℕ,
    1 ≤ d ∧ B ≤ 8 * d ∧
    204 * d + 17 * B + 12 < 2 ^ k ∧
    2 ^ k + 17 * B + 12 < 340 * d + 12 ∧
    InSpectrum d (204 * d) ∧
    InSpectrum d (340 * d + 12) ∧
    (∀ j : ℕ, ¬ InSpectrum d (2 ^ j))

-- The open canonical target; submissions must not import this module.
theorem target : statement := sorry

end Statements.ErdosGyarfasOrbitSpanningBarrier
