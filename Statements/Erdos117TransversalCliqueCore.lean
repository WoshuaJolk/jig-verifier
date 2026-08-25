import Mathlib.LinearAlgebra.BilinearForm.Properties

namespace Statements.Erdos117TransversalCliqueCore

open scoped BigOperators

universe u v

/-- Linear-algebra construction in Lecomte, arXiv:2608.20507v1,
Lemma 5.4, source lines 390--400. The second conclusion says that the
constructed vectors occupy pairwise distinct additive `U`-cosets. -/
abbrev statement : Prop :=
  ∀ (K : Type u) (V : Type v) (_ : Field K) (_ : AddCommGroup V)
      (_ : Module K V) (d : ℕ) (B : LinearMap.BilinForm K V)
      (U : Submodule K V) (x y : Fin d → V),
    B.IsAlt →
    (∀ u ∈ U, ∀ v ∈ U, B u v = 0) →
    (∀ i, y i ∈ U) →
    (∀ i r, B (x i) (x r) = 0) →
    (∀ i h, B (x i) (y h) = if i = h then 1 else 0) →
    ∃ a : Option (Fin d) → V,
      a none = ∑ h, y h ∧
      (∀ i, a (some i) =
        x i + ∑ h ∈ Finset.univ.filter (fun h => h < i), y h) ∧
      (∀ q r, q ≠ r → B (a q) (a r) ≠ 0) ∧
      (∀ q r, q ≠ r → a q - a r ∉ U)

theorem target : statement := sorry

end Statements.Erdos117TransversalCliqueCore
