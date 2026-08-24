import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic

namespace Statements.EllipticSeedK4N8Full

def CrossAdj (i j : Fin 8) : Prop :=
  j.val = i.val ∨
  j.val = (i.val + 2) % 8 ∨
  j.val = (9 - i.val) % 8 ∨
  j.val = (13 - i.val) % 8

def pair (u v : Fin 4 → ℂ) : ℂ := ∑ r, star (u r) * v r

abbrev statement : Prop :=
  ∃ point covector : Fin 8 → Fin 4 → ℂ,
    (∀ i, point i ≠ 0 ∧ covector i ≠ 0) ∧
    (∀ i j, pair (point i) (covector j) = 0 ↔ CrossAdj i j) ∧
    (∀ i j, i ≠ j → pair (point i) (point j) ≠ 0 ∧
      pair (covector i) (covector j) ≠ 0) ∧
    (∀ S : Finset (Fin 16), S.card + 1 ≤ 4 →
      LinearIndependent ℂ fun i : (S : Set (Fin 16)) =>
        Fin.append point covector i) ∧
    (∀ S : Finset (Fin 16), S.card = 5 →
      Submodule.span ℂ (Set.range fun i : (S : Set (Fin 16)) =>
        Fin.append point covector i) = ⊤)

theorem target : statement := sorry

end Statements.EllipticSeedK4N8Full
