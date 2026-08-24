import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic

namespace Statements.EllipticSeedK4N8Exists

def CrossAdj (i j : Fin 8) : Prop :=
  j.val = i.val ∨
  j.val = (i.val + 2) % 8 ∨
  j.val = (9 - i.val) % 8 ∨
  j.val = (13 - i.val) % 8

def pair (u v : Fin 4 → ℂ) : ℂ := ∑ r, star (u r) * v r

def EveryThreeIndependent (v : Fin 16 → Fin 4 → ℂ) : Prop :=
  ∀ f : Fin 3 → Fin 16, Function.Injective f →
    LinearIndependent ℂ (fun i => v (f i))

def EveryFiveSpanning (v : Fin 16 → Fin 4 → ℂ) : Prop :=
  ∀ f : Fin 5 → Fin 16, Function.Injective f →
    Submodule.span ℂ (Set.range fun i => v (f i)) = ⊤

abbrev statement : Prop :=
  ∃ point covector : Fin 8 → Fin 4 → ℂ,
    (∀ i j, pair (point i) (covector j) = 0 ↔ CrossAdj i j) ∧
    EveryThreeIndependent (Fin.append point covector) ∧
    EveryFiveSpanning (Fin.append point covector)

theorem target : statement := sorry

end Statements.EllipticSeedK4N8Exists
