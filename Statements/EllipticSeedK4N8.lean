import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# EllipticSeedK4N8

Canonical exact statement for the first nodal elliptic seed.  The auxiliary
type `QI2` stores `a + b√2 + i(c + d√2)` using four integer coefficients;
`eval` maps it into `ℂ`.
-/

namespace Statements.EllipticSeedK4N8

structure QI2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq

noncomputable def QI2.eval (z : QI2) : ℂ :=
  z.a + z.b * (Real.sqrt 2 : ℂ) +
    (z.c + z.d * (Real.sqrt 2 : ℂ)) * Complex.I

def pointQ : Fin 8 → Fin 4 → QI2 := ![
  ![⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩],
  ![⟨4, 0, 0, 0⟩, ⟨0, 1, 0, 1⟩, ⟨0, 0, 2, 0⟩, ⟨0, -1, 0, 1⟩],
  ![⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩],
  ![⟨4, 0, 0, 0⟩, ⟨0, -1, 0, 1⟩, ⟨0, 0, -2, 0⟩, ⟨0, 1, 0, 1⟩],
  ![⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩],
  ![⟨4, 0, 0, 0⟩, ⟨0, -1, 0, -1⟩, ⟨0, 0, 2, 0⟩, ⟨0, 1, 0, -1⟩],
  ![⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩],
  ![⟨4, 0, 0, 0⟩, ⟨0, 1, 0, -1⟩, ⟨0, 0, -2, 0⟩, ⟨0, -1, 0, -1⟩]
]

def sectionQ : Fin 8 → Fin 4 → QI2 := ![
  ![⟨0, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, ⟨2, 0, 0, 0⟩, ⟨-1, 0, 1, 0⟩],
  ![⟨1, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩],
  ![⟨0, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, ⟨2, 0, 0, 0⟩, ⟨-1, 0, -1, 0⟩],
  ![⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩],
  ![⟨0, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, ⟨2, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩],
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩],
  ![⟨0, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, ⟨2, 0, 0, 0⟩, ⟨1, 0, 1, 0⟩],
  ![⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩]
]

noncomputable def point (i : Fin 8) : Fin 4 → ℂ := fun r => (pointQ i r).eval
noncomputable def covector (i : Fin 8) : Fin 4 → ℂ := fun r => (sectionQ i r).eval

def seedQ : Fin 16 → Fin 4 → QI2 := Fin.append pointQ sectionQ
noncomputable def seed (i : Fin 16) : Fin 4 → ℂ := fun r => (seedQ i r).eval

/-- The offsets `{0,2}` and anti-offsets `{1,5}` modulo eight. -/
def CrossAdj (i j : Fin 8) : Prop :=
  j.val = i.val ∨
  j.val = (i.val + 2) % 8 ∨
  j.val = (9 - i.val) % 8 ∨
  j.val = (13 - i.val) % 8

/-- Standard Hermitian pairing, conjugate-linear in the first argument. -/
def pair (u v : Fin 4 → ℂ) : ℂ := ∑ r, star (u r) * v r

def EveryThreeIndependent (v : Fin 16 → Fin 4 → ℂ) : Prop :=
  ∀ f : Fin 3 → Fin 16, Function.Injective f →
    LinearIndependent ℂ (fun i => v (f i))

def EveryFiveSpanning (v : Fin 16 → Fin 4 → ℂ) : Prop :=
  ∀ f : Fin 5 → Fin 16, Function.Injective f →
    Submodule.span ℂ (Set.range fun i => v (f i)) = ⊤

abbrev statement : Prop :=
  (∀ i j, pair (point i) (covector j) = 0 ↔ CrossAdj i j) ∧
  EveryThreeIndependent seed ∧
  EveryFiveSpanning seed

theorem target : statement := sorry

end Statements.EllipticSeedK4N8
