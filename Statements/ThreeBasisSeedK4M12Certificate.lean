import Mathlib

namespace Statements.ThreeBasisSeedK4M12Certificate

def vZ : Fin 12 → Fin 4 → ℤ := ![
  ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
  ![0, 1, 1, 1], ![1, 0, 1, -1], ![1, -3, 1, 2], ![3, 1, -2, 1],
  ![12, 4, -14, 7], ![-4, 12, -7, -14], ![7, -7, 0, -8], ![7, 7, 8, 0]
]

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def crossMatch (i j : Fin 12) : Prop :=
  (i.val = 0 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0) ∨
  (i.val = 1 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 1) ∨
  (i.val = 2 ∧ j.val = 10) ∨ (i.val = 10 ∧ j.val = 2) ∨
  (i.val = 3 ∧ j.val = 11) ∨ (i.val = 11 ∧ j.val = 3) ∨
  (i.val = 6 ∧ j.val = 8) ∨ (i.val = 8 ∧ j.val = 6) ∨
  (i.val = 7 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 7)

def edge (i j : Fin 12) : Prop :=
  i ≠ j ∧ (i.val / 4 = j.val / 4 ∨ crossMatch i j)

instance crossMatchDecidable (i j : Fin 12) : Decidable (crossMatch i j) := by
  unfold crossMatch
  infer_instance

instance edgeDecidable (i j : Fin 12) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel edge

def minor3 (x y z : Fin 4 → ℤ) (c0 c1 c2 : Fin 4) : ℤ :=
  x c0 * y c1 * z c2 - x c0 * y c2 * z c1
    - x c1 * y c0 * z c2 + x c1 * y c2 * z c0
    + x c2 * y c0 * z c1 - x c2 * y c1 * z c0

def det4Z (x y z t : Fin 4 → ℤ) : ℤ :=
  x 0 * y 1 * z 2 * t 3 - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3 + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2 - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3 + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3 - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2 + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3 - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3 + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1 - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2 + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2 - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1 + x 3 * y 2 * z 1 * t 0

abbrev statement : Prop :=
  (∀ i : Fin 12, ∃ r, vZ i r ≠ 0) ∧
  (∀ i j : Fin 12, dot4Z (vZ i) (vZ j) = 0 ↔ edge i j) ∧
  (∀ i, ((Finset.univ : Finset (Fin 12)).filter (edge i)).card = 4) ∧
  graph.Connected ∧
  (∀ i j k : Fin 12, i < j → j < k →
    minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0) ∧
  (∀ i j k l t : Fin 12, i < j → j < k → k < l → l < t →
    det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
    det4Z (vZ i) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
    det4Z (vZ i) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
    det4Z (vZ i) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
    det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0)

theorem target : statement := sorry

end Statements.ThreeBasisSeedK4M12Certificate
