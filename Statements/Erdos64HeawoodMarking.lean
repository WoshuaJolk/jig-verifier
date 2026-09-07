import Mathlib

namespace Statements.Erdos64HeawoodMarking

/-- The standard 14-cycle plus alternating length-five chords. -/
def adjacent (u v : Fin 14) : Bool :=
  decide ((u.val + 1) % 14 = v.val ∨ (v.val + 1) % 14 = u.val ∨
    (u.val + (if u.val % 2 = 0 then 5 else 9)) % 14 = v.val)

/-- Explicit short simple cycles, with cyclic order retained. -/
def cycles : List (List (Fin 14)) :=
  [[0, 1, 2, 3, 4, 5],
   [0, 1, 2, 3, 12, 13],
   [0, 1, 2, 7, 6, 5],
   [0, 1, 2, 7, 8, 13],
   [0, 1, 10, 9, 4, 5],
   [0, 1, 10, 9, 8, 13],
   [0, 1, 10, 11, 6, 5],
   [0, 1, 10, 11, 12, 13],
   [0, 13, 8, 7, 6, 5],
   [0, 13, 8, 9, 4, 5],
   [0, 13, 12, 3, 4, 5],
   [0, 13, 12, 11, 6, 5],
   [1, 2, 3, 4, 9, 10],
   [1, 2, 3, 12, 11, 10],
   [1, 2, 7, 6, 11, 10],
   [1, 2, 7, 8, 9, 10],
   [2, 3, 4, 9, 8, 7],
   [2, 3, 12, 11, 6, 7],
   [5, 4, 3, 2, 7, 6],
   [5, 4, 3, 12, 11, 6],
   [5, 4, 9, 8, 7, 6],
   [5, 4, 9, 10, 11, 6],
   [10, 9, 4, 3, 12, 11],
   [10, 9, 8, 7, 6, 11],
   [13, 8, 7, 2, 3, 12],
   [13, 8, 7, 6, 11, 12],
   [13, 8, 9, 4, 3, 12],
   [13, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 9, 8, 13],
   [0, 1, 2, 3, 12, 11, 6, 5],
   [0, 1, 2, 7, 6, 11, 12, 13],
   [0, 1, 2, 7, 8, 9, 4, 5],
   [0, 1, 10, 9, 4, 3, 12, 13],
   [0, 1, 10, 9, 8, 7, 6, 5],
   [0, 1, 10, 11, 6, 7, 8, 13],
   [0, 1, 10, 11, 12, 3, 4, 5],
   [0, 13, 8, 7, 2, 3, 4, 5],
   [0, 13, 8, 9, 10, 11, 6, 5],
   [0, 13, 12, 3, 2, 7, 6, 5],
   [0, 13, 12, 11, 10, 9, 4, 5],
   [1, 2, 3, 4, 5, 6, 11, 10],
   [1, 2, 3, 12, 13, 8, 9, 10],
   [1, 2, 7, 6, 5, 4, 9, 10],
   [1, 2, 7, 8, 13, 12, 11, 10],
   [2, 3, 4, 9, 10, 11, 6, 7],
   [2, 3, 12, 11, 10, 9, 8, 7],
   [3, 4, 9, 8, 7, 6, 11, 12],
   [13, 8, 7, 6, 5, 4, 3, 12],
   [13, 8, 9, 4, 5, 6, 11, 12]]

def validCycle (c : List (Fin 14)) : Bool :=
  decide c.Nodup && (c.zip (c.rotate 1)).all (fun e => adjacent e.1 e.2) &&
    (c.length == 6 || c.length == 8)

def markedCount (m : List Bool) (c : List (Fin 14)) : Nat :=
  (c.filter (fun v => m[v.val]!)).length

/-- A base cycle whose triangle-lift interval contains 8 or 16. -/
def favorable (m : List Bool) (c : List (Fin 14)) : Bool :=
  let r := markedCount m c
  (c.length + r ≤ 8 && 8 ≤ c.length + 2*r) ||
    (c.length + r ≤ 16 && 16 ≤ c.length + 2*r)

/-- All listed cycles are valid, and every 14-bit marking has a favorable one.
The graph-level triangle-expansion corollary is not part of this predicate. -/
def statement : Prop :=
  cycles.all validCycle = true ∧
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool,
      cycles.any (favorable [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13]) = true

end Statements.Erdos64HeawoodMarking
