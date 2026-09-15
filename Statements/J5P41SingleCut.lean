import Init

namespace Statements.J5P41SingleCut

def Edge (k i j : Nat) : Prop := i < j ∧ j < k
def Cross (c i j : Nat) : Prop := i ≤ c ∧ c < j
instance (c i j : Nat) : Decidable (Cross c i j) :=
  inferInstanceAs (Decidable (i ≤ c ∧ c < j))
def Shift (a : Nat → Int) (c : Nat) (h : Int) (i : Nat) : Int :=
  a i - if c < i then h else 0
def Unique (a : Nat → Int) (k : Nat) : Prop :=
  ∀ i j l m, Edge k i j → Edge k l m → a j-a i=a m-a l → i=l ∧ j=m
def NoCollision (a : Nat → Int) (k c : Nat) (h : Int) : Prop :=
  ∀ i j l m, Edge k i j → Edge k l m → Cross c i j → ¬Cross c l m →
    a j-a i-h ≠ a m-a l


/-- Exact indexed integer cut-shift criterion, with positivity stated separately. -/
abbrev statement : Prop :=
  ∀ (a : Nat → Int) (k c : Nat) (h : Int),
    (Unique a k →
      (Unique (Shift a c h) k ↔ NoCollision a k c h)) ∧
    ((∀ i j, Edge k i j → 0 < a j - a i) →
      (∀ i j, Edge k i j → Cross c i j → h < a j - a i) →
      ∀ i j, Edge k i j → 0 < Shift a c h j - Shift a c h i)

end Statements.J5P41SingleCut
