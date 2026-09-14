import Init

namespace Statements.J4P16PathClosure

def DistinctFive {X : Type} (a b c d e : X) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
    c ≠ d ∧ c ≠ e ∧ d ≠ e

def DisjointEdges {X : Type} (a b c d : X) : Prop :=
  a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

def DegreeTwo {X : Type} (E : X → X → Prop) : Prop :=
  ∀ x a b c, E x a → E x b → E x c → a ≠ b → a ≠ c → b ≠ c → False

def MatchingTwo {X : Type} (E : X → X → Prop) : Prop :=
  ∀ a b c d e f, E a b → E c d → E e f →
    DisjointEdges a b c d → DisjointEdges a b e f → DisjointEdges c d e f → False


def statement : Prop :=
(∀ {X : Type} {E : X → X → Prop}
    (sym : ∀ {x y}, E x y → E y x) (loop : ∀ x, ¬ E x x)
    (degree : DegreeTwo E) (matching : MatchingTwo E)
    (a b c d e : X) (distinct : DistinctFive a b c d e)
    (hab : E a b) (hbc : E b c) (hcd : E c d) (hde : E d e)
    {u v : X} (huv : E u v),
(u = a ∧ (v = b ∨ v = e)) ∨
    (u = b ∧ (v = a ∨ v = c)) ∨
    (u = c ∧ (v = b ∨ v = d)) ∨
    (u = d ∧ (v = c ∨ v = e)) ∨
    (u = e ∧ (v = d ∨ v = a)))

end Statements.J4P16PathClosure
