import Mathlib.Data.Set.Card

namespace Statements.Erdos20MemberTransitive

def IsSunflower {α : Type} (family : Set (Set α)) : Prop :=
  ∃ kernel : Set α, family.Pairwise fun left right => left ∩ right = kernel

def SunflowerFree {α : Type} (r : ℕ) (family : Set (Set α)) : Prop :=
  ¬ ∃ subfamily ⊆ family, subfamily.ncard = r ∧ IsSunflower subfamily

/-- Transitivity on members under ambient permutations preserving the family. -/
def MemberTransitive {α : Type} (family : Set (Set α)) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, ∃ e : Equiv.Perm α,
    (fun S : Set α => e '' S) '' family = family ∧ e '' A = B

def MemberTransitiveBound (r B : ℕ) : Prop :=
  ∀ {α : Type} (w : ℕ) (family : Set (Set α)),
    0 < w → family.Finite →
    (∀ member ∈ family, member.ncard = w) →
    SunflowerFree r family → MemberTransitive family → family.ncard ≤ B ^ w

def UniformBound (r B : ℕ) : Prop :=
  ∀ {α : Type} (w : ℕ) (family : Set (Set α)),
    0 < w → family.Finite →
    (∀ member ∈ family, member.ncard = w) →
    SunflowerFree r family → family.ncard ≤ B ^ w

/-- Conditional reduction for every fixed petal count at least three.
This does not assert existence of a base satisfying the premise. -/
abbrev statement : Prop :=
  ∀ r B : ℕ, 3 ≤ r → MemberTransitiveBound r B → UniformBound r (B ^ 2)

end Statements.Erdos20MemberTransitive
