import Mathlib.Data.ZMod.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

/-!
Canonical statement draft only. This is the standard interval-to-group
reduction, not a new asymptotic estimate. The IsSidon body below is copied
exactly from the canonical problem 41 root. Statements 11–14 do not state
this reduction; statement 13 assumes its group Sidon input. The proof
package reuses the existing local IntervalBridge.lean helpers.
-/
namespace Statements.Erdos30IntervalReduction

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

abbrev statement : Prop :=
  ∀ (N M : ℕ) (A : Finset ℕ),
    IsSidon A → A ⊆ Finset.Icc 1 N → 2 * N < M →
    (A.image (fun a : ℕ => (a : ZMod M))).card = A.card ∧
      (∀ a ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ b ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ c ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ d ∈ A.image (fun a : ℕ => (a : ZMod M)),
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c))

theorem target : statement := sorry

end Statements.Erdos30IntervalReduction
