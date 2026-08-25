import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Order.OrderClosed

open Filter

/-!
# Erdős problem 1212

Is there a simple path to infinity through coprime lattice points whose
coordinates both exceed one and are not simultaneously prime?
-/

namespace Statements.Erdos1212CompositeVisiblePath

def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧
    (¬ p.1.Prime ∨ ¬ p.2.Prime)

def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
    (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

abbrev statement : Prop :=
  ∃ f : ℕ → ℕ × ℕ,
    Function.Injective f ∧
      (∀ n, Adj (f n) (f (n + 1))) ∧
        (∀ n, Valid (f n)) ∧
          Tendsto (fun n => (f n).1 + (f n).2) atTop atTop

theorem target : statement := sorry

end Statements.Erdos1212CompositeVisiblePath
