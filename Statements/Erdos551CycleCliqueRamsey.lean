import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Lattice

namespace Statements.Erdos551CycleCliqueRamsey

def HasRedCycle {N : ℕ} (red : Fin N → Fin N → Prop) (k : ℕ) : Prop :=
  ∃ c : Fin k ↪ Fin N,
    ∀ i j : Fin k, j.val = (i.val + 1) % k → red (c i) (c j)

def HasBlueClique {N : ℕ} (red : Fin N → Fin N → Prop) (n : ℕ) : Prop :=
  ∃ c : Fin n ↪ Fin N,
    ∀ i j : Fin n, i ≠ j → ¬red (c i) (c j)

def ForcesCycleOrClique (N k n : ℕ) : Prop :=
  ∀ red : Fin N → Fin N → Prop, Symmetric red →
    HasRedCycle red k ∨ HasBlueClique red n

/-- The Erdős–Faudree–Rousseau–Schelp cycle-complete Ramsey conjecture. -/
abbrev statement : Prop :=
  ∀ k n : ℕ, 3 ≤ n → n ≤ k → (k, n) ≠ (3, 3) →
    IsLeast {N : ℕ | ForcesCycleOrClique N k n}
      ((k - 1) * (n - 1) + 1)

theorem target : statement := sorry

end Statements.Erdos551CycleCliqueRamsey
