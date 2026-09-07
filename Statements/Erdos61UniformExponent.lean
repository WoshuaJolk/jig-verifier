import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos61UniformExponent

open Filter SimpleGraph Real

def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) →
      G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

def HasErdosHajnalProperty {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

abbrev statement : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
    HasErdosHajnalProperty H ↔
      ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n),
        (¬∃ g : α ↪ Fin n, H = G.comap g) →
          n < (max G.indepNum G.cliqueNum) ^ k

theorem target : statement := sorry

end Statements.Erdos61UniformExponent
