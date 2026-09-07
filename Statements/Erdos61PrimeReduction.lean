import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos61PrimeReduction

open Filter SimpleGraph Real

def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) →
      G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

def HasErdosHajnalProperty {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

def IsModule {α : Type*} (H : SimpleGraph α) (S : Set α) : Prop :=
  ∀ x, x ∉ S → ∀ a, a ∈ S → ∀ b, b ∈ S → (H.Adj x a ↔ H.Adj x b)

/-- Prime means absence of nontrivial modules, including the degenerate small orders. -/
def IsPrime {α : Type*} [Fintype α] (H : SimpleGraph α) : Prop :=
  ∀ S : Finset α, 1 < S.card → S.card < Fintype.card α → ¬IsModule H (S : Set α)

universe u

abbrev statement : Prop :=
    (∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      HasErdosHajnalProperty H) ↔
    (∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      IsPrime H → HasErdosHajnalProperty H)

end Statements.Erdos61PrimeReduction
