import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos61Substitution

open Filter SimpleGraph Real

def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) →
      G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

def HasErdosHajnalProperty {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

abbrev Away {α : Type*} (v : α) := {a : α // a ≠ v}

variable {α δ : Type*}

def replacement (H₁ : SimpleGraph α) (H₂ : SimpleGraph δ) (v : α) :
    SimpleGraph (Away v ⊕ δ) where
  Adj
    | .inl u, .inl w => H₁.Adj u.val w.val
    | .inl u, .inr _ => H₁.Adj v u.val
    | .inr _, .inl u => H₁.Adj v u.val
    | .inr x, .inr y => H₂.Adj x y
  symm.symm
    | .inl _, .inl _ => H₁.adj_symm
    | .inl _, .inr _ => id
    | .inr _, .inl _ => id
    | .inr _, .inr _ => H₂.adj_symm
  loopless.irrefl
    | .inl _ => H₁.irrefl
    | .inr _ => H₂.irrefl

abbrev statement : Prop :=
  ∀ {α δ : Type*} [Fintype α] [Fintype δ] [DecidableEq α] [DecidableEq δ]
    (H₁ : SimpleGraph α) (H₂ : SimpleGraph δ) (v : α),
    HasErdosHajnalProperty H₁ → HasErdosHajnalProperty H₂ →
      HasErdosHajnalProperty (replacement H₁ H₂ v)

end Statements.Erdos61Substitution
