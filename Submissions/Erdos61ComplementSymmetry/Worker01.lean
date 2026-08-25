import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Submissions.Erdos61ComplementSymmetry.Worker01

open Filter SimpleGraph Real

def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) →
      G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

def HasErdosHajnalProperty {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

private theorem complement_forward {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) :
    HasErdosHajnalProperty H → HasErdosHajnalProperty Hᶜ := by
  rintro ⟨c, hc, hbound⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound] with n hn
  intro G hfree
  have hfree_compl : ¬∃ g : α ↪ Fin n, H = Gᶜ.comap g := by
    rintro ⟨g, hg⟩
    apply hfree
    refine ⟨g, ?_⟩
    rw [hg]
    ext u v
    simp only [compl_adj, comap_adj]
    constructor
    · rintro ⟨huv, hnot⟩
      by_contra hAdj
      exact hnot ⟨fun hEq => huv (g.injective hEq), hAdj⟩
    · intro hadj
      refine ⟨fun huv => G.ne_of_adj hadj (congrArg g huv), ?_⟩
      rintro ⟨_, hnot⟩
      exact hnot hadj
  simpa [or_comm] using hn Gᶜ hfree_compl

theorem proof :
    ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      HasErdosHajnalProperty H ↔ HasErdosHajnalProperty Hᶜ := by
  intro α _ _ H
  constructor
  · exact complement_forward H
  · intro h
    simpa using complement_forward Hᶜ h

end Submissions.Erdos61ComplementSymmetry.Worker01
