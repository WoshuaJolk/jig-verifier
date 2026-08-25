import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos911DenseSizeRamseyZeroRefutation.ZeroVertex

open scoped Classical

noncomputable def edgeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeFinset.card

def ramseyFor {n : ℕ}
    (host : Σ k : ℕ, SimpleGraph (Fin k))
    (target : SimpleGraph (Fin n)) : Prop :=
  ∀ red : Fin host.1 → Fin host.1 → Bool,
    (∀ u v, red u v = red v u) →
    ∃ f : Fin n ↪ Fin host.1,
      (∀ u v, target.Adj u v → host.2.Adj (f u) (f v)) ∧
      ∃ colour : Bool, ∀ u v, target.Adj u v →
        red (f u) (f v) = colour

noncomputable def sizeRamsey {n : ℕ}
    (target : SimpleGraph (Fin n)) : ℕ :=
  sInf {m : ℕ | ∃ host : Σ k : ℕ, SimpleGraph (Fin k),
    edgeCount host.2 = m ∧ ramseyFor host target}

theorem emptyHost_ramseyFor :
    ramseyFor ⟨0, ⊥⟩ (⊥ : SimpleGraph (Fin 0)) := by
  intro red hsymmetric
  refine ⟨Function.Embedding.refl (Fin 0), ?_, false, ?_⟩
  · intro u
    exact Fin.elim0 u
  · intro u
    exact Fin.elim0 u

theorem edgeCount_empty :
    edgeCount (⊥ : SimpleGraph (Fin 0)) = 0 := by
  rw [edgeCount, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro edge
  exact isEmptyElim edge

theorem sizeRamsey_empty :
    sizeRamsey (⊥ : SimpleGraph (Fin 0)) = 0 := by
  rw [sizeRamsey, Nat.sInf_eq_zero]
  left
  exact ⟨⟨0, ⊥⟩, edgeCount_empty, emptyHost_ramseyFor⟩

theorem proof :
    (let edgeCount : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ :=
        fun {_n} G => G.edgeFinset.card
      let ramseyFor : ∀ {n : ℕ},
          (Σ k : ℕ, SimpleGraph (Fin k)) → SimpleGraph (Fin n) → Prop :=
        fun {n} host target =>
          ∀ red : Fin host.1 → Fin host.1 → Bool,
            (∀ u v, red u v = red v u) →
            ∃ f : Fin n ↪ Fin host.1,
              (∀ u v, target.Adj u v → host.2.Adj (f u) (f v)) ∧
              ∃ colour : Bool, ∀ u v, target.Adj u v →
                red (f u) (f v) = colour
      let sizeRamsey : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ :=
        fun {_n} target =>
          sInf {m : ℕ | ∃ host : Σ k : ℕ, SimpleGraph (Fin k),
            edgeCount host.2 = m ∧ ramseyFor host target}
      ¬ ∃ f : ℕ → ℝ,
        Tendsto (fun C : ℕ => f C / C) atTop atTop ∧
        ∀ᶠ C : ℕ in atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
          C * n ≤ edgeCount G →
            f C * edgeCount G < sizeRamsey G) := by
  change ¬ ∃ f : ℕ → ℝ,
    Tendsto (fun C : ℕ => f C / C) atTop atTop ∧
    ∀ᶠ C : ℕ in atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      C * n ≤ edgeCount G →
        f C * edgeCount G < sizeRamsey G
  rintro ⟨f, hgrowth, hbound⟩
  obtain ⟨C, hC⟩ := hbound.exists
  have h :=
    hC 0 (⊥ : SimpleGraph (Fin 0)) (by simp [edgeCount])
  simpa [edgeCount_empty, sizeRamsey_empty] using h

end Submissions.Erdos911DenseSizeRamseyZeroRefutation.ZeroVertex
