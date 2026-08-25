import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph
open scoped BigOperators

namespace Submissions.Erdos60CodegreeIncidence.LengthTwoPaths

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

private abbrev Pairs := {p : V × V // p.1 ≠ p.2}
private abbrev CodegreeWitnesses :=
  Σ p : Pairs (V := V), G.commonNeighbors p.1.1 p.1.2
private abbrev DegreeWitnesses :=
  Σ x : V, ↥((Finset.univ : Finset (G.neighborSet x)).offDiag)

private noncomputable def witnessEquiv :
    CodegreeWitnesses G ≃ DegreeWitnesses G where
  toFun w := by
    rcases w with ⟨⟨⟨u, v⟩, huv⟩, ⟨x, hxu, hxv⟩⟩
    refine ⟨x, ⟨(⟨u, ?_⟩, ⟨v, ?_⟩), ?_⟩⟩
    · simpa using hxu.symm
    · simpa using hxv.symm
    · simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
      intro h
      exact huv (congrArg Subtype.val h)
  invFun w := by
    rcases w with ⟨x, ⟨⟨⟨u, hxu⟩, ⟨v, hxv⟩⟩, huv⟩⟩
    refine ⟨⟨(u, v), ?_⟩, ⟨x, ?_, ?_⟩⟩
    · intro h
      have hne : (⟨u, hxu⟩ : G.neighborSet x) ≠ ⟨v, hxv⟩ := by
        simpa only [Finset.mem_offDiag, Finset.mem_univ,
          true_and] using huv
      exact hne (Subtype.ext h)
    · simpa using hxu.symm
    · simpa using hxv.symm
  left_inv w := by
    rcases w with ⟨⟨⟨u, v⟩, huv⟩, ⟨x, hxu, hxv⟩⟩
    rfl
  right_inv w := by
    rcases w with ⟨x, ⟨⟨⟨u, hxu⟩, ⟨v, hxv⟩⟩, huv⟩⟩
    rfl

private theorem incidence :
    (∑ p : Pairs (V := V),
      (G.commonNeighbors p.1.1 p.1.2).ncard) =
    ∑ x : V, G.degree x * (G.degree x - 1) := by
  classical
  calc
    _ = Nat.card (CodegreeWitnesses G) := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Set.ncard_eq_toFinset_card',
        Set.toFinset_card, Nat.card_eq_fintype_card]
    _ = Nat.card (DegreeWitnesses G) :=
      Nat.card_congr (witnessEquiv G)
    _ = ∑ x : V,
        Nat.card ↥((Finset.univ : Finset (G.neighborSet x)).offDiag) :=
      Nat.card_sigma
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.card_eq_fintype_card, Fintype.card_coe,
        Finset.offDiag_card]
      change Fintype.card (G.neighborSet x) *
          Fintype.card (G.neighborSet x) -
          Fintype.card (G.neighborSet x) =
        G.degree x * (G.degree x - 1)
      rw [G.card_neighborSet_eq_degree x]
      simp [Nat.mul_sub_left_distrib]

theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∑ p : {p : Fin n × Fin n // p.1 ≠ p.2},
        (G.commonNeighbors p.1.1 p.1.2).ncard) =
      ∑ x : Fin n, G.degree x * (G.degree x - 1) := by
  intro n G _
  exact incidence G

end Submissions.Erdos60CodegreeIncidence.LengthTwoPaths
