import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

namespace Submissions.Erdos44AggregateCarryArcs.Direct

open Set Finset
open scoped symmDiff

def rot (n c x : ℕ) : ℕ := (x + n - c) % n

abbrev Quad := (((ℕ × ℕ) × ℕ) × ℕ)

abbrev PairCarry (n c x y : ℕ) : Prop :=
  rot n c x + rot n c y < n

abbrev SameCarry (n c : ℕ) (p : Quad) : Prop :=
  PairCarry n c p.1.1.1 p.1.1.2 ↔ PairCarry n c p.2 p.1.2

def CarryCuts (n x y : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun c => PairCarry n c x y

def DisagreementCuts (n : ℕ) (p : Quad) : Finset ℕ :=
  CarryCuts n p.1.1.1 p.1.1.2 ∆ CarryCuts n p.2 p.1.2

def SurvivalCuts (n : ℕ) (p : Quad) : Finset ℕ :=
  (Finset.range n).filter fun c => SameCarry n c p

def CutSurvivors (n c : ℕ) (E : Finset Quad) : Finset Quad :=
  E.filter (SameCarry n c)

theorem proof :
    (∀ (n : ℕ) (p : Quad),
      SurvivalCuts n p = Finset.range n \ DisagreementCuts n p) ∧
    (∀ (n : ℕ) (E : Finset Quad),
      (∑ c ∈ Finset.range n, (CutSurvivors n c E).card) +
        (∑ p ∈ E, (DisagreementCuts n p).card) =
          n * E.card) := by
  have hid :
      ∀ (n : ℕ) (p : Quad),
        SurvivalCuts n p = Finset.range n \ DisagreementCuts n p := by
    intro n p
    apply Finset.ext
    intro c
    simp only [SurvivalCuts, DisagreementCuts, CarryCuts, Finset.mem_filter,
      Finset.mem_range, Finset.mem_sdiff, Finset.mem_symmDiff]
    tauto
  refine ⟨hid, ?_⟩
  intro n E
  have hsurv :
      ∑ c ∈ Finset.range n, (CutSurvivors n c E).card =
        ∑ p ∈ E, (SurvivalCuts n p).card := by
    simp only [CutSurvivors, SurvivalCuts, Finset.card_filter]
    rw [Finset.sum_comm]
  have hpoint :
      ∀ p : Quad,
        (SurvivalCuts n p).card + (DisagreementCuts n p).card = n := by
    intro p
    have hsub : DisagreementCuts n p ⊆ Finset.range n := by
      intro c hc
      simp only [DisagreementCuts, Finset.mem_symmDiff] at hc
      rcases hc with hc | hc
      · exact (Finset.mem_filter.mp hc.1).1
      · exact (Finset.mem_filter.mp hc.1).1
    rw [hid n p]
    have hcard := Finset.card_sdiff_add_card
      (Finset.range n) (DisagreementCuts n p)
    rw [Finset.union_eq_left.mpr hsub] at hcard
    simpa using hcard
  rw [hsurv, ← Finset.sum_add_distrib]
  calc
    ∑ p ∈ E, ((SurvivalCuts n p).card + (DisagreementCuts n p).card) =
        ∑ _p ∈ E, n := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hpoint p
    _ = n * E.card := by simp [Nat.mul_comm]

end Submissions.Erdos44AggregateCarryArcs.Direct
