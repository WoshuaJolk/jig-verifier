import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Submissions.Erdos44CutAverage.Direct

open Set Finset

def rot (n c x : ℕ) : ℕ := (x + n - c) % n

abbrev Quad := (((ℕ × ℕ) × ℕ) × ℕ)

abbrev SameCarry (n c : ℕ) (p : Quad) : Prop :=
  (rot n c p.1.1.1 + rot n c p.1.1.2 < n) ↔
    (rot n c p.2 + rot n c p.1.2 < n)

abbrev ModWitness (n : ℕ) (p : Quad) : Prop :=
  (p.1.1.1 + p.1.1.2) % n = (p.2 + p.1.2) % n

def CutSurvivors (n c : ℕ) (E : Finset Quad) : Finset Quad :=
  E.filter (SameCarry n c)

def SurvivalCuts (n : ℕ) (p : Quad) : Finset ℕ :=
  (Finset.range n).filter fun c => SameCarry n c p

private theorem rot_zero_of_two_le
    (n c : ℕ) (hc : 2 ≤ c) (hcn : c < n) :
    rot n c 0 = n - c := by
  unfold rot
  have hlt : n - c < n := by omega
  simp only [zero_add]
  rw [Nat.mod_eq_of_lt hlt]

private theorem rot_one_of_two_le
    (n c : ℕ) (hc : 2 ≤ c) (hcn : c < n) :
    rot n c 1 = n + 1 - c := by
  unfold rot
  have heq : 1 + n - c = n + 1 - c := by omega
  rw [heq]
  have hlt : n + 1 - c < n := by omega
  rw [Nat.mod_eq_of_lt hlt]

private theorem rot_last
    (n c : ℕ) (hn : 2 ≤ n) (hcn : c < n) :
    rot n c (n - 1) = n - 1 - c := by
  unfold rot
  have hge : n ≤ n - 1 + n - c := by omega
  rw [Nat.mod_eq_sub_mod hge]
  have heq : n - 1 + n - c - n = n - 1 - c := by omega
  rw [heq]
  have hlt : n - 1 - c < n := by omega
  rw [Nat.mod_eq_of_lt hlt]

theorem proof :
    (∀ (n : ℕ) (E : Finset Quad),
      ∑ c ∈ Finset.range n, (CutSurvivors n c E).card =
        ∑ p ∈ E, (SurvivalCuts n p).card) ∧
    (∀ n : ℕ, 3 ≤ n →
      let p : Quad := (((0, 0), n - 1), 1)
      ModWitness n p ∧ n - 2 ≤ (SurvivalCuts n p).card) := by
  constructor
  · intro n E
    simp only [CutSurvivors, SurvivalCuts, Finset.card_filter]
    rw [Finset.sum_comm]
  · intro n hn
    let p : Quad := (((0, 0), n - 1), 1)
    have hmod : ModWitness n p := by
      change (0 + 0) % n = (1 + (n - 1)) % n
      have heq : 1 + (n - 1) = n := by omega
      simp [heq]
    have hsub : Finset.Ico 2 n ⊆ SurvivalCuts n p := by
      intro c hc
      have hcb := Finset.mem_Ico.mp hc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hcb.2, ?_⟩
      change
        (rot n c 0 + rot n c 0 < n) ↔
          (rot n c 1 + rot n c (n - 1) < n)
      rw [rot_zero_of_two_le n c hcb.1 hcb.2,
        rot_one_of_two_le n c hcb.1 hcb.2,
        rot_last n c (by omega) hcb.2]
      have heq :
          (n - c) + (n - c) =
            (n + 1 - c) + (n - 1 - c) := by omega
      simp [heq]
    refine ⟨hmod, ?_⟩
    calc
      n - 2 = (Finset.Ico 2 n).card := by simp
      _ ≤ (SurvivalCuts n p).card := Finset.card_le_card hsub

end Submissions.Erdos44CutAverage.Direct
