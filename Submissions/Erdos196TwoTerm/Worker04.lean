import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic

namespace Submissions.Erdos196TwoTerm.Worker04

def ListIsAPOfLengthWith (s : List ℕ) (k a d : ℕ) : Prop :=
  s = (List.range k).map (fun n ↦ a + n • d) ∨
  s = (List.range k).reverse.map (fun n ↦ a + n • d)

def ListIsAPOfLength (s : List ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, ListIsAPOfLengthWith s k a d

def HasMonotoneAP (f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ l : List ℕ, ListIsAPOfLength (l.map f) k ∧ l.Pairwise (· < ·)

theorem proof : ∀ f : ℕ ≃ ℕ, HasMonotoneAP f 2 := by
  intro f
  have hne : f 0 ≠ f 1 := by
    intro h
    have := f.injective h
    omega
  refine ⟨[0, 1], ?_, by norm_num⟩
  by_cases h : f 0 < f 1
  · refine ⟨f 0, f 1 - f 0, Or.inl ?_⟩
    norm_num [List.range_succ, Nat.add_sub_of_le h.le]
  · have hr : f 1 < f 0 := by omega
    refine ⟨f 1, f 0 - f 1, Or.inr ?_⟩
    norm_num [List.range_succ, Nat.add_sub_of_le hr.le]

end Submissions.Erdos196TwoTerm.Worker04
