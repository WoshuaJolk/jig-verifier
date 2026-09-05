import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.ErdosMultiplesStaticPeelingDead.Witness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def generators : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

abbrev good (a n m : ℕ) : Prop :=
  (∀ b ∈ generators, b ≤ n) ∧ n < m ∧
    n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ generators, b ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ generators, b ∣ k)).card ∧
    2 * m * ((Finset.Icc 1 n).filter
      (fun k => a ∣ k ∧ ∀ b ∈ generators.erase a, ¬ b ∣ k)).card <
      n * ((Finset.Icc 1 m).filter
        (fun k => a ∣ k ∧ ∀ b ∈ generators.erase a, ¬ b ∣ k)).card

lemma witness2 : good 2 61 542 := by decide

lemma witness3 : good 3 80 327 := by decide

lemma witness5 : good 5 124 215 := by decide

lemma witness7 : good 7 216 301 := by decide

lemma witness11 : good 11 120 1133 := by decide

lemma witness13 : good 13 168 793 := by decide

lemma witness17 : good 17 288 697 := by decide

lemma witness19 : good 19 360 703 := by decide

lemma witness23 : good 23 528 713 := by decide

lemma witness29 : good 29 840 899 := by decide

theorem proof :
  ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    (∀ b ∈ A, ∀ c ∈ A, b ∣ c → b = c) ∧
    ∀ a ∈ A, ∃ n m : ℕ, (∀ b ∈ A, b ≤ n) ∧ n < m ∧
      n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ A, b ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ A, b ∣ k)).card ∧
      2 * m * ((Finset.Icc 1 n).filter
        (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card <
        n * ((Finset.Icc 1 m).filter
          (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card := by
  refine ⟨generators, by decide, by decide, by decide, ?_⟩
  intro a ha
  simp only [generators, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨61, 542, witness2⟩
  · exact ⟨80, 327, witness3⟩
  · exact ⟨124, 215, witness5⟩
  · exact ⟨216, 301, witness7⟩
  · exact ⟨120, 1133, witness11⟩
  · exact ⟨168, 793, witness13⟩
  · exact ⟨288, 697, witness17⟩
  · exact ⟨360, 703, witness19⟩
  · exact ⟨528, 713, witness23⟩
  · exact ⟨840, 899, witness29⟩

end Submissions.ErdosMultiplesStaticPeelingDead.Witness
