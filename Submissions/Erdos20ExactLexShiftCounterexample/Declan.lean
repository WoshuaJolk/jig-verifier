import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

namespace Submissions.Erdos20ExactLexShiftCounterexample.Declan

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def core : Finset ℕ := Finset.range 12

/-- Thirteen sets of size thirteen on the ordered ground set `{0,...,36}`. -/
def original : Finset (Finset ℕ) :=
  insert (core ∪ {12}) ((Finset.range 12).image fun i => (core.erase i) ∪ {13+i,25+i})

def elementaryShift (i j : ℕ) (F : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  F.image fun A =>
    if i ∉ A ∧ j ∈ A ∧ insert i (A.erase j) ∉ F then insert i (A.erase j) else A

/-- Exactly the ascending all-pairs schedule: first target `i`, then source `j>i`.
Each of the 666 pairs occurs exactly once. -/
def fullLexSchedule : List (ℕ × ℕ) :=
  (List.range 37).flatMap fun i =>
    ((List.range 37).filter fun j => i < j).map fun j => (i,j)

def finalFamily : Finset (Finset ℕ) :=
  fullLexSchedule.foldl (fun F p => elementaryShift p.1 p.2 F) original

def star : Finset (Finset ℕ) :=
  (Finset.range 13).image fun i => core ∪ {12+i}

theorem original_card : original.card = 13 := by decide

theorem original_uniform : ∀ A ∈ original, A.card = 13 := by decide

theorem original_ground : ∀ A ∈ original, A ⊆ Finset.range 37 := by decide

theorem original_no_three :
    ∀ A ∈ original, ∀ B ∈ original, ∀ C ∈ original,
    A ≠ B → A ≠ C → B ≠ C →
      ¬ (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C) := by decide

theorem schedule_length : fullLexSchedule.length = 666 := by decide

theorem exact_lex_output : finalFamily = star := by decide

theorem star_card : star.card = 13 := by decide

theorem star_intersections :
    ∀ A ∈ star, ∀ B ∈ star, A ≠ B → A ∩ B = core := by decide

/-- This finite example refutes a universal `3 * 2^2` bound on the sunflower
size after the exact full lexicographic ordinary-shift schedule, starting
with no three-petal sunflower. It does not refute Erdős problem #20. -/
theorem proof :
    original.card = 13 ∧
    (∀ A ∈ original, A.card = 13 ∧ A ⊆ Finset.range 37) ∧
    (∀ A ∈ original, ∀ B ∈ original, ∀ C ∈ original,
      A ≠ B → A ≠ C → B ≠ C →
        ¬ (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C)) ∧
    finalFamily = star ∧
    finalFamily.card = 13 ∧
    (∀ A ∈ finalFamily, ∀ B ∈ finalFamily, A ≠ B → A ∩ B = core) ∧
    3 * 2^2 < finalFamily.card := by
  refine ⟨original_card, ?_, original_no_three, exact_lex_output, ?_, ?_, ?_⟩
  · intro A hA
    exact ⟨original_uniform A hA, original_ground A hA⟩
  · rw [exact_lex_output]
    exact star_card
  · rw [exact_lex_output]
    exact star_intersections
  · rw [exact_lex_output, star_card]
    norm_num

#print axioms proof

end Submissions.Erdos20ExactLexShiftCounterexample.Declan
