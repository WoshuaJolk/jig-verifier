import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

namespace Statements.Erdos20ExactLexShiftCounterexample

def core : Finset ℕ := Finset.range 12

def original : Finset (Finset ℕ) :=
  insert (core ∪ {12}) ((Finset.range 12).image fun i => (core.erase i) ∪ {13+i,25+i})

def elementaryShift (i j : ℕ) (F : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  F.image fun A =>
    if i ∉ A ∧ j ∈ A ∧ insert i (A.erase j) ∉ F then insert i (A.erase j) else A

def fullLexSchedule : List (ℕ × ℕ) :=
  (List.range 37).flatMap fun i =>
    ((List.range 37).filter fun j => i < j).map fun j => (i,j)

def finalFamily : Finset (Finset ℕ) :=
  fullLexSchedule.foldl (fun F p => elementaryShift p.1 p.2 F) original

def star : Finset (Finset ℕ) :=
  (Finset.range 13).image fun i => core ∪ {12+i}

abbrev statement : Prop :=
    original.card = 13 ∧
    (∀ A ∈ original, A.card = 13 ∧ A ⊆ Finset.range 37) ∧
    (∀ A ∈ original, ∀ B ∈ original, ∀ C ∈ original,
      A ≠ B → A ≠ C → B ≠ C →
        ¬ (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C)) ∧
    finalFamily = star ∧
    finalFamily.card = 13 ∧
    (∀ A ∈ finalFamily, ∀ B ∈ finalFamily, A ≠ B → A ∩ B = core) ∧
    3 * 2^2 < finalFamily.card

theorem target : statement := sorry

end Statements.Erdos20ExactLexShiftCounterexample
