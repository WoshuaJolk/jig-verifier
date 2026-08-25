import Mathlib.Tactic

namespace Submissions.Erdos829SmallTwoCubeCounts.Worker01

def isCube (m : ℕ) : Bool :=
  (List.range (m + 1)).any fun k ↦ k ^ 3 == m

def sumRepCubes (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun a ↦ isCube a && isCube (n - a)).card

theorem proof :
    sumRepCubes 0 = 1 ∧ sumRepCubes 2 = 1 ∧ sumRepCubes 3 = 0 := by
  decide

end Submissions.Erdos829SmallTwoCubeCounts.Worker01
