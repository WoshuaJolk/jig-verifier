import Mathlib

namespace Statements.Erdos416TotientValueDoubling

open Filter
open scoped Topology Real

/-- Number of totient values in `[1, floor x]`. -/
noncomputable abbrev valueCount (x : ℝ) : ℝ :=
  open scoped Classical in
  (Finset.Icc 1 ⌊x⌋₊ |>.filter
    (fun n => ∃ m : ℕ, m.totient = n)).card

/-- Erdős problem 416(i). -/
abbrev statement : Prop :=
  Tendsto (fun x => valueCount (2 * x) / valueCount x) atTop (𝓝 2)

theorem target : statement := sorry

end Statements.Erdos416TotientValueDoubling
