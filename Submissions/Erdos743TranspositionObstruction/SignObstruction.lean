import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic

namespace Submissions.Erdos743TranspositionObstruction.SignObstruction

open scoped BigOperators

abbrev Grid := Fin 3 → Fin 3 → Fin 3
abbrev Sequence := Fin 3 → Fin 3 → Fin 3

/-- Definition 3.8 with its necessary correction: strict descent only for positive vertices. -/
def Descending (g : Sequence) : Prop :=
  ∀ k, g k 0 = 0 ∧
    (∀ v, k.val < v.val → g k v = v) ∧
    (∀ v, 0 < v.val → v.val ≤ k.val → (g k v).val < v.val)

def stars : Sequence := fun k v ↦ if v.val ≤ k.val then 0 else v

def leafSwap (v : Fin 3) : Fin 3 := if v = 1 then 2 else if v = 2 then 1 else v

def swapped (X : Grid) : Grid := fun k v ↦ if k = 2 then X k (leafSwap v) else X k v

def witness : Grid := fun k v ↦
  if k = 0 then v
  else if k = 1 then (if v = 0 then 1 else if v = 1 then 0 else 2)
  else (if v = 0 then 2 else if v = 1 then 0 else 1)

/-- Exact evaluation of Definition 2.1's unsquared Vandermonde factor at n=3. -/
def vandermonde (X : Grid) : ℤ :=
  ∏ k : Fin 3, ∏ u : Fin 3, ∏ v : Fin 3,
    if u < v then ((X k v).val : ℤ) - (X k u).val else 1

def edgeLabel (g : Sequence) (X : Grid) (y : ℤ) (k v : Fin 3) : ℤ :=
  (y - (X k (g k v)).val) * (y - (X k v).val)

/-- Every cross-tree factor, including the functional root loops, exactly as Definition 2.1. -/
def edgeFactor (g : Sequence) (X : Grid) (y : ℤ) : ℤ :=
  ∏ i : Fin 3, ∏ j : Fin 3, ∏ u : Fin 3, ∏ v : Fin 3,
    if i < j ∧ u.val ≤ i.val ∧ v.val ≤ j.val
    then edgeLabel g X y j v - edgeLabel g X y i u else 1

def certificate (g : Sequence) (X : Grid) (y : ℤ) : ℤ :=
  vandermonde X * edgeFactor g X y

theorem hypotheses : Descending stars ∧
    stars 2 1 = stars 2 2 ∧
    (∀ v, stars 2 v ≠ 1 ∧ stars 2 v ≠ 2) ∧
    (∀ v, leafSwap (leafSwap v) = v) ∧
    (∀ v, stars 2 (leafSwap v) = leafSwap (stars 2 v)) := by
  unfold Descending
  decide

theorem evaluations :
    vandermonde witness = -8 ∧ vandermonde (swapped witness) = 8 ∧
    edgeFactor stars witness 4 = -77414400 ∧
    edgeFactor stars (swapped witness) 4 = -77414400 ∧
    certificate stars witness 4 = 619315200 ∧
    certificate stars (swapped witness) 4 = -619315200 := by decide

/-- Any representative agreeing with the certificate on the grid fails leaf-swap invariance. -/
theorem proof : Descending stars ∧
    stars 2 1 = stars 2 2 ∧
    (∀ v, stars 2 v ≠ 1 ∧ stars 2 v ≠ 2) ∧
    (∀ v, leafSwap (leafSwap v) = v) ∧
    (∀ v, stars 2 (leafSwap v) = leafSwap (stars 2 v)) ∧
    certificate stars witness 4 = 619315200 ∧
    certificate stars (swapped witness) 4 = -619315200 ∧
    ∀ R : Grid → ℚ, (∀ X, R X = (certificate stars X 4 : ℚ)) →
      ¬ (∀ X, R (swapped X) = R X) := by
  refine ⟨hypotheses.1, hypotheses.2.1, hypotheses.2.2.1,
    hypotheses.2.2.2.1, hypotheses.2.2.2.2,
    evaluations.2.2.2.2.1, evaluations.2.2.2.2.2, ?_⟩
  intro R hR hInv
  have h := hInv witness
  rw [hR, hR, evaluations.2.2.2.2.1, evaluations.2.2.2.2.2] at h
  exact (by decide : (-619315200 : ℚ) ≠ 619315200) h

end Submissions.Erdos743TranspositionObstruction.SignObstruction
