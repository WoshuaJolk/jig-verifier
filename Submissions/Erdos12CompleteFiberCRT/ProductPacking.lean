import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos12CompleteFiberCRT.ProductPacking

/-- Complete-fiber opposite exclusions multiply across coordinates.  The
folded coordinate fingerprint is injective, so a box with coordinate moduli
`m i` contains at most `∏ i, floor (m i / 2)` selected points. -/
theorem proof :
    ∀ {ι X : Type} [DecidableEq ι] [DecidableEq X]
      (I : Finset ι) (m : ι → ℕ) (coord : ι → X → ℕ) (B : Finset X),
      (∀ x ∈ B, ∀ i ∈ I, 0 < coord i x ∧ coord i x < m i) →
      (∀ x ∈ B, ∀ y ∈ B, ∀ i ∈ I,
        coord i x + coord i y = m i → x = y) →
      (∀ x ∈ B, ∀ y ∈ B,
        (∀ i ∈ I, coord i x = coord i y) → x = y) →
      B.card ≤ ∏ i ∈ I, m i / 2 := by
  intro ι X _ _ I m coord B hrange hopposite hjoint
  classical
  let J := {i // i ∈ I}
  let F := (i : J) → {v // v ∈ Finset.Ioc 0 (m i.1 / 2)}
  let f : {x // x ∈ B} → F := fun x i ↦
    ⟨min (coord i.1 x.1) (m i.1 - coord i.1 x.1), by
      obtain ⟨hx0, hxm⟩ := hrange x.1 x.2 i.1 i.2
      have href0 : 0 < m i.1 - coord i.1 x.1 := by omega
      have hupper :
          min (coord i.1 x.1) (m i.1 - coord i.1 x.1) ≤ m i.1 / 2 := by
        rcases le_total (coord i.1 x.1) (m i.1 - coord i.1 x.1) with h | h
        · rw [min_eq_left h]
          omega
        · rw [min_eq_right h]
          omega
      exact Finset.mem_Ioc.mpr ⟨lt_min hx0 href0, hupper⟩⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_cases hne : x.1 = y.1
    · exact hne
    apply hjoint x.1 x.2 y.1 y.2
    intro i hi
    have hcoord :
        min (coord i x.1) (m i - coord i x.1) =
          min (coord i y.1) (m i - coord i y.1) := by
      have h := congrArg Subtype.val (congrFun hxy ⟨i, hi⟩)
      simpa [f] using h
    obtain ⟨hx0, hxm⟩ := hrange x.1 x.2 i hi
    obtain ⟨hy0, hym⟩ := hrange y.1 y.2 i hi
    by_cases hxside : coord i x.1 ≤ m i - coord i x.1
    · rw [min_eq_left hxside] at hcoord
      by_cases hyside : coord i y.1 ≤ m i - coord i y.1
      · rwa [min_eq_left hyside] at hcoord
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hcoord
        exfalso
        apply hne
        apply hopposite x.1 x.2 y.1 y.2 i hi
        omega
    · rw [min_eq_right (Nat.le_of_not_ge hxside)] at hcoord
      by_cases hyside : coord i y.1 ≤ m i - coord i y.1
      · rw [min_eq_left hyside] at hcoord
        exfalso
        apply hne
        apply hopposite x.1 x.2 y.1 y.2 i hi
        omega
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hcoord
        omega
  have hcard := Fintype.card_le_of_injective f hf_inj
  have hcard' : B.card ≤ Fintype.card F := by simpa using hcard
  calc
    B.card ≤ Fintype.card F := hcard'
    _ = ∏ i ∈ I, m i / 2 := by
      simp only [F, J, Fintype.card_pi, Fintype.card_coe]
      simpa using (Finset.prod_attach I (fun i ↦ m i / 2))

end Submissions.Erdos12CompleteFiberCRT.ProductPacking
