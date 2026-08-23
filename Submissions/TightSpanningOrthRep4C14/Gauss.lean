import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace Submissions.TightSpanningOrthRep4C14.Gauss

open GaussianInt

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- Gaussian-integer witness: Hermitian orthogonality graph exactly the circulant
`C_14(1,2)`, every three vectors linearly independent (tight), no five in a common
hyperplane (5-spanning). -/
def cZ : Fin 14 → Fin 4 → GaussianInt := ![
  ![⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩],
  ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩],
  ![⟨2, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩],
  ![⟨2, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩],
  ![⟨0, 0⟩, ⟨3, 0⟩, ⟨2, 0⟩, ⟨-1, 0⟩],
  ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩],
  ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨3, 0⟩, ⟨3, 0⟩],
  ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩],
  ![⟨3, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 0⟩],
  ![⟨1, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩],
  ![⟨2, 0⟩, ⟨4, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩],
  ![⟨-13, 3⟩, ⟨-4, 3⟩, ⟨14, -6⟩, ⟨-23, 15⟩],
  ![⟨38, 21⟩, ⟨-7, 3⟩, ⟨-16, -18⟩, ⟨-30, -12⟩],
  ![⟨-238, 72⟩, ⟨654, -18⟩, ⟨-317, -24⟩, ⟨-198, -60⟩]]

/-- The statement's circulant distance, restated verbatim. -/
abbrev circDist (i j : Fin 14) : ℕ :=
  let d := (i.val + 14 - j.val) % 14
  min d (14 - d)

/-- The statement's circulant adjacency, restated verbatim. -/
abbrev circEdge (i j : Fin 14) : Prop :=
  circDist i j = 1 ∨ circDist i j = 2

/-- The statement's five-point rank-4 disjunction, restated verbatim. -/
abbrev Rank4of5 (v : Fin 14 → Fin 4 → ℂ) (i j k l t : Fin 14) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

/-- Hermitian Gaussian pairing (conjugate-linear in the first slot). -/
def gdotG (x y : Fin 4 → GaussianInt) : GaussianInt :=
  star (x 0) * y 0 + star (x 1) * y 1 + star (x 2) * y 2 + star (x 3) * y 3

def det3G (x y z : Fin 3 → GaussianInt) : GaussianInt :=
  x 0 * y 1 * z 2 - x 0 * y 2 * z 1
    - x 1 * y 0 * z 2 + x 1 * y 2 * z 0
    + x 2 * y 0 * z 1 - x 2 * y 1 * z 0

def det3C (x y z : Fin 3 → ℂ) : ℂ :=
  x 0 * y 1 * z 2 - x 0 * y 2 * z 1
    - x 1 * y 0 * z 2 + x 1 * y 2 * z 0
    + x 2 * y 0 * z 1 - x 2 * y 1 * z 0

def det4G (x y z t : Fin 4 → GaussianInt) : GaussianInt :=
  x 0 * y 1 * z 2 * t 3
    - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3
    + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2
    - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3
    + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3
    - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2
    + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3
    - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3
    + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1
    - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2
    + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2
    - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1
    + x 3 * y 2 * z 1 * t 0

def det4C (x y z t : Fin 4 → ℂ) : ℂ :=
  x 0 * y 1 * z 2 * t 3
    - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3
    + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2
    - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3
    + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3
    - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2
    + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3
    - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3
    + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1
    - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2
    + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2
    - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1
    + x 3 * y 2 * z 1 * t 0

/-- Delete column `c` of a row. -/
def delCol (c : Fin 4) (x : Fin 4 → GaussianInt) : Fin 3 → GaussianInt :=
  fun r => x (c.succAbove r)

theorem nzG : ∀ i : Fin 14, ∃ r, cZ i r ≠ 0 := by decide +kernel

theorem orthExact :
    ∀ i j : Fin 14, i ≠ j → (circEdge i j ↔ gdotG (cZ i) (cZ j) = 0) := by
  decide +kernel

theorem tight3 :
    ∀ i1 i2 : Fin 14, i1 < i2 → ∀ i3 : Fin 14, i2 < i3 →
      det3G (delCol 0 (cZ i1)) (delCol 0 (cZ i2)) (delCol 0 (cZ i3)) ≠ 0 ∨
      det3G (delCol 1 (cZ i1)) (delCol 1 (cZ i2)) (delCol 1 (cZ i3)) ≠ 0 ∨
      det3G (delCol 2 (cZ i1)) (delCol 2 (cZ i2)) (delCol 2 (cZ i3)) ≠ 0 ∨
      det3G (delCol 3 (cZ i1)) (delCol 3 (cZ i2)) (delCol 3 (cZ i3)) ≠ 0 := by
  decide +kernel

theorem span5 :
    ∀ i1 i2 : Fin 14, i1 < i2 → ∀ i3 : Fin 14, i2 < i3 →
    ∀ i4 : Fin 14, i3 < i4 → ∀ i5 : Fin 14, i4 < i5 →
      det4G (cZ i1) (cZ i2) (cZ i3) (cZ i4) ≠ 0 ∨
      det4G (cZ i1) (cZ i2) (cZ i3) (cZ i5) ≠ 0 ∨
      det4G (cZ i1) (cZ i2) (cZ i4) (cZ i5) ≠ 0 ∨
      det4G (cZ i1) (cZ i3) (cZ i4) (cZ i5) ≠ 0 ∨
      det4G (cZ i2) (cZ i3) (cZ i4) (cZ i5) ≠ 0 := by
  decide +kernel

lemma starcast (w : GaussianInt) :
    star ((w : ℂ)) = ((star w : GaussianInt) : ℂ) := by
  rw [Complex.star_def, GaussianInt.toComplex_star]

lemma gdot_cast (x y : Fin 4 → GaussianInt) :
    (∑ r, star ((x r : ℂ)) * ((y r : ℂ))) = ((gdotG x y : GaussianInt) : ℂ) := by
  simp only [gdotG, Fin.sum_univ_four, starcast, ← GaussianInt.toComplex_mul,
    ← GaussianInt.toComplex_add]

lemma det4G_cast (x y z t : Fin 4 → GaussianInt) :
    det4C (fun r => ((x r : ℂ))) (fun r => ((y r : ℂ)))
        (fun r => ((z r : ℂ))) (fun r => ((t r : ℂ)))
      = ((det4G x y z t : GaussianInt) : ℂ) := by
  simp only [det4C, det4G, ← GaussianInt.toComplex_mul, ← GaussianInt.toComplex_add,
    ← GaussianInt.toComplex_sub]

lemma det3G_cast (x y z : Fin 3 → GaussianInt) :
    det3C (fun r => ((x r : ℂ))) (fun r => ((y r : ℂ))) (fun r => ((z r : ℂ)))
      = ((det3G x y z : GaussianInt) : ℂ) := by
  simp only [det3C, det3G, ← GaussianInt.toComplex_mul, ← GaussianInt.toComplex_add,
    ← GaussianInt.toComplex_sub]

/-- The complex witness: entrywise cast of `cZ`. -/
def v (i : Fin 14) : Fin 4 → ℂ := fun r => ((cZ i r : GaussianInt) : ℂ)

/-- Column restriction along `c.succAbove` as a linear map. -/
def restrict3 (c : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun g := fun r => g (c.succAbove r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma linInd_of_det4 {x y z t : Fin 4 → GaussianInt}
    (hd : det4G x y z t ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => ((x r : ℂ))),
      (fun r : Fin 4 => ((y r : ℂ))),
      (fun r : Fin 4 => ((z r : ℂ))),
      (fun r : Fin 4 => ((t r : ℂ)))] := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![((x 0 : ℂ)), ((x 1 : ℂ)), ((x 2 : ℂ)), ((x 3 : ℂ));
       ((y 0 : ℂ)), ((y 1 : ℂ)), ((y 2 : ℂ)), ((y 3 : ℂ));
       ((z 0 : ℂ)), ((z 1 : ℂ)), ((z 2 : ℂ)), ((z 3 : ℂ));
       ((t 0 : ℂ)), ((t 1 : ℂ)), ((t 2 : ℂ)), ((t 3 : ℂ))]
  have hdetC : M.det = det4C (fun r => ((x r : ℂ))) (fun r => ((y r : ℂ)))
      (fun r => ((z r : ℂ))) (fun r => ((t r : ℂ))) := by
    simp [M, Matrix.det_succ_row_zero, det4C, Fin.sum_univ_succ,
      Fin.val_succ, Fin.val_eq_zero, Fin.succAbove]
    ring
  have hdet : M.det = ((det4G x y z t : GaussianInt) : ℂ) := by
    rw [hdetC, det4G_cast]
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact fun h => hd (GaussianInt.toComplex_eq_zero.mp h)
  have hrows : LinearIndependent ℂ (fun i : Fin 4 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam :
      (fun i : Fin 4 => M i) =
        ![(fun r : Fin 4 => ((x r : ℂ))), (fun r : Fin 4 => ((y r : ℂ))),
          (fun r : Fin 4 => ((z r : ℂ))), (fun r : Fin 4 => ((t r : ℂ)))] := by
    ext i r
    fin_cases i <;> fin_cases r <;> simp [M]
  rwa [hfam] at hrows

lemma linInd_of_det3 (c : Fin 4) {x y z : Fin 4 → GaussianInt}
    (hd : det3G (delCol c x) (delCol c y) (delCol c z) ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => ((x r : ℂ))),
      (fun r : Fin 4 => ((y r : ℂ))),
      (fun r : Fin 4 => ((z r : ℂ)))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![((delCol c x 0 : ℂ)), ((delCol c x 1 : ℂ)), ((delCol c x 2 : ℂ));
       ((delCol c y 0 : ℂ)), ((delCol c y 1 : ℂ)), ((delCol c y 2 : ℂ));
       ((delCol c z 0 : ℂ)), ((delCol c z 1 : ℂ)), ((delCol c z 2 : ℂ))]
  have hdetC : M.det = det3C (fun r => ((delCol c x r : ℂ)))
      (fun r => ((delCol c y r : ℂ))) (fun r => ((delCol c z r : ℂ))) := by
    simp [M, Matrix.det_succ_row_zero, det3C, Fin.sum_univ_succ,
      Fin.val_succ, Fin.val_eq_zero, Fin.succAbove]
    ring
  have hdet : M.det
      = ((det3G (delCol c x) (delCol c y) (delCol c z) : GaussianInt) : ℂ) := by
    rw [hdetC, det3G_cast]
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact fun h => hd (GaussianInt.toComplex_eq_zero.mp h)
  have hrows : LinearIndependent ℂ (fun s : Fin 3 => M s) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam :
      (fun s : Fin 3 => M s) =
        (⇑(restrict3 c)) ∘ ![(fun r : Fin 4 => ((x r : ℂ))),
          (fun r : Fin 4 => ((y r : ℂ))), (fun r : Fin 4 => ((z r : ℂ)))] := by
    ext s r
    fin_cases s <;> fin_cases r <;> simp [M, restrict3, delCol]
  rw [hfam] at hrows
  exact LinearIndependent.of_comp (restrict3 c) hrows

lemma linInd4 (i j k l : Fin 14)
    (hd : det4G (cZ i) (cZ j) (cZ k) (cZ l) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k, v l] := by
  have h := linInd_of_det4 hd
  convert h using 1
  ext s r
  fin_cases s <;> simp [v]

lemma linInd3 (i j k : Fin 14) (c : Fin 4)
    (hd : det3G (delCol c (cZ i)) (delCol c (cZ j)) (delCol c (cZ k)) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k] := by
  have h := linInd_of_det3 c hd
  convert h using 1
  ext s r
  fin_cases s <;> simp [v]

theorem proof :
    ∃ v : Fin 14 → Fin 4 → ℂ,
      (∀ i, v i ≠ 0) ∧
      (∀ i j, i ≠ j → (circEdge i j ↔ (∑ r, star (v i r) * v j r) = 0)) ∧
      (∀ i j k : Fin 14, i < j → j < k → LinearIndependent ℂ ![v i, v j, v k]) ∧
      (∀ i j k l t : Fin 14, i < j → j < k → k < l → l < t → Rank4of5 v i j k l t) := by
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨r, hr⟩ := nzG i
    apply hr
    apply GaussianInt.toComplex_eq_zero.mp
    have h := congr_fun hi r
    simpa [v] using h
  · intro i j hij
    have hdot : (∑ r, star (v i r) * v j r)
        = ((gdotG (cZ i) (cZ j) : GaussianInt) : ℂ) := by
      simpa [v] using gdot_cast (cZ i) (cZ j)
    constructor
    · intro he
      rw [hdot, (orthExact i j hij).mp he]
      exact GaussianInt.toComplex_zero
    · intro hip
      apply (orthExact i j hij).mpr
      apply GaussianInt.toComplex_eq_zero.mp
      rw [← hdot]
      exact hip
  · intro i j k hij hjk
    rcases tight3 i j hij k hjk with h | h | h | h
    · exact linInd3 i j k 0 h
    · exact linInd3 i j k 1 h
    · exact linInd3 i j k 2 h
    · exact linInd3 i j k 3 h
  · intro i j k l t hij hjk hkl hlt
    rcases span5 i j hij k hjk l hkl t hlt with h | h | h | h | h
    · exact Or.inl (linInd4 i j k l h)
    · exact Or.inr <| Or.inl (linInd4 i j k t h)
    · exact Or.inr <| Or.inr <| Or.inl (linInd4 i j l t h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (linInd4 i k l t h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (linInd4 j k l t h)

end Submissions.TightSpanningOrthRep4C14.Gauss
