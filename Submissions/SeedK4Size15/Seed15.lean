import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace Submissions.SeedK4Size15.Seed15

open GaussianInt

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-! ## The statement's definitions, restated verbatim -/

/-- Hermitian pairing. -/
def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The orthogonality graph of a family. -/
def orthGraph {k m : ℕ} (v : Fin m → Fin k → ℂ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i i' => pair (v i) (v i') = 0

/-! ## Gaussian-integer witness

15 vectors in `ℤ[i]⁴`: the deformed `C₁₄(1,2)` family (dropped chords `{3,5}`, `{7,9}`)
plus one inserted vertex (index 14) orthogonal to `3, 5, 7, 9`. -/

def cZ : Fin 15 → Fin 4 → GaussianInt := ![
  ![⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩],
  ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩],
  ![⟨2, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩],
  ![⟨2, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩],
  ![⟨0, 0⟩, ⟨3, 0⟩, ⟨2, 0⟩, ⟨-1, 0⟩],
  ![⟨-15, -22⟩, ⟨3, -4⟩, ⟨-1, 6⟩, ⟨7, 0⟩],
  ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨3, 0⟩, ⟨3, 0⟩],
  ![⟨4, 3⟩, ⟨22, -15⟩, ⟨6, 1⟩, ⟨0, -7⟩],
  ![⟨3, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 0⟩],
  ![⟨-4, -3⟩, ⟨8, 6⟩, ⟨-8, -6⟩, ⟨-4, -3⟩],
  ![⟨2, 0⟩, ⟨4, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩],
  ![⟨-13, 3⟩, ⟨-4, 3⟩, ⟨14, -6⟩, ⟨-23, 15⟩],
  ![⟨38, 21⟩, ⟨-7, 3⟩, ⟨-16, -18⟩, ⟨-30, -12⟩],
  ![⟨-238, 72⟩, ⟨654, -18⟩, ⟨-317, -24⟩, ⟨-198, -60⟩],
  ![⟨53, 56⟩, ⟨-53, -56⟩, ⟨-205, 0⟩, ⟨251, -168⟩]]

/-- The neighbour sets of the target graph: the circulant `C₁₄(1,2)` on `0..13` minus
the chords `{3,5}` and `{7,9}`, plus the star `{14,3}, {14,5}, {14,7}, {14,9}`. -/
def nbr : Fin 15 → Finset (Fin 15) := ![
  ({1, 2, 12, 13} : Finset (Fin 15)),
  ({0, 2, 3, 13} : Finset (Fin 15)),
  ({0, 1, 3, 4} : Finset (Fin 15)),
  ({1, 2, 4, 14} : Finset (Fin 15)),
  ({2, 3, 5, 6} : Finset (Fin 15)),
  ({4, 6, 7, 14} : Finset (Fin 15)),
  ({4, 5, 7, 8} : Finset (Fin 15)),
  ({5, 6, 8, 14} : Finset (Fin 15)),
  ({6, 7, 9, 10} : Finset (Fin 15)),
  ({8, 10, 11, 14} : Finset (Fin 15)),
  ({8, 9, 11, 12} : Finset (Fin 15)),
  ({9, 10, 12, 13} : Finset (Fin 15)),
  ({0, 10, 11, 13} : Finset (Fin 15)),
  ({0, 1, 11, 12} : Finset (Fin 15)),
  ({3, 5, 7, 9} : Finset (Fin 15))]

/-! ## Exact arithmetic cores -/

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

/-! ## Kernel certificates -/

theorem nzG : ∀ i : Fin 15, ∃ r, cZ i r ≠ 0 := by decide +kernel

/-- The Hermitian Gram is zero exactly on the prescribed neighbour sets — all 225
ordered pairs, the diagonal included. -/
theorem orthG : ∀ i i' : Fin 15, gdotG (cZ i) (cZ i') = 0 ↔ i' ∈ nbr i := by
  decide +kernel

theorem cardN : ∀ i : Fin 15, (nbr i).card = 4 := by decide +kernel

theorem tight3 :
    ∀ i1 i2 : Fin 15, i1 < i2 → ∀ i3 : Fin 15, i2 < i3 →
      det3G (delCol 0 (cZ i1)) (delCol 0 (cZ i2)) (delCol 0 (cZ i3)) ≠ 0 ∨
      det3G (delCol 1 (cZ i1)) (delCol 1 (cZ i2)) (delCol 1 (cZ i3)) ≠ 0 ∨
      det3G (delCol 2 (cZ i1)) (delCol 2 (cZ i2)) (delCol 2 (cZ i3)) ≠ 0 ∨
      det3G (delCol 3 (cZ i1)) (delCol 3 (cZ i2)) (delCol 3 (cZ i3)) ≠ 0 := by
  decide +kernel

theorem span5 :
    ∀ i1 i2 : Fin 15, i1 < i2 → ∀ i3 : Fin 15, i2 < i3 →
    ∀ i4 : Fin 15, i3 < i4 → ∀ i5 : Fin 15, i4 < i5 →
      det4G (cZ i1) (cZ i2) (cZ i3) (cZ i4) ≠ 0 ∨
      det4G (cZ i1) (cZ i2) (cZ i3) (cZ i5) ≠ 0 ∨
      det4G (cZ i1) (cZ i2) (cZ i4) (cZ i5) ≠ 0 ∨
      det4G (cZ i1) (cZ i3) (cZ i4) (cZ i5) ≠ 0 ∨
      det4G (cZ i2) (cZ i3) (cZ i4) (cZ i5) ≠ 0 := by
  decide +kernel

/-! ## Casting `ℤ[i] → ℂ` -/

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
def v (i : Fin 15) : Fin 4 → ℂ := fun r => ((cZ i r : GaussianInt) : ℂ)

/-! ## The orthogonality certificate over `ℂ` -/

lemma pair_eq (i i' : Fin 15) :
    pair (v i) (v i') = ((gdotG (cZ i) (cZ i') : GaussianInt) : ℂ) := by
  simpa [pair, v] using gdot_cast (cZ i) (cZ i')

lemma orthIff : ∀ i i' : Fin 15, pair (v i) (v i') = 0 ↔ i' ∈ nbr i := by
  intro i i'
  rw [pair_eq]
  constructor
  · intro h
    exact (orthG i i').mp (GaussianInt.toComplex_eq_zero.mp h)
  · intro h
    rw [(orthG i i').mpr h]
    exact GaussianInt.toComplex_zero

/-! ## Tightness -/

/-- Column restriction along `c.succAbove` as a linear map. -/
def restrict3 (c : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun g := fun r => g (c.succAbove r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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

lemma linInd3 (i j k : Fin 15) (c : Fin 4)
    (hd : det3G (delCol c (cZ i)) (delCol c (cZ j)) (delCol c (cZ k)) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k] := by
  have h := linInd_of_det3 c hd
  convert h using 1
  ext s r
  fin_cases s <;> simp [v]

lemma tight_sorted (i j k : Fin 15) (hij : i < j) (hjk : j < k) :
    LinearIndependent ℂ ![v i, v j, v k] := by
  rcases tight3 i j hij k hjk with h | h | h | h
  · exact linInd3 i j k 0 h
  · exact linInd3 i j k 1 h
  · exact linInd3 i j k 2 h
  · exact linInd3 i j k 3 h

/-- A three-element `Finset`, as a set-indexed family, is linearly independent. -/
lemma tightT (T : Finset (Fin 15)) (hT : T.card = 3) :
    LinearIndependent ℂ fun x : (T : Set (Fin 15)) => v x := by
  let e := T.orderIsoOfFin hT
  have h01 : ((e 0 : T) : Fin 15) < ((e 1 : T) : Fin 15) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (0 : Fin 3) < 1))
  have h12 : ((e 1 : T) : Fin 15) < ((e 2 : T) : Fin 15) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (1 : Fin 3) < 2))
  have h3 : LinearIndependent ℂ ![v (e 0), v (e 1), v (e 2)] :=
    tight_sorted _ _ _ h01 h12
  let g : ↥(T : Set (Fin 15)) → Fin 3 := fun x => e.symm ⟨x.1, Finset.mem_coe.mp x.2⟩
  have hg : Function.Injective g := by
    intro x1 x2 h
    have h' := e.symm.injective h
    exact Subtype.ext (congrArg Subtype.val h')
  have hm : ∀ j : Fin 3,
      (![v (e 0), v (e 1), v (e 2)] : Fin 3 → Fin 4 → ℂ) j = v (e j) := by
    intro j; fin_cases j <;> rfl
  have hfam : (fun x : ↥(T : Set (Fin 15)) => v x)
      = (![v (e 0), v (e 1), v (e 2)] : Fin 3 → Fin 4 → ℂ) ∘ g := by
    funext x
    have hx : e (g x) = ⟨x.1, Finset.mem_coe.mp x.2⟩ := e.apply_symm_apply _
    have hval : ((e (g x) : T) : Fin 15) = (x : Fin 15) := congrArg Subtype.val hx
    simp only [Function.comp_apply, hm (g x), hval]
  rw [hfam]
  exact h3.comp g hg

/-- Tightness in the statement's form: every subset of at most three indices is
linearly independent. -/
lemma tightAll : ∀ S : Finset (Fin 15), S.card ≤ 3 →
    LinearIndependent ℂ fun i : (S : Set (Fin 15)) => v i := by
  intro S hS
  obtain ⟨T, hST, -, hT⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ S)
      hS (by decide : 3 ≤ (Finset.univ : Finset (Fin 15)).card)
  have h : LinearIndepOn ℂ v (T : Set (Fin 15)) := tightT T hT
  exact h.mono (Finset.coe_subset.mpr hST)

/-! ## 5-spanning -/

/-- A nonzero `a` cannot be `pair`-orthogonal to four rows with a nonvanishing
Gaussian determinant. -/
lemma perp4 {x y z t : Fin 4 → GaussianInt}
    (hd : det4G x y z t ≠ 0) {a : Fin 4 → ℂ}
    (hx : star (a 0) * ((x 0 : ℂ)) + star (a 1) * ((x 1 : ℂ))
        + star (a 2) * ((x 2 : ℂ)) + star (a 3) * ((x 3 : ℂ)) = 0)
    (hy : star (a 0) * ((y 0 : ℂ)) + star (a 1) * ((y 1 : ℂ))
        + star (a 2) * ((y 2 : ℂ)) + star (a 3) * ((y 3 : ℂ)) = 0)
    (hz : star (a 0) * ((z 0 : ℂ)) + star (a 1) * ((z 1 : ℂ))
        + star (a 2) * ((z 2 : ℂ)) + star (a 3) * ((z 3 : ℂ)) = 0)
    (ht : star (a 0) * ((t 0 : ℂ)) + star (a 1) * ((t 1 : ℂ))
        + star (a 2) * ((t 2 : ℂ)) + star (a 3) * ((t 3 : ℂ)) = 0) :
    a = 0 := by
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
  have hdet0 : M.det ≠ 0 := by
    rw [hdetC, det4G_cast]
    exact fun h => hd (GaussianInt.toComplex_eq_zero.mp h)
  have hmul : M.mulVec (fun r => star (a r)) = 0 := by
    funext j
    rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
    fin_cases j
    · show ((x 0 : ℂ)) * star (a 0) + ((x 1 : ℂ)) * star (a 1)
          + ((x 2 : ℂ)) * star (a 2) + ((x 3 : ℂ)) * star (a 3) = 0
      linear_combination hx
    · show ((y 0 : ℂ)) * star (a 0) + ((y 1 : ℂ)) * star (a 1)
          + ((y 2 : ℂ)) * star (a 2) + ((y 3 : ℂ)) * star (a 3) = 0
      linear_combination hy
    · show ((z 0 : ℂ)) * star (a 0) + ((z 1 : ℂ)) * star (a 1)
          + ((z 2 : ℂ)) * star (a 2) + ((z 3 : ℂ)) * star (a 3) = 0
      linear_combination hz
    · show ((t 0 : ℂ)) * star (a 0) + ((t 1 : ℂ)) * star (a 1)
          + ((t 2 : ℂ)) * star (a 2) + ((t 3 : ℂ)) * star (a 3) = 0
      linear_combination ht
  have hstar : (fun r => star (a r)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet0 hmul
  funext r
  have h := congrFun hstar r
  simpa [star_eq_zero] using h

lemma pairExpand (a : Fin 4 → ℂ) (i : Fin 15) (h : pair a (v i) = 0) :
    star (a 0) * ((cZ i 0 : ℂ)) + star (a 1) * ((cZ i 1 : ℂ))
      + star (a 2) * ((cZ i 2 : ℂ)) + star (a 3) * ((cZ i 3 : ℂ)) = 0 := by
  have h' : (∑ r, star (a r) * ((cZ i r : ℂ))) = 0 := h
  rwa [Fin.sum_univ_four] at h'

lemma span_sorted {i1 i2 i3 i4 i5 : Fin 15} (h12 : i1 < i2) (h23 : i2 < i3)
    (h34 : i3 < i4) (h45 : i4 < i5) {a : Fin 4 → ℂ}
    (hp1 : pair a (v i1) = 0) (hp2 : pair a (v i2) = 0) (hp3 : pair a (v i3) = 0)
    (hp4 : pair a (v i4) = 0) (hp5 : pair a (v i5) = 0) : a = 0 := by
  rcases span5 i1 i2 h12 i3 h23 i4 h34 i5 h45 with h | h | h | h | h
  · exact perp4 h (pairExpand a i1 hp1) (pairExpand a i2 hp2)
      (pairExpand a i3 hp3) (pairExpand a i4 hp4)
  · exact perp4 h (pairExpand a i1 hp1) (pairExpand a i2 hp2)
      (pairExpand a i3 hp3) (pairExpand a i5 hp5)
  · exact perp4 h (pairExpand a i1 hp1) (pairExpand a i2 hp2)
      (pairExpand a i4 hp4) (pairExpand a i5 hp5)
  · exact perp4 h (pairExpand a i1 hp1) (pairExpand a i3 hp3)
      (pairExpand a i4 hp4) (pairExpand a i5 hp5)
  · exact perp4 h (pairExpand a i2 hp2) (pairExpand a i3 hp3)
      (pairExpand a i4 hp4) (pairExpand a i5 hp5)

/-- 5-spanning in the statement's form. -/
lemma spanAll : ∀ S : Finset (Fin 15), S.card = 5 → ∀ a : Fin 4 → ℂ, a ≠ 0 →
    ∃ i ∈ S, pair a (v i) ≠ 0 := by
  intro S hS a ha
  by_contra hcon
  push Not at hcon
  apply ha
  let e := S.orderIsoOfFin hS
  have h01 : ((e 0 : S) : Fin 15) < ((e 1 : S) : Fin 15) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (0 : Fin 5) < 1))
  have h12 : ((e 1 : S) : Fin 15) < ((e 2 : S) : Fin 15) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (1 : Fin 5) < 2))
  have h23 : ((e 2 : S) : Fin 15) < ((e 3 : S) : Fin 15) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (2 : Fin 5) < 3))
  have h34 : ((e 3 : S) : Fin 15) < ((e 4 : S) : Fin 15) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (3 : Fin 5) < 4))
  exact span_sorted h01 h12 h23 h34
    (hcon _ (e 0).2) (hcon _ (e 1).2) (hcon _ (e 2).2)
    (hcon _ (e 3).2) (hcon _ (e 4).2)

/-! ## Connectivity -/

lemma adjOf {i j : Fin 15} (hne : i ≠ j) (hj : j ∈ nbr i) : (orthGraph v).Adj i j :=
  (SimpleGraph.fromRel_adj (fun i i' => pair (v i) (v i') = 0) i j).mpr
    ⟨hne, Or.inl ((orthIff i j).mpr hj)⟩

lemma connG : (orthGraph v).Connected := by
  have step : ∀ i j : Fin 15, i ≠ j → j ∈ nbr i → (orthGraph v).Reachable i j :=
    fun i j h1 h2 => (adjOf h1 h2).reachable
  have r0 : (orthGraph v).Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have r1 : (orthGraph v).Reachable 0 1 := step 0 1 (by decide) (by decide)
  have r2 := r1.trans (step 1 2 (by decide) (by decide))
  have r3 := r2.trans (step 2 3 (by decide) (by decide))
  have r4 := r3.trans (step 3 4 (by decide) (by decide))
  have r5 := r4.trans (step 4 5 (by decide) (by decide))
  have r6 := r5.trans (step 5 6 (by decide) (by decide))
  have r7 := r6.trans (step 6 7 (by decide) (by decide))
  have r8 := r7.trans (step 7 8 (by decide) (by decide))
  have r9 := r8.trans (step 8 9 (by decide) (by decide))
  have r10 := r9.trans (step 9 10 (by decide) (by decide))
  have r11 := r10.trans (step 10 11 (by decide) (by decide))
  have r12 := r11.trans (step 11 12 (by decide) (by decide))
  have r13 := r12.trans (step 12 13 (by decide) (by decide))
  have r14 := r3.trans (step 3 14 (by decide) (by decide))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro w
  fin_cases w
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14

/-! ## The seed statement -/

theorem proof :
    ∃ v : Fin 15 → Fin 4 → ℂ, ∃ N : Fin 15 → Finset (Fin 15),
      (∀ i, v i ≠ 0) ∧
      (∀ i i', pair (v i) (v i') = 0 ↔ i' ∈ N i) ∧
      (∀ i, (N i).card = 4) ∧
      (orthGraph v).Connected ∧
      (∀ S : Finset (Fin 15), S.card ≤ 3 →
        LinearIndependent ℂ fun i : (S : Set (Fin 15)) => v i) ∧
      (∀ S : Finset (Fin 15), S.card = 5 → ∀ a : Fin 4 → ℂ, a ≠ 0 →
        ∃ i ∈ S, pair a (v i) ≠ 0) := by
  refine ⟨v, nbr, ?_, orthIff, cardN, connG, tightAll, spanAll⟩
  intro i hi
  obtain ⟨r, hr⟩ := nzG i
  apply hr
  apply GaussianInt.toComplex_eq_zero.mp
  have h := congr_fun hi r
  simpa [v] using h

end Submissions.SeedK4Size15.Seed15
