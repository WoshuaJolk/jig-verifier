import Mathlib

namespace Submissions.Erdos64PSLTriangleFamily.Cole


-- Source: PSLTriangleMatrices.lean
section

namespace PSLTriangle

open Matrix

variable {R : Type*} [CommRing R]

def aMatrix : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 1]
def bMatrix : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]
def uMatrix (t : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; -t, 1]
def hMatrix : Matrix (Fin 2) (Fin 2) R := !![-1, -1; 2, 1]
def hInvMatrix : Matrix (Fin 2) (Fin 2) R := !![1, 1; -2, -1]

theorem det_aMatrix : (aMatrix : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  simp [aMatrix, Matrix.det_fin_two]

theorem det_bMatrix : (bMatrix : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  simp [bMatrix, Matrix.det_fin_two]

theorem det_uMatrix (t : R) : (uMatrix t).det = 1 := by
  simp [uMatrix, Matrix.det_fin_two]

theorem det_hMatrix : (hMatrix : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  simp [hMatrix, Matrix.det_fin_two]
  ring

theorem aMatrix_square : (aMatrix : Matrix (Fin 2) (Fin 2) R) * aMatrix =
    !![-1, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem aMatrix_cube : (aMatrix : Matrix (Fin 2) (Fin 2) R) ^ 3 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pow_succ, aMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem bMatrix_square : (bMatrix : Matrix (Fin 2) (Fin 2) R) * bMatrix = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem aMatrix_mul_bMatrix : (aMatrix : Matrix (Fin 2) (Fin 2) R) * bMatrix =
    -uMatrix 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [aMatrix, bMatrix, uMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem uMatrix_add (s t : R) : uMatrix (s+t) = uMatrix s * uMatrix t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [uMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem first_intersection_matrix (i j : R) :
    uMatrix (-i) * hMatrix * uMatrix j =
    !![j-1, -1; i*(j-1)+2-j, 1-i] := by
  ext x y; fin_cases x <;> fin_cases y <;>
    simp [uMatrix, hMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem outer_intersection_matrix (i j t : R) :
    (uMatrix (-i) * hInvMatrix * uMatrix t * hMatrix * uMatrix j :
      Matrix (Fin 2) (Fin 2) R) 0 1 = t := by
  simp [uMatrix, hMatrix, hInvMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem hMatrix_mul_aMatrix : (hMatrix : Matrix (Fin 2) (Fin 2) R) * aMatrix =
    -uMatrix 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [aMatrix, hMatrix, uMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem hMatrix_mul_uMatrix : (hMatrix : Matrix (Fin 2) (Fin 2) R) * uMatrix 1 =
    aMatrix := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [aMatrix, hMatrix, uMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring


end PSLTriangle
end


-- Source: PSLTriangleProjective.lean
section

namespace PSLTriangle

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

def aSL : SL(2, F) := ⟨aMatrix, det_aMatrix⟩
def bSL : SL(2, F) := ⟨bMatrix, det_bMatrix⟩
def uSL (t : F) : SL(2, F) := ⟨uMatrix t, det_uMatrix t⟩
def hSL : SL(2, F) := ⟨hMatrix, det_hMatrix⟩

theorem center_SL_two_iff (x : SL(2, F)) :
    x ∈ Subgroup.center SL(2, F) ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    obtain ⟨r, hr, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
    simp only [Fintype.card_fin] at hr
    rcases (sq_eq_one_iff).mp hr with hr | hr
    · left
      apply Subtype.ext
      rw [← he, hr]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · right
      apply Subtype.ext
      rw [← he, hr]
      ext i j; fin_cases i <;> fin_cases j <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
      refine ⟨-1, by simp, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp

theorem projective_eq_iff (x y : SL(2, F)) :
    (QuotientGroup.mk x : PSL(2, F)) = QuotientGroup.mk y ↔ x = y ∨ x = -y := by
  rw [QuotientGroup.eq_iff_div_mem, center_SL_two_iff]
  simp [div_eq_iff_eq_mul]

def project (x : SL(2, F)) : PSL(2, F) := QuotientGroup.mk x
def aP : PSL(2, F) := project aSL
def bP : PSL(2, F) := project bSL
def uP (t : F) : PSL(2, F) := project (uSL t)
def hP : PSL(2, F) := project hSL

theorem project_mul (x y : SL(2, F)) : project (x*y) = project x * project y := rfl

theorem project_neg (x : SL(2, F)) : project (-x) = project x := by
  apply (projective_eq_iff (-x) x).mpr
  exact Or.inr rfl

theorem aP_cube : (aP : PSL(2, F)) ^ 3 = 1 := by
  have h : (aSL : SL(2, F)) ^ 3 = -1 := by
    apply Subtype.ext
    change (aMatrix : Matrix (Fin 2) (Fin 2) F) ^ 3 = -1
    exact aMatrix_cube
  have he := congrArg project h
  rw [project_neg] at he
  simpa [aP, project, QuotientGroup.mk_pow] using he

theorem bP_square : (bP : PSL(2, F)) * bP = 1 := by
  have h : (bSL : SL(2, F)) * bSL = -1 := by
    apply Subtype.ext
    change (bMatrix : Matrix (Fin 2) (Fin 2) F) * bMatrix = -1
    exact bMatrix_square
  have he := congrArg project h
  rw [project_mul, project_neg] at he
  exact he

theorem aP_mul_bP : (aP : PSL(2, F)) * bP = uP 1 := by
  have h : (aSL : SL(2, F)) * bSL = -uSL 1 := by
    apply Subtype.ext
    change (aMatrix : Matrix (Fin 2) (Fin 2) F) * bMatrix = -uMatrix 1
    exact aMatrix_mul_bMatrix
  have he := congrArg project h
  rw [project_mul, project_neg] at he
  exact he

theorem uP_add (s t : F) : uP (s+t) = uP s * uP t := by
  have h : uSL (s+t) = uSL s * uSL t := by
    apply Subtype.ext
    exact uMatrix_add s t
  exact congrArg project h

theorem uP_zero : (uP (0 : F)) = 1 := by
  have h : uSL (0 : F) = 1 := by
    apply Subtype.ext
    change uMatrix (0 : F) = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [uMatrix]
  exact congrArg project h

theorem uP_neg (t : F) : uP (-t) = (uP t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← uP_add, neg_add_cancel, uP_zero]

theorem hSL_inv_matrix : ((hSL : SL(2, F))⁻¹).val =
    hInvMatrix := by
  change Matrix.adjugate (hMatrix : Matrix (Fin 2) (Fin 2) F) = hInvMatrix
  rw [Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hMatrix, hInvMatrix]

theorem aP_ne_one : (aP : PSL(2, F)) ≠ 1 := by
  intro he
  change project aSL = project (1 : SL(2, F)) at he
  rcases (projective_eq_iff aSL 1).mp he with he | he
  all_goals
    have h01 := congrArg (fun x : SL(2, F) => x 0 1) he
    simpa [aSL, aMatrix] using h01

theorem bP_ne_one : (bP : PSL(2, F)) ≠ 1 := by
  intro he
  change project bSL = project (1 : SL(2, F)) at he
  rcases (projective_eq_iff bSL 1).mp he with he | he
  all_goals
    have h01 := congrArg (fun x : SL(2, F) => x 0 1) he
    simpa [bSL, bMatrix] using h01

def familyGraph (F : Type*) [Field F] : SimpleGraph PSL(2, F) :=
  SimpleGraph.mulCayley {aP, bP}

theorem familyGraph_matching_adj (x : PSL(2, F)) :
    (familyGraph F).Adj x (x*bP) := by
  rw [familyGraph, SimpleGraph.mulCayley_adj']
  refine ⟨?_, bP, by simp, Or.inl rfl⟩
  intro he
  apply bP_ne_one (F := F)
  simpa using he.symm

theorem family_matching_involutive :
    Function.Involutive (fun x : PSL(2, F) => x*bP) := by
  intro x
  simp [mul_assoc, bP_square]


end PSLTriangle
end


-- Source: PSLTriangleCosets.lean
section

namespace PSLTriangle

variable {G : Type*} [Group G]

/-- The cyclic triangle subgroup. No normality is assumed. -/
def triangleSubgroup (a : G) : Subgroup G := Subgroup.zpowers a

/-- Left cosets `x H`; right multiplication by `a` stays in a fiber. -/
abbrev TriangleCosets (a : G) := G ⧸ triangleSubgroup a

theorem orderOf_triangle_generator (a : G) (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    orderOf a = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime ha hne

theorem triangleSubgroup_mem_iff (a x : G) (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    x ∈ triangleSubgroup a ↔ x = 1 ∨ x = a ∨ x = a * a := by
  classical
  have hfin : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, ha⟩
  change x ∈ Subgroup.zpowers a ↔ _
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, orderOf_triangle_generator a ha hne]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, hkx⟩
    interval_cases k <;> simp_all [pow_two]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩
    · exact ⟨2, by decide, by simp [pow_two]⟩

theorem triangleCosets_eq_iff_mem (a x y : G) :
    (x : TriangleCosets a) = (y : TriangleCosets a) ↔
      x⁻¹ * y ∈ triangleSubgroup a :=
  QuotientGroup.eq

theorem triangleCosets_eq_iff (a x y : G) (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    (x : TriangleCosets a) = (y : TriangleCosets a) ↔
      x⁻¹ * y = 1 ∨ x⁻¹ * y = a ∨ x⁻¹ * y = a * a := by
  rw [triangleCosets_eq_iff_mem, triangleSubgroup_mem_iff a _ ha hne]


end PSLTriangle
end


-- Source: PSLTriangleIntersections.lean
section

namespace PSLTriangle

open Matrix

variable {F : Type*} [Field F]

def InTriangleMatrices (m : Matrix (Fin 2) (Fin 2) F) : Prop :=
  m = 1 ∨ m = aMatrix ∨ m = aMatrix * aMatrix ∨
  m = -1 ∨ m = -aMatrix ∨ m = -(aMatrix * aMatrix)

theorem triangle_upper_right {m : Matrix (Fin 2) (Fin 2) F}
    (hm : InTriangleMatrices m) : m 0 1 = 0 ∨ m 0 1 = 1 ∨ m 0 1 = -1 := by
  rcases hm with h | h | h | h | h | h <;> rw [h] <;>
    simp [aMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem outer_triangles_disjoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (i j : F) :
    ¬ InTriangleMatrices (uMatrix (-i) * hInvMatrix * uMatrix 2 * hMatrix * uMatrix j) := by
  intro hm
  have hu := triangle_upper_right hm
  rw [outer_intersection_matrix] at hu
  rcases hu with hu | hu | hu
  · exact h2 hu
  · have hz : (1 : F) = 0 := by linear_combination hu
    exact one_ne_zero hz
  · apply h3
    linear_combination hu

theorem first_intersection_only (h2 : (2 : F) ≠ 0) (i j : F)
    (hm : InTriangleMatrices (uMatrix (-i) * hMatrix * uMatrix j)) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  rw [first_intersection_matrix] at hm
  rcases hm with h | h | h | h | h | h
  · have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 1) h
    simp at he
  · left
    have hx := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 0) h
    have hy := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 1 1) h
    simp [aMatrix] at hx hy
    constructor
    · exact hy
    · linear_combination hx
  · right
    rw [aMatrix_square] at h
    have hx := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 0) h
    have hy := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 1 1) h
    simp at hx hy
    constructor
    · linear_combination -hy
    · linear_combination hx
  · have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 1) h
    simp at he
  · have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 1) h
    simp [aMatrix] at he
    exfalso
    apply h2
    linear_combination -he
  · rw [aMatrix_square] at h
    have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 1) h
    simp at he
    exfalso
    apply h2
    linear_combination -he


end PSLTriangle
end


-- Source: PSLTriangleQuotientMatrices.lean
section

namespace PSLTriangle

open Matrix
open scoped MatrixGroups
variable {F : Type*} [Field F]

theorem project_eq_matrix_iff (x y : SL(2, F)) :
    project x = project y ↔
      x.val = y.val ∨ x.val = -y.val := by
  constructor
  · intro he
    rcases (projective_eq_iff x y).mp he with h | h
    · exact Or.inl (congrArg (fun z : SL(2, F) => z.val) h)
    · exact Or.inr (congrArg (fun z : SL(2, F) => z.val) h)
  · intro he
    apply (projective_eq_iff x y).mpr
    rcases he with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem project_mem_triangle_iff (x : SL(2, F)) :
    project x ∈ triangleSubgroup aP ↔
      InTriangleMatrices (x : Matrix (Fin 2) (Fin 2) F) := by
  rw [triangleSubgroup_mem_iff aP _ aP_cube aP_ne_one]
  change (project x = project (1 : SL(2, F)) ∨ project x = project aSL ∨
    project x = project (aSL*aSL)) ↔ _
  rw [project_eq_matrix_iff, project_eq_matrix_iff, project_eq_matrix_iff]
  change ((x.val = 1 ∨ x.val = -1) ∨
    (x.val = aMatrix ∨ x.val = -aMatrix) ∨
    (x.val = aMatrix*aMatrix ∨ x.val = -(aMatrix*aMatrix))) ↔ _
  simp only [InTriangleMatrices]
  tauto

theorem first_coset_intersection (h2 : (2 : F) ≠ 0) (i j : F)
    (he : (uP i : TriangleCosets (aP : PSL(2, F))) =
      (hP*uP j : PSL(2, F))) :
    (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
  have hm := (triangleCosets_eq_iff_mem aP (uP i) (hP*uP j)).mp he
  rw [← uP_neg] at hm
  have hm' : project (uSL (-i)*hSL*uSL j) ∈ triangleSubgroup aP := by
    simpa only [project_mul, uP, hP, mul_assoc] using hm
  have hx := (project_mem_triangle_iff _).mp hm'
  change InTriangleMatrices (uMatrix (-i)*hMatrix*uMatrix j) at hx
  exact first_intersection_only h2 i j hx

theorem outer_cosets_disjoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (i j : F) :
    ((hP*uP i : PSL(2, F)) : TriangleCosets (aP : PSL(2, F))) ≠
      (uP 2*hP*uP j : PSL(2, F)) := by
  intro he
  have hm := (triangleCosets_eq_iff_mem aP (hP*uP i) (uP 2*hP*uP j)).mp he
  simp only [_root_.mul_inv_rev] at hm
  rw [← uP_neg] at hm
  have hm' : project (uSL (-i)*hSL⁻¹*uSL 2*hSL*uSL j) ∈ triangleSubgroup aP := by
    simpa only [uP, hP, project, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_assoc] using hm
  have hx := (project_mem_triangle_iff _).mp hm'
  change InTriangleMatrices (uMatrix (-i)*((hSL : SL(2,F))⁻¹).val*
    uMatrix 2*hMatrix*uMatrix j) at hx
  rw [hSL_inv_matrix] at hx
  exact outer_triangles_disjoint h2 h3 i j hx

theorem hP_mul_aP : (hP : PSL(2, F))*aP = uP 1 := by
  have he : (hSL : SL(2,F))*aSL = -uSL 1 := by
    apply Subtype.ext
    change (hMatrix : Matrix (Fin 2) (Fin 2) F)*aMatrix = -uMatrix 1
    exact hMatrix_mul_aMatrix
  have hh := congrArg project he
  rw [project_mul, project_neg] at hh
  exact hh

theorem hP_mul_uP_one : (hP : PSL(2, F))*uP 1 = aP := by
  have he : (hSL : SL(2,F))*uSL 1 = aSL := by
    apply Subtype.ext
    change (hMatrix : Matrix (Fin 2) (Fin 2) F)*uMatrix 1 = aMatrix
    exact hMatrix_mul_uMatrix
  exact congrArg project he


end PSLTriangle
end


-- Source: PSLTriangleFibers.lean
section

namespace PSLTriangle

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

def baseFiber (x : F × Fin 3) : PSL(2, F) := uP x.1 * aP ^ x.2.val

theorem baseFiber_injective (htwo : (2 : F) ≠ 0) :
    Function.Injective (baseFiber (F := F)) := by
  rintro ⟨s, k⟩ ⟨t, l⟩ he
  have he' : project (uSL s * aSL ^ k.val) =
      project (uSL t * aSL ^ l.val) := by
    simpa [baseFiber, project, uP, aP, QuotientGroup.mk_pow,
      QuotientGroup.mk_mul] using he
  rcases (projective_eq_iff _ _).mp he' with heq | heq
  all_goals
    have hm := congrArg (fun z : SL(2, F) => z.val) heq
    first
    | change uMatrix s * aMatrix ^ k.val = uMatrix t * aMatrix ^ l.val at hm
    | change uMatrix s * aMatrix ^ k.val = -(uMatrix t * aMatrix ^ l.val) at hm
    have h00 := congrArg (fun z : Matrix (Fin 2) (Fin 2) F => z 0 0) hm
    have h01 := congrArg (fun z : Matrix (Fin 2) (Fin 2) F => z 0 1) hm
    have h10 := congrArg (fun z : Matrix (Fin 2) (Fin 2) F => z 1 0) hm
    have h11 := congrArg (fun z : Matrix (Fin 2) (Fin 2) F => z 1 1) hm
    fin_cases k <;> fin_cases l <;>
      simp [uMatrix, aMatrix,
        pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11 ⊢
  all_goals first
    | exact h10
    | exact neg_injective h10
    | linear_combination h10
    | linear_combination h11
    | exfalso; apply htwo; linear_combination h00
    | exfalso; apply htwo; linear_combination h01
    | exfalso; apply htwo; linear_combination -h00
    | exfalso; apply htwo; linear_combination -h01


theorem baseFiber_triangle_adj (htwo : (2 : F) ≠ 0) (t : F)
    (k l : Fin 3) (hkl : k ≠ l) :
    (SimpleGraph.mulCayley ({aP, bP} : Set PSL(2, F))).Adj
      (baseFiber (t, k)) (baseFiber (t, l)) := by
  apply (SimpleGraph.mulCayley_adj' _ _ _).mpr
  refine ⟨?_, aP, by simp, ?_⟩
  · intro he
    exact hkl (congrArg Prod.snd (baseFiber_injective htwo he))
  · fin_cases k <;> fin_cases l <;> simp at hkl
    all_goals simp [baseFiber, mul_assoc, ← pow_succ, aP_cube]
    all_goals simp [pow_two]


end PSLTriangle
end


-- Source: PSLTriangleLift.lean
section

namespace PSLTriangleLift

def fiber {r t : ℕ} (ht : t ≤ r) (j : Fin (2*r+t)) : Fin r :=
  if h : j.val < 3*t then ⟨j.val / 3, by omega⟩
  else ⟨t + (j.val-3*t)/2, by omega⟩

def port {r t : ℕ} (j : Fin (2*r+t)) : Fin 3 :=
  if j.val < 3*t then
    if j.val % 3 = 0 then 0 else if j.val % 3 = 1 then 2 else 1
  else if (j.val-3*t)%2 = 0 then 0 else 1

def slot {r t : ℕ} (ht : t ≤ r) (j : Fin (2*r+t)) : Fin r × Fin 3 :=
  (fiber ht j, port j)

theorem slot_injective {r t : ℕ} (ht : t ≤ r) : Function.Injective (slot ht) := by
  intro a b hab
  have hf := congrArg (fun p : Fin r × Fin 3 => p.1.val) hab
  have hp := congrArg (fun p : Fin r × Fin 3 => p.2.val) hab
  simp only [slot, fiber, port] at hf hp
  split_ifs at hf hp <;> simp_all <;> apply Fin.ext <;> omega

theorem slot_step {r t : ℕ} (_hr : 3 ≤ r) (ht : t ≤ r)
    (a b : Fin (2*r+t))
    (hab : b.val = a.val+1 ∨ (a.val+1 = 2*r+t ∧ b.val=0)) :
    (fiber ht a = fiber ht b ∧ port a ≠ port b) ∨
    (port a = 1 ∧ port b = 0 ∧
      ((fiber ht b).val = (fiber ht a).val+1 ∨
       ((fiber ht a).val+1=r ∧ (fiber ht b).val=0))) := by
  simp only [fiber, port]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem sub_one_step {n : ℕ} (a b : Fin n) (h : (b-a).val=1) :
    b.val=a.val+1 ∨ (a.val+1=n ∧ b.val=0) := by
  by_cases hab : a ≤ b
  · rw [Fin.sub_val_of_le hab] at h
    left
    have : a.val ≤ b.val := hab
    omega
  · have hba : b < a := lt_of_not_ge hab
    rw [Fin.coe_sub_iff_lt.mpr hba] at h
    right
    omega

theorem triangle_cycle_lift {V : Type*} (G : SimpleGraph V)
    {r t : ℕ} (hr : 3 ≤ r) (ht : t ≤ r)
    (f : Fin r × Fin 3 → V) (hf : Function.Injective f)
    (triangle : ∀ i a b, a ≠ b → G.Adj (f (i,a)) (f (i,b)))
    (matching : ∀ i j : Fin r,
      (j.val=i.val+1 ∨ (i.val+1=r ∧ j.val=0)) →
      G.Adj (f (i,1)) (f (j,0))) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length=2*r+t := by
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < 2*r+t)).mp
  have forward : ∀ a b : Fin (2*r+t),
      (b.val=a.val+1 ∨ (a.val+1=2*r+t ∧ b.val=0)) →
      G.Adj (f (slot ht a)) (f (slot ht b)) := by
    intro a b hab
    rcases slot_step hr ht a b hab with ⟨he,hne⟩ | ⟨hpa,hpb,hnext⟩
    · dsimp [slot]
      rw [← he]
      exact triangle _ _ _ hne
    · simpa only [slot,hpa,hpb] using matching _ _ hnext
  refine ⟨⟨⟨fun a => f (slot ht a), ?_⟩, hf.comp (slot_injective ht)⟩⟩
  intro a b hab
  rcases SimpleGraph.cycleGraph_adj'.mp hab with hab | hab
  · exact (forward b a (sub_one_step b a hab)).symm
  · exact forward a b (sub_one_step a b hab)


end PSLTriangleLift
end


-- Source: PSLTriangleArithmetic.lean
section

namespace PSLTriangle

/-- The two quotient-cycle lift intervals contain a dyadic length below `8*p`.
This is only the arithmetic component of the triangle-generator family proof. -/
theorem dyadic_in_lift_intervals (p : ℕ) (hp : Nat.Prime p) (hfive : 5 ≤ p) :
    ∃ k : ℕ, 2 ≤ k ∧ 2 ^ k < 8 * p ∧
      ((2 * p ≤ 2 ^ k ∧ 2 ^ k ≤ 3 * p) ∨
       (2 * (3 * p - 4) ≤ 2 ^ k ∧ 2 ^ k ≤ 3 * (3 * p - 4))) := by
  by_cases hlarge : 13 ≤ p
  · let k := Nat.log 2 (2 * p - 1) + 1
    have hk : 2 ≤ k := by
      have := Nat.log_pos (b := 2) (n := 2 * p - 1) (by decide) (by omega)
      dsimp [k]
      omega
    have hlo : 2 * p ≤ 2 ^ k := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (2 * p - 1)
      change 2 * p - 1 < 2 ^ k at this
      omega
    have hhi : 2 ^ k < 4 * p := by
      have hlog := Nat.pow_log_le_self 2 (x := 2 * p - 1) (by omega)
      dsimp [k]
      rw [pow_succ]
      omega
    by_cases hfirst : 2 ^ k ≤ 3 * p
    · exact ⟨k, hk, by omega, Or.inl ⟨hlo, hfirst⟩⟩
    · refine ⟨k + 1, by omega, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        rw [pow_succ] <;> omega
  · have hsmall : p = 5 ∨ p = 7 ∨ p = 11 := by
      have : p ≤ 12 := by omega
      interval_cases p <;> (try norm_num at hp) <;> omega
    rcases hsmall with rfl | rfl | rfl
    · exact ⟨5, by decide⟩
    · exact ⟨4, by decide⟩
    · exact ⟨5, by decide⟩


end PSLTriangle
end


-- Source: PSLTriangleAssembly.lean
section

namespace PSLTriangle

/-- Explicit triangle fibers and consecutive matching ports. This is an
assumption on a graph, not a claim that the matrix family supplies it. -/
def TriangleRing {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ f : Fin r × Fin 3 → V, Function.Injective f ∧
    (∀ i a b, a ≠ b → G.Adj (f (i,a)) (f (i,b))) ∧
    (∀ i j : Fin r,
      (j.val=i.val+1 ∨ (i.val+1=r ∧ j.val=0)) →
      G.Adj (f (i,1)) (f (j,0)))

theorem TriangleRing.cycle_of_interval {V : Type*} {G : SimpleGraph V}
    {r n : ℕ} (ring : TriangleRing G r) (hr : 3 ≤ r)
    (hlo : 2*r ≤ n) (hhi : n ≤ 3*r) :
    ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length=n := by
  obtain ⟨f,hf,htri,hmatch⟩ := ring
  have ht : n-2*r ≤ r := by omega
  obtain ⟨v,walk,hcycle,hlen⟩ :=
    PSLTriangleLift.triangle_cycle_lift G hr ht f hf htri hmatch
  exact ⟨v,walk,hcycle,by omega⟩

/-- Conditional assembly only: the two explicit triangle rings are retained
as hypotheses. Discharging them for the PSL matrix family is separate. -/
theorem dyadic_cycle_of_two_triangle_rings {V : Type*} (G : SimpleGraph V)
    (p : ℕ) (hp : Nat.Prime p) (hfive : 5 ≤ p)
    (first : TriangleRing G p) (second : TriangleRing G (3*p-4)) :
    ∃ (k : ℕ) (v : V) (walk : G.Walk v v),
      2 ≤ k ∧ walk.IsCycle ∧ walk.length=2^k ∧ walk.length<8*p := by
  obtain ⟨k,hk,hbound,hrange⟩ := dyadic_in_lift_intervals p hp hfive
  have exists_cycle : ∃ (v : V) (walk : G.Walk v v),
      walk.IsCycle ∧ walk.length=2^k := by
    rcases hrange with ⟨hlo,hhi⟩ | ⟨hlo,hhi⟩
    · exact first.cycle_of_interval (by omega) hlo hhi
    · exact second.cycle_of_interval (by omega) hlo hhi
  obtain ⟨v,walk,hcycle,hlen⟩ := exists_cycle
  exact ⟨k,v,walk,hk,hcycle,hlen,by omega⟩


end PSLTriangle
end


-- Source: PSLTrianglePorts.lean
section

namespace PSLTriangle

def thirdPort (a b : Fin 3) : Fin 3 :=
  if a ≠ 0 ∧ b ≠ 0 then 0 else if a ≠ 1 ∧ b ≠ 1 then 1 else 2

def portRelabel (a b j : Fin 3) : Fin 3 :=
  if j=0 then a else if j=1 then b else thirdPort a b

@[simp] theorem portRelabel_zero (a b : Fin 3) : portRelabel a b 0 = a := by
  simp [portRelabel]

@[simp] theorem portRelabel_one (a b : Fin 3) : portRelabel a b 1 = b := by
  simp [portRelabel]

theorem portRelabel_injective (a b : Fin 3) (hab : a ≠ b) :
    Function.Injective (portRelabel a b) := by
  intro i j hij
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [portRelabel,thirdPort,Fin.ext_iff] at *

/-- Normalize arbitrary distinct incoming/outgoing ports in each triangle.
No matching uniqueness or extra graph structure is required. -/
theorem triangleRing_of_ports {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (f : Fin r × Fin 3 → V) (hf : Function.Injective f)
    (triangle : ∀ i a b, a ≠ b → G.Adj (f (i,a)) (f (i,b)))
    (incoming outgoing : Fin r → Fin 3)
    (distinct : ∀ i, incoming i ≠ outgoing i)
    (matching : ∀ i j : Fin r,
      (j.val=i.val+1 ∨ (i.val+1=r ∧ j.val=0)) →
      G.Adj (f (i,outgoing i)) (f (j,incoming j))) : TriangleRing G r := by
  let relabel : Fin r × Fin 3 → Fin r × Fin 3 :=
    fun x => (x.1, portRelabel (incoming x.1) (outgoing x.1) x.2)
  have hinj : Function.Injective relabel := by
    intro x y h
    have hfirst := congrArg (fun z : Fin r × Fin 3 => z.1) h
    change x.1=y.1 at hfirst
    apply Prod.ext hfirst
    have hsecond := congrArg Prod.snd h
    dsimp [relabel] at hsecond
    rw [← hfirst] at hsecond
    exact portRelabel_injective _ _ (distinct _) hsecond
  refine ⟨f ∘ relabel, hf.comp hinj, ?_, ?_⟩
  · intro i a b hab
    apply triangle
    exact fun h => hab (portRelabel_injective _ _ (distinct i) h)
  · intro i j hnext
    simpa [Function.comp_def,relabel] using matching i j hnext


end PSLTriangle
end


-- Source: PSLTriangleMatching.lean
section

namespace PSLTriangle

def ringNext {r : ℕ} (hr : 0 < r) (i : Fin r) : Fin r :=
  if h : i.val+1<r then ⟨i.val+1,h⟩ else ⟨0,hr⟩

def ringPrev {r : ℕ} (hr : 0 < r) (i : Fin r) : Fin r :=
  if i.val=0 then ⟨r-1,by omega⟩ else ⟨i.val-1,by omega⟩

theorem ringNext_step {r : ℕ} (hr : 0 < r) (i : Fin r) :
    (ringNext hr i).val=i.val+1 ∨ (i.val+1=r ∧ (ringNext hr i).val=0) := by
  unfold ringNext
  split_ifs <;> simp_all <;> omega

theorem ringNext_eq_of_step {r : ℕ} (hr : 0 < r) (i j : Fin r)
    (h : j.val=i.val+1 ∨ (i.val+1=r ∧ j.val=0)) : ringNext hr i=j := by
  apply Fin.ext
  simp only [ringNext]
  split_ifs <;> simp_all <;> omega

theorem ringNext_prev {r : ℕ} (hr : 0 < r) (i : Fin r) :
    ringNext hr (ringPrev hr i)=i := by
  apply Fin.ext
  simp only [ringNext,ringPrev]
  split_ifs <;> dsimp at * <;> simp_all <;> omega

theorem ringPrev_next_ne {r : ℕ} (hr : 3 ≤ r) (i : Fin r) :
    ringPrev (by omega : 0<r) i ≠ ringNext (by omega : 0<r) i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ringPrev,ringNext] at hv
  split_ifs at hv <;> simp_all <;> omega

/-- An involutive matching along a simple ring of at least three triangle
fibers automatically uses different incoming and outgoing ports. -/
theorem triangleRing_of_involutive_matching {V : Type*} (G : SimpleGraph V)
    {r : ℕ} (hr : 3 ≤ r)
    (f : Fin r × Fin 3 → V) (hf : Function.Injective f)
    (triangle : ∀ i a b, a ≠ b → G.Adj (f (i,a)) (f (i,b)))
    (mate : V → V) (hinv : Function.Involutive mate)
    (hmate : ∀ x, G.Adj x (mate x))
    (edges : ∀ i j : Fin r,
      (j.val=i.val+1 ∨ (i.val+1=r ∧ j.val=0)) →
      ∃ a b : Fin 3, mate (f (i,a))=f (j,b)) : TriangleRing G r := by
  classical
  have hpos : 0<r := by omega
  choose outgoing arrival hedge using fun i => edges i (ringNext hpos i) (ringNext_step hpos i)
  let incoming : Fin r → Fin 3 := fun i => arrival (ringPrev hpos i)
  have incoming_mate (i : Fin r) :
      mate (f (i,incoming i))=f (ringPrev hpos i,outgoing (ringPrev hpos i)) := by
    have h := congrArg mate (hedge (ringPrev hpos i))
    rw [hinv,ringNext_prev] at h
    exact h.symm
  have distinct (i : Fin r) : incoming i ≠ outgoing i := by
    intro heq
    have h := incoming_mate i
    rw [heq,hedge i] at h
    have he := congrArg (fun z : Fin r × Fin 3 => z.1) (hf h)
    exact ringPrev_next_ne hr i he.symm
  apply triangleRing_of_ports G f hf triangle incoming outgoing distinct
  intro i j hstep
  have hnext := ringNext_eq_of_step hpos i j hstep
  have hm := hmate (f (j,incoming j))
  rw [incoming_mate] at hm
  have hprev : ringPrev hpos j=i := by
    have hh := ringNext_prev hpos j
    have hi := ringNext_step hpos (ringPrev hpos j)
    have hj := ringNext_step hpos i
    rw [hh] at hi
    rw [hnext] at hj
    apply Fin.ext
    omega
  simpa only [hprev] using hm.symm


end PSLTriangle
end


-- Source: PSLTriangleSplice.lean
section

namespace PSLTriangle
open SimpleGraph

def CyclicAdjacent {Q : Type*} (G : SimpleGraph Q) {n : ℕ} (f : Fin n → Q) : Prop :=
  ∀ i j, i.val + 1 = j.val ∨ (i.val + 1 = n ∧ j.val = 0) → G.Adj (f i) (f j)

private def nextIndex {p : ℕ} (hp : 0 < p) (i : Fin p) : Fin p :=
  if h : i.val + 1 < p then ⟨i.val + 1, h⟩ else ⟨0, hp⟩

private theorem nextIndex_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (nextIndex hp) := by
  intro i j he
  have hv := congrArg Fin.val he
  simp only [nextIndex] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp only [Fin.val_mk] at hv <;> omega

private theorem nextIndex_adj {Q : Type*} {p : ℕ} (hp : 0 < p)
    (G : SimpleGraph Q) (f : Fin p → Q) (hf : CyclicAdjacent G f)
    (i j : Fin p) (hij : i.val + 1 = j.val) :
    G.Adj (f (nextIndex hp i)) (f (nextIndex hp j)) := by
  have hi := i.isLt
  have hj := j.isLt
  apply hf (nextIndex hp i) (nextIndex hp j)
  simp only [nextIndex]
  split_ifs <;> dsimp <;> omega

def spliceSequence {Q : Type*} {p : ℕ} (hp : 5 ≤ p)
    (C D E : Fin p → Q) (i : Fin (3 * p - 4)) : Q :=
  if h : i.val < p then D (nextIndex (by omega) ⟨i.val, h⟩)
  else if h' : i.val < 2 * p then
    E (nextIndex (by omega) ⟨i.val - p, by omega⟩)
  else C ⟨i.val - 2 * p + 4, by omega⟩

/-- Splice three rings at two disjoint central edges. Intersection hypotheses
refer to vertex equality and therefore permit parallel edges in an underlying
quotient presentation; the graph relation itself need not encode edge IDs. -/
theorem three_cycle_splice {Q : Type*} {p : ℕ} (hp : 5 ≤ p)
    (G : SimpleGraph Q) (C D E : Fin p → Q)
    (hc : Function.Injective C) (hd : Function.Injective D) (he : Function.Injective E)
    (cd : ∀ i j, C i = D j → i.val = 0 ∨ i.val = 1)
    (ce : ∀ i j, C i = E j → i.val = 2 ∨ i.val = 3)
    (de : ∀ i j, D i ≠ E j)
    (d0 : D ⟨0, by omega⟩ = C ⟨1, by omega⟩)
    (d1 : D ⟨1, by omega⟩ = C ⟨0, by omega⟩)
    (e0 : E ⟨0, by omega⟩ = C ⟨3, by omega⟩)
    (e1 : E ⟨1, by omega⟩ = C ⟨2, by omega⟩)
    (hca : CyclicAdjacent G C) (hda : CyclicAdjacent G D) (hea : CyclicAdjacent G E) :
    Function.Injective (spliceSequence hp C D E) ∧
      CyclicAdjacent G (spliceSequence hp C D E) := by
  have pp : 0 < p := by omega
  constructor
  · intro i j hij
    simp only [spliceSequence] at hij
    split_ifs at hij with hi hi' hj hj'
    all_goals try { exact Fin.ext (by
      have hv := congrArg Fin.val (nextIndex_injective pp (hd hij))
      simpa using hv) }
    all_goals try { exact False.elim (de _ _ hij) }
    all_goals try { exact False.elim (de _ _ hij.symm) }
    all_goals try { have hh := cd _ _ hij.symm; simp only [Fin.val_mk] at hh; omega }
    all_goals try { have hh := cd _ _ hij; simp only [Fin.val_mk] at hh; omega }
    all_goals try { have hh := ce _ _ hij.symm; simp only [Fin.val_mk] at hh; omega }
    all_goals try { have hh := ce _ _ hij; simp only [Fin.val_mk] at hh; omega }
    all_goals try
      have hv := congrArg Fin.val (nextIndex_injective pp (he hij))
      apply Fin.ext
      simp only [Fin.val_mk] at hv
      omega
    all_goals try
      have hv := congrArg Fin.val (hc hij)
      apply Fin.ext
      simp only [Fin.val_mk] at hv
      omega
  · intro i j hij
    simp only [spliceSequence]
    split_ifs with hi hj hj' hi' hj hj'
    all_goals try omega
    all_goals try { apply nextIndex_adj pp G D hda; simp only [Fin.val_mk]; omega }
    all_goals try { apply nextIndex_adj pp G E hea; simp only [Fin.val_mk]; omega }
    all_goals try { apply hca; simp only [Fin.val_mk]; omega }
    all_goals
      simp only [nextIndex]
      split_ifs
      all_goals try omega
      all_goals
        try simp only [Fin.val_mk] at *
        try
          have hjv : j.val = p := by omega
          simpa only [hjv, Nat.sub_self, Nat.zero_add, d0, e1] using
            hca ⟨1, by omega⟩ ⟨2, by omega⟩ (Or.inl rfl)
        try
          rw [e0]
          apply hca
          left
          dsimp
          omega
        try
          have hjv : j.val = 0 := by omega
          simp only [hjv, Nat.zero_add, d1]
          apply hca
          right
          constructor
          · dsimp; omega
          · rfl

end PSLTriangle
end


-- Source: PSLTriangleQuotientGraph.lean
section

namespace PSLTriangle
open scoped MatrixGroups
variable {F : Type*} [Field F]

abbrev FamilyCosets (F : Type*) [Field F] := TriangleCosets (aP : PSL(2,F))

def cosetGraph (F : Type*) [Field F] : SimpleGraph (FamilyCosets F) :=
  SimpleGraph.fromRel (fun q r => ∃ x : PSL(2,F),
    (x : FamilyCosets F) = q ∧ ((x*bP : PSL(2,F)) : FamilyCosets F) = r)

theorem familyCoset_mul_power (x : PSL(2,F)) (k : ℕ) :
    ((x*aP^k : PSL(2,F)) : FamilyCosets F) = (x : FamilyCosets F) := by
  apply QuotientGroup.mk_mul_of_mem
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem coset_eq_iff_exists_triangle_power (x y : PSL(2,F)) :
    (x : FamilyCosets F) = (y : FamilyCosets F) ↔
      ∃ k : Fin 3, y = x*aP^k.val := by
  rw [triangleCosets_eq_iff _ _ _ aP_cube aP_ne_one]
  constructor
  · rintro (he | he | he)
    · exact ⟨0, by simpa using (inv_mul_eq_iff_eq_mul.mp he)⟩
    · exact ⟨1, by simpa using (inv_mul_eq_iff_eq_mul.mp he)⟩
    · exact ⟨2, by simpa [pow_two] using (inv_mul_eq_iff_eq_mul.mp he)⟩
  · rintro ⟨k,rfl⟩
    fin_cases k <;> simp [pow_two]

theorem triangleRing_of_coset_cycle (htwo : (2 : F) ≠ 0)
    {r : ℕ} (hr : 3 ≤ r) (C : Fin r → FamilyCosets F)
    (hC : Function.Injective C) (hAdj : CyclicAdjacent (cosetGraph F) C) :
    TriangleRing (familyGraph F) r := by
  classical
  let rep : Fin r → PSL(2,F) := fun i => (C i).out
  have hrep (i : Fin r) : ((rep i) : FamilyCosets F) = C i := Quotient.out_eq' _
  let f : Fin r × Fin 3 → PSL(2,F) := fun x => rep x.1 * aP^x.2.val
  have hfcoset (i : Fin r) (k : Fin 3) : ((f (i,k)) : FamilyCosets F) = C i :=
    (familyCoset_mul_power _ _).trans (hrep i)
  have hf : Function.Injective f := by
    rintro ⟨i,k⟩ ⟨j,l⟩ he
    have hij : i=j := hC (by
      rw [← hfcoset i k, ← hfcoset j l]
      exact congrArg (fun x : PSL(2,F) => (x : FamilyCosets F)) he)
    subst j
    have hp : (aP : PSL(2,F))^k.val = aP^l.val := mul_left_cancel he
    have hb : baseFiber ((0:F),k) = baseFiber (0,l) := by
      simp only [baseFiber, hp]
    have hkl := congrArg Prod.snd (baseFiber_injective htwo hb)
    exact Prod.ext rfl hkl
  apply triangleRing_of_involutive_matching (familyGraph F) hr f hf
    (mate := fun x => x*bP) (hinv := family_matching_involutive)
    (hmate := familyGraph_matching_adj)
  · intro i k l hkl
    have ht := baseFiber_triangle_adj htwo (0:F) k l hkl
    simp only [baseFiber, uP_zero, one_mul] at ht
    exact (SimpleGraph.mulCayley_adj_mul_iff_right).mpr ht
  · intro i j hstep
    have hadj := hAdj i j (by rcases hstep with h | h; exact Or.inl h.symm; exact Or.inr h)
    rw [cosetGraph, SimpleGraph.fromRel_adj] at hadj
    have hedge : ∃ x : PSL(2,F), (x : FamilyCosets F)=C i ∧
        ((x*bP : PSL(2,F)) : FamilyCosets F)=C j := by
      rcases hadj.2 with h | h
      · exact h
      · obtain ⟨x,hx,hy⟩ := h
        refine ⟨x*bP,hy,?_⟩
        simpa [mul_assoc,bP_square] using hx
    obtain ⟨x,hx,hy⟩ := hedge
    obtain ⟨k,hk⟩ := (coset_eq_iff_exists_triangle_power (rep i) x).mp ((hrep i).trans hx.symm)
    obtain ⟨l,hl⟩ := (coset_eq_iff_exists_triangle_power (rep j) (x*bP)).mp
      ((hrep j).trans hy.symm)
    exact ⟨k,l,by change (rep i*aP^k.val)*bP=rep j*aP^l.val; rw [← hk,hl]⟩

end PSLTriangle
end


-- Source: PSLTriangleBaseRing.lean
section

namespace PSLTriangle

open scoped MatrixGroups

theorem zmod_two_ne_zero {p : ℕ} (hfive : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hv := ZMod.val_natCast_of_lt (n := p) (a := 2) (by omega)
  rw [show ((2 : ℕ) : ZMod p)=0 from h] at hv
  simp at hv

theorem zmod_three_ne_zero {p : ℕ} (hfive : 5 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have hv := ZMod.val_natCast_of_lt (n := p) (a := 3) (by omega)
  rw [show ((3 : ℕ) : ZMod p)=0 from h] at hv
  simp at hv

theorem successor_cast_eq {p : ℕ} (i j : Fin p)
    (h : j.val=i.val+1 ∨ (i.val+1=p ∧ j.val=0)) :
    (j.val : ZMod p)=(i.val : ZMod p)+1 := by
  rcases h with h | ⟨h,hj⟩
  · rw [h,Nat.cast_add,Nat.cast_one]
  · have hc := congrArg (fun n : ℕ => (n : ZMod p)) h
    simpa [Nat.cast_add,hj] using hc.symm

theorem fin_zmod_injective (p : ℕ) :
    Function.Injective (fun i : Fin p => (i.val : ZMod p)) := by
  intro i j h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt i.isLt,ZMod.val_natCast_of_lt j.isLt] at hv
  exact Fin.ext hv

theorem base_triangle_ring (p : ℕ) [Fact (Nat.Prime p)] (hfive : 5 ≤ p) :
    TriangleRing (familyGraph (ZMod p)) p := by
  let f : Fin p × Fin 3 → PSL(2,ZMod p) :=
    fun x => baseFiber ((x.1.val : ZMod p),x.2)
  have hf : Function.Injective f := by
    intro x y h
    have he := baseFiber_injective (zmod_two_ne_zero hfive) h
    exact Prod.ext
      (fin_zmod_injective p (congrArg (fun z : ZMod p × Fin 3 => z.1) he))
      (congrArg (fun z : ZMod p × Fin 3 => z.2) he)
  refine ⟨f,hf,?_,?_⟩
  · intro i a b hab
    exact baseFiber_triangle_adj (zmod_two_ne_zero hfive) _ a b hab
  · intro i j hstep
    have he : f (i,1)*bP=f (j,0) := by
      dsimp [f,baseFiber]
      simp only [pow_one,pow_zero,mul_one]
      rw [mul_assoc,aP_mul_bP,← uP_add,successor_cast_eq i j hstep]
    simpa only [he] using familyGraph_matching_adj (f (i,1))


end PSLTriangle
end


-- Source: PSLTriangleQuotientCycles.lean
section

namespace PSLTriangle
open scoped MatrixGroups

variable {F : Type*} [Field F]

theorem familyCoset_left_mul_eq_iff (g x y : PSL(2,F)) :
    ((g*x : PSL(2,F)) : FamilyCosets F) = ((g*y : PSL(2,F)) : FamilyCosets F) ↔
      (x : FamilyCosets F) = (y : FamilyCosets F) := by
  rw [QuotientGroup.eq, QuotientGroup.eq]
  simp [mul_assoc]

theorem unipotentCoset_injective (htwo : (2 : F) ≠ 0) :
    Function.Injective (fun t : F => (uP t : FamilyCosets F)) := by
  intro s t h
  obtain ⟨k,hk⟩ := (coset_eq_iff_exists_triangle_power (uP s) (uP t)).mp h
  have hh : baseFiber (t,(0 : Fin 3)) = baseFiber (s,k) := by
    simpa [baseFiber] using hk
  exact (congrArg Prod.fst (baseFiber_injective htwo hh)).symm

def translatedCycle {p : ℕ} [Fact (Nat.Prime p)] (g : PSL(2,ZMod p))
    (i : Fin p) : FamilyCosets (ZMod p) :=
  ((g * uP (i.val : ZMod p) : PSL(2,ZMod p)) : FamilyCosets (ZMod p))

def baseCosetCycle (p : ℕ) [Fact (Nat.Prime p)] (i : Fin p) :
    FamilyCosets (ZMod p) := (uP (i.val : ZMod p) : FamilyCosets (ZMod p))

theorem translatedCycle_injective {p : ℕ} [Fact (Nat.Prime p)] (hp : 5 ≤ p)
    (g : PSL(2,ZMod p)) : Function.Injective (translatedCycle g) := by
  intro i j h
  apply fin_zmod_injective p
  apply unipotentCoset_injective (zmod_two_ne_zero hp)
  exact (familyCoset_left_mul_eq_iff g _ _).mp h

theorem baseCosetCycle_injective {p : ℕ} [Fact (Nat.Prime p)] (hp : 5 ≤ p) :
    Function.Injective (baseCosetCycle p) := by
  intro i j h
  exact fin_zmod_injective p (unipotentCoset_injective (zmod_two_ne_zero hp) h)

theorem translatedCycle_cyclicAdjacent {p : ℕ} [Fact (Nat.Prime p)] (hp : 5 ≤ p)
    (g : PSL(2,ZMod p)) : CyclicAdjacent (cosetGraph (ZMod p)) (translatedCycle g) := by
  intro i j hij
  have hne : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    omega
  apply (SimpleGraph.fromRel_adj _ _ _).mpr
  refine ⟨fun h => hne (translatedCycle_injective hp g h), Or.inl ?_⟩
  refine ⟨g * uP (i.val : ZMod p) * aP, ?_, ?_⟩
  · simpa only [pow_one, translatedCycle] using
      familyCoset_mul_power (g * uP (i.val : ZMod p)) 1
  · have hj : (j.val : ZMod p) = (i.val : ZMod p) + 1 :=
      successor_cast_eq i j (by rcases hij with h | h; exact Or.inl h.symm; exact Or.inr h)
    dsimp [translatedCycle]
    congr 1
    rw [mul_assoc, aP_mul_bP, mul_assoc, ← uP_add, hj]

theorem baseCosetCycle_cyclicAdjacent {p : ℕ} [Fact (Nat.Prime p)] (hp : 5 ≤ p) :
    CyclicAdjacent (cosetGraph (ZMod p)) (baseCosetCycle p) := by
  simpa only [CyclicAdjacent, translatedCycle, one_mul, baseCosetCycle] using
    translatedCycle_cyclicAdjacent hp (1 : PSL(2,ZMod p))

end PSLTriangle
end


-- Source: PSLTriangleFamily.lean
section

namespace PSLTriangle

open scoped MatrixGroups

variable {p : ℕ} [Fact (Nat.Prime p)]

private theorem fin_cast_eq_nat (i : Fin p) (n : ℕ) (hn : n < p)
    (he : (i.val : ZMod p) = (n : ZMod p)) : i.val = n := by
  have hi : i = ⟨n,hn⟩ := fin_zmod_injective p he
  exact congrArg Fin.val hi

theorem second_triangle_ring (hp : 5 ≤ p) :
    TriangleRing (familyGraph (ZMod p)) (3*p-4) := by
  let C := baseCosetCycle p
  let D := translatedCycle (hP : PSL(2,ZMod p))
  let E := translatedCycle (uP 2*hP : PSL(2,ZMod p))
  have h2 := zmod_two_ne_zero hp
  have h3 := zmod_three_ne_zero hp
  have cd : ∀ i j, C i = D j → i.val=0 ∨ i.val=1 := by
    intro i j he
    have hx := first_coset_intersection h2 (i.val : ZMod p) (j.val : ZMod p) he
    rcases hx with hx | hx
    · exact Or.inl (fin_cast_eq_nat i 0 (by omega) (by simpa using hx.1))
    · exact Or.inr (fin_cast_eq_nat i 1 (by omega) (by simpa using hx.1))
  have ce : ∀ i j, C i = E j → i.val=2 ∨ i.val=3 := by
    intro i j he
    have he' : (uP ((i.val : ZMod p)-2) : FamilyCosets (ZMod p)) =
        ((hP*uP (j.val : ZMod p) : PSL(2,ZMod p)) : FamilyCosets (ZMod p)) := by
      apply (familyCoset_left_mul_eq_iff (uP 2) _ _).mp
      have hu : (uP 2 : PSL(2,ZMod p))*uP ((i.val : ZMod p)-2) =
          uP (i.val : ZMod p) := by
        rw [← uP_add]
        congr 1
        ring
      simpa only [hu, C, E, baseCosetCycle, translatedCycle, mul_assoc] using he
    have hx := first_coset_intersection h2 ((i.val : ZMod p)-2) (j.val : ZMod p) he'
    rcases hx with hx | hx
    · left
      apply fin_cast_eq_nat i 2 (by omega)
      linear_combination hx.1
    · right
      apply fin_cast_eq_nat i 3 (by omega)
      linear_combination hx.1
  have de : ∀ i j, D i ≠ E j := by
    intro i j
    exact outer_cosets_disjoint h2 h3 (i.val : ZMod p) (j.val : ZMod p)
  have d0 : D ⟨0,by omega⟩ = C ⟨1,by omega⟩ := by
    have he := (familyCoset_mul_power (hP : PSL(2,ZMod p)) 1).symm
    simpa [D, C, translatedCycle, baseCosetCycle, uP_zero, hP_mul_aP] using he
  have d1 : D ⟨1,by omega⟩ = C ⟨0,by omega⟩ := by
    have he := familyCoset_mul_power (1 : PSL(2,ZMod p)) 1
    simpa [D, C, translatedCycle, baseCosetCycle, uP_zero, hP_mul_uP_one] using he
  have e0 : E ⟨0,by omega⟩ = C ⟨3,by omega⟩ := by
    have he := (familyCoset_mul_power (uP 2*hP : PSL(2,ZMod p)) 1).symm
    have hsum : (2 : ZMod p)+1=3 := by ring
    simpa [E, C, translatedCycle, baseCosetCycle, uP_zero, mul_assoc,
      hP_mul_aP, ← uP_add, hsum] using he
  have e1 : E ⟨1,by omega⟩ = C ⟨2,by omega⟩ := by
    have he := familyCoset_mul_power (uP 2 : PSL(2,ZMod p)) 1
    simpa [E, C, translatedCycle, baseCosetCycle, mul_assoc, hP_mul_uP_one] using he
  obtain ⟨hsinj,hsadj⟩ := three_cycle_splice hp (cosetGraph (ZMod p)) C D E
    (baseCosetCycle_injective hp) (translatedCycle_injective hp hP)
    (translatedCycle_injective hp (uP 2*hP)) cd ce de d0 d1 e0 e1
    (baseCosetCycle_cyclicAdjacent hp) (translatedCycle_cyclicAdjacent hp hP)
    (translatedCycle_cyclicAdjacent hp (uP 2*hP))
  exact triangleRing_of_coset_cycle h2 (by omega) _ hsinj hsadj

/-- Specific-generator PSL family theorem; not unrestricted EGC. -/
theorem psl_triangle_family (hp : 5 ≤ p) :
    ∃ (k : ℕ) (v : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
      (walk : (familyGraph (ZMod p)).Walk v v),
      2 ≤ k ∧ walk.IsCycle ∧ walk.length = 2^k ∧ walk.length < 8*p := by
  exact dyadic_cycle_of_two_triangle_rings (familyGraph (ZMod p)) p
    Fact.out hp (base_triangle_ring p hp) (second_triangle_ring hp)


end PSLTriangle
end


-- Source: PSLTriangleStatementCheck.lean
section

namespace PSLTriangleStatementCheck
open Matrix
open scoped MatrixGroups

/-- Independent explicit-matrix export: no family graph or generator aliases
occur in the statement. -/
theorem explicit_matrix_family (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) :
    ∃ (k : ℕ) (v : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
      (walk : (SimpleGraph.mulCayley
        ({(QuotientGroup.mk
            (⟨!![0, -1; 1, 1], by simp [Matrix.det_fin_two]⟩ :
              Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)),
          (QuotientGroup.mk
            (⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩ :
              Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))} :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))).Walk v v),
      2 ≤ k ∧ walk.IsCycle ∧ walk.length = 2 ^ k ∧ walk.length < 8 * p := by
  exact PSLTriangle.psl_triangle_family hp

end PSLTriangleStatementCheck
end


theorem proof (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) :
    ∃ (k : ℕ) (v : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
      (walk : (SimpleGraph.mulCayley
        ({(QuotientGroup.mk
            (⟨!![0, -1; 1, 1], by simp [Matrix.det_fin_two]⟩ :
              Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)),
          (QuotientGroup.mk
            (⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩ :
              Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))} :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))).Walk v v),
      2 ≤ k ∧ walk.IsCycle ∧ walk.length = 2 ^ k ∧ walk.length < 8 * p := by
  exact PSLTriangleStatementCheck.explicit_matrix_family p hp


#print axioms proof
end Submissions.Erdos64PSLTriangleFamily.Cole
