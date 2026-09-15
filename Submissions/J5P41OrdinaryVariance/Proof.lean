import Init

namespace Submissions.J5P41OrdinaryVariance.Proof

def squares (xs : List Int) : Int := (xs.map (fun x => x*x)).sum
def rowEnergy (a : Int) (xs : List Int) : Int :=
  (xs.map (fun x => (x-a)*(x-a))).sum
def pairEnergy : List Int → Int
  | [] => 0
  | x::xs => rowEnergy x xs + pairEnergy xs

private theorem row_expansion (a : Int) (xs : List Int) :
    rowEnergy a xs = squares xs - 2*a*xs.sum + (xs.length : Int)*a*a := by
  induction xs with
  | nil => simp [rowEnergy, squares]
  | cons x xs ih =>
    simp only [rowEnergy, squares, List.map_cons, List.sum_cons,
      List.length_cons, Int.natCast_add, Int.natCast_one] at *
    grind

/- Exact pairwise formula; no Sidon or spectral premise is hidden here. -/
theorem pair_variance (xs : List Int) :
    pairEnergy xs = (xs.length : Int)*squares xs-xs.sum*xs.sum := by
  induction xs with
  | nil => simp [pairEnergy, squares]
  | cons x xs ih =>
    simp only [pairEnergy]
    rw [row_expansion, ih]
    simp only [squares, List.map_cons, List.sum_cons, List.length_cons,
      Int.natCast_add, Int.natCast_one]
    grind

def ordinarySums : List Int → List Int
  | [] => []
  | x::xs => (x+x)::((xs.map (fun y => x+y)) ++ ordinarySums xs)

def witness : List Int := [0,1,4,10,12,17,31]
def scaledDisplacements : List Int := [0,-36,-58,-59,-88,-96,-41]

/- Includes doubled summands, so it checks the ordinary Sidon definition. -/
theorem witness_ordinary_sidon : (ordinarySums witness).Nodup := by decide

/- V = pairEnergy(b)/7^3 = 130, versus V_perfect = 774/7.
   The explicit affine-displacement correspondence is also checked. -/
theorem witness_displacements :
    scaledDisplacements = (witness.zipIdx.map (fun p => 7*p.1-43*(p.2 : Int))) := by
  decide

theorem witness_exceeds_perfect_variance :
    pairEnergy scaledDisplacements = 44590 ∧ 7*44590 > 774*343 := by
  decide

theorem witness_rotation_not_ordinary_sidon :
    ¬ (ordinarySums [0,6,8,13,27,39,40]).Nodup := by decide

/- A symmetric signed defect has opposite quadratic and tent moments
   once its first moment is zero. This elementary reduction itself does
   not establish symmetry or zero mass for an arbitrary supplied list. -/
theorem signed_moment_identity (M : Int) (xs : List (Int × Int))
    (first : (xs.map (fun p => p.1*p.2)).sum = 0) :
    (xs.map (fun p => p.1*p.1*p.2)).sum =
      -(xs.map (fun p => p.1*(M-p.1)*p.2)).sum := by
  have h : (xs.map (fun p => p.1*p.1*p.2)).sum +
      (xs.map (fun p => p.1*(M-p.1)*p.2)).sum =
      M*(xs.map (fun p => p.1*p.2)).sum := by
    clear first
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      grind
  rw [first] at h
  omega

theorem solves :
  ((ordinarySums witness).Nodup) ∧
  (scaledDisplacements = (witness.zipIdx.map (fun p => 7*p.1-43*(p.2 : Int)))) ∧
  (pairEnergy scaledDisplacements = 44590 ∧ 7*44590 > 774*343) ∧
  (¬ (ordinarySums [0,6,8,13,27,39,40]).Nodup) := by
  exact ⟨@witness_ordinary_sidon, @witness_displacements, @witness_exceeds_perfect_variance, @witness_rotation_not_ordinary_sidon⟩

end Submissions.J5P41OrdinaryVariance.Proof
