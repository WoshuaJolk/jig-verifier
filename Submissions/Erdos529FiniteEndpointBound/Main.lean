import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

namespace Submissions.Erdos529FiniteEndpointBound.Main

/-!
The direction-word and vertex-path descriptions of a finite square-lattice walk
are equivalent. Point, step, position, and IsSelfAvoidingWalk are copied exactly
from the canonical definitions for Jig #289; only the namespace differs.
-/

namespace PlanarSAWDirectionBridge

abbrev Point := ℤ × ℤ

def step (d : Fin 4) : Point :=
  if d = 0 then (1, 0)
  else if d = 1 then (-1, 0)
  else if d = 2 then (0, 1)
  else (0, -1)

def position {n : ℕ} (s : Fin n → Fin 4) (t : Fin (n + 1)) : Point :=
  let ht : t.val ≤ n := Nat.le_of_lt_succ t.isLt
  ∑ i : Fin t.val, step (s (Fin.castLE ht i))

def IsSelfAvoidingWalk {n : ℕ} (s : Fin n → Fin 4) : Prop :=
  Function.Injective (position s)

def GridAdjacent (x y : Point) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
  (y.1 = x.1 ∧ y.2 = x.2 - 1)

def HasUnitSteps {n : ℕ} (p : Fin (n + 1) → Point) : Prop :=
  ∀ i : Fin n, GridAdjacent (p i.castSucc) (p i.succ)

theorem step_injective : Function.Injective step := by
  unfold Function.Injective
  decide

theorem position_zero {n : ℕ} (s : Fin n → Fin 4) :
    position s 0 = (0, 0) := by
  unfold position
  apply Finset.sum_eq_zero
  intro i _
  exact Fin.elim0 i

theorem position_succ {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) :
    position s i.succ = position s i.castSucc + step (s i) := by
  simp only [position, Fin.val_succ, Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc]
  congr 1

theorem position_injective {n : ℕ} :
    Function.Injective (@position n) := by
  intro s t h
  funext i
  apply step_injective
  have hnext := congrFun h i.succ
  have hcurrent := congrFun h i.castSucc
  rw [position_succ, position_succ, hcurrent] at hnext
  exact add_left_cancel hnext

theorem gridAdjacent_iff_exists_step (x y : Point) :
    GridAdjacent x y ↔ ∃ d : Fin 4, y = x + step d := by
  constructor
  · intro h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine ⟨0, ?_⟩
      apply Prod.ext
      · simpa [step] using h₁
      · simpa [step] using h₂
    · refine ⟨1, ?_⟩
      apply Prod.ext
      · simpa [step, sub_eq_add_neg] using h₁
      · simpa [step] using h₂
    · refine ⟨2, ?_⟩
      apply Prod.ext
      · simpa [step] using h₁
      · simpa [step] using h₂
    · refine ⟨3, ?_⟩
      apply Prod.ext
      · simpa [step] using h₁
      · simpa [step, sub_eq_add_neg] using h₂
  · rintro ⟨d, rfl⟩
    by_cases h₀ : d = 0
    · left
      simp [step, h₀]
    · by_cases h₁ : d = 1
      · right; left
        simp [step, h₁, sub_eq_add_neg]
      · by_cases h₂ : d = 2
        · right; right; left
          simp [step, h₂]
        · right; right; right
          simp [step, h₀, h₁, h₂, sub_eq_add_neg]

theorem position_hasUnitSteps {n : ℕ} (s : Fin n → Fin 4) :
    HasUnitSteps (position s) := by
  intro i
  exact (gridAdjacent_iff_exists_step _ _).mpr ⟨s i, position_succ s i⟩

/-- Every rooted unit-step vertex path is the partial-sum path of a direction
word. No self-avoidance assumption is needed for this representation theorem. -/
theorem exists_directionWord {n : ℕ} (p : Fin (n + 1) → Point)
    (hzero : p 0 = (0, 0)) (hsteps : HasUnitSteps p) :
    ∃ s : Fin n → Fin 4, position s = p := by
  classical
  have hd : ∀ i : Fin n, ∃ d : Fin 4, p i.succ = p i.castSucc + step d :=
    fun i => (gridAdjacent_iff_exists_step _ _).mp (hsteps i)
  let s : Fin n → Fin 4 := fun i => Classical.choose (hd i)
  have hs : ∀ i : Fin n, p i.succ = p i.castSucc + step (s i) :=
    fun i => Classical.choose_spec (hd i)
  refine ⟨s, ?_⟩
  funext t
  refine Fin.induction ?_ ?_ t
  · exact (position_zero s).trans hzero.symm
  · intro i hi
    rw [position_succ, hi, ← hs i]

theorem existsUnique_directionWord {n : ℕ} (p : Fin (n + 1) → Point)
    (hzero : p 0 = (0, 0)) (hsteps : HasUnitSteps p) :
    ∃! s : Fin n → Fin 4, position s = p := by
  obtain ⟨s, hs⟩ := exists_directionWord p hzero hsteps
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact position_injective (ht.trans hs.symm)

theorem exists_selfAvoidingWord {n : ℕ} (p : Fin (n + 1) → Point)
    (hzero : p 0 = (0, 0)) (hsteps : HasUnitSteps p)
    (hp : Function.Injective p) :
    ∃ s : Fin n → Fin 4, IsSelfAvoidingWalk s ∧ position s = p := by
  obtain ⟨s, hs⟩ := exists_directionWord p hzero hsteps
  refine ⟨s, ?_, hs⟩
  unfold IsSelfAvoidingWalk
  rw [hs]
  exact hp

theorem exists_directionWord_iff {n : ℕ} (p : Fin (n + 1) → Point) :
    (∃ s : Fin n → Fin 4, position s = p) ↔
      p 0 = (0, 0) ∧ HasUnitSteps p := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨position_zero s, position_hasUnitSteps s⟩
  · rintro ⟨hzero, hsteps⟩
    exact exists_directionWord p hzero hsteps

theorem exists_selfAvoidingWord_iff {n : ℕ} (p : Fin (n + 1) → Point) :
    (∃ s : Fin n → Fin 4, IsSelfAvoidingWalk s ∧ position s = p) ↔
      p 0 = (0, 0) ∧ HasUnitSteps p ∧ Function.Injective p := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨position_zero s, position_hasUnitSteps s, hs⟩
  · rintro ⟨hzero, hsteps, hp⟩
    exact exists_selfAvoidingWord p hzero hsteps hp

end PlanarSAWDirectionBridge


namespace PlanarSAWTailBound

theorem max_natAbs_le_euclidean (z : ℤ × ℤ) :
    ((max z.1.natAbs z.2.natAbs : ℕ) : ℝ) ≤
      Real.sqrt ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) := by
  rw [Nat.cast_max]
  apply max_le
  · rw [Nat.cast_natAbs, Int.cast_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  · rw [Nat.cast_natAbs, Int.cast_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

/-- The reflection counting inequality forces a lower bound for the first moment.
The high-endpoint set contributes both its baseline m and its excess above m. -/
theorem mean_sum_bound {α : Type*} (s : Finset α) (R : α → ℝ) (m : ℝ)
    (hm : 0 ≤ m) (hR : ∀ x ∈ s, 0 ≤ R x)
    (hcount : ((s.filter (fun x => R x ≤ m)).card : ℝ) ≤
      (m + 1) * ((s.filter (fun x => m * (m + 2) ≤ R x)).card : ℝ)) :
    m * s.card ≤ ∑ x ∈ s, R x := by
  classical
  have hpoint (x : α) (hx : x ∈ s) :
      m ≤ R x + (if R x ≤ m then m else 0) -
        (if m * (m + 2) ≤ R x then m * (m + 1) else 0) := by
    have hnonneg := hR x hx
    split_ifs <;> nlinarith [sq_nonneg m]
  have hsum := Finset.sum_le_sum (s := s) hpoint
  have hlow : (∑ x ∈ s, if R x ≤ m then m else 0) =
      ((s.filter (fun x => R x ≤ m)).card : ℝ) * m := by
    rw [← Finset.sum_filter]
    simp
  have hhigh : (∑ x ∈ s, if m * (m + 2) ≤ R x then m * (m + 1) else 0) =
      ((s.filter (fun x => m * (m + 2) ≤ R x)).card : ℝ) * (m * (m + 1)) := by
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hlow, hhigh,
    Finset.sum_const, nsmul_eq_mul] at hsum
  have hweighted := mul_le_mul_of_nonneg_left hcount hm
  nlinarith [hsum, hweighted]

theorem mean_bound {α : Type*} (s : Finset α) (R : α → ℝ) (m : ℝ)
    (hne : s.Nonempty) (hm : 0 ≤ m) (hR : ∀ x ∈ s, 0 ≤ R x)
    (hcount : ((s.filter (fun x => R x ≤ m)).card : ℝ) ≤
      (m + 1) * ((s.filter (fun x => m * (m + 2) ≤ R x)).card : ℝ)) :
    m ≤ (∑ x ∈ s, R x) / s.card := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hne
  exact (le_div_iff₀ hc).mpr (mean_sum_bound s R m hm hR hcount)

end PlanarSAWTailBound

namespace PlanarSAWDirectionBridge

noncomputable def walks (n : ℕ) : Finset (Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter IsSelfAvoidingWalk

noncomputable def endpointDistance {n : ℕ} (s : Fin n → Fin 4) : ℝ :=
  Real.sqrt (((position s (Fin.last n)).1 : ℝ)^2 +
             ((position s (Fin.last n)).2 : ℝ)^2)

noncomputable def expectedDistance (n : ℕ) : ℝ :=
  ((walks n).sum endpointDistance) / (walks n).card

def endpointNorm {n : ℕ} (s : Fin n → Fin 4) : ℕ :=
  max (position s (Fin.last n)).1.natAbs (position s (Fin.last n)).2.natAbs

theorem position_allEast {n : ℕ} (t : Fin (n + 1)) :
    position (fun _ : Fin n => (0 : Fin 4)) t = ((t.val : ℤ), 0) := by
  simp [position, step]

theorem walks_nonempty (n : ℕ) : (walks n).Nonempty := by
  classical
  refine ⟨fun _ => 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro a b h
  simp only [position_allEast, Prod.mk.injEq] at h
  apply Fin.ext
  exact_mod_cast h.1

theorem endpointNorm_le_distance {n : ℕ} (s : Fin n → Fin 4) :
    (endpointNorm s : ℝ) ≤ endpointDistance s :=
  PlanarSAWTailBound.max_natAbs_le_euclidean (position s (Fin.last n))


theorem expectedDistance_ge_of_counts (n m : ℕ)
    (hcount : ((walks n).filter (fun s => endpointNorm s ≤ m)).card ≤
      ((walks n).filter (fun s => m * (m + 2) ≤ endpointNorm s)).card * (m + 1)) :
    (m : ℝ) ≤ expectedDistance n := by
  classical
  let R : (Fin n → Fin 4) → ℝ := fun s => endpointNorm s
  have hlow : (walks n).filter (fun s => R s ≤ (m : ℝ)) =
      (walks n).filter (fun s => endpointNorm s ≤ m) := by
    ext s
    simp [R]
  have hhigh : (walks n).filter (fun s => (m : ℝ) * ((m : ℝ) + 2) ≤ R s) =
      (walks n).filter (fun s => m * (m + 2) ≤ endpointNorm s) := by
    ext s
    simp only [Finset.mem_filter, R]
    norm_cast
  have hcountReal : (((walks n).filter (fun s => R s ≤ (m : ℝ))).card : ℝ) ≤
      ((m : ℝ) + 1) * (((walks n).filter
        (fun s => (m : ℝ) * ((m : ℝ) + 2) ≤ R s)).card : ℝ) := by
    rw [hlow, hhigh]
    have hcast := (Nat.cast_le (α := ℝ)).mpr hcount
    push_cast at hcast
    nlinarith [hcast]
  have hm := PlanarSAWTailBound.mean_bound (walks n) R (m : ℝ)
    (walks_nonempty n) (Nat.cast_nonneg m)
    (fun s _ => Nat.cast_nonneg (endpointNorm s)) hcountReal
  have hsum : (∑ s ∈ walks n, R s) ≤ (walks n).sum endpointDistance := by
    apply Finset.sum_le_sum
    intro s _
    exact endpointNorm_le_distance s
  exact hm.trans (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _))

end PlanarSAWDirectionBridge


/-!
Choose the first vertex of maximal lattice sup radius, then choose a coordinate
attaining that radius. The path has n+1 vertices, so it is nonempty even at n=0.
-/

namespace PlanarSAWMaximalCut

abbrev Point := ℤ × ℤ

def normInfNat (x : Point) : ℕ :=
  max x.1.natAbs x.2.natAbs

def coord (axis : Fin 2) (x : Point) : ℤ :=
  if axis = 0 then x.1 else x.2

/-- Ties are resolved in favour of the horizontal coordinate. -/
def maximalAxis (x : Point) : Fin 2 :=
  if x.1.natAbs = normInfNat x then 0 else 1

theorem coord_natAbs_le_normInfNat (axis : Fin 2) (x : Point) :
    (coord axis x).natAbs ≤ normInfNat x := by
  by_cases h : axis = 0
  · simpa only [coord, if_pos h, normInfNat] using
      Nat.le_max_left x.1.natAbs x.2.natAbs
  · simpa only [coord, if_neg h, normInfNat] using
      Nat.le_max_right x.1.natAbs x.2.natAbs

theorem maximalAxis_natAbs (x : Point) :
    (coord (maximalAxis x) x).natAbs = normInfNat x := by
  by_cases h : x.1.natAbs = normInfNat x
  · simp [maximalAxis, h, coord]
  · have hy : x.2.natAbs = normInfNat x := by
      rcases le_total x.1.natAbs x.2.natAbs with hxy | hyx
      · exact (max_eq_right hxy).symm
      · exact False.elim (h (max_eq_left hyx).symm)
    simpa [maximalAxis, h, coord] using hy

theorem maximalAxis_eq_zero_iff (x : Point) :
    maximalAxis x = 0 ↔ x.1.natAbs = normInfNat x := by
  simp [maximalAxis]

theorem maximalAxis_eq_one_of_not (x : Point)
    (h : x.1.natAbs ≠ normInfNat x) : maximalAxis x = 1 := by
  simp only [maximalAxis, if_neg h]

theorem exists_first_maximal_cut {n : ℕ} (p : Fin (n + 1) → Point) :
    ∃ L : Fin (n + 1),
      (∀ t, normInfNat (p t) ≤ normInfNat (p L)) ∧
      (∀ t, t < L → normInfNat (p t) < normInfNat (p L)) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (n + 1))) (fun t => normInfNat (p t))
    ⟨0, Finset.mem_univ 0⟩
  let S : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun t => normInfNat (p t) = normInfNat (p a))
  have hS : S.Nonempty := by
    refine ⟨a, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, and_self]
  obtain ⟨L, hL, hmin⟩ := Finset.exists_min_image S Fin.val hS
  have hLradius : normInfNat (p L) = normInfNat (p a) :=
    (Finset.mem_filter.mp hL).2
  have hmax : ∀ t, normInfNat (p t) ≤ normInfNat (p L) := by
    intro t
    rw [hLradius]
    exact ha t (Finset.mem_univ t)
  refine ⟨L, hmax, ?_⟩
  intro t ht
  have hle := hmax t
  have hne : normInfNat (p t) ≠ normInfNat (p L) := by
    intro heq
    have htS : t ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ t, heq.trans hLradius⟩
    have hLt := hmin t htS
    omega
  omega

theorem first_maximal_cut_unique {n : ℕ} (p : Fin (n + 1) → Point)
    (L K : Fin (n + 1))
    (hLmax : ∀ t, normInfNat (p t) ≤ normInfNat (p L))
    (hLbefore : ∀ t, t < L → normInfNat (p t) < normInfNat (p L))
    (hKmax : ∀ t, normInfNat (p t) ≤ normInfNat (p K))
    (hKbefore : ∀ t, t < K → normInfNat (p t) < normInfNat (p K)) : L = K := by
  have hnotLK : ¬ L < K := by
    intro h
    have hlt := hKbefore L h
    have hle := hLmax K
    omega
  have hnotKL : ¬ K < L := by
    intro h
    have hlt := hLbefore K h
    have hle := hKmax L
    omega
  omega

noncomputable def firstMaxCut {n : ℕ} (p : Fin (n + 1) → Point) : Fin (n + 1) :=
  Classical.choose (exists_first_maximal_cut p)

theorem firstMaxCut_max {n : ℕ} (p : Fin (n + 1) → Point) (t : Fin (n + 1)) :
    normInfNat (p t) ≤ normInfNat (p (firstMaxCut p)) :=
  (Classical.choose_spec (exists_first_maximal_cut p)).1 t

theorem firstMaxCut_before {n : ℕ} (p : Fin (n + 1) → Point)
    (t : Fin (n + 1)) (ht : t < firstMaxCut p) :
    normInfNat (p t) < normInfNat (p (firstMaxCut p)) :=
  (Classical.choose_spec (exists_first_maximal_cut p)).2 t ht

noncomputable def selectedAxis {n : ℕ} (p : Fin (n + 1) → Point) : Fin 2 :=
  maximalAxis (p (firstMaxCut p))

theorem selectedAxis_natAbs {n : ℕ} (p : Fin (n + 1) → Point) :
    (coord (selectedAxis p) (p (firstMaxCut p))).natAbs =
      normInfNat (p (firstMaxCut p)) :=
  maximalAxis_natAbs (p (firstMaxCut p))

theorem selectedAxis_before {n : ℕ} (p : Fin (n + 1) → Point)
    (t : Fin (n + 1)) (ht : t < firstMaxCut p) :
    (coord (selectedAxis p) (p t)).natAbs < normInfNat (p (firstMaxCut p)) :=
  lt_of_le_of_lt (coord_natAbs_le_normInfNat (selectedAxis p) (p t))
    (firstMaxCut_before p t ht)

theorem selectedAxis_le {n : ℕ} (p : Fin (n + 1) → Point)
    (t : Fin (n + 1)) :
    (coord (selectedAxis p) (p t)).natAbs ≤ normInfNat (p (firstMaxCut p)) :=
  le_trans (coord_natAbs_le_normInfNat (selectedAxis p) (p t)) (firstMaxCut_max p t)

theorem selectedAxis_after {n : ℕ} (p : Fin (n + 1) → Point)
    (t : Fin (n + 1)) (_ht : firstMaxCut p < t) :
    (coord (selectedAxis p) (p t)).natAbs ≤ normInfNat (p (firstMaxCut p)) :=
  selectedAxis_le p t

theorem selectedAxis_first_visit {n : ℕ} (p : Fin (n + 1) → Point)
    (t : Fin (n + 1)) (ht : t < firstMaxCut p) :
    coord (selectedAxis p) (p t) ≠ coord (selectedAxis p) (p (firstMaxCut p)) := by
  intro heq
  have hbefore := selectedAxis_before p t ht
  rw [heq, selectedAxis_natAbs p] at hbefore
  omega

theorem selectedAxis_eq_zero_iff {n : ℕ} (p : Fin (n + 1) → Point) :
    selectedAxis p = 0 ↔
      (p (firstMaxCut p)).1.natAbs = normInfNat (p (firstMaxCut p)) :=
  maximalAxis_eq_zero_iff (p (firstMaxCut p))

end PlanarSAWMaximalCut


namespace PlanarSAWPacking

/-- An injective lattice path in a square uses at most the square's vertices. -/
theorem length_le_box_card {n r : ℕ} (p : Fin (n + 1) → ℤ × ℤ)
    (hp : Function.Injective p)
    (hbox : ∀ t, -(r : ℤ) ≤ (p t).1 ∧ (p t).1 ≤ r ∧
      -(r : ℤ) ≤ (p t).2 ∧ (p t).2 ≤ r) :
    n + 1 ≤ (2 * r + 1) ^ 2 := by
  let I := Finset.Icc (-(r : ℤ)) (r : ℤ)
  have hI : I.card = 2 * r + 1 := by
    rw [Int.card_Icc]
    omega
  have hsub : Finset.univ.image p ⊆ I ×ˢ I := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    rcases hbox t with ⟨h₁, h₂, h₃, h₄⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h₁, h₂⟩,
      Finset.mem_Icc.mpr ⟨h₃, h₄⟩⟩
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hp, Finset.card_univ,
    Fintype.card_fin, Finset.card_product, hI, pow_two] using hcard

/-- A path longer than the number of square vertices must leave the square. -/
theorem exists_outside_box {n r : ℕ} (p : Fin (n + 1) → ℤ × ℤ)
    (hp : Function.Injective p) (hn : (2 * r + 1) ^ 2 < n + 1) :
    ∃ t, (p t).1 < -(r : ℤ) ∨ (r : ℤ) < (p t).1 ∨
      (p t).2 < -(r : ℤ) ∨ (r : ℤ) < (p t).2 := by
  by_contra h
  push Not at h
  have hbound := length_le_box_card p hp (fun t => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h t
    exact ⟨h₁, h₂, h₃, h₄⟩)
  omega

end PlanarSAWPacking


/-!
Coordinate reflection of a finite square-lattice path at its first maximum or
minimum. These deterministic lemmas do not assert an endpoint probability bound.
-/

namespace PlanarSAWSignedReflection

abbrev Point := ℤ × ℤ

def coord (axis : Fin 2) (x : Point) : ℤ := if axis = 0 then x.1 else x.2

def otherCoord (axis : Fin 2) (x : Point) : ℤ := if axis = 0 then x.2 else x.1

theorem point_ext {axis : Fin 2} {x y : Point}
    (h : coord axis x = coord axis y) (hother : otherCoord axis x = otherCoord axis y) :
    x = y := by
  by_cases ha : axis = 0
  · exact Prod.ext (by simpa [coord, ha] using h) (by simpa [otherCoord, ha] using hother)
  · exact Prod.ext (by simpa [otherCoord, ha] using hother) (by simpa [coord, ha] using h)

def coordinateReflection (axis : Fin 2) (H : ℤ) (x : Point) : Point :=
  if axis = 0 then (2 * H - x.1, x.2) else (x.1, 2 * H - x.2)

theorem reflection_coord (axis : Fin 2) (H : ℤ) (x : Point) :
    coord axis (coordinateReflection axis H x) = 2 * H - coord axis x := by
  by_cases ha : axis = 0 <;> simp [coord, coordinateReflection, ha]

theorem reflection_otherCoord (axis : Fin 2) (H : ℤ) (x : Point) :
    otherCoord axis (coordinateReflection axis H x) = otherCoord axis x := by
  by_cases ha : axis = 0 <;> simp [otherCoord, coordinateReflection, ha]

theorem coordinateReflection_involutive (axis : Fin 2) (H : ℤ) :
    Function.Involutive (coordinateReflection axis H) := by
  intro x
  apply point_ext (axis := axis)
  · rw [reflection_coord, reflection_coord]
    omega
  · rw [reflection_otherCoord, reflection_otherCoord]

theorem coordinateReflection_injective (axis : Fin 2) (H : ℤ) :
    Function.Injective (coordinateReflection axis H) := by
  intro x y h
  have hh := congrArg (coordinateReflection axis H) h
  simpa only [coordinateReflection_involutive axis H x,
    coordinateReflection_involutive axis H y] using hh

theorem coordinateReflection_fixed (axis : Fin 2) (H : ℤ) (x : Point)
    (hx : coord axis x = H) : coordinateReflection axis H x = x := by
  apply point_ext (axis := axis)
  · rw [reflection_coord, hx]
    omega
  · exact reflection_otherCoord axis H x

def reflectSuffix {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L t : Fin (n + 1)) : Point :=
  if t ≤ L then p t else coordinateReflection axis H (p t)

theorem reflectSuffix_of_le {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L t : Fin (n + 1)) (ht : t ≤ L) :
    reflectSuffix axis H p L t = p t := by
  simp only [reflectSuffix, if_pos ht]

theorem reflectSuffix_of_gt {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L t : Fin (n + 1)) (ht : L < t) :
    reflectSuffix axis H p L t = coordinateReflection axis H (p t) := by
  have hh : ¬ t ≤ L := by omega
  simp only [reflectSuffix, if_neg hh]

theorem reflectSuffix_involutive {n : ℕ} (axis : Fin 2) (H : ℤ)
    (L : Fin (n + 1)) :
    Function.Involutive (fun p : Fin (n + 1) → Point => reflectSuffix axis H p L) := by
  intro p
  funext t
  by_cases ht : t ≤ L
  · simp only [reflectSuffix, if_pos ht]
  · simp only [reflectSuffix, if_neg ht, coordinateReflection_involutive axis H (p t)]

theorem reflectSuffix_zero {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1)) :
    reflectSuffix axis H p L 0 = p 0 :=
  reflectSuffix_of_le axis H p L 0 (Fin.zero_le L)

theorem reflectSuffix_endpoint {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1)) (hcut : coord axis (p L) = H) :
    reflectSuffix axis H p L (Fin.last n) = coordinateReflection axis H (p (Fin.last n)) := by
  by_cases h : Fin.last n ≤ L
  · have heq : Fin.last n = L := Fin.ext (Nat.le_antisymm h (Fin.le_last L))
    rw [reflectSuffix_of_le axis H p L (Fin.last n) h, heq]
    exact (coordinateReflection_fixed axis H (p L) hcut).symm
  · simp only [reflectSuffix, if_neg h]

/-- `positive=true` uses a first maximum, and `positive=false` a first minimum. -/
theorem prefix_ne_reflected_suffix {n : ℕ} (axis : Fin 2) (H : ℤ) (positive : Bool)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1)) (hp : Function.Injective p)
    (hcut : coord axis (p L) = H)
    (hbefore : ∀ t, t < L → if positive then coord axis (p t) < H else H < coord axis (p t))
    (hafter : ∀ t, L < t → if positive then coord axis (p t) ≤ H else H ≤ coord axis (p t))
    (a b : Fin (n + 1)) (ha : a ≤ L) (hb : L < b) :
    p a ≠ coordinateReflection axis H (p b) := by
  intro h
  by_cases haL : a = L
  · subst a
    have hh := congrArg (coordinateReflection axis H) h
    have hpLb : p L = p b := by
      simpa only [coordinateReflection_fixed axis H (p L) hcut,
        coordinateReflection_involutive axis H (p b)] using hh
    have hLb := hp hpLb
    omega
  · have ha' : a < L := by omega
    have hleft := hbefore a ha'
    have hright := hafter b hb
    have hcoord := congrArg (coord axis) h
    rw [reflection_coord] at hcoord
    cases positive <;> simp at hleft hright <;> omega

theorem reflectSuffix_injective {n : ℕ} (axis : Fin 2) (H : ℤ) (positive : Bool)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1)) (hp : Function.Injective p)
    (hcut : coord axis (p L) = H)
    (hbefore : ∀ t, t < L → if positive then coord axis (p t) < H else H < coord axis (p t))
    (hafter : ∀ t, L < t → if positive then coord axis (p t) ≤ H else H ≤ coord axis (p t)) :
    Function.Injective (reflectSuffix axis H p L) := by
  intro a b h
  by_cases ha : a ≤ L
  · by_cases hb : b ≤ L
    · apply hp
      simpa only [reflectSuffix, if_pos ha, if_pos hb] using h
    · exact False.elim (prefix_ne_reflected_suffix axis H positive p L hp hcut hbefore hafter
        a b ha (by omega) (by simpa only [reflectSuffix, if_pos ha, if_neg hb] using h))
  · by_cases hb : b ≤ L
    · exact False.elim (prefix_ne_reflected_suffix axis H positive p L hp hcut hbefore hafter
        b a hb (by omega) (by simpa only [reflectSuffix, if_pos hb, if_neg ha] using h.symm))
    · apply hp
      apply coordinateReflection_injective axis H
      simpa only [reflectSuffix, if_neg ha, if_neg hb] using h

def GridAdjacent (x y : Point) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
  (y.1 = x.1 ∧ y.2 = x.2 - 1)

def HasUnitSteps {n : ℕ} (p : Fin (n + 1) → Point) : Prop :=
  ∀ i : Fin n, GridAdjacent (p i.castSucc) (p i.succ)

theorem coordinateReflection_gridAdjacent (axis : Fin 2) (H : ℤ) {x y : Point}
    (h : GridAdjacent x y) :
    GridAdjacent (coordinateReflection axis H x) (coordinateReflection axis H y) := by
  by_cases ha : axis = 0
  · simp only [coordinateReflection, if_pos ha]
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · right; left; constructor <;> dsimp <;> omega
    · left; constructor <;> dsimp <;> omega
    · right; right; left; constructor <;> dsimp <;> omega
    · right; right; right; constructor <;> dsimp <;> omega
  · simp only [coordinateReflection, if_neg ha]
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · left; constructor <;> dsimp <;> omega
    · right; left; constructor <;> dsimp <;> omega
    · right; right; right; constructor <;> dsimp <;> omega
    · right; right; left; constructor <;> dsimp <;> omega

theorem reflectSuffix_hasUnitSteps {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1))
    (hcut : coord axis (p L) = H) (hsteps : HasUnitSteps p) :
    HasUnitSteps (reflectSuffix axis H p L) := by
  intro i
  have hi := hsteps i
  have hiSucc : i.succ.val = i.castSucc.val + 1 := rfl
  by_cases ha : i.castSucc ≤ L
  · by_cases hb : i.succ ≤ L
    · simpa only [reflectSuffix, if_pos ha, if_pos hb] using hi
    · have hiL : i.castSucc = L := by omega
      have hfix : coordinateReflection axis H (p i.castSucc) = p i.castSucc := by
        apply coordinateReflection_fixed
        simpa only [hiL] using hcut
      have href := coordinateReflection_gridAdjacent axis H hi
      simpa only [reflectSuffix, if_pos ha, if_neg hb, hfix] using href
  · have hb : ¬ i.succ ≤ L := by omega
    simpa only [reflectSuffix, if_neg ha, if_neg hb] using
      coordinateReflection_gridAdjacent axis H hi

theorem reflectSuffix_preserves_walk {n : ℕ} (axis : Fin 2) (H : ℤ) (positive : Bool)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1))
    (hp : Function.Injective p) (hzero : p 0 = (0, 0)) (hsteps : HasUnitSteps p)
    (hcut : coord axis (p L) = H)
    (hbefore : ∀ t, t < L → if positive then coord axis (p t) < H else H < coord axis (p t))
    (hafter : ∀ t, L < t → if positive then coord axis (p t) ≤ H else H ≤ coord axis (p t)) :
    let q := reflectSuffix axis H p L
    Function.Injective q ∧ q 0 = (0, 0) ∧ HasUnitSteps q ∧
      coord axis (q (Fin.last n)) = 2 * H - coord axis (p (Fin.last n)) ∧
      otherCoord axis (q (Fin.last n)) = otherCoord axis (p (Fin.last n)) := by
  refine ⟨reflectSuffix_injective axis H positive p L hp hcut hbefore hafter, ?_,
    reflectSuffix_hasUnitSteps axis H p L hcut hsteps, ?_, ?_⟩
  · rw [reflectSuffix_zero, hzero]
  · rw [reflectSuffix_endpoint axis H p L hcut, reflection_coord]
  · rw [reflectSuffix_endpoint axis H p L hcut, reflection_otherCoord]

def signedToward (H x : ℤ) : ℤ := if 0 ≤ H then x else -x

/-- Beyond the original endpoint's box, reflection stretches its selected coordinate. -/
theorem abs_reflection_eq (H x m : ℤ) (hx : |x| ≤ m) (hH : m < |H|) :
    |2 * H - x| = 2 * |H| - signedToward H x := by
  have hb := abs_le'.mp hx
  have hm : 0 ≤ m := le_trans (abs_nonneg x) hx
  by_cases hpos : 0 ≤ H
  · rw [abs_of_nonneg hpos] at hH ⊢
    have href : 0 ≤ 2 * H - x := by omega
    rw [abs_of_nonneg href]
    simp only [signedToward, if_pos hpos]
  · have hneg : H ≤ 0 := by omega
    rw [abs_of_nonpos hneg] at hH ⊢
    have href : 2 * H - x ≤ 0 := by omega
    rw [abs_of_nonpos href]
    simp only [signedToward, if_neg hpos]
    omega

theorem signedToward_le (H x m : ℤ) (hx : |x| ≤ m) : signedToward H x ≤ m := by
  have hb := abs_le'.mp hx
  unfold signedToward
  split <;> omega

theorem reflected_endpoint_outside_box {n : ℕ} (axis : Fin 2) (H m : ℤ)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1))
    (hcut : coord axis (p L) = H)
    (hselected : |coord axis (p (Fin.last n))| ≤ m)
    (hother : |otherCoord axis (p (Fin.last n))| ≤ m) (hH : m < |H|) :
    let q := reflectSuffix axis H p L
    |coord axis (q (Fin.last n))| =
      2 * |H| - signedToward H (coord axis (p (Fin.last n))) ∧
    2 * |H| - m ≤ |coord axis (q (Fin.last n))| ∧
    m < |coord axis (q (Fin.last n))| ∧
    otherCoord axis (q (Fin.last n)) = otherCoord axis (p (Fin.last n)) ∧
    |otherCoord axis (q (Fin.last n))| ≤ m := by
  dsimp only
  rw [reflectSuffix_endpoint axis H p L hcut, reflection_coord, reflection_otherCoord]
  have heq := abs_reflection_eq H (coord axis (p (Fin.last n))) m hselected hH
  have hsigned := signedToward_le H (coord axis (p (Fin.last n))) m hselected
  refine ⟨heq, ?_, ?_, rfl, hother⟩ <;> omega

/-- A point with only one coordinate outside the box uniquely identifies that axis. -/
theorem axis_recoverable (x : Point) (m : ℤ) (a b : Fin 2)
    (_ha : m < |coord a x|) (haother : |otherCoord a x| ≤ m)
    (hb : m < |coord b x|) : a = b := by
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · exact ha0.trans hb0.symm
    · simp only [otherCoord, if_pos ha0] at haother
      simp only [coord, if_neg hb0] at hb
      omega
  · by_cases hb0 : b = 0
    · simp only [otherCoord, if_neg ha0] at haother
      simp only [coord, if_pos hb0] at hb
      omega
    · have ha1 : a = 1 := by omega
      have hb1 : b = 1 := by omega
      exact ha1.trans hb1.symm

end PlanarSAWSignedReflection


/-!
Fiber counting for coordinate reflection with path-dependent axis and height.
Only the exact geometric helpers needed from SignedReflection.lean are repeated.
No self-avoidance or extremum-selection theorem is assumed in the counting step.
-/

namespace PlanarSAWAxisFiberRecovery

abbrev Point := ℤ × ℤ

def coord (axis : Fin 2) (x : Point) : ℤ := if axis = 0 then x.1 else x.2

def otherCoord (axis : Fin 2) (x : Point) : ℤ := if axis = 0 then x.2 else x.1

theorem point_ext {axis : Fin 2} {x y : Point}
    (h : coord axis x = coord axis y) (hother : otherCoord axis x = otherCoord axis y) :
    x = y := by
  by_cases ha : axis = 0
  · exact Prod.ext (by simpa [coord, ha] using h) (by simpa [otherCoord, ha] using hother)
  · exact Prod.ext (by simpa [otherCoord, ha] using hother) (by simpa [coord, ha] using h)

def coordinateReflection (axis : Fin 2) (H : ℤ) (x : Point) : Point :=
  if axis = 0 then (2 * H - x.1, x.2) else (x.1, 2 * H - x.2)

theorem reflection_coord (axis : Fin 2) (H : ℤ) (x : Point) :
    coord axis (coordinateReflection axis H x) = 2 * H - coord axis x := by
  by_cases ha : axis = 0 <;> simp [coord, coordinateReflection, ha]

theorem reflection_otherCoord (axis : Fin 2) (H : ℤ) (x : Point) :
    otherCoord axis (coordinateReflection axis H x) = otherCoord axis x := by
  by_cases ha : axis = 0 <;> simp [otherCoord, coordinateReflection, ha]

theorem coordinateReflection_involutive (axis : Fin 2) (H : ℤ) :
    Function.Involutive (coordinateReflection axis H) := by
  intro x
  apply point_ext (axis := axis)
  · rw [reflection_coord, reflection_coord]
    omega
  · rw [reflection_otherCoord, reflection_otherCoord]

theorem coordinateReflection_fixed (axis : Fin 2) (H : ℤ) (x : Point)
    (hx : coord axis x = H) : coordinateReflection axis H x = x := by
  apply point_ext (axis := axis)
  · rw [reflection_coord, hx]
    omega
  · exact reflection_otherCoord axis H x

def reflectSuffix {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L t : Fin (n + 1)) : Point :=
  if t ≤ L then p t else coordinateReflection axis H (p t)

theorem reflectSuffix_of_le {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L t : Fin (n + 1)) (ht : t ≤ L) :
    reflectSuffix axis H p L t = p t := by
  simp only [reflectSuffix, if_pos ht]

theorem reflectSuffix_involutive {n : ℕ} (axis : Fin 2) (H : ℤ)
    (L : Fin (n + 1)) :
    Function.Involutive (fun p : Fin (n + 1) → Point => reflectSuffix axis H p L) := by
  intro p
  funext t
  by_cases ht : t ≤ L
  · simp only [reflectSuffix, if_pos ht]
  · simp only [reflectSuffix, if_neg ht, coordinateReflection_involutive axis H (p t)]

theorem reflectSuffix_endpoint {n : ℕ} (axis : Fin 2) (H : ℤ)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1)) (hcut : coord axis (p L) = H) :
    reflectSuffix axis H p L (Fin.last n) = coordinateReflection axis H (p (Fin.last n)) := by
  by_cases h : Fin.last n ≤ L
  · have heq : Fin.last n = L := Fin.ext (Nat.le_antisymm h (Fin.le_last L))
    rw [reflectSuffix_of_le axis H p L (Fin.last n) h, heq]
    exact (coordinateReflection_fixed axis H (p L) hcut).symm
  · simp only [reflectSuffix, if_neg h]

def signedToward (H x : ℤ) : ℤ := if 0 ≤ H then x else -x

theorem abs_reflection_eq (H x m : ℤ) (hx : |x| ≤ m) (hH : m < |H|) :
    |2 * H - x| = 2 * |H| - signedToward H x := by
  have hb := abs_le'.mp hx
  have hm : 0 ≤ m := le_trans (abs_nonneg x) hx
  by_cases hpos : 0 ≤ H
  · rw [abs_of_nonneg hpos] at hH ⊢
    have href : 0 ≤ 2 * H - x := by omega
    rw [abs_of_nonneg href]
    simp only [signedToward, if_pos hpos]
  · have hneg : H ≤ 0 := by omega
    rw [abs_of_nonpos hneg] at hH ⊢
    have href : 2 * H - x ≤ 0 := by omega
    rw [abs_of_nonpos href]
    simp only [signedToward, if_neg hpos]
    omega

theorem signedToward_le (H x m : ℤ) (hx : |x| ≤ m) : signedToward H x ≤ m := by
  have hb := abs_le'.mp hx
  unfold signedToward
  split <;> omega

theorem reflected_endpoint_outside_box {n : ℕ} (axis : Fin 2) (H m : ℤ)
    (p : Fin (n + 1) → Point) (L : Fin (n + 1))
    (hcut : coord axis (p L) = H)
    (hselected : |coord axis (p (Fin.last n))| ≤ m)
    (hother : |otherCoord axis (p (Fin.last n))| ≤ m) (hH : m < |H|) :
    let q := reflectSuffix axis H p L
    |coord axis (q (Fin.last n))| =
      2 * |H| - signedToward H (coord axis (p (Fin.last n))) ∧
    2 * |H| - m ≤ |coord axis (q (Fin.last n))| ∧
    m < |coord axis (q (Fin.last n))| ∧
    otherCoord axis (q (Fin.last n)) = otherCoord axis (p (Fin.last n)) ∧
    |otherCoord axis (q (Fin.last n))| ≤ m := by
  dsimp only
  rw [reflectSuffix_endpoint axis H p L hcut, reflection_coord, reflection_otherCoord]
  have heq := abs_reflection_eq H (coord axis (p (Fin.last n))) m hselected hH
  have hsigned := signedToward_le H (coord axis (p (Fin.last n))) m hselected
  refine ⟨heq, ?_, ?_, rfl, hother⟩ <;> omega

theorem axis_recoverable (x : Point) (m : ℤ) (a b : Fin 2)
    (_ha : m < |coord a x|) (haother : |otherCoord a x| ≤ m)
    (hb : m < |coord b x|) : a = b := by
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · exact ha0.trans hb0.symm
    · simp only [otherCoord, if_pos ha0] at haother
      simp only [coord, if_neg hb0] at hb
      omega
  · by_cases hb0 : b = 0
    · simp only [otherCoord, if_neg ha0] at haother
      simp only [coord, if_pos hb0] at hb
      omega
    · have ha1 : a = 1 := by omega
      have hb1 : b = 1 := by omega
      exact ha1.trans hb1.symm

def FirstCoordinateHit {n : ℕ} (axis : Fin 2) (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) : Prop :=
  coord axis (p L) = H ∧ ∀ t, t < L → coord axis (p t) ≠ H

theorem cut_and_path_eq_of_reflectSuffix_eq {n : ℕ} (axis : Fin 2)
    (p q : Fin (n + 1) → Point) (L K : Fin (n + 1)) (H : ℤ)
    (hp : FirstCoordinateHit axis p L H) (hq : FirstCoordinateHit axis q K H)
    (heq : reflectSuffix axis H p L = reflectSuffix axis H q K) :
    L = K ∧ p = q := by
  have hnotLK : ¬ L < K := by
    intro hLK
    have hLL : L ≤ L := by omega
    have hle : L ≤ K := by omega
    have hcoord := congrArg (fun r => coord axis (r L)) heq
    simp only [reflectSuffix, if_pos hLL, if_pos hle] at hcoord
    have hbefore := hq.2 L hLK
    have hcut := hp.1
    omega
  have hnotKL : ¬ K < L := by
    intro hKL
    have hKK : K ≤ K := by omega
    have hle : K ≤ L := by omega
    have hcoord := congrArg (fun r => coord axis (r K)) heq
    simp only [reflectSuffix, if_pos hKK, if_pos hle] at hcoord
    have hbefore := hp.2 K hKL
    have hcut := hq.1
    omega
  have hcuts : L = K := by omega
  refine ⟨hcuts, ?_⟩
  subst K
  have hundo := congrArg (fun r => reflectSuffix axis H r L) heq
  simpa only [reflectSuffix_involutive axis H L p,
    reflectSuffix_involutive axis H L q] using hundo

theorem otherCoord_abs_le (x : Point) (m : ℤ)
    (hbound : ∀ a : Fin 2, |coord a x| ≤ m) (axis : Fin 2) :
    |otherCoord axis x| ≤ m := by
  by_cases ha : axis = 0
  · simpa [otherCoord, coord, ha] using hbound 1
  · simpa [otherCoord, coord, ha] using hbound 0

/-- The common output determines the axis even when inputs choose different axes. -/
theorem axes_eq_of_reflectSuffix_eq {n : ℕ} (a b : Fin 2) (H K m : ℤ)
    (p q : Fin (n + 1) → Point) (L M : Fin (n + 1))
    (hpCut : coord a (p L) = H) (hqCut : coord b (q M) = K)
    (hpBound : ∀ c : Fin 2, |coord c (p (Fin.last n))| ≤ m)
    (hqBound : ∀ c : Fin 2, |coord c (q (Fin.last n))| ≤ m)
    (hH : m < |H|) (hK : m < |K|)
    (heq : reflectSuffix a H p L = reflectSuffix b K q M) : a = b := by
  have hpout := reflected_endpoint_outside_box a H m p L hpCut
    (hpBound a) (otherCoord_abs_le _ m hpBound a) hH
  have hqout := reflected_endpoint_outside_box b K m q M hqCut
    (hqBound b) (otherCoord_abs_le _ m hqBound b) hK
  apply axis_recoverable (reflectSuffix b K q M (Fin.last n)) m a b
  · rw [← heq]
    exact hpout.2.2.1
  · rw [← heq]
    exact hpout.2.2.2.2
  · exact hqout.2.2.1

def reflectionOutput {n : ℕ}
    (axis : (Fin (n + 1) → Point) → Fin 2)
    (cut : (Fin (n + 1) → Point) → Fin (n + 1))
    (height : (Fin (n + 1) → Point) → ℤ) (p : Fin (n + 1) → Point) :
    Fin (n + 1) → Point := reflectSuffix (axis p) (height p) p (cut p)

/-- Once the axis is recovered from the output endpoint, output plus height
recovers the first-hit cut and then the entire original path. -/
theorem reflection_height_injOn {n : ℕ} (A : Finset (Fin (n + 1) → Point))
    (axis : (Fin (n + 1) → Point) → Fin 2)
    (cut : (Fin (n + 1) → Point) → Fin (n + 1))
    (height : (Fin (n + 1) → Point) → ℤ) (m : ℕ)
    (hfirst : ∀ p ∈ A, FirstCoordinateHit (axis p) p (cut p) (height p))
    (hbound : ∀ p ∈ A, ∀ a : Fin 2, |coord a (p (Fin.last n))| ≤ (m : ℤ))
    (hheight : ∀ p ∈ A, (m : ℤ) < |height p|) :
    Set.InjOn (fun p => (reflectionOutput axis cut height p, height p)) A := by
  intro p hp q hq h
  have hH : height p = height q := congrArg Prod.snd h
  have hout := congrArg Prod.fst h
  have ha : axis p = axis q := axes_eq_of_reflectSuffix_eq
    (axis p) (axis q) (height p) (height q) m p q (cut p) (cut q)
    (hfirst p hp).1 (hfirst q hq).1 (hbound p hp) (hbound q hq)
    (hheight p hp) (hheight q hq) hout
  have hpfirst : FirstCoordinateHit (axis q) p (cut p) (height q) := by
    simpa only [ha, hH] using hfirst p hp
  have hout' : reflectSuffix (axis q) (height q) p (cut p) =
      reflectSuffix (axis q) (height q) q (cut q) := by
    simpa only [reflectionOutput, ha, hH] using hout
  exact (cut_and_path_eq_of_reflectSuffix_eq (axis q) p q (cut p) (cut q) (height q)
    hpfirst (hfirst q hq) hout').2

noncomputable def reflectionFiber {n : ℕ} (A : Finset (Fin (n + 1) → Point))
    (axis : (Fin (n + 1) → Point) → Fin 2)
    (cut : (Fin (n + 1) → Point) → Fin (n + 1))
    (height : (Fin (n + 1) → Point) → ℤ) (ψ : Fin (n + 1) → Point) :
    Finset (Fin (n + 1) → Point) := by
  classical
  exact A.filter (fun p => reflectionOutput axis cut height p = ψ)

/-- No extra axis or sign factor: a nonempty fiber fixes its axis through its
output endpoint, and the remaining integer height interval has at most m+1 points. -/
theorem reflectionFiber_card_le {n : ℕ} (A : Finset (Fin (n + 1) → Point))
    (axis : (Fin (n + 1) → Point) → Fin 2)
    (cut : (Fin (n + 1) → Point) → Fin (n + 1))
    (height : (Fin (n + 1) → Point) → ℤ) (m : ℕ)
    (hfirst : ∀ p ∈ A, FirstCoordinateHit (axis p) p (cut p) (height p))
    (hbound : ∀ p ∈ A, ∀ a : Fin 2, |coord a (p (Fin.last n))| ≤ (m : ℤ))
    (hheight : ∀ p ∈ A, (m : ℤ) < |height p|) (ψ : Fin (n + 1) → Point) :
    (reflectionFiber A axis cut height ψ).card ≤ m + 1 := by
  classical
  by_cases hempty : (reflectionFiber A axis cut height ψ).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hempty
    have hp₀' := Finset.mem_filter.mp (show p₀ ∈ A.filter
      (fun p => reflectionOutput axis cut height p = ψ) from hp₀)
    let a : Fin 2 := axis p₀
    let lo : ℤ := (coord a (ψ (Fin.last n)) - (m : ℤ) + 1) / 2
    let hi : ℤ := (coord a (ψ (Fin.last n)) + (m : ℤ)) / 2
    calc
      (reflectionFiber A axis cut height ψ).card ≤ (Finset.Icc lo hi).card := by
        apply Finset.card_le_card_of_injOn height
        · intro p hp
          have hp' := Finset.mem_filter.mp (show p ∈ A.filter
            (fun p => reflectionOutput axis cut height p = ψ) from hp)
          have ha : axis p = a := axes_eq_of_reflectSuffix_eq
            (axis p) (axis p₀) (height p) (height p₀) m p p₀ (cut p) (cut p₀)
            (hfirst p hp'.1).1 (hfirst p₀ hp₀'.1).1 (hbound p hp'.1) (hbound p₀ hp₀'.1)
            (hheight p hp'.1) (hheight p₀ hp₀'.1) (hp'.2.trans hp₀'.2.symm)
          have hendpoint := congrArg (fun r => coord a (r (Fin.last n))) hp'.2
          dsimp only [reflectionOutput] at hendpoint
          rw [reflectSuffix_endpoint (axis p) (height p) p (cut p) (hfirst p hp'.1).1,
            ha, reflection_coord] at hendpoint
          have hb := abs_le'.mp (hbound p hp'.1 a)
          change height p ∈ Finset.Icc lo hi
          rw [Finset.mem_Icc]
          dsimp [lo, hi]
          constructor <;> omega
        · intro p hp q hq hH
          have hp' := Finset.mem_filter.mp (show p ∈ A.filter
            (fun p => reflectionOutput axis cut height p = ψ) from hp)
          have hq' := Finset.mem_filter.mp (show q ∈ A.filter
            (fun p => reflectionOutput axis cut height p = ψ) from hq)
          exact reflection_height_injOn A axis cut height m hfirst hbound hheight hp'.1 hq'.1
            (Prod.ext (hp'.2.trans hq'.2.symm) hH)
      _ ≤ m + 1 := by
        rw [Int.card_Icc, Int.toNat_le]
        dsimp [lo, hi]
        omega
  · have hz : reflectionFiber A axis cut height ψ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hz, Finset.card_empty]
    omega

theorem card_le_output_card_mul {n : ℕ} (A B : Finset (Fin (n + 1) → Point))
    (axis : (Fin (n + 1) → Point) → Fin 2)
    (cut : (Fin (n + 1) → Point) → Fin (n + 1))
    (height : (Fin (n + 1) → Point) → ℤ) (m : ℕ)
    (hfirst : ∀ p ∈ A, FirstCoordinateHit (axis p) p (cut p) (height p))
    (hbound : ∀ p ∈ A, ∀ a : Fin 2, |coord a (p (Fin.last n))| ≤ (m : ℤ))
    (hheight : ∀ p ∈ A, (m : ℤ) < |height p|)
    (himage : ∀ p ∈ A, reflectionOutput axis cut height p ∈ B) :
    A.card ≤ B.card * (m + 1) := by
  classical
  have hf : Set.MapsTo (reflectionOutput axis cut height) A B := himage
  rw [Finset.card_eq_sum_card_fiberwise hf]
  calc
    ∑ ψ ∈ B, (A.filter (fun p => reflectionOutput axis cut height p = ψ)).card
        ≤ ∑ _ψ ∈ B, (m + 1) := by
      apply Finset.sum_le_sum
      intro ψ _
      exact reflectionFiber_card_le A axis cut height m hfirst hbound hheight ψ
    _ = B.card * (m + 1) := by simp

end PlanarSAWAxisFiberRecovery


/-!
The deterministic Madras reflection map on Jig #289's canonical direction words.
Imports are compiled copies of the previously checked local proof files. A final
submission can flatten those sources without changing the definitions or proofs.
-/

namespace PlanarSAWMadrasMap

open PlanarSAWDirectionBridge

abbrev normInfNat := PlanarSAWMaximalCut.normInfNat
abbrev coord := PlanarSAWSignedReflection.coord
abbrev otherCoord := PlanarSAWSignedReflection.otherCoord

noncomputable def chosenCut {n : ℕ} (s : Fin n → Fin 4) : Fin (n + 1) :=
  PlanarSAWMaximalCut.firstMaxCut (position s)

noncomputable def chosenAxis {n : ℕ} (s : Fin n → Fin 4) : Fin 2 :=
  PlanarSAWMaximalCut.selectedAxis (position s)

noncomputable def chosenHeight {n : ℕ} (s : Fin n → Fin 4) : ℤ :=
  coord (chosenAxis s) (position s (chosenCut s))

noncomputable def reflectedPath {n : ℕ} (s : Fin n → Fin 4) : Fin (n + 1) → Point :=
  PlanarSAWSignedReflection.reflectSuffix (chosenAxis s) (chosenHeight s)
    (position s) (chosenCut s)

theorem chosenHeight_natAbs {n : ℕ} (s : Fin n → Fin 4) :
    (chosenHeight s).natAbs = normInfNat (position s (chosenCut s)) :=
  PlanarSAWMaximalCut.selectedAxis_natAbs (position s)

theorem chosen_before_abs {n : ℕ} (s : Fin n → Fin 4) (t : Fin (n + 1))
    (ht : t < chosenCut s) : |coord (chosenAxis s) (position s t)| < |chosenHeight s| := by
  have h : (coord (chosenAxis s) (position s t)).natAbs < (chosenHeight s).natAbs := by
    rw [chosenHeight_natAbs]
    exact PlanarSAWMaximalCut.selectedAxis_before (position s) t ht
  have hh := Int.ofNat_lt.mpr h
  simpa only [Int.natCast_natAbs] using hh

theorem chosen_coord_abs_le {n : ℕ} (s : Fin n → Fin 4) (t : Fin (n + 1)) :
    |coord (chosenAxis s) (position s t)| ≤ |chosenHeight s| := by
  have h : (coord (chosenAxis s) (position s t)).natAbs ≤ (chosenHeight s).natAbs := by
    rw [chosenHeight_natAbs]
    exact PlanarSAWMaximalCut.selectedAxis_le (position s) t
  have hh := Int.ofNat_le.mpr h
  simpa only [Int.natCast_natAbs] using hh

theorem chosen_first_hit {n : ℕ} (s : Fin n → Fin 4) :
    coord (chosenAxis s) (position s (chosenCut s)) = chosenHeight s ∧
      ∀ t, t < chosenCut s → coord (chosenAxis s) (position s t) ≠ chosenHeight s := by
  refine ⟨rfl, ?_⟩
  intro t ht
  exact PlanarSAWMaximalCut.selectedAxis_first_visit (position s) t ht

theorem signed_side_lt (H x : ℤ) (h : |x| < |H|) :
    if decide (0 ≤ H) then x < H else H < x := by
  have hx := abs_le'.mp (le_refl |x|)
  by_cases hH : 0 ≤ H
  · simp only [hH, decide_true, if_true]
    rw [abs_of_nonneg hH] at h
    omega
  · simp only [hH, decide_false, Bool.false_eq_true, if_false]
    have hH' : H ≤ 0 := by omega
    rw [abs_of_nonpos hH'] at h
    omega

theorem signed_side_le (H x : ℤ) (h : |x| ≤ |H|) :
    if decide (0 ≤ H) then x ≤ H else H ≤ x := by
  have hx := abs_le'.mp (le_refl |x|)
  by_cases hH : 0 ≤ H
  · simp only [hH, decide_true, if_true]
    rw [abs_of_nonneg hH] at h
    omega
  · simp only [hH, decide_false, Bool.false_eq_true, if_false]
    have hH' : H ≤ 0 := by omega
    rw [abs_of_nonpos hH'] at h
    omega

theorem reflectedPath_injective {n : ℕ} (s : Fin n → Fin 4)
    (hs : IsSelfAvoidingWalk s) : Function.Injective (reflectedPath s) := by
  apply PlanarSAWSignedReflection.reflectSuffix_injective
    (chosenAxis s) (chosenHeight s) (decide (0 ≤ chosenHeight s))
    (position s) (chosenCut s) hs rfl
  · intro t ht
    exact signed_side_lt _ _ (chosen_before_abs s t ht)
  · intro t _
    exact signed_side_le _ _ (chosen_coord_abs_le s t)

theorem reflectedPath_zero {n : ℕ} (s : Fin n → Fin 4) :
    reflectedPath s 0 = (0, 0) := by
  rw [reflectedPath, PlanarSAWSignedReflection.reflectSuffix_zero, position_zero]

theorem reflectedPath_hasUnitSteps {n : ℕ} (s : Fin n → Fin 4) :
    HasUnitSteps (reflectedPath s) :=
  PlanarSAWSignedReflection.reflectSuffix_hasUnitSteps
    (chosenAxis s) (chosenHeight s) (position s) (chosenCut s) rfl (position_hasUnitSteps s)

/-- This map is defined on every direction word. Its SAW preservation is proved
separately, so no proof argument is part of the choice of output. -/
noncomputable def reflectedWord {n : ℕ} (s : Fin n → Fin 4) : Fin n → Fin 4 :=
  Classical.choose (exists_directionWord (reflectedPath s)
    (reflectedPath_zero s) (reflectedPath_hasUnitSteps s))

theorem reflectedWord_position {n : ℕ} (s : Fin n → Fin 4) :
    position (reflectedWord s) = reflectedPath s :=
  Classical.choose_spec (exists_directionWord (reflectedPath s)
    (reflectedPath_zero s) (reflectedPath_hasUnitSteps s))

theorem reflectedWord_isSelfAvoiding {n : ℕ} (s : Fin n → Fin 4)
    (hs : IsSelfAvoidingWalk s) : IsSelfAvoidingWalk (reflectedWord s) := by
  unfold IsSelfAvoidingWalk
  rw [reflectedWord_position]
  exact reflectedPath_injective s hs

theorem reflectedWord_unique {n : ℕ} (s t : Fin n → Fin 4)
    (ht : position t = reflectedPath s) : t = reflectedWord s :=
  position_injective (ht.trans (reflectedWord_position s).symm)

theorem coord_abs_le_of_norm_le (axis : Fin 2) (x : Point) (m : ℕ)
    (hx : normInfNat x ≤ m) : |coord axis x| ≤ (m : ℤ) := by
  have h := le_trans (PlanarSAWMaximalCut.coord_natAbs_le_normInfNat axis x) hx
  have hh := Int.ofNat_le.mpr h
  simpa only [Int.natCast_natAbs, coord, PlanarSAWSignedReflection.coord,
    PlanarSAWMaximalCut.coord] using hh

theorem otherCoord_abs_le_of_norm_le (axis : Fin 2) (x : Point) (m : ℕ)
    (hx : normInfNat x ≤ m) : |otherCoord axis x| ≤ (m : ℤ) := by
  by_cases ha : axis = 0
  · have h := coord_abs_le_of_norm_le (1 : Fin 2) x m hx
    simpa [otherCoord, coord, PlanarSAWSignedReflection.otherCoord,
      PlanarSAWSignedReflection.coord, ha] using h
  · have h := coord_abs_le_of_norm_le (0 : Fin 2) x m hx
    simpa [otherCoord, coord, PlanarSAWSignedReflection.otherCoord,
      PlanarSAWSignedReflection.coord, ha] using h

theorem point_box_of_norm_le (x : Point) (r : ℕ) (hx : normInfNat x ≤ r) :
    -(r : ℤ) ≤ x.1 ∧ x.1 ≤ r ∧ -(r : ℤ) ≤ x.2 ∧ x.2 ≤ r := by
  have h₁ := coord_abs_le_of_norm_le 0 x r hx
  have h₂ := coord_abs_le_of_norm_le 1 x r hx
  simp [coord, PlanarSAWSignedReflection.coord] at h₁ h₂
  have hb₁ := abs_le'.mp h₁
  have hb₂ := abs_le'.mp h₂
  omega

theorem chosenHeight_natAbs_gt {n r : ℕ} (s : Fin n → Fin 4)
    (hs : IsSelfAvoidingWalk s) (hn : (2 * r + 1) ^ 2 < n + 1) :
    r < (chosenHeight s).natAbs := by
  by_contra h
  have hle : (chosenHeight s).natAbs ≤ r := by omega
  have hmax : normInfNat (position s (chosenCut s)) ≤ r := by
    rw [← chosenHeight_natAbs]
    exact hle
  have hbox : ∀ t, -(r : ℤ) ≤ (position s t).1 ∧ (position s t).1 ≤ r ∧
      -(r : ℤ) ≤ (position s t).2 ∧ (position s t).2 ≤ r := by
    intro t
    apply point_box_of_norm_le
    exact le_trans (PlanarSAWMaximalCut.firstMaxCut_max (position s) t) hmax
  have hcard := PlanarSAWPacking.length_le_box_card (position s) hs hbox
  omega

theorem chosenHeight_abs_gt {n r : ℕ} (s : Fin n → Fin 4)
    (hs : IsSelfAvoidingWalk s) (hn : (2 * r + 1) ^ 2 < n + 1) :
    (r : ℤ) < |chosenHeight s| := by
  have h := Int.ofNat_lt.mpr (chosenHeight_natAbs_gt s hs hn)
  simpa only [Int.natCast_natAbs] using h

/-- The two-coordinate output information is what identifies the reflection axis
in the finite-fibre counting theorem. -/
theorem reflectedPath_endpoint_bounds {n r m : ℕ} (s : Fin n → Fin 4)
    (hs : IsSelfAvoidingWalk s) (hmr : m ≤ r)
    (hn : (2 * r + 1) ^ 2 < n + 1)
    (hend : normInfNat (position s (Fin.last n)) ≤ m) :
    2 * |chosenHeight s| - (m : ℤ) ≤
        |coord (chosenAxis s) (reflectedPath s (Fin.last n))| ∧
      (m : ℤ) < |coord (chosenAxis s) (reflectedPath s (Fin.last n))| ∧
      |otherCoord (chosenAxis s) (reflectedPath s (Fin.last n))| ≤ (m : ℤ) := by
  have hH := chosenHeight_abs_gt s hs hn
  have hmrcast := Int.ofNat_le.mpr hmr
  have hHm : (m : ℤ) < |chosenHeight s| := by omega
  have h := PlanarSAWSignedReflection.reflected_endpoint_outside_box
    (chosenAxis s) (chosenHeight s) (m : ℤ) (position s) (chosenCut s) rfl
    (coord_abs_le_of_norm_le (chosenAxis s) _ m hend)
    (otherCoord_abs_le_of_norm_le (chosenAxis s) _ m hend) hHm
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem reflectedWord_endpoint_growth {n r m : ℕ} (s : Fin n → Fin 4)
    (hs : IsSelfAvoidingWalk s) (hmr : m ≤ r)
    (hn : (2 * r + 1) ^ 2 < n + 1)
    (hend : normInfNat (position s (Fin.last n)) ≤ m) :
    2 * (r + 1) - m ≤ normInfNat (position (reflectedWord s) (Fin.last n)) := by
  rw [reflectedWord_position]
  have hheight := chosenHeight_abs_gt s hs hn
  have hgrowth := (reflectedPath_endpoint_bounds s hs hmr hn hend).1
  have hcoord := coord_abs_le_of_norm_le (chosenAxis s)
    (reflectedPath s (Fin.last n)) (normInfNat (reflectedPath s (Fin.last n))) (le_refl _)
  omega

theorem reflectedWord_endpoint_outside {n r m : ℕ} (s : Fin n → Fin 4)
    (hs : IsSelfAvoidingWalk s) (hmr : m ≤ r)
    (hn : (2 * r + 1) ^ 2 < n + 1)
    (hend : normInfNat (position s (Fin.last n)) ≤ m) :
    r + 1 ≤ normInfNat (position (reflectedWord s) (Fin.last n)) := by
  have h := reflectedWord_endpoint_growth s hs hmr hn hend
  omega

theorem reflectedWord_spec {n r m : ℕ} (s : Fin n → Fin 4)
    (hs : IsSelfAvoidingWalk s) (hmr : m ≤ r)
    (hn : (2 * r + 1) ^ 2 < n + 1)
    (hend : normInfNat (position s (Fin.last n)) ≤ m) :
    IsSelfAvoidingWalk (reflectedWord s) ∧
      position (reflectedWord s) = reflectedPath s ∧
      r + 1 ≤ normInfNat (position (reflectedWord s) (Fin.last n)) ∧
      (r : ℤ) < |chosenHeight s| :=
  ⟨reflectedWord_isSelfAvoiding s hs, reflectedWord_position s,
    reflectedWord_endpoint_outside s hs hmr hn hend, chosenHeight_abs_gt s hs hn⟩

end PlanarSAWMadrasMap

namespace PlanarSAWDirectionBridge
open PlanarSAWMadrasMap

noncomputable def vertexAxis {n : ℕ} (p : Fin (n + 1) → Point) : Fin 2 :=
  PlanarSAWMaximalCut.selectedAxis p
noncomputable def vertexCut {n : ℕ} (p : Fin (n + 1) → Point) : Fin (n + 1) :=
  PlanarSAWMaximalCut.firstMaxCut p
noncomputable def vertexHeight {n : ℕ} (p : Fin (n + 1) → Point) : ℤ :=
  PlanarSAWSignedReflection.coord (vertexAxis p) (p (vertexCut p))

theorem reflection_count {n r m : ℕ} (hmr : m ≤ r)
    (hn : (2 * r + 1) ^ 2 < n + 1) :
    ((walks n).filter (fun s => endpointNorm s ≤ m)).card ≤
      ((walks n).filter (fun s => r + 1 ≤ endpointNorm s)).card * (m + 1) := by
  classical
  let A := (walks n).filter (fun s => endpointNorm s ≤ m)
  let B := (walks n).filter (fun s => r + 1 ≤ endpointNorm s)
  have hcard := PlanarSAWAxisFiberRecovery.card_le_output_card_mul
    (A.image position) (B.image position) vertexAxis vertexCut vertexHeight m
    (by
      intro p hp
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
      exact chosen_first_hit s)
    (by
      intro p hp a
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
      exact coord_abs_le_of_norm_le a _ m (Finset.mem_filter.mp hs).2)
    (by
      intro p hp
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
      have hsaw : IsSelfAvoidingWalk s :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
      exact lt_of_le_of_lt (Int.ofNat_le.mpr hmr) (chosenHeight_abs_gt s hsaw hn))
    (by
      intro p hp
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
      have hsaw : IsSelfAvoidingWalk s :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
      have hend := (Finset.mem_filter.mp hs).2
      refine Finset.mem_image.mpr ⟨reflectedWord s, ?_, reflectedWord_position s⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, reflectedWord_isSelfAvoiding s hsaw⟩,
        reflectedWord_endpoint_outside s hsaw hmr hn hend⟩)
  simpa only [Finset.card_image_of_injective _ position_injective] using hcard


/-- A finite first-moment consequence of the classical reflection argument.
The threshold grows quartically in m, so this does not assert superdiffusivity. -/
theorem expectedDistance_finite_lower_bound (n m : ℕ)
    (hn : (2 * (m * (m + 2)) + 1) ^ 2 < n + 1) :
    (m : ℝ) ≤ expectedDistance n := by
  classical
  apply expectedDistance_ge_of_counts
  have hmr : m ≤ m * (m + 2) := by nlinarith
  have hc := reflection_count hmr hn
  have hsub : (walks n).filter (fun s => m * (m + 2) + 1 ≤ endpointNorm s) ⊆
      (walks n).filter (fun s => m * (m + 2) ≤ endpointNorm s) := by
    intro s hs
    obtain ⟨hw, hb⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨hw, by omega⟩
  exact hc.trans (Nat.mul_le_mul_right (m + 1) (Finset.card_le_card hsub))

end PlanarSAWDirectionBridge

theorem proof : ∀ n m : ℕ, (2 * (m * (m + 2)) + 1) ^ 2 < n + 1 →
    (m : ℝ) ≤ PlanarSAWDirectionBridge.expectedDistance n :=
  PlanarSAWDirectionBridge.expectedDistance_finite_lower_bound

end Submissions.Erdos529FiniteEndpointBound.Main
