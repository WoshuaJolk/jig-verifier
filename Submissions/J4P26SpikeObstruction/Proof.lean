import Init

namespace Submissions.J4P26SpikeObstruction.Proof

def axisSpike {K : Type u} [Lean.Grind.CommRing K] [DecidableEq K]
    (c x y z : K) : K := if x = 0 ∧ y = 0 then c*z else 0

theorem cross_minor_inputs
    {K : Type u} [Lean.Grind.CommRing K]
    (u0 u1 u2 h0 h1 h2 v0 v1 v2 : K)
    (hu : u0*v0+u1*v1+u2*v2 = 0)
    (hh : h0*v0+h1*v1+h2*v2 = 0) :
    (u1*h2-u2*h1)*v2 = (u0*h1-u1*h0)*v0 ∧
      (u2*h0-u0*h2)*v2 = (u0*h1-u1*h0)*v1 := by
  constructor <;> grind

theorem spike_switch
    {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
    (a b c x y z : K)
    (hx : a*z = c*x) (hy : b*z = c*y) :
    axisSpike c x y z = if a = 0 ∧ b = 0 then c*z else 0 := by
  by_cases hv : x = 0 ∧ y = 0
  · by_cases hw : a = 0 ∧ b = 0
    · simp only [axisSpike, hv, hw, ite_true]
    · have hz : z = 0 := by
        by_cases ha : a = 0
        · have hb : b ≠ 0 := by grind
          have hh : b*z = 0 := by grind
          exact (Lean.Grind.Field.of_mul_eq_zero hh).resolve_left hb
        · have hh : a*z = 0 := by grind
          exact (Lean.Grind.Field.of_mul_eq_zero hh).resolve_left ha
      simp only [axisSpike, hv, hw, ite_true, ite_false]
      grind
  · by_cases hw : a = 0 ∧ b = 0
    · have hc : c = 0 := by
        by_cases hxx : x = 0
        · have hyy : y ≠ 0 := by grind
          have hh : c*y = 0 := by grind
          exact (Lean.Grind.Field.of_mul_eq_zero hh).resolve_right hyy
        · have hh : c*x = 0 := by grind
          exact (Lean.Grind.Field.of_mul_eq_zero hh).resolve_right hxx
      simp only [axisSpike, hv, hw, ite_false, ite_true]
      grind
    · simp only [axisSpike, hv, hw, ite_false]

def third {K : Type u} [Lean.Grind.CommRing K] (f : K → K) : K :=
  f 3 - 3*f 2 + 3*f 1 - f 0

def fourth {K : Type u} [Lean.Grind.CommRing K] (f : K → K) : K :=
  f 4 - 4*f 3 + 6*f 2 - 4*f 1 + f 0

theorem quadratic_third_zero
    {K : Type u} [Lean.Grind.CommRing K] (a b c : K) :
    third (fun t => a*t*t+b*t+c) = 0 := by
  simp only [third]
  grind

theorem cubic_fourth_zero
    {K : Type u} [Lean.Grind.CommRing K] (a b c d : K) :
    fourth (fun t => a*t*t*t+b*t*t+c*t+d) = 0 := by
  simp only [fourth]
  grind

theorem spike_third_difference
    {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    third (fun t : K => axisSpike (-1) t 0 1) = 1 := by
  have h1 : (1 : K) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
  simp [third, axisSpike, h1, h2, h3] <;> grind

theorem spike_fourth_difference
    {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h4 : (4 : K) ≠ 0) :
    fourth (fun t : K => axisSpike (-1) t 0 1) = -1 := by
  have h1 : (1 : K) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
  simp [fourth, axisSpike, h1, h2, h3, h4] <;> grind

theorem no_quadratic_spike_extension
    {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    ¬ ∃ a b c : K, ∀ t : K, a*t*t+b*t+c = axisSpike (-1) t 0 1 := by
  rintro ⟨a, b, c, hh⟩
  have he : (fun t : K => a*t*t+b*t+c) =
      (fun t : K => axisSpike (-1) t 0 1) := funext hh
  have hz := quadratic_third_zero a b c
  rw [he] at hz
  have ho := spike_third_difference h2 h3
  exact Lean.Grind.Field.zero_ne_one (hz.symm.trans ho)

theorem no_cubic_spike_extension
    {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h4 : (4 : K) ≠ 0) :
    ¬ ∃ a b c d : K, ∀ t : K, a*t*t*t+b*t*t+c*t+d = axisSpike (-1) t 0 1 := by
  rintro ⟨a, b, c, d, hh⟩
  have he : (fun t : K => a*t*t*t+b*t*t+c*t+d) =
      (fun t : K => axisSpike (-1) t 0 1) := funext hh
  have hz := cubic_fourth_zero a b c d
  rw [he] at hz
  have ho := spike_fourth_difference h2 h3 h4
  have hn : (0 : K) = -1 := hz.symm.trans ho
  have heq : (0 : K) = 1 := by grind
  exact Lean.Grind.Field.zero_ne_one heq

theorem padding_membership
    {K : Type u} [Lean.Grind.CommRing K] :
    (1 : K)*1+0*1+0*0+1*(-1) = 0 ∧
      (1 : K)*1+0*(-2)+0*0+1*(-1) = 0 ∧
      (1 : K)*1+1*(-2)+0*0+(-1)*(-1) = 0 := by
  constructor
  · grind
  · constructor <;> grind

theorem padding_additive_defect
    {K : Type u} [Lean.Grind.Field K] [DecidableEq K] :
    axisSpike (1 : K) 0 0 1 + axisSpike (1 : K) 1 (-2) 0 -
      axisSpike (1 : K) 1 (-2) 1 = 1 := by
  have h1 : (1 : K) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
  simp [axisSpike, h1] <;> grind

theorem affine_anchor_additive
    {V : Type u} [Lean.Grind.IntModule V]
    (f0 fx fy fxy : V) (h : f0-fx-fy+fxy = 0) :
    fxy-f0 = (fx-f0)+(fy-f0) := by
  grind

theorem solves :
(∀ {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0),
¬ ∃ a b c : K, ∀ t : K, a*t*t+b*t+c = axisSpike (-1) t 0 1) ∧
(∀ {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h4 : (4 : K) ≠ 0),
¬ ∃ a b c d : K, ∀ t : K, a*t*t*t+b*t*t+c*t+d = axisSpike (-1) t 0 1) := by
  exact ⟨@no_quadratic_spike_extension, @no_cubic_spike_extension⟩

end Submissions.J4P26SpikeObstruction.Proof

