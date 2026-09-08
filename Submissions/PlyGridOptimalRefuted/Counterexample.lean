import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic

namespace Submissions.PlyGridOptimalRefuted.Counterexample

/- Component: FiniteLayerCertificate; SHA256 89447059b466526a6dcbac55d216dd1c685120f6a50145e1fc63a41b87bb4430. -/
/-!
Integer flat-layer certificate for the frozen rational data independently
checked in finite-layer-certificate.py, SHA256
27338d3644e41a87bcd159796ff3dd1d8ae8098801237d989263c8af72859532.
The data encode z=Z/10^6, r=R/10^6, w=W/10^12, and x=10^6*t.
No claim about a finite collection of Euclidean balls is made here.
-/

namespace FiniteLayerCertificate

abbrev Layer := ℤ × ℤ × ℤ

def center (a : Layer) : ℤ := a.1
def radius (a : Layer) : ℤ := a.2.1
def weight (a : Layer) : ℤ := a.2.2

def halfData : List Layer := [
  (-539165512, 410313463, 5939755),
  (-538885512, 410067886, 5946871),
  (-126178876, 48060932, 432931635),
  (-125898876, 47889294, 436040503),
  (-74866362, 18268319, 2996598342),
  (-74586362, 18140570, 3038951795),
  (-54190803, 9851580, 10305684347),
  (-53910803, 9756189, 10508196904),
  (-42555317, 6306529, 25155663125),
  (-42275317, 6232625, 25755774913),
  (-34873134, 4473369, 50022078725),
  (-34593134, 4414270, 51370470870),
  (-29296820, 3398638, 86723798094),
  (-29016820, 3350272, 89245856929),
  (-24984071, 2713079, 136222992903),
  (-24704071, 2672851, 140354325061),
  (-21492091, 2248741, 198533369686),
  (-21212091, 2214918, 204642964399),
  (-18563974, 1920091, 272713256316),
  (-18283974, 1891472, 281028495521),
  (-16039343, 1679761, 356925006301),
  (-15759343, 1655481, 367470998241),
  (-13812168, 1499765, 448546309584),
  (-13532168, 1479194, 461108936153),
  (-11808970, 1362718, 544322054099),
  (-11528970, 1345382, 558440349988),
  (-9976727, 1257375, 640547224344),
  (-9696727, 1242917, 655536715474),
  (-8275755, 1176244, 733272006231),
  (-7995755, 1164391, 748276775093),
  (-6675312, 1114219, 818520014319),
  (-6395312, 1104766, 832587825867),
  (-5150760, 1067787, 892509720114),
  (-4870760, 1060579, 904681807459),
  (-3681642, 1034535, 951868170140),
  (-3401642, 1029461, 961273495814),
  (-2250335, 1012853, 993825390223),
  (-1970335, 1009838, 999768565760),
  (-841036, 1001751, 1016377875984),
  (-561036, 1000751, 1018410544546)
]

def layers : List Layer :=
  halfData ++ halfData.reverse.map (fun a => (-center a, radius a, weight a))

def degree (a : Layer) : ℤ :=
  (layers.map (fun b => weight b *
    max 0 ((radius a + radius b) ^ 2 - (center a - center b) ^ 2))).sum

def depth (data : List Layer) (x : ℝ) : ℝ :=
  (data.map (fun a => (weight a : ℝ) *
    max 0 ((radius a : ℝ) ^ 2 - (x - center a) ^ 2))).sum

lemma quadratic_bound {A B C T x : ℝ} (hA : 0 < A)
    (hdisc : A * C + B ^ 2 ≤ A * T) : C + 2 * B * x - A * x ^ 2 ≤ T := by
  by_contra! h
  have hp := mul_pos hA (sub_pos.mpr h)
  nlinarith [sq_nonneg (A * x - B)]

lemma kernel_inside {R Z x : ℝ} (hlo : Z - R ≤ x) (hhi : x ≤ Z + R) :
    max 0 (R ^ 2 - (x - Z) ^ 2) = R ^ 2 - (x - Z) ^ 2 := by
  apply max_eq_right
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith

lemma kernel_outside {R Z x : ℝ} (hR : 0 ≤ R)
    (hx : x ≤ Z - R ∨ Z + R ≤ x) : max 0 (R ^ 2 - (x - Z) ^ 2) = 0 := by
  apply max_eq_left
  rcases hx with hx | hx
  · have hp := mul_nonneg (show 0 ≤ Z - x - R by linarith)
      (show 0 ≤ Z - x + R by linarith)
    nlinarith
  · have hp := mul_nonneg (show 0 ≤ x - Z - R by linarith)
      (show 0 ≤ x - Z + R by linarith)
    nlinarith

def rawDepth (data : List Layer) (x : ℝ) : ℝ :=
  (data.map (fun a => (weight a : ℝ) *
    ((radius a : ℝ) ^ 2 - (x - center a) ^ 2))).sum

def coeffA (data : List Layer) : ℤ := (data.map weight).sum
def coeffB (data : List Layer) : ℤ := (data.map (fun a => weight a * center a)).sum
def coeffC (data : List Layer) : ℤ :=
  (data.map (fun a => weight a * (radius a ^ 2 - center a ^ 2))).sum

lemma rawDepth_eq (data : List Layer) (x : ℝ) :
    rawDepth data x = (coeffC data : ℝ) + 2 * coeffB data * x - coeffA data * x ^ 2 := by
  induction data with
  | nil => simp [rawDepth, coeffA, coeffB, coeffC]
  | cons a data ih =>
    simp only [rawDepth, coeffA, coeffB, coeffC, List.map_cons, List.sum_cons,
      Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_pow] at *
    rw [ih]
    ring

def inside (lo hi : ℤ) (a : Layer) : Prop :=
  center a - radius a ≤ lo ∧ hi ≤ center a + radius a

instance (lo hi : ℤ) (a : Layer) : Decidable (inside lo hi a) :=
  inferInstanceAs (Decidable (_ ∧ _))

def active (data : List Layer) (lo hi : ℤ) : List Layer :=
  data.filter (fun a => decide (inside lo hi a))

lemma depth_eq_raw_active (data : List Layer) (lo hi : ℤ) (x : ℝ)
    (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ))
    (hclass : ∀ a ∈ data, 0 ≤ radius a ∧
      (inside lo hi a ∨ hi ≤ center a - radius a ∨ center a + radius a ≤ lo)) :
    depth data x = rawDepth (active data lo hi) x := by
  induction data with
  | nil => simp [depth, rawDepth, active]
  | cons a data ih =>
    have ha := hclass a (by simp)
    have ht : ∀ b ∈ data, 0 ≤ radius b ∧
        (inside lo hi b ∨ hi ≤ center b - radius b ∨ center b + radius b ≤ lo) := by
      intro b hb
      exact hclass b (by simp [hb])
    have hiht := ih ht
    by_cases hin : inside lo hi a
    · have hl : (center a : ℝ) - radius a ≤ x := by
        have hc : (center a : ℝ) - radius a ≤ lo := by exact_mod_cast hin.1
        linarith
      have hh : x ≤ (center a : ℝ) + radius a := by
        have hc : (hi : ℝ) ≤ (center a : ℝ) + radius a := by exact_mod_cast hin.2
        linarith
      simp only [depth, rawDepth, active, List.map_cons, List.sum_cons,
        List.filter_cons, hin, decide_true, if_true] at *
      rw [kernel_inside hl hh, hiht]
    · have hout : x ≤ (center a : ℝ) - radius a ∨ (center a : ℝ) + radius a ≤ x := by
        rcases ha.2 with h | h | h
        · exact False.elim (hin h)
        · left
          have hc : (hi : ℝ) ≤ (center a : ℝ) - radius a := by exact_mod_cast h
          linarith
        · right
          have hc : (center a : ℝ) + radius a ≤ lo := by exact_mod_cast h
          linarith
      have hr : (0 : ℝ) ≤ radius a := by exact_mod_cast ha.1
      simp only [depth, rawDepth, active, List.map_cons, List.sum_cons,
        List.filter_cons, hin, decide_false, Bool.false_eq_true, if_false] at *
      rw [kernel_outside hr hout, mul_zero, zero_add, hiht]

def GoodPiece (data : List Layer) (lo hi T : ℤ) : Prop :=
  (∀ a ∈ data, 0 ≤ radius a ∧
    (inside lo hi a ∨ hi ≤ center a - radius a ∨ center a + radius a ≤ lo)) ∧
  0 < coeffA (active data lo hi) ∧
  coeffA (active data lo hi) * coeffC (active data lo hi) +
    coeffB (active data lo hi) ^ 2 ≤ coeffA (active data lo hi) * T

instance (data : List Layer) (lo hi T : ℤ) : Decidable (GoodPiece data lo hi T) :=
  inferInstanceAs (Decidable (_ ∧ _))

lemma goodPiece_bound (data : List Layer) (lo hi T : ℤ) (hgood : GoodPiece data lo hi T)
    (x : ℝ) (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) : depth data x ≤ T := by
  rw [depth_eq_raw_active data lo hi x hxlo hxhi hgood.1, rawDepth_eq]
  apply quadratic_bound
  · exact_mod_cast hgood.2.1
  · exact_mod_cast hgood.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
lemma degree_check : layers.all (fun a => decide (16047 * 10 ^ 21 < degree a)) = true := by
  decide

lemma every_degree (a : Layer) (ha : a ∈ layers) :
    16047 * 10 ^ 21 < degree a := by
  have h := List.all_eq_true.mp degree_check a ha
  exact of_decide_eq_true h

set_option maxRecDepth 100000 in
lemma positive_check : layers.all (fun a => decide (0 < radius a ∧ 0 < weight a)) = true := by
  decide

lemma positive (a : Layer) (ha : a ∈ layers) : 0 < radius a ∧ 0 < weight a := by
  exact of_decide_eq_true (List.all_eq_true.mp positive_check a ha)

lemma depth_zero_outside (data : List Layer) (x : ℝ)
    (hout : ∀ a ∈ data, (0 : ℝ) ≤ radius a ∧
      (x ≤ (center a : ℝ) - radius a ∨ (center a : ℝ) + radius a ≤ x)) :
    depth data x = 0 := by
  unfold depth
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  rw [kernel_outside (hout a ha).1 (hout a ha).2, mul_zero]

/-- A finite chain of intervals, together with its two exterior rays,
covers the real line. No monotonicity premise is needed. -/
lemma chain_bound (f : ℝ → ℝ) (T : ℝ) (a : ℤ) (rest : List ℤ)
    (hleft : ∀ x, x ≤ (a : ℝ) → f x ≤ T)
    (hright : ∀ x, (rest.getLastD a : ℝ) ≤ x → f x ≤ T)
    (hpieces : ∀ p ∈ (a :: rest).zip rest, ∀ x,
      (p.1 : ℝ) ≤ x → x ≤ (p.2 : ℝ) → f x ≤ T) : ∀ x, f x ≤ T := by
  induction rest generalizing a with
  | nil =>
    intro x
    by_cases hx : x ≤ (a : ℝ)
    · exact hleft x hx
    · exact hright x (le_of_lt (lt_of_not_ge hx))
  | cons b rest ih =>
    apply ih b
    · intro x hx
      by_cases ha : x ≤ (a : ℝ)
      · exact hleft x ha
      · exact hpieces (a, b) (by simp) x (le_of_lt (lt_of_not_ge ha)) hx
    · simpa only [List.getLastD_cons] using hright
    · intro p hp x hlo hhi
      exact hpieces p (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hp)
        x hlo hhi

def lowerEndpoint : ℤ := -949478975
def upperEndpoint : ℤ := 949478975
def depthThreshold : ℤ := 2001 * 10 ^ 21

set_option maxRecDepth 100000 in
lemma left_check : layers.all (fun a => decide
    (0 ≤ radius a ∧ lowerEndpoint ≤ center a - radius a)) = true := by decide

set_option maxRecDepth 100000 in
lemma right_check : layers.all (fun a => decide
    (0 ≤ radius a ∧ center a + radius a ≤ upperEndpoint)) = true := by decide

lemma depth_left (x : ℝ) (hx : x ≤ (lowerEndpoint : ℝ)) : depth layers x = 0 := by
  apply depth_zero_outside
  intro a ha
  have hc := of_decide_eq_true (List.all_eq_true.mp left_check a ha)
  constructor
  · exact_mod_cast hc.1
  · left
    have hh : (lowerEndpoint : ℝ) ≤ (center a : ℝ) - radius a := by exact_mod_cast hc.2
    linarith

lemma depth_right (x : ℝ) (hx : (upperEndpoint : ℝ) ≤ x) : depth layers x = 0 := by
  apply depth_zero_outside
  intro a ha
  have hc := of_decide_eq_true (List.all_eq_true.mp right_check a ha)
  constructor
  · exact_mod_cast hc.1
  · right
    have hh : (center a : ℝ) + radius a ≤ upperEndpoint := by exact_mod_cast hc.2
    linarith

def cutRest : List ℤ := [
  -948953398, -174239808, -173788170, -128852049, -128817626, -93134681, -92726932, -78117944,
  -78009582, -64042383, -63666992, -56598043, -56445792, -48861846, -48507942, -44339223,
  -44154614, -39346503, -39007404, -36248788, -36042692, -32695458, -32367092, -30399765,
  -30178864, -27697150, -27376922, -25898182, -25666548, -23740832, -23427009, -22270992,
  -22031220, -20484065, -20175446, -19243350, -18997173, -17719104, -17414824, -16643883,
  -16392502, -15311933, -15011362, -14359582, -14103862, -13171688, -12874352, -12312403,
  -12052974, -11234102, -10939644, -10446252, -10183588, -9451999, -9160146, -8719352,
  -8453810, -7789531, -7500078, -7099511, -6831364, -6218547, -5931339, -5561093,
  -5290546, -4716177, -4431103, -4082973, -3810181, -3263188, -2980173, -2647107,
  -2372181, -1842787, -1561787, -1237482, -960497, -439715, -160715, 160715,
  439715, 960497, 1237482, 1561787, 1842787, 2372181, 2647107, 2980173,
  3263188, 3810181, 4082973, 4431103, 4716177, 5290546, 5561093, 5931339,
  6218547, 6831364, 7099511, 7500078, 7789531, 8453810, 8719352, 9160146,
  9451999, 10183588, 10446252, 10939644, 11234102, 12052974, 12312403, 12874352,
  13171688, 14103862, 14359582, 15011362, 15311933, 16392502, 16643883, 17414824,
  17719104, 18997173, 19243350, 20175446, 20484065, 22031220, 22270992, 23427009,
  23740832, 25666548, 25898182, 27376922, 27697150, 30178864, 30399765, 32367092,
  32695458, 36042692, 36248788, 39007404, 39346503, 44154614, 44339223, 48507942,
  48861846, 56445792, 56598043, 63666992, 64042383, 78009582, 78117944, 92726932,
  93134681, 128817626, 128852049, 173788170, 174239808, 948953398, 949478975
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma pieces_check : ((lowerEndpoint :: cutRest).zip cutRest).all
    (fun p => decide (GoodPiece layers p.1 p.2 depthThreshold)) = true := by
  decide

lemma last_cut : cutRest.getLastD lowerEndpoint = upperEndpoint := by decide

theorem global_depth_bound (x : ℝ) : depth layers x ≤ (depthThreshold : ℝ) := by
  apply chain_bound (depth layers) (depthThreshold : ℝ) lowerEndpoint cutRest
  · intro y hy
    rw [depth_left y hy]
    norm_num [depthThreshold]
  · intro y hy
    rw [last_cut] at hy
    rw [depth_right y hy]
    norm_num [depthThreshold]
  · intro p hp y hlo hhi
    have hgood := of_decide_eq_true (List.all_eq_true.mp pieces_check p hp)
    exact goodPiece_bound layers p.1 p.2 depthThreshold hgood y hlo hhi

theorem layer_count : layers.length = 80 := by decide

/-- The finite indexed family consumed by the geometric lifting arguments. -/
abbrev Index := Fin layers.length

def datum (i : Index) : Layer := layers.get i

noncomputable def z (i : Index) : ℝ := (center (datum i) : ℝ) / 10 ^ 6
noncomputable def r (i : Index) : ℝ := (radius (datum i) : ℝ) / 10 ^ 6
noncomputable def w (i : Index) : ℝ := (weight (datum i) : ℝ) / 10 ^ 12

theorem index_card : Fintype.card Index = 80 := by
  simp only [Index, Fintype.card_fin, layer_count]

lemma datum_mem (i : Index) : datum i ∈ layers := List.get_mem layers i

theorem r_pos (i : Index) : 0 < r i := by
  apply div_pos
  · exact_mod_cast (positive (datum i) (datum_mem i)).1
  · norm_num

theorem w_pos (i : Index) : 0 < w i := by
  apply div_pos
  · exact_mod_cast (positive (datum i) (datum_mem i)).2
  · norm_num

set_option maxRecDepth 100000 in
lemma spatial_check : layers.all (fun a => decide
    (-950 * 10 ^ 6 < center a - radius a ∧ center a < 540 * 10 ^ 6 ∧
      radius a < 411 * 10 ^ 6 ∧ -540 * 10 ^ 6 < center a)) = true := by decide

lemma spatial_bounds (i : Index) :
    -950 * 10 ^ 6 < center (datum i) - radius (datum i) ∧
    center (datum i) < 540 * 10 ^ 6 ∧ radius (datum i) < 411 * 10 ^ 6 ∧
    -540 * 10 ^ 6 < center (datum i) :=
  of_decide_eq_true (List.all_eq_true.mp spatial_check (datum i) (datum_mem i))

theorem z_sub_r_gt_neg950 (i : Index) : (-950 : ℝ) < z i - r i := by
  dsimp only [z, r]
  rw [← sub_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)]
  exact_mod_cast (spatial_bounds i).1

theorem z_lt_540 (i : Index) : z i < 540 := by
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)).2
  exact_mod_cast (spatial_bounds i).2.1

theorem r_lt_411 (i : Index) : r i < 411 := by
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)).2
  exact_mod_cast (spatial_bounds i).2.2.1

theorem neg540_lt_z (i : Index) : (-540 : ℝ) < z i := by
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)).2
  exact_mod_cast (spatial_bounds i).2.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
lemma integer_center_strictMono : StrictMono (fun i : Index => center (datum i)) := by
  decide

theorem z_strictMono : StrictMono z := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 10 ^ 6)).2
  exact_mod_cast integer_center_strictMono hij

theorem z_injective : Function.Injective z := z_strictMono.injective

lemma sum_datum {α : Type*} [AddCommMonoid α] (f : Layer → α) :
    (∑ i : Index, f (datum i)) = (layers.map f).sum := by
  simpa only [datum, List.get_eq_getElem] using Fin.sum_univ_fun_getElem layers f

lemma cast_list_sum (s : List ℤ) : (s.sum : ℝ) = (s.map (fun n : ℤ => (n : ℝ))).sum := by
  induction s with
  | nil => simp
  | cons a s ih => simp only [List.sum_cons, Int.cast_add, List.map_cons, ih]

lemma weighted_scale (W V : ℝ) :
    (W / 10 ^ 12) * max 0 (V / 10 ^ 12) = W * max 0 V / 10 ^ 24 := by
  have hm : max 0 (V / (10 : ℝ) ^ 12) = max 0 V / 10 ^ 12 := by
    simpa only [zero_div] using max_div_div_right
      (by norm_num : (0 : ℝ) ≤ 10 ^ 12) 0 V
  rw [hm]
  ring

lemma real_degree_term_scaled (i j : Index) :
    w j * max 0 ((r i + r j) ^ 2 - (z i - z j) ^ 2) =
      ((weight (datum j) * max 0
        ((radius (datum i) + radius (datum j)) ^ 2 -
          (center (datum i) - center (datum j)) ^ 2) : ℤ) : ℝ) / 10 ^ 24 := by
  have hs : (r i + r j) ^ 2 - (z i - z j) ^ 2 =
      (((radius (datum i) : ℝ) + radius (datum j)) ^ 2 -
        ((center (datum i) : ℝ) - center (datum j)) ^ 2) / 10 ^ 12 := by
    dsimp only [r, z]
    ring
  rw [hs]
  dsimp only [w]
  rw [weighted_scale]
  simp only [Int.cast_mul, Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_pow,
    Int.cast_add]

lemma real_degree_eq_scaled (i : Index) :
    (∑ j : Index, w j * max 0 ((r i + r j) ^ 2 - (z i - z j) ^ 2)) =
      (degree (datum i) : ℝ) / 10 ^ 24 := by
  simp_rw [real_degree_term_scaled, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  rw [sum_datum (fun b : Layer => ((weight b * max 0
    ((radius (datum i) + radius b) ^ 2 - (center (datum i) - center b) ^ 2) : ℤ) : ℝ))]
  simp only [degree, cast_list_sum, List.map_map, Function.comp_def]

lemma real_depth_term_scaled (j : Index) (t : ℝ) :
    w j * max 0 ((r j) ^ 2 - (t - z j) ^ 2) =
      (weight (datum j) : ℝ) * max 0
        ((radius (datum j) : ℝ) ^ 2 - ((10 : ℝ) ^ 6 * t - center (datum j)) ^ 2) /
      10 ^ 24 := by
  have hs : (r j) ^ 2 - (t - z j) ^ 2 =
      ((radius (datum j) : ℝ) ^ 2 - ((10 : ℝ) ^ 6 * t - center (datum j)) ^ 2) /
        10 ^ 12 := by
    dsimp only [r, z]
    ring
  rw [hs]
  exact weighted_scale _ _

lemma real_depth_eq_scaled (t : ℝ) :
    (∑ j : Index, w j * max 0 ((r j) ^ 2 - (t - z j) ^ 2)) =
      depth layers ((10 : ℝ) ^ 6 * t) / 10 ^ 24 := by
  simp_rw [real_depth_term_scaled, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1

theorem real_degree_bound (i : Index) :
    (16047 : ℝ) / 1000 <
      ∑ j : Index, w j * max 0 ((r i + r j) ^ 2 - (z i - z j) ^ 2) := by
  rw [real_degree_eq_scaled]
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 24)).2
  have hd : (16047 * 10 ^ 21 : ℝ) < degree (datum i) := by
    exact_mod_cast every_degree (datum i) (datum_mem i)
  norm_num at hd ⊢
  exact hd

theorem real_depth_bound (t : ℝ) :
    (∑ j : Index, w j * max 0 ((r j) ^ 2 - (t - z j) ^ 2)) ≤ (2001 : ℝ) / 1000 := by
  rw [real_depth_eq_scaled]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 24)).2
  have hd := global_depth_bound ((10 : ℝ) ^ 6 * t)
  norm_num [depthThreshold] at hd ⊢
  exact hd

end FiniteLayerCertificate

/- Component: LayerLift; SHA256 7007f6e6b4ff5632f678358111a325186e78abf33a2294915b329fe13faa171f. -/
/-!
Ball-to-cap algebra for the finite layer certificate. The cap mass law is an
explicit hypothesis here; constructing the spherical probability measure and
proving its law are separate obligations. No measure or root is postulated.
Pinned Mathlib inner-product expansion/scalar rules and nonnegative square
comparison were inspected before this file was compiled.
-/
namespace PlyLayerLift

noncomputable section
open Set Metric
open scoped BigOperators

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev S := Metric.sphere (0 : E) 1

def cap (v : E) (t : ℝ) : Set S := {u | t ≤ inner ℝ (u : E) v}
def capArea (t : ℝ) : ℝ := min 1 (max 0 ((1-t)/2))

lemma unit_norm (u : S) : ‖(u : E)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using u.property

lemma scaled_dist_sq (R : ℝ) (hR : 0 ≤ R) (u : S) (x : E) :
    dist (R • (u : E)) x ^ 2 =
      R^2 + ‖x‖^2 - 2*R*inner ℝ (u : E) x := by
  rw [dist_eq_norm, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hR, unit_norm, real_inner_smul_left]
  ring

lemma normalized_norm (x : E) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

lemma cap_threshold_pos (R ρ r : ℝ) (hR : 0 < R) (hρ : 0 < ρ)
    (hr : 0 ≤ r) (hrR : r < R) :
    0 < (R^2+ρ^2-r^2)/(2*R*ρ) := by
  apply div_pos _ (by positivity)
  nlinarith [sq_nonneg ρ, mul_pos (sub_pos.mpr hrR) (by linarith : 0 < R+r)]

lemma cap_threshold_half (R ρ r : ℝ) (hR : 0 < R) (hρ : 0 < ρ)
    (hr : 0 ≤ r) (hrR : r ≤ R/2) :
    (1:ℝ)/2 ≤ (R^2+ρ^2-r^2)/(2*R*ρ) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*R*ρ)).2
  nlinarith [sq_nonneg (ρ-R/2), mul_nonneg (by linarith : 0 ≤ R/2-r)
    (by linarith : 0 ≤ R/2+r)]

lemma membership_cap (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r)
    (x : E) (hx : x ≠ 0) :
    {u : S | x ∈ closedBall (R • (u : E)) r} =
      cap (‖x‖⁻¹ • x) ((R^2 + ‖x‖^2-r^2)/(2*R*‖x‖)) := by
  ext u
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd : 0 < 2*R*‖x‖ := by positivity
  have hid : (‖x‖⁻¹ * inner ℝ (u : E) x) * (2*R*‖x‖) =
      2*R*inner ℝ (u : E) x := by field_simp
  simp only [mem_ofPred_eq, cap, mem_closedBall]
  rw [dist_comm, ← sq_le_sq₀ dist_nonneg hr, scaled_dist_sq R hR.le,
    div_le_iff₀ hd, real_inner_smul_right, hid]
  constructor <;> intro h <;> linarith

lemma capArea_radii (R ρ r : ℝ) (hR : 0 < R) (hρ : 0 < ρ)
    (hr : 0 ≤ r) (hrR : r < R) :
    capArea ((R^2+ρ^2-r^2)/(2*R*ρ)) =
      max 0 (r^2-(ρ-R)^2)/(4*R*ρ) := by
  have hden : 0 < 4*R*ρ := by positivity
  have hden' : 0 < 2*R*ρ := by positivity
  have ht := cap_threshold_pos R ρ r hR hρ hr hrR
  have he : (1-(R^2+ρ^2-r^2)/(2*R*ρ))/2 =
      (r^2-(ρ-R)^2)/(4*R*ρ) := by field_simp; ring
  unfold capArea
  rw [he]
  have hlt : (r^2-(ρ-R)^2)/(4*R*ρ) < 1 := by rw [← he]; linarith
  rw [min_eq_right (max_le (by norm_num) hlt.le)]
  by_cases hnum : 0 ≤ r^2-(ρ-R)^2
  · rw [max_eq_right hnum, max_eq_right (div_nonneg hnum hden.le)]
  · have hh : r^2-(ρ-R)^2 ≤ 0 := le_of_not_ge hnum
    rw [max_eq_left hh, max_eq_left (div_nonpos_of_nonpos_of_nonneg hh hden.le), zero_div]

/-- The only measure-specific input is the explicitly stated cap law. -/
theorem point_mass (mass : Set S → ℝ)
    (hcap : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t → mass (cap v t) = capArea t)
    (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (x : E) (hx : x ≠ 0) :
    mass {u : S | x ∈ closedBall (R • (u : E)) r} =
      max 0 (r^2-(‖x‖-R)^2)/(4*R*‖x‖) := by
  rw [membership_cap R r hR hr x hx,
    hcap _ (normalized_norm x hx) _
      (cap_threshold_pos R ‖x‖ r hR (norm_pos_iff.mpr hx) hr hrR),
    capArea_radii R ‖x‖ r hR
      (norm_pos_iff.mpr hx) hr hrR]

lemma origin_misses (R r : ℝ) (hR : 0 ≤ R) (hrR : r < R) :
    {u : S | (0 : E) ∈ closedBall (R • (u : E)) r} = ∅ := by
  ext u
  simp only [mem_ofPred_eq, mem_closedBall, dist_zero_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hR, unit_norm, mul_one,
    mem_empty_iff_false, iff_false]
  exact not_le_of_gt hrR

lemma balls_inter_iff (x y : E) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (closedBall x a ∩ closedBall y b).Nonempty ↔ dist x y ≤ a+b := by
  constructor
  · exact dist_le_add_of_nonempty_closedBall_inter_closedBall
  · intro h
    have hab : 0 < a+b := add_pos ha hb
    let t := a/(a+b)
    have ht : 0 ≤ t := div_nonneg ha.le hab.le
    have ht1 : t ≤ 1 := (div_le_one hab).mpr (by linarith)
    let p := (1-t) • x + t • y
    have hpx : p-x = t • (y-x) := by
      dsimp [p]
      rw [sub_smul, one_smul, smul_sub]
      abel
    have hpy : p-y = (1-t) • (x-y) := by
      dsimp [p]
      simp only [sub_smul, one_smul, smul_sub]
      abel
    refine ⟨p, ?_, ?_⟩
    · change dist p x ≤ a
      rw [dist_eq_norm, hpx, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      calc
        t * ‖y-x‖ ≤ t*(a+b) := by
          apply mul_le_mul_of_nonneg_left _ ht
          simpa only [← dist_eq_norm, dist_comm] using h
        _ = a := by dsimp [t]; field_simp
    · change dist p y ≤ b
      rw [dist_eq_norm, hpy, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1)]
      calc
        (1-t)*‖x-y‖ ≤ (1-t)*(a+b) := by
          apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht1)
          simpa only [dist_eq_norm] using h
        _ = b := by dsimp [t]; field_simp <;> ring

theorem neighborhood_mass (mass : Set S → ℝ)
    (hcap : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t → mass (cap v t) = capArea t)
    (Ri Rj ri rj : ℝ) (hRi : 0 < Ri) (hRj : 0 < Rj)
    (hri : 0 < ri) (hrj : 0 < rj) (hsum : ri+rj < Rj) (u : S) :
    mass {v : S | (closedBall (Ri • (u : E)) ri ∩
      closedBall (Rj • (v : E)) rj).Nonempty} =
      max 0 ((ri+rj)^2-(Ri-Rj)^2)/(4*Ri*Rj) := by
  have hn : ‖Ri • (u : E)‖ = Ri := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hRi.le, unit_norm, mul_one]
  have hx : Ri • (u : E) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hn]
    exact hRi.ne'
  have he : {v : S | (closedBall (Ri • (u : E)) ri ∩
      closedBall (Rj • (v : E)) rj).Nonempty} =
      {v : S | Ri • (u : E) ∈ closedBall (Rj • (v : E)) (ri+rj)} := by
    ext v
    exact balls_inter_iff _ _ _ _ hri hrj
  rw [he, point_mass mass hcap Rj (ri+rj) hRj (add_pos hri hrj).le
    hsum _ hx, hn]
  congr 1
  ring

def layerDepth {n : ℕ} (z r w : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, w i * max 0 ((r i)^2-(t-z i)^2)

def layerDegree {n : ℕ} (z r w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, w j * max 0 ((r i+r j)^2-(z i-z j)^2)

theorem weighted_depth_identity {n : ℕ} (mass : Set S → ℝ)
    (hcap : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t → mass (cap v t) = capArea t)
    (z r w : Fin n → ℝ) (R0 : ℝ)
    (hR : ∀ i, 0 < R0+z i) (hr : ∀ i, 0 ≤ r i)
    (hsmall : ∀ i, r i < R0+z i) (x : E) (hx : x ≠ 0) :
    (∑ i, (4*(R0+z i)*w i) *
      mass {u : S | x ∈ closedBall ((R0+z i) • (u : E)) (r i)}) =
      layerDepth z r w (‖x‖-R0)/‖x‖ := by
  unfold layerDepth
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [point_mass mass hcap (R0+z i) (r i) (hR i) (hr i) (hsmall i) x hx]
  have he : ‖x‖-(R0+z i) = ‖x‖-R0-z i := by ring
  rw [he]
  field_simp [(hR i).ne', norm_ne_zero_iff.mpr hx]
  <;> ring

theorem weighted_neighborhood_identity {n : ℕ} (mass : Set S → ℝ)
    (hcap : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t → mass (cap v t) = capArea t)
    (z r w : Fin n → ℝ) (R0 : ℝ)
    (hR : ∀ i, 0 < R0+z i) (hr : ∀ i, 0 < r i)
    (i : Fin n) (hsmall : ∀ j, r i+r j < R0+z j) (u : S) :
    (∑ j, (4*(R0+z j)*w j) * mass {v : S |
      (closedBall ((R0+z i) • (u : E)) (r i) ∩
       closedBall ((R0+z j) • (v : E)) (r j)).Nonempty}) =
      layerDegree z r w i/(R0+z i) := by
  unfold layerDegree
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [neighborhood_mass mass hcap (R0+z i) (R0+z j) (r i) (r j)
    (hR i) (hR j) (hr i) (hr j) (hsmall j) u]
  have he : (R0+z i)-(R0+z j) = z i-z j := by ring
  rw [he]
  field_simp [(hR i).ne', (hR j).ne']
  <;> ring

lemma layerDepth_zero_below {n : ℕ} (z r w : Fin n → ℝ) (t : ℝ)
    (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, t ≤ z i-r i) :
    layerDepth z r w t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hq : (r i)^2-(t-z i)^2 ≤ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ z i-t-r i by linarith [ht i])
      (show 0 ≤ z i-t+r i by linarith [ht i, hr i])]
  rw [max_eq_left hq, mul_zero]

theorem weighted_depth_bound {n : ℕ} (mass : Set S → ℝ)
    (hempty : mass ∅ = 0)
    (hcap : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t → mass (cap v t) = capArea t)
    (z r w : Fin n → ℝ) (R0 A K : ℝ)
    (hA : 0 < A) (hK : 0 ≤ K)
    (hR : ∀ i, 0 < R0+z i) (hr : ∀ i, 0 ≤ r i)
    (hsmall : ∀ i, r i < R0+z i)
    (hsupport : ∀ i, A ≤ R0+z i-r i)
    (hdepth : ∀ t, layerDepth z r w t ≤ K) (x : E) :
    (∑ i, (4*(R0+z i)*w i) *
      mass {u : S | x ∈ closedBall ((R0+z i) • (u : E)) (r i)}) ≤ K/A := by
  by_cases hx : x = 0
  · subst x
    have he : ∀ i, mass {u : S | (0:E) ∈
        closedBall ((R0+z i) • (u:E)) (r i)} = 0 := by
      intro i
      rw [origin_misses _ _ (hR i).le (hsmall i), hempty]
    simp only [he, mul_zero, Finset.sum_const_zero]
    exact div_nonneg hK hA.le
  rw [weighted_depth_identity mass hcap z r w R0 hR hr hsmall x hx]
  by_cases hρ : A ≤ ‖x‖
  · exact le_trans (div_le_div_of_nonneg_right (hdepth _) (norm_nonneg x))
      (div_le_div_of_nonneg_left hK hA hρ)
  · have ht : ∀ i, ‖x‖-R0 ≤ z i-r i := by
      intro i
      linarith [hsupport i]
    rw [layerDepth_zero_below z r w _ hr ht, zero_div]
    exact div_nonneg hK hA.le

theorem weighted_neighborhood_bound {n : ℕ} (mass : Set S → ℝ)
    (hcap : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t → mass (cap v t) = capArea t)
    (z r w : Fin n → ℝ) (R0 B D : ℝ) (hD : 0 ≤ D)
    (hR : ∀ i, 0 < R0+z i) (hr : ∀ i, 0 < r i)
    (hupper : ∀ i, R0+z i ≤ B)
    (hdegree : ∀ i, D ≤ layerDegree z r w i)
    (i : Fin n) (hsmall : ∀ j, r i+r j < R0+z j) (u : S) :
    D/B ≤ ∑ j, (4*(R0+z j)*w j) * mass {v : S |
      (closedBall ((R0+z i) • (u:E)) (r i) ∩
       closedBall ((R0+z j) • (v:E)) (r j)).Nonempty} := by
  rw [weighted_neighborhood_identity mass hcap z r w R0 hR hr i hsmall u]
  exact le_trans (div_le_div_of_nonneg_left hD (hR i) (hupper i))
    (div_le_div_of_nonneg_right (hdegree i) (hR i).le)

lemma numeric_spherical_gap :
    (3:ℝ)/200000000 < (16047/1000)/1000540 - 8*((2001/1000)/999050) := by
  norm_num

end
end PlyLayerLift

/- Component: SphereCaps; SHA256 24d79060ff276b9e7035f10c49d6759241557787e1184e654859b087222eb49d. -/
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal Pointwise

namespace PlySphereCaps

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev S := Metric.sphere (0 : E3) 1

def cap (v : E3) (t : ℝ) : Set S :=
  {u | t ≤ inner ℝ (u : E3) v}

def μ : Measure S :=
  (((volume : Measure E3).toSphere) Set.univ)⁻¹ •
    (volume : Measure E3).toSphere

instance μ_isProbabilityMeasure : IsProbabilityMeasure μ := by
  let : NeZero ((volume : Measure E3).toSphere) :=
    ⟨Measure.toSphere_ne_zero (volume : Measure E3)⟩
  unfold μ
  infer_instance

theorem sphere_area_univ :
    (volume : Measure E3).toSphere Set.univ = ENNReal.ofReal (4 * Real.pi) := by
  calc
    (volume : Measure E3).toSphere Set.univ =
        (3 : ℝ≥0∞) * ENNReal.ofReal (Real.pi * 4 / 3) := by simp
    _ = ENNReal.ofReal ((3 : ℝ) * (Real.pi * 4 / 3)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ = ENNReal.ofReal (4 * Real.pi) := by congr 1; ring

theorem sphere_norm (u : S) : ‖(u : E3)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using u.property

theorem cap_measurable (v : E3) (t : ℝ) : MeasurableSet (cap v t) := by
  exact measurableSet_le measurable_const
    (continuous_subtype_val.inner continuous_const).measurable

theorem inner_le_one (u : S) {v : E3} (hv : ‖v‖ = 1) :
    inner ℝ (u : E3) v ≤ 1 := by
  calc
    inner ℝ (u : E3) v ≤ ‖(u : E3)‖ * ‖v‖ := real_inner_le_norm _ _
    _ = 1 := by rw [sphere_norm, hv]; norm_num

theorem cap_eq_empty {v : E3} (hv : ‖v‖ = 1) {t : ℝ} (ht : 1 < t) :
    cap v t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact (not_le.mpr (ht.trans_le' (inner_le_one u hv))) hu

def radialCone (v : E3) (t : ℝ) : Set E3 :=
  {x | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ t * ‖x‖ ≤ inner ℝ x v}

def closedCone (v : E3) (t : ℝ) : Set E3 :=
  {x | ‖x‖ ≤ 1 ∧ t * ‖x‖ ≤ inner ℝ x v}

theorem closedCone_measurable (v : E3) (t : ℝ) :
    MeasurableSet (closedCone v t) :=
  (measurableSet_le continuous_norm.measurable measurable_const).inter
    (measurableSet_le (continuous_const.mul continuous_norm).measurable
      (continuous_id.inner continuous_const).measurable)

theorem volume_closedCone_isometry (L : E3 ≃ₗᵢ[ℝ] E3) (v : E3) (t : ℝ) :
    volume (closedCone (L v) t) = volume (closedCone v t) := by
  calc
    volume (closedCone (L v) t) =
        volume (L ⁻¹' closedCone (L v) t) :=
      (L.measurePreserving.measure_preimage
        (closedCone_measurable (L v) t).nullMeasurableSet).symm
    _ = volume (closedCone v t) := by
      congr 1
      ext x
      simp [closedCone]

theorem volume_closedCone_eq_of_norm_eq {v w : E3}
    (h : ‖v‖ = ‖w‖) (t : ℝ) :
    volume (closedCone v t) = volume (closedCone w t) := by
  let L : E3 ≃ₗᵢ[ℝ] E3 := Submodule.reflection (ℝ ∙ (v - w))ᗮ
  have hL : L v = w := Submodule.reflection_sub h
  simpa only [hL] using (volume_closedCone_isometry L v t).symm

theorem radialCone_ae_eq_closedCone (v : E3) (t : ℝ) :
    radialCone v t =ᵐ[(volume : Measure E3)] closedCone v t := by
  have hboundary : ∀ᵐ x ∂(volume : Measure E3), x ∉ Metric.sphere (0 : E3) 1 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using
      (Measure.addHaar_sphere (volume : Measure E3) (0 : E3) 1)
  filter_upwards [Measure.ae_ne (volume : Measure E3) 0, hboundary] with x hx hb
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hne : ‖x‖ ≠ 1 := by simpa only [mem_sphere, dist_zero_right] using hb
  apply propext
  change (0 < ‖x‖ ∧ ‖x‖ < 1 ∧ t * ‖x‖ ≤ inner ℝ x v) ↔
    (‖x‖ ≤ 1 ∧ t * ‖x‖ ≤ inner ℝ x v)
  constructor
  · rintro ⟨_, hlt, hi⟩
    exact ⟨hlt.le, hi⟩
  · rintro ⟨hle, hi⟩
    exact ⟨hpos, lt_of_le_of_ne hle hne, hi⟩

theorem volume_radialCone_eq (v : E3) (t : ℝ) :
    volume (radialCone v t) = volume (closedCone v t) :=
  measure_congr (radialCone_ae_eq_closedCone v t)

theorem radialCone_eq_smul (v : E3) (t : ℝ) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' cap v t) = radialCone v t := by
  ext x
  constructor
  · rintro ⟨a, ha, y, ⟨u, hu, rfl⟩, rfl⟩
    have hn : ‖a • (u : E3)‖ = a := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha.1, sphere_norm, mul_one]
    change 0 < ‖a • (u : E3)‖ ∧ ‖a • (u : E3)‖ < 1 ∧
      t * ‖a • (u : E3)‖ ≤ inner ℝ (a • (u : E3)) v
    rw [hn, real_inner_smul_left]
    exact ⟨ha.1, ha.2, by
      have := mul_le_mul_of_nonneg_left hu ha.1.le
      nlinarith⟩
  · intro hx
    rcases hx with ⟨hpos, hlt, hinner⟩
    let u : S := ⟨‖x‖⁻¹ • x, by
      simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']⟩
    have hu : u ∈ cap v t := by
      change t ≤ inner ℝ (‖x‖⁻¹ • x) v
      rw [real_inner_smul_left, mul_comm, ← div_eq_mul_inv]
      exact (le_div_iff₀ hpos).mpr hinner
    refine ⟨‖x‖, ⟨hpos, hlt⟩, (u : E3), ⟨u, hu, rfl⟩, ?_⟩
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

theorem sphere_area_cap (v : E3) (t : ℝ) :
    (volume : Measure E3).toSphere (cap v t) =
      3 * volume (radialCone v t) := by
  rw [Measure.toSphere_apply' _ (cap_measurable v t), radialCone_eq_smul]
  simp

theorem cone_sqrt_inequality {t z q : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    t * Real.sqrt (z ^ 2 + q ^ 2) ≤ z ↔
      q ^ 2 ≤ (1 / t ^ 2 - 1) * z ^ 2 := by
  have hsum : 0 ≤ z ^ 2 + q ^ 2 := by positivity
  have hsqrt : (Real.sqrt (z ^ 2 + q ^ 2)) ^ 2 = z ^ 2 + q ^ 2 :=
    Real.sq_sqrt hsum
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hr :
      q ^ 2 ≤ (1 / t ^ 2 - 1) * z ^ 2 ↔
        t ^ 2 * (z ^ 2 + q ^ 2) ≤ z ^ 2 := by
    have hid : (1 / t ^ 2 - 1) * z ^ 2 = ((1 - t ^ 2) * z ^ 2) / t ^ 2 := by
      field_simp
    rw [hid, le_div_iff₀ ht2]
    constructor <;> intro h <;> nlinarith
  rw [hr]
  have hsquare : (t * Real.sqrt (z ^ 2 + q ^ 2)) ^ 2 =
      t ^ 2 * (z ^ 2 + q ^ 2) := by rw [mul_pow, hsqrt]
  rw [← hsquare]
  exact (sq_le_sq₀ (by positivity) hz).symm

def coneSection (t z : ℝ) : Set E2 :=
  {y | z ^ 2 + ‖y‖ ^ 2 ≤ 1 ∧
    t * Real.sqrt (z ^ 2 + ‖y‖ ^ 2) ≤ z}

theorem coneSection_eq_closedBall {t z : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    coneSection t z =
      Metric.closedBall (0 : E2)
        (Real.sqrt (min (1 - z ^ 2) ((1 / t ^ 2 - 1) * z ^ 2))) := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hcoef : 0 ≤ 1 / t ^ 2 - 1 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ ht2).mpr
    nlinarith
  have hmin : 0 ≤ min (1 - z ^ 2) ((1 / t ^ 2 - 1) * z ^ 2) := by
    apply le_min
    · nlinarith
    · positivity
  ext y
  simp only [coneSection, mem_ofPred_eq, mem_closedBall, dist_zero_right,
    Real.le_sqrt (norm_nonneg _) hmin, le_min_iff,
    cone_sqrt_inequality ht hz]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

theorem coneSection_radius_sq_low {t z : ℝ}
    (ht : 0 < t) (hz : 0 ≤ z) (hzt : z ≤ t) :
    min (1 - z ^ 2) ((1 / t ^ 2 - 1) * z ^ 2) =
      (1 / t ^ 2 - 1) * z ^ 2 := by
  apply min_eq_right
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hz2 : z ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hz ht.le).mpr hzt
  have hd : z ^ 2 / t ^ 2 ≤ 1 := (div_le_one ht2).mpr hz2
  have hid : (1 / t ^ 2 - 1) * z ^ 2 + z ^ 2 = z ^ 2 / t ^ 2 := by
    ring
  nlinarith

theorem coneSection_radius_sq_high {t z : ℝ}
    (ht : 0 < t) (htz : t ≤ z) :
    min (1 - z ^ 2) ((1 / t ^ 2 - 1) * z ^ 2) = 1 - z ^ 2 := by
  apply min_eq_left
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hz2 : t ^ 2 ≤ z ^ 2 := (sq_le_sq₀ ht.le (ht.le.trans htz)).mpr htz
  have hd : 1 ≤ z ^ 2 / t ^ 2 := (le_div_iff₀ ht2).mpr (by simpa using hz2)
  have hid : (1 / t ^ 2 - 1) * z ^ 2 + z ^ 2 = z ^ 2 / t ^ 2 := by
    ring
  nlinarith

theorem cone_polynomial_integrals {t : ℝ} (ht : t ≠ 0) :
    (∫ z in (0 : ℝ)..t, (1 / t ^ 2 - 1) * z ^ 2) +
      (∫ z in t..1, (1 - z ^ 2)) = (2 / 3 : ℝ) * (1 - t) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_pow 2)]
  norm_num [integral_pow]
  field_simp
  ring

theorem coneSection_eq_empty {t z : ℝ} (ht : 0 < t)
    (hz : z < 0 ∨ 1 < z) : coneSection t z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  change z ^ 2 + ‖y‖ ^ 2 ≤ 1 ∧
    t * Real.sqrt (z ^ 2 + ‖y‖ ^ 2) ≤ z at hy
  rcases hz with hz | hz
  · have : 0 ≤ t * Real.sqrt (z ^ 2 + ‖y‖ ^ 2) := by positivity
    linarith [hy.2]
  · nlinarith [hy.1, sq_nonneg ‖y‖]

def splitCoords (x : E3) : ℝ × E2 :=
  (x 0, WithLp.toLp 2 (fun j : Fin 2 => x j.succ))

theorem splitCoords_norm_sq (x : E3) :
    ‖x‖ ^ 2 = (splitCoords x).1 ^ 2 + ‖(splitCoords x).2‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, splitCoords, Fin.sum_univ_succ]

theorem splitCoords_measurePreserving : MeasurePreserving splitCoords := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin 3)
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h₃ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin 2))
  convert h₃.comp (h₂.comp h₁) using 1
  · rfl
  · exact Measure.volume_eq_prod _ _

def axis : E3 := EuclideanSpace.single 0 1

theorem axis_norm : ‖axis‖ = 1 := by simp [axis]

def axisBody (t : ℝ) : Set (ℝ × E2) :=
  {p | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ 1 ∧
    t * Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) ≤ p.1}

theorem axisBody_measurable (t : ℝ) : MeasurableSet (axisBody t) := by
  have hc : Continuous (fun p : ℝ × E2 => p.1 ^ 2 + ‖p.2‖ ^ 2) :=
    (continuous_fst.pow 2).add (continuous_snd.norm.pow 2)
  exact (measurableSet_le hc.measurable measurable_const).inter
    (measurableSet_le (continuous_const.mul hc.sqrt).measurable continuous_fst.measurable)

theorem closedCone_axis_eq_preimage (t : ℝ) :
    closedCone axis t = splitCoords ⁻¹' axisBody t := by
  ext x
  change (‖x‖ ≤ 1 ∧ t * ‖x‖ ≤ inner ℝ x axis) ↔
    ((splitCoords x).1 ^ 2 + ‖(splitCoords x).2‖ ^ 2 ≤ 1 ∧
      t * Real.sqrt ((splitCoords x).1 ^ 2 + ‖(splitCoords x).2‖ ^ 2) ≤ x 0)
  rw [← splitCoords_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  have hi : inner ℝ x axis = x 0 := by
    simp [axis, EuclideanSpace.inner_single_right]
  rw [hi]
  have hn : ‖x‖ ^ 2 ≤ 1 ↔ ‖x‖ ≤ 1 := by
    constructor <;> intro h <;> nlinarith [norm_nonneg x]
  rw [hn]

theorem volume_closedCone_axis (t : ℝ) :
    volume (closedCone axis t) = ∫⁻ z : ℝ, volume (coneSection t z) := by
  rw [closedCone_axis_eq_preimage,
    splitCoords_measurePreserving.measure_preimage (axisBody_measurable t).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply (axisBody_measurable t)]
  rfl

theorem cone_coefficient_nonneg {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ 1 / t ^ 2 - 1 := by
  apply sub_nonneg.mpr
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  nlinarith

theorem coneSection_volume_low {t z : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hz : 0 ≤ z) (hzt : z ≤ t) :
    volume (coneSection t z) =
      ENNReal.ofReal (Real.pi * ((1 / t ^ 2 - 1) * z ^ 2)) := by
  have hnonneg : 0 ≤ (1 / t ^ 2 - 1) * z ^ 2 :=
    mul_nonneg (cone_coefficient_nonneg ht ht1) (sq_nonneg z)
  rw [coneSection_eq_closedBall ht ht1 hz (hzt.trans ht1),
    coneSection_radius_sq_low ht hz hzt, EuclideanSpace.volume_closedBall_fin_two,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt hnonneg,
    ENNReal.ofReal_mul Real.pi_pos.le]
  exact mul_comm _ _

theorem coneSection_volume_high {t z : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (htz : t ≤ z) (hz1 : z ≤ 1) :
    volume (coneSection t z) = ENNReal.ofReal (Real.pi * (1 - z ^ 2)) := by
  have hnonneg : 0 ≤ 1 - z ^ 2 := by nlinarith [ht.le.trans htz]
  rw [coneSection_eq_closedBall ht ht1 (ht.le.trans htz) hz1,
    coneSection_radius_sq_high ht htz, EuclideanSpace.volume_closedBall_fin_two,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt hnonneg,
    ENNReal.ofReal_mul Real.pi_pos.le]
  exact mul_comm _ _

theorem interval_lintegral_ofReal {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hfi : IntervalIntegrable f volume a b)
    (hnn : ∀ x ∈ Ioc a b, 0 ≤ f x) :
    (∫⁻ x in Ioc a b, ENNReal.ofReal (f x)) =
      ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab]
  symm
  apply ofReal_integral_eq_lintegral_ofReal hfi.1
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hnn x hx

theorem coneSection_integral_low {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∫⁻ z in Icc (0 : ℝ) t, volume (coneSection t z)) =
      ENNReal.ofReal (Real.pi * ∫ z in (0 : ℝ)..t, (1 / t ^ 2 - 1) * z ^ 2) := by
  calc
    (∫⁻ z in Icc (0 : ℝ) t, volume (coneSection t z)) =
        ∫⁻ z in Ioc (0 : ℝ) t, volume (coneSection t z) :=
      setLIntegral_congr Ioc_ae_eq_Icc.symm
    _ = ∫⁻ z in Ioc (0 : ℝ) t,
        ENNReal.ofReal (Real.pi * ((1 / t ^ 2 - 1) * z ^ 2)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro z hz
      exact coneSection_volume_low ht ht1 hz.1.le hz.2
    _ = ENNReal.ofReal (∫ z in (0 : ℝ)..t,
        Real.pi * ((1 / t ^ 2 - 1) * z ^ 2)) := by
      apply interval_lintegral_ofReal ht.le
      · exact (continuous_const.mul
          (continuous_const.mul (continuous_pow 2))).intervalIntegrable 0 t
      · intro z hz
        exact mul_nonneg Real.pi_pos.le
          (mul_nonneg (cone_coefficient_nonneg ht ht1) (sq_nonneg z))
    _ = _ := by rw [intervalIntegral.integral_const_mul]

theorem coneSection_integral_high {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∫⁻ z in Ioc t (1 : ℝ), volume (coneSection t z)) =
      ENNReal.ofReal (Real.pi * ∫ z in t..1, (1 - z ^ 2)) := by
  calc
    (∫⁻ z in Ioc t (1 : ℝ), volume (coneSection t z)) =
        ∫⁻ z in Ioc t (1 : ℝ), ENNReal.ofReal (Real.pi * (1 - z ^ 2)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro z hz
      exact coneSection_volume_high ht ht1 hz.1.le hz.2
    _ = ENNReal.ofReal (∫ z in t..1, Real.pi * (1 - z ^ 2)) := by
      apply interval_lintegral_ofReal ht1
      · exact (continuous_const.mul
          (continuous_const.sub (continuous_pow 2))).intervalIntegrable t 1
      · intro z hz
        apply mul_nonneg Real.pi_pos.le
        nlinarith [ht.le.trans hz.1.le, hz.2]
    _ = _ := by rw [intervalIntegral.integral_const_mul]

theorem volume_closedCone_axis_value {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    volume (closedCone axis t) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (1 - t)) := by
  rw [volume_closedCone_axis]
  have hsupport :
      Function.support (fun z : ℝ => volume (coneSection t z)) ⊆ Icc (0 : ℝ) 1 := by
    intro z hz
    by_contra h
    have hz' : z < 0 ∨ 1 < z := by
      simpa only [mem_Icc, not_and_or, not_le] using h
    change volume (coneSection t z) ≠ 0 at hz
    exact hz (by rw [coneSection_eq_empty ht hz', measure_empty])
  rw [← setLIntegral_eq_of_support_subset hsupport]
  have hu : Icc (0 : ℝ) 1 = Icc 0 t ∪ Ioc t 1 := by
    ext z
    simp only [mem_Icc, mem_union, mem_Ioc]
    constructor
    · intro hz
      by_cases hzt : z ≤ t
      · exact Or.inl ⟨hz.1, hzt⟩
      · exact Or.inr ⟨lt_of_not_ge hzt, hz.2⟩
    · rintro (hz | hz)
      · exact ⟨hz.1, hz.2.trans ht1⟩
      · exact ⟨ht.le.trans hz.1.le, hz.2⟩
  have hd : Disjoint (Icc (0 : ℝ) t) (Ioc t 1) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (not_lt_of_ge hz.2) hz'.1
  rw [hu, lintegral_union measurableSet_Ioc hd,
    coneSection_integral_low ht ht1, coneSection_integral_high ht ht1]
  have hlow : 0 ≤ ∫ z in (0 : ℝ)..t, (1 / t ^ 2 - 1) * z ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.le
      (fun z => mul_nonneg (cone_coefficient_nonneg ht ht1) (sq_nonneg z))
  have hhigh : 0 ≤ ∫ z in t..1, (1 - z ^ 2) := by
    apply intervalIntegral.integral_nonneg ht1
    intro z hz
    nlinarith [ht.le.trans hz.1, hz.2]
  rw [← ENNReal.ofReal_add (mul_nonneg Real.pi_pos.le hlow)
    (mul_nonneg Real.pi_pos.le hhigh)]
  congr 1
  rw [← mul_add, cone_polynomial_integrals ht.ne']
  ring

theorem cap_real_of_pos_le_one {v : E3} (hv : ‖v‖ = 1)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    μ.real (cap v t) = (1 - t) / 2 := by
  have hnorm : ‖v‖ = ‖axis‖ := hv.trans axis_norm.symm
  rw [Measure.real, μ, Measure.smul_apply, smul_eq_mul, sphere_area_univ,
    sphere_area_cap, volume_radialCone_eq,
    volume_closedCone_eq_of_norm_eq hnorm,
    volume_closedCone_axis_value ht ht1]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  norm_num
  field_simp
  ring

theorem cap_real {v : E3} (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) :
    μ.real (cap v t) = min 1 (max 0 ((1 - t) / 2)) := by
  by_cases ht1 : t ≤ 1
  · rw [cap_real_of_pos_le_one hv ht ht1,
      max_eq_right (by linarith), min_eq_right (by linarith)]
  · rw [cap_eq_empty hv (lt_of_not_ge ht1)]
    simp only [measureReal_empty]
    rw [max_eq_left (by linarith), min_eq_right (by norm_num)]


end PlySphereCaps

end

/- Component: FiniteCapApprox; SHA256 7ad78fabf8d6a5df39dcca1708fdcaa233872039c1c975d58451046cd7b890e6. -/
/-! Finite quantization conditional on an explicit spherical-cap law.
This file does not establish that law or a ball-family counterexample. -/

open Set Metric MeasureTheory
open scoped RealInnerProductSpace
open scoped Classical

namespace FiniteCapApprox

noncomputable section

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev S := Metric.sphere (0 : E) 1

def cap (v : E) (t : ℝ) : Set S := {u | t ≤ inner ℝ (u : E) v}

def profile (t : ℝ) : ℝ := min 1 (max 0 ((1 - t) / 2))

def CapLaw (μ : Measure S) : Prop :=
  ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, μ.real (cap v t) = profile t

def PositiveCapLaw (μ : Measure S) : Prop :=
  ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t → μ.real (cap v t) = profile t

theorem exists_simpleFunc_dist_lt {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] {h : ℝ} (hh : 0 < h) :
    ∃ f : SimpleFunc X X, ∀ x, dist (f x) x < h := by
  classical
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq X
  have hcover : (univ : Set X) ⊆ ⋃ n : ℕ, ball (e n) h := by
    intro x _
    obtain ⟨n, hn⟩ := he.exists_dist_lt x hh
    exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun n : ℕ => ball (e n) h) (fun _ => isOpen_ball) hcover
  refine ⟨SimpleFunc.nearestPt e (s.sup id), fun x => ?_⟩
  obtain ⟨n, hn, hnx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hnear := SimpleFunc.edist_nearestPt_le e x (Finset.le_sup (f := id) hn)
  apply edist_lt_ofReal.mp
  apply hnear.trans_lt
  exact edist_lt_ofReal.mpr (by simpa only [mem_ball, dist_comm, id_eq] using hnx)

theorem profile_sub_le (t h : ℝ) (hh : 0 ≤ h) :
    profile (t - h) ≤ profile t + h / 2 := by
  simp only [profile, min_def, max_def]
  split_ifs <;> linarith

theorem cap_quantization_bounds (f : S → S) {h : ℝ}
    (hf : ∀ u, dist (f u) u < h) (v : E) (hv : ‖v‖ = 1) (t : ℝ) :
    cap v (t + h) ⊆ f ⁻¹' cap v t ∧ f ⁻¹' cap v t ⊆ cap v (t - h) := by
  have hi (u : S) : |inner ℝ (f u : E) v - inner ℝ (u : E) v| < h := by
    have hcs := abs_real_inner_le_norm ((f u : E) - (u : E)) v
    rw [inner_sub_left, hv, mul_one] at hcs
    exact hcs.trans_lt (by simpa only [dist_eq_norm, Subtype.dist_eq] using hf u)
  constructor
  · intro u hu
    have hu' : t + h ≤ inner ℝ (u : E) v := hu
    have hd := (abs_lt.mp (hi u)).1
    change t ≤ inner ℝ (f u : E) v
    linarith
  · intro u hu
    have hu' : t ≤ inner ℝ (f u : E) v := hu
    have hd := (abs_lt.mp (hi u)).2
    change t - h ≤ inner ℝ (u : E) v
    linarith

theorem quantization_cap_error (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : CapLaw μ) (f : S → S) {h : ℝ} (hh : 0 ≤ h)
    (hf : ∀ u, dist (f u) u < h) (v : E) (hv : ‖v‖ = 1) (t : ℝ) :
    |μ.real (f ⁻¹' cap v t) - μ.real (cap v t)| ≤ h / 2 := by
  obtain ⟨hlo, hhi⟩ := cap_quantization_bounds f hf v hv t
  have h₁ := measureReal_mono (μ := μ) hlo
  have h₂ := measureReal_mono (μ := μ) hhi
  rw [hlaw v hv (t + h)] at h₁
  rw [hlaw v hv (t - h)] at h₂
  rw [hlaw v hv t]
  have hp := profile_sub_le t h hh
  have hm := profile_sub_le (t + h) h hh
  have heq : t + h - h = t := by ring
  rw [heq] at hm
  apply abs_le.mpr
  constructor <;> linarith

theorem exists_finite_cap_quantization (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : CapLaw μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : SimpleFunc S S, (∀ u, dist (f u) u < ε) ∧
      ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ,
        |μ.real (f ⁻¹' cap v t) - μ.real (cap v t)| ≤ ε / 2 := by
  letI : Nonempty S := nonempty_of_isProbabilityMeasure μ
  obtain ⟨f, hf⟩ := exists_simpleFunc_dist_lt (X := S) hε
  exact ⟨f, hf, fun v hv t => quantization_cap_error μ hlaw f hε.le hf v hv t⟩

theorem nullSingletonClass_of_capLaw (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : CapLaw μ) : NullSingletonClass μ := by
  constructor
  intro u
  have hu : ‖(u : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hcap : μ.real (cap (u : E) 1) = 0 := by
    rw [hlaw (u : E) hu]
    norm_num [profile]
  have hsub : ({u} : Set S) ⊆ cap (u : E) 1 := by
    intro x hx
    have hxu : x = u := Set.mem_singleton_iff.mp hx
    subst x
    change (1 : ℝ) ≤ inner ℝ (u : E) (u : E)
    rw [inner_self_eq_one_of_norm_eq_one hu]
  exact measure_mono_null hsub ((measureReal_eq_zero_iff (μ := μ)).mp hcap)

theorem exists_points_avoiding_of_nullSingleton (μ : Measure S) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (A : Set S) (hA : 0 < μ.real A)
    (F : Finset S) (n : ℕ) :
    ∃ P : Finset S, (↑P : Set S) ⊆ A ∧ Disjoint P F ∧ P.card = n := by
  classical
  have hInf : A.Infinite := by
    intro hFin
    have hz := hFin.measure_zero μ
    have hz' : μ.real A = 0 := by simp only [measureReal_def, hz, ENNReal.toReal_zero]
    linarith
  obtain ⟨P, hP, hcard⟩ := (hInf.sdiff F.finite_toSet).exists_subset_card_eq n
  refine ⟨P, fun x hx => (hP hx).1, ?_, hcard⟩
  exact Finset.disjoint_left.mpr fun x hx hxF => (hP hx).2 hxF

theorem exists_disjoint_points_family_of_nullSingleton
    (μ : Measure S) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {ι : Type*} (A : ι → Set S) (n : ι → ℕ)
    (s : Finset ι) (hA : ∀ i ∈ s, 0 < n i → 0 < μ.real (A i)) :
    ∃ P : ι → Finset S,
      (∀ i ∈ s, (↑(P i) : Set S) ⊆ A i ∧ (P i).card = n i) ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (P i) (P j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨P, hP, hPP⟩ := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    let F := s.biUnion P
    have hQ : ∃ Q : Finset S,
        (↑Q : Set S) ⊆ A i ∧ Disjoint Q F ∧ Q.card = n i := by
      by_cases hn : n i = 0
      · exact ⟨∅, by simp, by simp, by simp [hn]⟩
      · exact exists_points_avoiding_of_nullSingleton μ (A i)
          (hA i (Finset.mem_insert_self i s) (Nat.pos_of_ne_zero hn)) F (n i)
    obtain ⟨Q, hQA, hQF, hQn⟩ := hQ
    have hQP (j : ι) (hj : j ∈ s) : Disjoint Q (P j) := by
      apply Finset.disjoint_left.mpr
      intro x hxQ hxP
      apply Finset.disjoint_left.mp hQF hxQ
      exact Finset.mem_biUnion.mpr ⟨j, hj, hxP⟩
    refine ⟨Function.update P i Q, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using And.intro hQA hQn
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa [Function.update_of_ne hji] using hP j hj
    · intro j hj k hk hjk
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := Ne.symm hjk
        have hks : k ∈ s := (Finset.mem_insert.mp hk).resolve_left hki
        simpa [Function.update_of_ne hki] using hQP k hks
      · have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hji
        by_cases hki : k = i
        · subst k
          simpa [Function.update_of_ne hji] using (hQP j hjs).symm
        · have hks : k ∈ s := (Finset.mem_insert.mp hk).resolve_left hki
          simpa [Function.update_of_ne hji, Function.update_of_ne hki]
            using hPP j hjs k hks hjk

theorem exists_points_avoiding (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : CapLaw μ) (A : Set S) (hA : 0 < μ.real A)
    (F : Finset S) (n : ℕ) :
    ∃ P : Finset S, (↑P : Set S) ⊆ A ∧ Disjoint P F ∧ P.card = n := by
  letI := nullSingletonClass_of_capLaw μ hlaw
  exact exists_points_avoiding_of_nullSingleton μ A hA F n

theorem exists_disjoint_points_family (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : CapLaw μ) {ι : Type*} (A : ι → Set S) (n : ι → ℕ)
    (s : Finset ι) (hA : ∀ i ∈ s, 0 < n i → 0 < μ.real (A i)) :
    ∃ P : ι → Finset S,
      (∀ i ∈ s, (↑(P i) : Set S) ⊆ A i ∧ (P i).card = n i) ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (P i) (P j) := by
  letI := nullSingletonClass_of_capLaw μ hlaw
  exact exists_disjoint_points_family_of_nullSingleton μ A n s hA

theorem nullSingletonClass_of_positiveCapLaw (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : PositiveCapLaw μ) : NullSingletonClass μ := by
  constructor
  intro u
  have hu : ‖(u : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hcap : μ.real (cap (u : E) 1) = 0 := by
    rw [hlaw (u : E) hu 1 (by norm_num)]
    norm_num [profile]
  have hsub : ({u} : Set S) ⊆ cap (u : E) 1 := by
    intro x hx
    have hxu : x = u := Set.mem_singleton_iff.mp hx
    subst x
    change (1 : ℝ) ≤ inner ℝ (u : E) (u : E)
    rw [inner_self_eq_one_of_norm_eq_one hu]
  exact measure_mono_null hsub ((measureReal_eq_zero_iff (μ := μ)).mp hcap)

theorem floor_mass_error {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) :
    0 ≤ a - (⌊T * a⌋₊ : ℝ) / T ∧
      a - (⌊T * a⌋₊ : ℝ) / T < 1 / T := by
  have h₁ := Nat.floor_le (mul_nonneg hT.le ha)
  have h₂ := Nat.lt_floor_add_one (T * a)
  have hcancel : (⌊T * a⌋₊ : ℝ) / T * T = (⌊T * a⌋₊ : ℝ) :=
    div_mul_cancel₀ _ hT.ne'
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_iff₀ hT).mpr (by nlinarith)
  · apply (lt_div_iff₀ hT).mpr
    nlinarith

theorem exists_samples_with_fiber_counts
    (μ : Measure S) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {ι : Type*} [Fintype ι] (f : SimpleFunc S S) (W : ι → ℝ)
    (hW : ∀ i, 0 < W i) {T : ℝ} (hT : 0 < T) :
    ∃ Q : ι → Finset S,
      (∀ i a, a ∈ f.range →
        ((Q i).filter (fun u => f u = a)).card =
          ⌊T * (W i * μ.real (f ⁻¹' {a}))⌋₊) ∧
      ∀ i j, i ≠ j → Disjoint (Q i) (Q j) := by
  classical
  let s : Finset (ι × S) := Finset.univ.product f.range
  let A : (ι × S) → Set S := fun j => f ⁻¹' {j.2}
  let n : (ι × S) → ℕ := fun j => ⌊T * (W j.1 * μ.real (A j))⌋₊
  have hA : ∀ j ∈ s, 0 < n j → 0 < μ.real (A j) := by
    intro j _ hj
    have hp : 0 < T * (W j.1 * μ.real (A j)) := Nat.pos_of_floor_pos hj
    have hn : 0 ≤ μ.real (A j) := measureReal_nonneg
    by_contra! hz
    have he : μ.real (A j) = 0 := le_antisymm hz hn
    simp only [he, mul_zero, lt_self_iff_false] at hp
  obtain ⟨P, hP, hPP⟩ := exists_disjoint_points_family_of_nullSingleton μ A n s hA
  have hj (i : ι) (a : S) (ha : a ∈ f.range) : (i, a) ∈ s := by
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩
  let Q : ι → Finset S := fun i => f.range.biUnion (fun a => P (i, a))
  have hfiber (i : ι) (a : S) (ha : a ∈ f.range) :
      (Q i).filter (fun u => f u = a) = P (i, a) := by
    ext u
    constructor
    · intro hu
      obtain ⟨huQ, hua⟩ := Finset.mem_filter.mp hu
      obtain ⟨b, hb, hub⟩ := Finset.mem_biUnion.mp huQ
      have hub' : f u = b := (hP (i, b) (hj i b hb)).1 hub
      have hab : a = b := hua.symm.trans hub'
      simpa only [hab] using hub
    · intro hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨a, ha, hu⟩, ?_⟩
      exact (hP (i, a) (hj i a ha)).1 hu
  refine ⟨Q, ?_, ?_⟩
  · intro i a ha
    rw [hfiber i a ha]
    exact (hP (i, a) (hj i a ha)).2
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro u hui huj
    obtain ⟨a, ha, hua⟩ := Finset.mem_biUnion.mp hui
    obtain ⟨b, hb, hub⟩ := Finset.mem_biUnion.mp huj
    have hpij : (i, a) ≠ (j, b) := fun h => hij (congrArg Prod.fst h)
    exact Finset.disjoint_left.mp (hPP _ (hj i a ha) _ (hj j b hb) hpij) hua hub

def count (Q : Finset S) (B : Set S) : ℝ := by
  classical
  exact ((Q.filter (fun u => u ∈ B)).card : ℝ)

theorem count_mono (Q : Finset S) {A B : Set S} (h : A ⊆ B) :
    count Q A ≤ count Q B := by
  classical
  unfold count
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro u hu
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, h (Finset.mem_filter.mp hu).2⟩

theorem rounded_projected_count_error (μ : Measure S) [IsProbabilityMeasure μ]
    (f : SimpleFunc S S) (Q : Finset S) {W T : ℝ} (hW : 0 ≤ W) (hT : 0 < T)
    (hcounts : ∀ a ∈ f.range,
      (Q.filter (fun u => f u = a)).card = ⌊T * (W * μ.real (f ⁻¹' {a}))⌋₊)
    (B : Set S) :
    0 ≤ W * μ.real (f ⁻¹' B) - count Q (f ⁻¹' B) / T ∧
      W * μ.real (f ⁻¹' B) - count Q (f ⁻¹' B) / T ≤ (f.range.card : ℝ) / T := by
  classical
  let J := f.range.filter (fun a => a ∈ B)
  have hs : (∑ a ∈ J, μ.real (f ⁻¹' {a})) = μ.real (f ⁻¹' B) := by
    rw [sum_measureReal_preimage_singleton J (fun a _ => f.measurableSet_fiber a)]
    congr 1
    ext u
    simp only [J, Set.mem_preimage, Finset.mem_coe, Finset.mem_filter,
      f.mem_range_self u, true_and]
  have hc : (∑ a ∈ J, ⌊T * (W * μ.real (f ⁻¹' {a}))⌋₊) =
      (Q.filter (fun u => f u ∈ B)).card := by
    calc
      _ = ∑ a ∈ J, (Q.filter (fun u => f u = a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (hcounts a (Finset.mem_filter.mp ha).1).symm
      _ = (Q.filter (fun u => f u ∈ J)).card :=
        Finset.sum_card_fiberwise_eq_card_filter Q J f
      _ = _ := by
        congr 1
        ext u
        simp only [Finset.mem_filter, J, f.mem_range_self u, true_and]
  have hr : (∑ a ∈ J, (⌊T * (W * μ.real (f ⁻¹' {a}))⌋₊ : ℝ)) =
      count Q (f ⁻¹' B) := by
    rw [← Nat.cast_sum, hc]
    rfl
  have hid : W * μ.real (f ⁻¹' B) - count Q (f ⁻¹' B) / T =
      ∑ a ∈ J, (W * μ.real (f ⁻¹' {a}) -
        (⌊T * (W * μ.real (f ⁻¹' {a}))⌋₊ : ℝ) / T) := by
    symm
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, hs, hr]
  rw [hid]
  constructor
  · exact Finset.sum_nonneg fun a _ =>
      (floor_mass_error (mul_nonneg hW measureReal_nonneg) hT).1
  · calc
      _ ≤ ∑ _a ∈ J, (1 : ℝ) / T := Finset.sum_le_sum fun a _ =>
        (floor_mass_error (mul_nonneg hW measureReal_nonneg) hT).2.le
      _ = (J.card : ℝ) / T := by simp [div_eq_mul_inv]
      _ ≤ (f.range.card : ℝ) / T := by
        apply div_le_div_of_nonneg_right _ hT.le
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun a => a ∈ B) f.range)

theorem sampled_cap_error_positive (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : PositiveCapLaw μ) (f : SimpleFunc S S) (Q : Finset S)
    {W T h : ℝ} (hW : 0 ≤ W) (hT : 0 < T) (hh : 0 < h) (hh' : h < 1 / 8)
    (hf : ∀ u, dist (f u) u < h)
    (hcounts : ∀ a ∈ f.range,
      (Q.filter (fun u => f u = a)).card = ⌊T * (W * μ.real (f ⁻¹' {a}))⌋₊)
    (v : E) (hv : ‖v‖ = 1) (t : ℝ) (ht : 1 / 2 ≤ t) :
    |count Q (cap v t) / T - W * μ.real (cap v t)| ≤
      W * h + (f.range.card : ℝ) / T := by
  have hlo : f ⁻¹' cap v (t + h) ⊆ cap v t := by
    simpa only [add_sub_cancel_right] using
      (cap_quantization_bounds f hf v hv (t + h)).2
  have hhi : cap v t ⊆ f ⁻¹' cap v (t - h) := by
    simpa only [sub_add_cancel] using
      (cap_quantization_bounds f hf v hv (t - h)).1
  have hc₁ := div_le_div_of_nonneg_right (count_mono Q hlo) hT.le
  have hc₂ := div_le_div_of_nonneg_right (count_mono Q hhi) hT.le
  have hr₁ := (rounded_projected_count_error μ f Q hW hT hcounts (cap v (t + h))).2
  have hr₂ := (rounded_projected_count_error μ f Q hW hT hcounts (cap v (t - h))).1
  have hm₁ := measureReal_mono (μ := μ)
    (cap_quantization_bounds f hf v hv (t + h)).1
  have hm₂ := measureReal_mono (μ := μ)
    (cap_quantization_bounds f hf v hv (t - h)).2
  have he₁ : t + h + h = t + 2 * h := by ring
  have he₂ : t - h - h = t - 2 * h := by ring
  rw [he₁, hlaw v hv (t + 2 * h) (by linarith)] at hm₁
  rw [he₂, hlaw v hv (t - 2 * h) (by linarith)] at hm₂
  have hw₁ := mul_le_mul_of_nonneg_left hm₁ hW
  have hw₂ := mul_le_mul_of_nonneg_left hm₂ hW
  have hp := profile_sub_le t (2 * h) (by linarith)
  have hm := profile_sub_le (t + 2 * h) (2 * h) (by linarith)
  rw [add_sub_cancel_right] at hm
  have hwp := mul_le_mul_of_nonneg_left hp hW
  have hwm := mul_le_mul_of_nonneg_left hm hW
  have hn : 0 ≤ (f.range.card : ℝ) / T := div_nonneg (Nat.cast_nonneg _) hT.le
  rw [hlaw v hv t (by linarith)]
  apply abs_le.mpr
  constructor <;> nlinarith

theorem sampled_total_mass_error (μ : Measure S) [IsProbabilityMeasure μ]
    (f : SimpleFunc S S) (Q : Finset S) {W T : ℝ} (hW : 0 ≤ W) (hT : 0 < T)
    (hcounts : ∀ a ∈ f.range,
      (Q.filter (fun u => f u = a)).card = ⌊T * (W * μ.real (f ⁻¹' {a}))⌋₊) :
    0 ≤ W - (Q.card : ℝ) / T ∧
      W - (Q.card : ℝ) / T ≤ (f.range.card : ℝ) / T := by
  simpa [count, measureReal_def] using
    rounded_projected_count_error μ f Q hW hT hcounts Set.univ

theorem exists_uniform_samples_positive (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : PositiveCapLaw μ) {ι : Type*} [Fintype ι]
    (W : ι → ℝ) (hW : ∀ i, 0 < W i) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ T : ℝ, (N : ℝ) ≤ T →
      ∃ Q : ι → Finset S,
        (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
        (∀ i, |((Q i).card : ℝ) / T - W i| ≤ ε) ∧
        ∀ i (v : E), ‖v‖ = 1 → ∀ t : ℝ, 1 / 2 ≤ t →
          |count (Q i) (cap v t) / T - W i * μ.real (cap v t)| ≤ ε := by
  classical
  letI : Nonempty S := nonempty_of_isProbabilityMeasure μ
  letI := nullSingletonClass_of_positiveCapLaw μ hlaw
  let B : ℝ := (∑ i, W i) + 1
  have hsum : 0 ≤ ∑ i, W i := Finset.sum_nonneg fun i _ => (hW i).le
  have hB : 0 < B := by dsimp [B]; linarith
  have hWi (i : ι) : W i ≤ B := by
    have hi : W i ≤ ∑ j, W j :=
      Finset.single_le_sum (fun j _ => (hW j).le) (Finset.mem_univ i)
    dsimp [B]
    linarith
  let h : ℝ := min (1 / 16) (ε / (4 * B))
  have hh : 0 < h := lt_min (by norm_num) (div_pos hε (by positivity))
  have hh' : h < 1 / 8 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hWh (i : ι) : W i * h ≤ ε / 4 := by
    have hsmall : h ≤ ε / (4 * B) := min_le_right _ _
    have hsmall' := (le_div_iff₀ (show 0 < 4 * B by positivity)).mp hsmall
    have hw := mul_le_mul_of_nonneg_right (hWi i) hh.le
    nlinarith
  obtain ⟨f, hf⟩ := exists_simpleFunc_dist_lt (X := S) hh
  obtain ⟨N, hN⟩ := exists_nat_gt (1 + 2 * (f.range.card : ℝ) / ε)
  refine ⟨N, fun T hNT => ?_⟩
  have hm : 0 ≤ 2 * (f.range.card : ℝ) / ε := by positivity
  have hT : 0 < T := by linarith
  have hratio : (f.range.card : ℝ) / T ≤ ε / 2 := by
    have hbig : 2 * (f.range.card : ℝ) / ε < T := by linarith
    have hmul := (div_lt_iff₀ hε).mp hbig
    apply (div_le_iff₀ hT).mpr
    nlinarith
  obtain ⟨Q, hQ, hQQ⟩ := exists_samples_with_fiber_counts μ f W hW hT
  refine ⟨Q, hQQ, ?_, fun i v hv t ht => ?_⟩
  · intro i
    obtain ⟨hn, hb⟩ := sampled_total_mass_error μ f (Q i) (hW i).le hT (hQ i)
    apply abs_le.mpr
    constructor <;> linarith
  · have he := sampled_cap_error_positive μ hlaw f (Q i) (hW i).le hT hh hh'
      hf (hQ i) v hv t ht
    exact he.trans (by have hi := hWh i; linarith)

end

end FiniteCapApprox

/- Component: FiniteBallGap; SHA256 d61310fe6bdd9397c10150a1803141943d2939baf4f19342639a9dfdf92d4392. -/
/-!
Generic final counting bridge for Jig #2. The canonical Root body below was
read from sources/PlyGridOptimal.lean and copied as a proposition only; its
placeholder theorem is neither imported nor used. The paper-level lift in
finite-layer-lift.md supplies motivation, not a hypothesis silently assumed
by this module. All sampling and geometric estimates remain explicit inputs.

Scoped new API review: Nat.le_ceil and Nat.ceil_lt_add_one in
Mathlib/Algebra/Order/Floor/Semiring.lean:178,357; Archimedean real instance
and FloorRing in Algebra/Order/Archimedean/Real/Basic.lean:32-39;
Set.ncard_insert_of_notMem in Data/Set/Card.lean:715; the finite reindexing
pattern reuses the reviewed count_equiv/root_finite proof in SlackRemoval.
No source placeholder, native evaluation, custom elaborator, or axiom is used.
-/

namespace PlyFiniteBallGap

open Set Metric

noncomputable def pointCount {ι X : Type*} (B : ι → Set X) (p : X) : ℕ :=
  {i | p ∈ B i}.ncard

noncomputable def closedCount {ι X : Type*} (B : ι → Set X) (i : ι) : ℕ :=
  {j | (B j ∩ B i).Nonempty}.ncard

noncomputable def ordinaryCount {ι X : Type*} (B : ι → Set X) (i : ι) : ℕ :=
  {j | j ≠ i ∧ (B j ∩ B i).Nonempty}.ncard

lemma closedCount_eq_add_one {ι X : Type*} [Finite ι]
    (B : ι → Set X) (hB : ∀ i, (B i).Nonempty) (i : ι) :
    closedCount B i = ordinaryCount B i + 1 := by
  classical
  have hset : {j | (B j ∩ B i).Nonempty} =
      insert i {j | j ≠ i ∧ (B j ∩ B i).Nonempty} := by
    ext j
    by_cases h : j = i
    · subst j
      simp [hB i]
    · simp [h]
  unfold closedCount ordinaryCount
  rw [hset, Set.ncard_insert_of_notMem (by simp)]

/-- The constant nine pays eight for ceiling the ply bound and one for
removing the queried set from its own closed neighborhood. -/
theorem count_gap {ι X : Type*} [Finite ι]
    (B : ι → Set X) (hB : ∀ i, (B i).Nonempty)
    (A D : ℝ) (C : ℕ) (hA : 0 ≤ A)
    (hpoint : ∀ p, (pointCount B p : ℝ) ≤ A)
    (hclosed : ∀ i, D ≤ (closedCount B i : ℝ))
    (hgap : 8 * A + C + 9 < D) :
    ∃ k : ℕ, (∀ p, pointCount B p ≤ k) ∧
      ∀ i, 8 * k + C < ordinaryCount B i := by
  let k : ℕ := Nat.ceil A
  have hk_lower : A ≤ (k : ℝ) := Nat.le_ceil A
  have hk_upper : (k : ℝ) < A + 1 := Nat.ceil_lt_add_one hA
  refine ⟨k, ?_, ?_⟩
  · intro p
    exact_mod_cast (hpoint p).trans hk_lower
  · intro i
    have hc : (closedCount B i : ℝ) = (ordinaryCount B i : ℝ) + 1 := by
      exact_mod_cast closedCount_eq_add_one B hB i
    have hd := hclosed i
    have hh : 8 * (k : ℝ) + C < (ordinaryCount B i : ℝ) := by linarith
    exact_mod_cast hh

/-- Counting estimates produced by a sampler, with all error and rounding
losses explicit. No existence of such a sampler is asserted here. -/
theorem sampled_gap {ι X : Type*} [Finite ι]
    (B : ι → Set X) (hB : ∀ i, (B i).Nonempty)
    (T C : ℕ) (Ks Ds E : ℝ) (hbase : 0 ≤ Ks + E)
    (hpoint : ∀ p, (pointCount B p : ℝ) ≤ T * (Ks + E))
    (hclosed : ∀ i, T * (Ds - E) ≤ (closedCount B i : ℝ))
    (hscale : (C : ℝ) + 9 < T * (Ds - 8 * Ks - 9 * E)) :
    ∃ k : ℕ, (∀ p, pointCount B p ≤ k) ∧
      ∀ i, 8 * k + C < ordinaryCount B i := by
  apply count_gap B hB (T * (Ks + E)) (T * (Ds - E)) C
    (mul_nonneg (Nat.cast_nonneg T) hbase) hpoint hclosed
  nlinarith

/-- Positive surplus permits natural sample scales above any prescribed
lower bound, including the ceiling and self-removal allowance. -/
theorem exists_scale (gap : ℝ) (hgap : 0 < gap) (C N : ℕ) :
    ∃ T : ℕ, N ≤ T ∧ 0 < T ∧ (C : ℝ) + 9 < T * gap := by
  obtain ⟨T, hT⟩ := exists_nat_gt (max ((N : ℝ) + 1) (((C : ℝ) + 9) / gap))
  have hN : (N : ℝ) + 1 < T := (le_max_left _ _).trans_lt hT
  have hratio : ((C : ℝ) + 9) / gap < T := (le_max_right _ _).trans_lt hT
  refine ⟨T, ?_, ?_, (div_lt_iff₀ hgap).mp hratio⟩
  · have : (N : ℝ) ≤ T := by linarith
    exact_mod_cast this
  · have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (0 : ℝ) < T := by nlinarith
    exact_mod_cast this

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The exact proposition of the canonical root, restated without importing
the canonical placeholder theorem. -/
abbrev Root : Prop :=
  ∃ C : ℕ → ℕ,
    ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
      ∀ (x : Fin n → E d) (r : Fin n → ℝ),
        (∀ i, 0 < r i) → Function.Injective (fun i => (x i, r i)) →
        (∀ p, {i | p ∈ closedBall (x i) (r i)}.ncard ≤ k) →
        ∃ i₀, {i | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩
          closedBall (x i₀) (r i₀)).Nonempty}.ncard ≤ 2 ^ d * k + C d

def BallCounterexample (C : ℕ) : Prop :=
  ∃ (n k : ℕ) (x : Fin n → E 3) (r : Fin n → ℝ),
    0 < n ∧ (∀ i, 0 < r i) ∧ Function.Injective (fun i => (x i, r i)) ∧
    (∀ p, pointCount (fun i => closedBall (x i) (r i)) p ≤ k) ∧
    ∀ i, 8 * k + C < ordinaryCount (fun i => closedBall (x i) (r i)) i

lemma count_equiv {α β : Type*} (e : α ≃ β) (P : β → Prop) :
    {a | P (e a)}.ncard = {b | P b}.ncard := by
  apply Set.ncard_preimage_of_injective_subset_range e.injective
  intro b _
  exact e.surjective b

/-- Convert any finite nonempty index type, including a finite selected-point
subtype or sigma type, to the exact `Fin n` indexing of the root. -/
theorem counterexample_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    (C k : ℕ) (x : ι → E 3) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hinj : Function.Injective (fun i => (x i, r i)))
    (hthin : ∀ p, pointCount (fun i => closedBall (x i) (r i)) p ≤ k)
    (hdegree : ∀ i, 8 * k + C < ordinaryCount (fun i => closedBall (x i) (r i)) i) :
    BallCounterexample C := by
  letI : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, k, (fun j => x (e.symm j)), (fun j => r (e.symm j)),
    Fintype.card_pos, (fun j => hr (e.symm j)), hinj.comp e.symm.injective, ?_, ?_⟩
  · intro p
    exact (count_equiv e.symm (fun j => p ∈ closedBall (x j) (r j))).le.trans (hthin p)
  · intro i
    have hc := count_equiv e.symm (fun j => j ≠ e.symm i ∧
      (closedBall (x j) (r j) ∩ closedBall (x (e.symm i)) (r (e.symm i))).Nonempty)
    simp only [ne_eq, Equiv.apply_eq_iff_eq] at hc
    unfold ordinaryCount
    rw [hc]
    exact hdegree (e.symm i)

/-- The sampler-facing bridge. Geometry, injectivity, positivity, and uniform
counting estimates are explicit assumptions. -/
theorem ball_counterexample_of_counts {ι : Type*} [Finite ι] [Nonempty ι]
    (C T : ℕ) (Ks Ds error : ℝ) (hbase : 0 ≤ Ks + error)
    (x : ι → E 3) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hinj : Function.Injective (fun i => (x i, r i)))
    (hpoint : ∀ p, (pointCount (fun i => closedBall (x i) (r i)) p : ℝ) ≤
      T * (Ks + error))
    (hclosed : ∀ i, T * (Ds - error) ≤
      (closedCount (fun i => closedBall (x i) (r i)) i : ℝ))
    (hscale : (C : ℝ) + 9 < T * (Ds - 8 * Ks - 9 * error)) :
    BallCounterexample C := by
  obtain ⟨k, hk, hd⟩ := sampled_gap (fun i => closedBall (x i) (r i))
    (fun i => Metric.nonempty_closedBall.mpr (hr i).le) T C Ks Ds error
    hbase hpoint hclosed hscale
  exact counterexample_of_finite C k x r hr hinj hk hd

/-- Arbitrary additive surplus in dimension three refutes the exact root. -/
theorem not_root_of_counterexamples (hbad : ∀ C : ℕ, BallCounterexample C) : ¬ Root := by
  rintro ⟨C, hC⟩
  obtain ⟨n, k, x, r, hn, hr, hinj, hthin, hdegree⟩ := hbad (C 3)
  obtain ⟨i, hi⟩ := hC 3 k n (by decide) hn x r hr hinj hthin
  have hd := hdegree i
  norm_num at hi
  exact (not_lt_of_ge hi) hd

end PlyFiniteBallGap

/- Component: FiniteLayerLift; SHA256 ae158f3f1c9bce8eb712cdb6530182dba36c1313b6ccccb6668ed0d704a4cf92. -/
/-!
The exact eighty-layer certificate instantiated in the conditional spherical
lifting algebra. Both imported local sources were read before reliance; only
reviewed, green copies are to be staged under these Commons module paths.
The spherical cap law and the mass of the empty set remain explicit inputs.
This module does not construct a measure, sampler, or finite counterexample.
-/

namespace PlyFiniteLayerLift

noncomputable section

open Set Metric
open scoped BigOperators

abbrev Index := FiniteLayerCertificate.Index
abbrev E := PlyLayerLift.E
abbrev S := PlyLayerLift.S
abbrev z := FiniteLayerCertificate.z
abbrev r := FiniteLayerCertificate.r
abbrev w := FiniteLayerCertificate.w

def shellR (i : Index) : ℝ := 1000000 + z i
def W (i : Index) : ℝ := 4 * shellR i * w i
def Ks : ℝ := (2001 / 1000) / 999050
def Ds : ℝ := (16047 / 1000) / 1000540

def shellCenter (i : Index) (u : S) : E := shellR i • (u : E)
def ball (i : Index) (u : S) : Set E := closedBall (shellCenter i u) (r i)

theorem r_pos (i : Index) : 0 < r i := FiniteLayerCertificate.r_pos i
theorem w_pos (i : Index) : 0 < w i := FiniteLayerCertificate.w_pos i

theorem shellR_pos (i : Index) : 0 < shellR i := by
  dsimp only [shellR]
  linarith [FiniteLayerCertificate.neg540_lt_z i]

theorem W_pos (i : Index) : 0 < W i :=
  mul_pos (mul_pos (by norm_num) (shellR_pos i)) (w_pos i)

theorem Ks_pos : 0 < Ks := by norm_num [Ks]
theorem Ds_pos : 0 < Ds := by norm_num [Ds]

theorem sum_r_le_shell_half (i j : Index) : r i + r j ≤ shellR j / 2 := by
  dsimp only [shellR]
  linarith [FiniteLayerCertificate.r_lt_411 i, FiniteLayerCertificate.r_lt_411 j,
    FiniteLayerCertificate.neg540_lt_z j]

theorem r_le_shell_half (i : Index) : r i ≤ shellR i / 2 := by
  linarith [sum_r_le_shell_half i i, r_pos i]

theorem r_lt_shell (i : Index) : r i < shellR i :=
  (r_le_shell_half i).trans_lt (half_lt_self (shellR_pos i))

theorem sum_r_lt_shell (i j : Index) : r i + r j < shellR j :=
  (sum_r_le_shell_half i j).trans_lt (half_lt_self (shellR_pos j))

theorem shell_support (i : Index) : 999050 ≤ shellR i - r i := by
  dsimp only [shellR]
  linarith [FiniteLayerCertificate.z_sub_r_gt_neg950 i]

theorem shell_upper (i : Index) : shellR i ≤ 1000540 := by
  dsimp only [shellR]
  linarith [FiniteLayerCertificate.z_lt_540 i]

def pointThreshold (i : Index) (ρ : ℝ) : ℝ :=
  (shellR i ^ 2 + ρ ^ 2 - r i ^ 2) / (2 * shellR i * ρ)

def neighborhoodThreshold (i j : Index) : ℝ :=
  (shellR j ^ 2 + shellR i ^ 2 - (r i + r j) ^ 2) /
    (2 * shellR j * shellR i)

theorem point_threshold_half (i : Index) (ρ : ℝ) (hρ : 0 < ρ) :
    (1 : ℝ) / 2 ≤ pointThreshold i ρ :=
  PlyLayerLift.cap_threshold_half (shellR i) ρ (r i) (shellR_pos i) hρ
    (r_pos i).le (r_le_shell_half i)

theorem neighborhood_threshold_half (i j : Index) :
    (1 : ℝ) / 2 ≤ neighborhoodThreshold i j :=
  PlyLayerLift.cap_threshold_half (shellR j) (shellR i) (r i + r j)
    (shellR_pos j) (shellR_pos i) (add_pos (r_pos i) (r_pos j)).le
    (sum_r_le_shell_half i j)

theorem point_threshold_pos (i : Index) (ρ : ℝ) (hρ : 0 < ρ) :
    0 < pointThreshold i ρ := lt_of_lt_of_le (by norm_num) (point_threshold_half i ρ hρ)

theorem neighborhood_threshold_pos (i j : Index) :
    0 < neighborhoodThreshold i j :=
  lt_of_lt_of_le (by norm_num) (neighborhood_threshold_half i j)

lemma shellCenter_norm (i : Index) (u : S) : ‖shellCenter i u‖ = shellR i := by
  rw [shellCenter, norm_smul, Real.norm_eq_abs, abs_of_pos (shellR_pos i),
    PlyLayerLift.unit_norm, mul_one]

/-- Distinct heights make the full family of shell centers injective, even
when directions are repeated between different shells. -/
theorem shell_centers_injective :
    Function.Injective (fun a : Index × S => shellCenter a.1 a.2) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  have hR : shellR i = shellR j := by
    simpa only [shellCenter_norm] using congrArg norm h
  have hz : z i = z j := by
    dsimp only [shellR] at hR
    linarith
  have hij := FiniteLayerCertificate.z_injective hz
  subst j
  have huv : (u : E) = (v : E) := by
    have hh := congrArg (fun p : E => (shellR i)⁻¹ • p) h
    simpa only [shellCenter, smul_smul, inv_mul_cancel₀ (shellR_pos i).ne', one_smul] using hh
  exact Prod.ext rfl (Subtype.ext huv)

theorem selected_centers_injective (directions : Index → Finset S) :
    Function.Injective (fun a : (i : Index) × {u : S // u ∈ directions i} =>
      shellCenter a.1 a.2.1) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  have hp : (i, u.1) = (j, v.1) := shell_centers_injective h
  have hij : i = j := congrArg Prod.fst hp
  subst j
  have huv : u = v := Subtype.ext (congrArg Prod.snd hp)
  subst v
  rfl

theorem selected_balls_injective (directions : Index → Finset S) :
    Function.Injective (fun a : (i : Index) × {u : S // u ∈ directions i} =>
      (shellCenter a.1 a.2.1, r a.1)) := by
  intro a b h
  exact selected_centers_injective directions (congrArg Prod.fst h)

/-- Counts on the finite selected-point sigma type split into the sum of the
per-shell filtered counts. The decidability argument is computational only. -/
theorem selected_ncard (Q : Index → Finset S) (P : Index → S → Prop)
    [∀ i, DecidablePred (P i)] :
    {a : (i : Index) × {u : S // u ∈ Q i} | P a.1 a.2.1}.ncard =
      ∑ i : Index, ((Q i).filter (P i)).card := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  calc
    _ = ∑ a : (i : Index) × {u : S // u ∈ Q i},
        if P a.1 a.2.1 then (1 : ℕ) else 0 := by
      simpa using (Finset.natCast_card_filter (R := ℕ)
        (fun a : (i : Index) × {u : S // u ∈ Q i} => P a.1 a.2.1) Finset.univ)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ y : (Q i), if P i (y : S) then (1 : ℕ) else 0) = _
      rw [Finset.sum_coe_sort (Q i) (fun y : S => if P i y then (1 : ℕ) else 0)]
      simpa using (Finset.sum_boole (R := ℕ) (P i) (Q i))

theorem weighted_depth_bound (mass : Set S → ℝ) (hempty : mass ∅ = 0)
    (hcap : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t →
      mass (PlyLayerLift.cap v t) = PlyLayerLift.capArea t) (x : E) :
    (∑ i : Index, W i * mass {u : S | x ∈ ball i u}) ≤ Ks := by
  have hd (t : ℝ) : PlyLayerLift.layerDepth z r w t ≤ (2001 : ℝ) / 1000 :=
    FiniteLayerCertificate.real_depth_bound t
  simpa only [W, shellR, ball, shellCenter, Ks] using
    PlyLayerLift.weighted_depth_bound mass hempty hcap z r w 1000000 999050 (2001 / 1000)
      (by norm_num) (by norm_num) shellR_pos (fun i => (r_pos i).le)
      r_lt_shell shell_support hd x

theorem weighted_neighborhood_bound (mass : Set S → ℝ)
    (hcap : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t →
      mass (PlyLayerLift.cap v t) = PlyLayerLift.capArea t) (i : Index) (u : S) :
    Ds ≤ ∑ j : Index, W j * mass {v : S | (ball i u ∩ ball j v).Nonempty} := by
  have hd (j : Index) : (16047 : ℝ) / 1000 ≤ PlyLayerLift.layerDegree z r w j :=
    (FiniteLayerCertificate.real_degree_bound j).le
  simpa only [W, shellR, ball, shellCenter, Ds] using
    PlyLayerLift.weighted_neighborhood_bound mass hcap z r w 1000000 1000540
      (16047 / 1000) (by norm_num) shellR_pos r_pos shell_upper hd i
      (sum_r_lt_shell i) u

theorem spherical_gap : (3 : ℝ) / 200000000 < Ds - 8 * Ks := by
  simpa only [Ds, Ks] using PlyLayerLift.numeric_spherical_gap

end
end PlyFiniteLayerLift

/- Component: SampleRefutation; SHA256 73712ce19e255750e4a0031505aa7272e1a29af1047b178a8f58e904074d6657. -/
/-! Uniform finite cap samples imply the faithful root's negation.
The conditional construction is instantiated with the checked spherical
probability measure and positive-cap law in the final refutation. -/

namespace PlySampleRefutation

noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators
open PlyFiniteLayerLift

abbrev Samples (Q : Index → Finset S) := (i : Index) × {u : S // u ∈ Q i}
abbrev B := PlyFiniteLayerLift.ball
def family (Q : Index → Finset S) (a : Samples Q) : Set E := B a.1 a.2.1

lemma point_set_cap (i : Index) (x : E) (hx : x ≠ 0) :
    {u : S | x ∈ B i u} =
      FiniteCapApprox.cap (‖x‖⁻¹ • x) (pointThreshold i ‖x‖) := by
  exact PlyLayerLift.membership_cap (shellR i) (r i) (shellR_pos i) (r_pos i).le x hx

lemma neighborhood_set_cap (i j : Index) (u : S) :
    {v : S | (B i u ∩ B j v).Nonempty} =
      FiniteCapApprox.cap (‖shellCenter i u‖⁻¹ • shellCenter i u)
        (neighborhoodThreshold i j) := by
  have hx : shellCenter i u ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [shellCenter_norm]
    exact (shellR_pos i).ne'
  have he : {v : S | (B i u ∩ B j v).Nonempty} =
      {v : S | shellCenter i u ∈ closedBall (shellCenter j v) (r i+r j)} := by
    ext v
    exact PlyLayerLift.balls_inter_iff _ _ _ _ (r_pos i) (r_pos j)
  rw [he]
  have hm := PlyLayerLift.membership_cap (shellR j) (r i+r j) (shellR_pos j)
    (add_pos (r_pos i) (r_pos j)).le (shellCenter i u) hx
  simpa only [shellCenter, norm_smul, Real.norm_eq_abs,
    abs_of_pos (shellR_pos i), PlyLayerLift.unit_norm, mul_one,
    neighborhoodThreshold, FiniteCapApprox.cap, PlyLayerLift.cap] using hm

lemma sampled_count_sum (Q : Index → Finset S) (P : Index → S → Prop) (T : ℝ) :
    ({a : Samples Q | P a.1 a.2.1}.ncard : ℝ) / T =
      ∑ i, FiniteCapApprox.count (Q i) {u | P i u} / T := by
  classical
  rw [selected_ncard, Nat.cast_sum, Finset.sum_div]
  rfl

theorem counts_from_cap_samples (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : FiniteCapApprox.PositiveCapLaw μ)
    (Q : Index → Finset S) (T ε : ℝ) (hT : 0 < T) (hε : 0 ≤ ε)
    (hQ : ∀ i (v : E), ‖v‖ = 1 → ∀ t : ℝ, 1/2 ≤ t →
      |FiniteCapApprox.count (Q i) (FiniteCapApprox.cap v t) / T -
        W i * μ.real (FiniteCapApprox.cap v t)| ≤ ε) :
    (∀ x, (PlyFiniteBallGap.pointCount (family Q) x : ℝ) ≤ T*(Ks+80*ε)) ∧
    ∀ a : Samples Q, T*(Ds-80*ε) ≤
      (PlyFiniteBallGap.closedCount (family Q) a : ℝ) := by
  classical
  have hgeom : ∀ v : E, ‖v‖ = 1 → ∀ t : ℝ, 0 < t →
      μ.real (PlyLayerLift.cap v t) = PlyLayerLift.capArea t := hlaw
  have hpoint (x : E) (i : Index) :
      |FiniteCapApprox.count (Q i) {u : S | x ∈ B i u} / T -
        W i * μ.real {u : S | x ∈ B i u}| ≤ ε := by
    by_cases hx : x = 0
    · subst x
      have he : {u : S | (0:E) ∈ B i u} = ∅ :=
        PlyLayerLift.origin_misses (shellR i) (r i) (shellR_pos i).le (r_lt_shell i)
      simp only [he, FiniteCapApprox.count, Set.mem_empty_iff_false, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero, zero_div, measureReal_empty,
        mul_zero, sub_self, abs_zero]
      exact hε
    · rw [point_set_cap i x hx]
      exact hQ i _ (PlyLayerLift.normalized_norm x hx) _
        (point_threshold_half i ‖x‖ (norm_pos_iff.mpr hx))
  have hneighbor (i j : Index) (u : S) :
      |FiniteCapApprox.count (Q j) {v : S | (B i u ∩ B j v).Nonempty} / T -
        W j * μ.real {v : S | (B i u ∩ B j v).Nonempty}| ≤ ε := by
    have hx : shellCenter i u ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [shellCenter_norm]
      exact (shellR_pos i).ne'
    rw [neighborhood_set_cap i j u]
    exact hQ j _ (PlyLayerLift.normalized_norm _ hx) _ (neighborhood_threshold_half i j)
  constructor
  · intro x
    have hs : (∑ i, FiniteCapApprox.count (Q i) {u : S | x ∈ B i u} / T) ≤
        (∑ i, W i * μ.real {u : S | x ∈ B i u}) + 80*ε := by
      calc
        _ ≤ ∑ i, (W i * μ.real {u : S | x ∈ B i u} + ε) := by
          apply Finset.sum_le_sum
          intro i _
          have h := (abs_le.mp (hpoint x i)).2
          linarith
        _ = _ := by simp [Finset.sum_add_distrib, FiniteLayerCertificate.layer_count]
    have hb := weighted_depth_bound μ.real (by simp) hgeom x
    have hc : (PlyFiniteBallGap.pointCount (family Q) x : ℝ)/T ≤ Ks+80*ε := by
      rw [PlyFiniteBallGap.pointCount]
      change ({a : Samples Q | x ∈ B a.1 a.2.1}.ncard : ℝ)/T ≤ _
      rw [sampled_count_sum Q (fun i u => x ∈ B i u) T]
      linarith
    have ht := (div_le_iff₀ hT).mp hc
    nlinarith
  · intro a
    have hs : (∑ j, W j * μ.real {v : S | (B a.1 a.2.1 ∩ B j v).Nonempty}) - 80*ε ≤
        ∑ j, FiniteCapApprox.count (Q j) {v : S | (B a.1 a.2.1 ∩ B j v).Nonempty} / T := by
      calc
        _ = ∑ j, (W j * μ.real {v : S | (B a.1 a.2.1 ∩ B j v).Nonempty} - ε) := by
          simp [Finset.sum_sub_distrib, FiniteLayerCertificate.layer_count]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          have h := (abs_le.mp (hneighbor a.1 j a.2.1)).1
          linarith
    have hb := weighted_neighborhood_bound μ.real hgeom a.1 a.2.1
    have hc : Ds-80*ε ≤ (PlyFiniteBallGap.closedCount (family Q) a : ℝ)/T := by
      unfold PlyFiniteBallGap.closedCount family
      simp_rw [Set.inter_comm (B _ _) (B a.1 a.2.1)]
      rw [sampled_count_sum Q (fun j v => (B a.1 a.2.1 ∩ B j v).Nonempty) T]
      linarith
    have ht := (le_div_iff₀ hT).mp hc
    nlinarith

theorem not_root_of_positive_cap_law (μ : Measure S) [IsProbabilityMeasure μ]
    (hlaw : FiniteCapApprox.PositiveCapLaw μ) : ¬ PlyFiniteBallGap.Root := by
  classical
  apply PlyFiniteBallGap.not_root_of_counterexamples
  intro C
  let i₀ : Index := ⟨0, by decide⟩
  let ε : ℝ := min (1/1000000000000) (W i₀/2)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos (W_pos i₀) (by norm_num))
  have hεsmall : ε ≤ 1/1000000000000 := min_le_left _ _
  have hεW : ε ≤ W i₀/2 := min_le_right _ _
  have hgap : 0 < Ds-8*Ks-9*(80*ε) := by
    have hg := spherical_gap
    linarith
  obtain ⟨N, hN⟩ := FiniteCapApprox.exists_uniform_samples_positive μ hlaw W W_pos hε
  obtain ⟨T, hNT, hT, hscale⟩ := PlyFiniteBallGap.exists_scale
    (Ds-8*Ks-9*(80*ε)) hgap C N
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  obtain ⟨Q, _, hmass, hcaps⟩ := hN T (by exact_mod_cast hNT)
  have hQpos : 0 < (Q i₀).card := by
    have hm := (abs_le.mp (hmass i₀)).1
    have hw := W_pos i₀
    have hc : (0:ℝ) < (Q i₀).card / T := by linarith
    have hp : (0:ℝ) < (Q i₀).card := by
      rcases div_pos_iff.mp hc with h | h
      · exact h.1
      · linarith [h.2]
    exact_mod_cast hp
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hQpos
  letI : Nonempty (Samples Q) := ⟨⟨i₀, ⟨u, hu⟩⟩⟩
  obtain ⟨hp, hd⟩ := counts_from_cap_samples μ hlaw Q T ε hTr hε.le hcaps
  exact PlyFiniteBallGap.ball_counterexample_of_counts C T Ks Ds (80*ε)
    (add_nonneg Ks_pos.le (mul_nonneg (by norm_num) hε.le))
    (fun a : Samples Q => shellCenter a.1 a.2.1)
    (fun a => r a.1) (fun a => r_pos a.1) (selected_balls_injective Q)
    hp hd hscale

theorem refutation : ¬ PlyFiniteBallGap.Root := by
  apply not_root_of_positive_cap_law PlySphereCaps.μ
  intro v hv t ht
  exact PlySphereCaps.cap_real hv ht

end
end PlySampleRefutation

theorem proof : ¬ PlyFiniteBallGap.Root :=
  PlySampleRefutation.refutation

end Submissions.PlyGridOptimalRefuted.Counterexample
