import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace Submissions.QuarticUPBTwoModFour.Assembly

/- Source: cusp_assembly/OddGraph.lean. Reused authorship is retained in the source comments and artifact citations. -/
namespace P14OddGraph

abbrev Cyclic (N : ℕ) := ZMod (2*N+1)
abbrev Vertex (N : ℕ) := Cyclic N ⊕ Cyclic N

instance (N : ℕ) : NeZero (2*N+1) := ⟨by omega⟩

lemma double_inverse (N : ℕ) : (2 : Cyclic N) * (N+1) = 1 := by
  have h := ZMod.natCast_self (2*N+1)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  linear_combination h

lemma double_injective (N : ℕ) : Function.Injective (fun x : Cyclic N => 2*x) := by
  intro x y he
  have h := congrArg (fun z : Cyclic N => (N+1)*z) he
  have hi : ((N : Cyclic N)+1) * 2 = 1 := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using double_inverse N
  simpa only [← mul_assoc, hi, one_mul] using h

/-- The two translate matchings alone connect the odd cyclic bipartite graph. -/
theorem connected_of_two_matchings (N : ℕ) (G : SimpleGraph (Vertex N))
    (h0 : ∀ i : Cyclic N, G.Adj (.inl i) (.inr (i-1)))
    (h2 : ∀ i : Cyclic N, G.Adj (.inl i) (.inr (i+1))) : G.Connected := by
  have hstep (i : Cyclic N) : G.Reachable (.inl i) (.inl (i+2)) :=
    (h2 i).reachable.trans (by convert (h0 (i+2)).symm.reachable using 1; congr 2; ring)
  have hnat : ∀ t : ℕ, G.Reachable (.inl 0) (.inl (2*(t : Cyclic N))) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h := ih.trans (hstep (2*(t : Cyclic N)))
      simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using h
  have hleft (i : Cyclic N) : G.Reachable (.inl 0) (.inl i) := by
    have h := hnat ((N+1)*i.val)
    have hi : (2 : Cyclic N) * (((N+1)*i.val : ℕ) : Cyclic N) = i := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
      rw [← mul_assoc, double_inverse, one_mul]
    simpa only [hi] using h
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨.inl 0, ?_⟩
  rintro (i | i)
  · exact hleft i
  · exact (hleft (i+1)).trans (by simpa using (h0 (i+1)).reachable)

def defect (N : ℕ) (t : Fin 4) : Cyclic N := N + t.val

lemma defect_injective (N : ℕ) (hN : 3 ≤ N) : Function.Injective (defect N) := by
  intro s t h
  have hval := congrArg ZMod.val h
  have hs : N+s.val < 2*N+1 := by omega
  have ht : N+t.val < 2*N+1 := by omega
  simp only [defect, ← Nat.cast_add] at hval
  rw [ZMod.val_natCast_of_lt hs, ZMod.val_natCast_of_lt ht] at hval
  exact Fin.ext (by omega)

lemma double_defect (N : ℕ) (t : Fin 4) :
    2 * defect N t = 2 * (t.val : Cyclic N) - 1 := by
  have h := double_inverse N
  dsimp [defect]
  linear_combination h

/-- Normalize the right labels by subtracting one; the cross relation becomes symmetric. -/
def cross (N : ℕ) (x : Cyclic N) : Finset (Cyclic N) :=
  {x-1,x+1,-x,-x+4}

lemma cross_symm (N : ℕ) (x y : Cyclic N) : y ∈ cross N x ↔ x ∈ cross N y := by
  simp only [cross, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> rintro (h | h | h | h)
  · right; left; linear_combination -h
  · left; linear_combination -h
  · right; right; left; linear_combination h
  · right; right; right; linear_combination h
  · right; left; linear_combination -h
  · left; linear_combination -h
  · right; right; left; linear_combination h
  · right; right; right; linear_combination h

lemma cross_collisions (N : ℕ) (x : Cyclic N) :
    (x-1 = -x ↔ x = defect N 1) ∧
    (x-1 = -x+4 ↔ x = defect N 3) ∧
    (x+1 = -x ↔ x = defect N 0) ∧
    (x+1 = -x+4 ↔ x = defect N 2) := by
  have hd := double_defect N
  have hi := double_injective N
  constructor
  · constructor
    · intro h; apply hi; have he := hd 1; norm_num at he; linear_combination h - he
    · rintro rfl; have he := hd 1; norm_num at he; linear_combination he
  constructor
  · constructor
    · intro h; apply hi; have he := hd 3; norm_num at he; linear_combination h - he
    · rintro rfl; have he := hd 3; norm_num at he; linear_combination he
  constructor
  · constructor
    · intro h; apply hi; have he := hd 0; norm_num at he; linear_combination h - he
    · rintro rfl; have he := hd 0; norm_num at he; linear_combination he
  · constructor
    · intro h; apply hi; have he := hd 2; norm_num at he; linear_combination h - he
    · rintro rfl; have he := hd 2; norm_num at he; linear_combination he

lemma natCast_ne_zero (N k : ℕ) (hk : 0 < k) (hlt : k < 2*N+1) :
    (k : Cyclic N) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
  omega

lemma cross_branch_distinct (N : ℕ) (hN : 3 ≤ N) (x : Cyclic N) :
    x-1 ≠ x+1 ∧ -x ≠ -x+4 := by
  constructor
  · intro h
    apply natCast_ne_zero N 2 (by omega) (by omega)
    linear_combination -h
  · intro h
    apply natCast_ne_zero N 4 (by omega) (by omega)
    linear_combination -h

theorem cross_card (N : ℕ) (hN : 3 ≤ N) (x : Cyclic N) :
    (cross N x).card = if ∃ t : Fin 4, x = defect N t then 3 else 4 := by
  classical
  have hd := defect_injective N hN
  have hc := cross_collisions N x
  have hb := cross_branch_distinct N hN x
  have hs (s t : Fin 4) : defect N s = defect N t ↔ s = t := hd.eq_iff
  have hex : (∃ t : Fin 4, x = defect N t) ↔
      x = defect N 0 ∨ x = defect N 1 ∨ x = defect N 2 ∨ x = defect N 3 := by
    constructor
    · rintro ⟨t, ht⟩; fin_cases t <;> simp_all
    · rintro (h | h | h | h)
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
      · exact ⟨3,h⟩
  simp only [cross, Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
    hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hb.1, hb.2, false_or,
    Finset.card_singleton, hex]
  by_cases h0 : x = defect N 0
  · subst x; simp [hs]
  by_cases h1 : x = defect N 1
  · subst x; simp [hs]
  by_cases h2 : x = defect N 2
  · subst x; simp [hs]
  by_cases h3 : x = defect N 3
  · subst x; simp [hs]
  simp [h0,h1,h2,h3]

def pair : Fin 4 → Fin 4 := ![1,0,3,2]

lemma pair_involutive : Function.Involutive pair := by intro t; fin_cases t <;> rfl

lemma pair_ne (t : Fin 4) : pair t ≠ t := by fin_cases t <;> decide

def within (N : ℕ) (x : Cyclic N) : Finset (Cyclic N) :=
  (Finset.univ.filter (fun t : Fin 4 => x = defect N t)).image (fun t => defect N (pair t))

lemma mem_within (N : ℕ) (x y : Cyclic N) :
    y ∈ within N x ↔ ∃ t : Fin 4, x = defect N t ∧ y = defect N (pair t) := by
  simp only [within, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun t => and_congr_right fun _ => eq_comm

lemma within_symm (N : ℕ) (x y : Cyclic N) : y ∈ within N x ↔ x ∈ within N y := by
  simp only [mem_within]
  constructor <;> rintro ⟨t,ht,hy⟩ <;> exact ⟨pair t,hy,by simpa [pair_involutive t] using ht⟩

lemma within_no_loop (N : ℕ) (hN : 3 ≤ N) (x : Cyclic N) : x ∉ within N x := by
  rw [mem_within]
  rintro ⟨t,ht,hy⟩
  exact pair_ne t ((defect_injective N hN) (hy.symm.trans ht))

lemma within_at_defect (N : ℕ) (hN : 3 ≤ N) (t : Fin 4) :
    within N (defect N t) = {defect N (pair t)} := by
  ext y
  simp only [mem_within, (defect_injective N hN).eq_iff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨s,rfl,hs⟩; exact hs
  · intro h; exact ⟨t,rfl,h⟩

lemma within_card (N : ℕ) (hN : 3 ≤ N) (x : Cyclic N) :
    (within N x).card = if ∃ t : Fin 4, x = defect N t then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨t,rfl⟩ := h
    simp [within_at_defect N hN t]
  · have he : within N x = ∅ := by
      ext y
      simp only [mem_within, Finset.notMem_empty, iff_false, not_exists, not_and]
      intro t ht
      exact (h ⟨t,ht⟩).elim
    simp [he]

def graph (N : ℕ) (hN : 3 ≤ N) : SimpleGraph (Vertex N) where
  Adj
    | .inl x, .inl y => y ∈ within N x
    | .inr x, .inr y => y ∈ within N x
    | .inl x, .inr y => y ∈ cross N x
    | .inr x, .inl y => y ∈ cross N x
  symm := ⟨by
    rintro (x | x) (y | y)
    · exact (within_symm N x y).mp
    · exact (cross_symm N x y).mp
    · exact (cross_symm N x y).mp
    · exact (within_symm N x y).mp⟩
  loopless := ⟨by rintro (x | x) <;> exact within_no_loop N hN x⟩

instance (N : ℕ) (hN : 3 ≤ N) : DecidableRel (graph N hN).Adj := by
  rintro (x | x) (y | y) <;> dsimp [graph] <;> infer_instance

theorem graph_connected (N : ℕ) (hN : 3 ≤ N) : (graph N hN).Connected := by
  apply connected_of_two_matchings
  · intro i; change i-1 ∈ cross N i; simp [cross]
  · intro i; change i+1 ∈ cross N i; simp [cross]

lemma neighborFinset_left (N : ℕ) (hN : 3 ≤ N) (x : Cyclic N) :
    (graph N hN).neighborFinset (.inl x) =
      (within N x).image Sum.inl ∪ (cross N x).image Sum.inr := by
  classical
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  rcases y with y | y <;> simp [graph]

lemma neighborFinset_right (N : ℕ) (hN : 3 ≤ N) (x : Cyclic N) :
    (graph N hN).neighborFinset (.inr x) =
      (cross N x).image Sum.inl ∪ (within N x).image Sum.inr := by
  classical
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  rcases y with y | y <;> simp [graph]

lemma halves_disjoint (N : ℕ) (s t : Finset (Cyclic N)) :
    Disjoint (s.image (Sum.inl : Cyclic N → Vertex N)) (t.image Sum.inr) := by
  apply Finset.disjoint_left.mpr
  intro v h1 h2
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp h1
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp h2
  cases ha.trans hb.symm

theorem graph_degree (N : ℕ) (hN : 3 ≤ N) (v : Vertex N) :
    (graph N hN).degree v = 4 := by
  classical
  rcases v with x | x
  · rw [SimpleGraph.degree, neighborFinset_left, Finset.card_union_of_disjoint (halves_disjoint ..),
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective, within_card N hN, cross_card N hN]
    split_ifs <;> rfl
  · rw [SimpleGraph.degree, neighborFinset_right, Finset.card_union_of_disjoint (halves_disjoint ..),
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective, within_card N hN, cross_card N hN]
    split_ifs <;> rfl

end P14OddGraph


/- Source: cusp_assembly/RealComplex.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
namespace P14RealComplex

def embed {d : Type*} : (d → ℝ) →ₗ[ℝ] (d → ℂ) where
  toFun v j := v j
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

lemma embed_injective {d : Type*} : Function.Injective (@embed d) := by
  intro v w h
  ext j
  exact Complex.ofReal_injective (congrFun h j)

theorem independent_of_complex {ι d : Type*} (v : ι → d → ℝ)
    (hv : LinearIndependent ℂ (fun i => embed (v i))) : LinearIndependent ℝ v := by
  exact (hv.restrict_scalars' ℝ).of_comp embed

theorem independent {ι d : Type*} [Fintype ι] (v : ι → d → ℝ)
    (hv : LinearIndependent ℝ v) : LinearIndependent ℂ (fun i => embed (v i)) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc i
  have hr : ∑ i, (c i).re • v i = 0 := by
    ext j
    have h := congrArg Complex.re (congrFun hc j)
    simpa [embed, Complex.mul_re] using h
  have hi : ∑ i, (c i).im • v i = 0 := by
    ext j
    have h := congrArg Complex.im (congrFun hc j)
    simpa [embed, Complex.mul_im] using h
  apply Complex.ext
  · exact hv _ hr i
  · exact hv _ hi i

theorem spanning {ι d : Type*} (v : ι → d → ℝ)
    (hv : Submodule.span ℝ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => embed (v i)) = ⊤ := by
  let W := Submodule.span ℂ (Set.range fun i => embed (v i))
  have hreal : ∀ x : d → ℝ, embed x ∈ W := by
    have hs : Submodule.span ℝ (Set.range v) ≤
        (W.restrictScalars ℝ).comap embed := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span (Set.mem_range_self i)
    intro x
    exact hs (by rw [hv]; trivial)
  apply top_unique
  intro z _
  have h := W.add_mem (hreal (fun j => (z j).re))
    (W.smul_mem Complex.I (hreal (fun j => (z j).im)))
  have he : embed (fun j => (z j).re) + Complex.I • embed (fun j => (z j).im) = z := by
    ext j
    simpa [embed, mul_comm] using Complex.re_add_im (z j)
  rwa [he] at h

theorem pair {d : Type*} [Fintype d] (v w : d → ℝ) :
    (∑ j, star (embed v j) * embed w j) = ((∑ j, v j * w j : ℝ) : ℂ) := by
  simp [embed]

theorem spanning_of_complex {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℝ) (hv : Submodule.span ℂ (Set.range fun i => embed (v i)) = ⊤) :
    Submodule.span ℝ (Set.range v) = ⊤ := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℂ (fun i => embed (v i))
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = Fintype.card d := by
    rw [← finrank_span_eq_card hli, hspan, hv]
    simp
  have hr : LinearIndependent ℝ (fun q => v (a q)) := independent_of_complex _ hli
  have ht : Submodule.span ℝ (Set.range fun q => v (a q)) = ⊤ :=
    hr.span_eq_top_of_card_eq_finrank' (by simpa using hc)
  apply top_unique
  rw [← ht]
  apply Submodule.span_mono
  rintro _ ⟨q,rfl⟩
  exact ⟨a q,rfl⟩

end P14RealComplex
end


/- Source: cusp_assembly/MetricRealization.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
namespace P14MetricRealization
open Matrix
open scoped MatrixOrder

/-- A positive real metric can be realized by an invertible change of Euclidean coordinates. -/
theorem exists_coordinates {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (hH : H.PosDef) :
    ∃ F : (d → ℝ) ≃ₗ[ℝ] (d → ℝ),
      ∀ v w, dotProduct (F v) (F w) = dotProduct v (H *ᵥ w) := by
  obtain ⟨L,hL,hfac⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hH.isStrictlyPositive
  let F : (d → ℝ) ≃ₗ[ℝ] (d → ℝ) :=
    LinearEquiv.ofBijective L.mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hL, Matrix.mulVec_surjective_iff_isUnit.mpr hL⟩
  refine ⟨F, ?_⟩
  intro v w
  change dotProduct (L *ᵥ v) (L *ᵥ w) = dotProduct v (H *ᵥ w)
  rw [hfac, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    ← Matrix.mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, vecMul_transpose]

end P14MetricRealization
end


/- Source: cusp_assembly/SeedInterface.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
namespace P14SeedInterface
open Matrix Submodule
open scoped ComplexOrder

def pair (v w : Fin 4 → ℂ) : ℂ := ∑ j, star (v j) * w j

def orthGraph {m : ℕ} (v : Fin m → Fin 4 → ℂ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i j => pair (v i) (v j) = 0

/-- The exact k=4 seed predicate used by the corrected seed-supply route. -/
def Seed (m : ℕ) : Prop :=
  ∃ v : Fin m → Fin 4 → ℂ, ∃ N : Fin m → Finset (Fin m),
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ j ∈ N i) ∧
    (∀ i, (N i).card = 4) ∧
    (orthGraph v).Connected ∧
    (∀ S : Finset (Fin m), S.card ≤ 3 →
      LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i) ∧
    (∀ S : Finset (Fin m), S.card = 5 → ∀ a : Fin 4 → ℂ, a ≠ 0 →
      ∃ i ∈ S, pair a (v i) ≠ 0)

def pairMap (a : Fin 4 → ℂ) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun := pair a
  map_add' := by intro x y; simp [pair, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [pair, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma spanning_survivor {ι : Type*} (v : ι → Fin 4 → ℂ)
    (hv : span ℂ (Set.range v) = ⊤) (a : Fin 4 → ℂ) (ha : a ≠ 0) :
    ∃ i, pair a (v i) ≠ 0 := by
  by_contra h
  push Not at h
  have hs : span ℂ (Set.range v) ≤ LinearMap.ker (pairMap a) := by
    apply span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact h i
  have he : pair a a = 0 := hs (by rw [hv]; trivial)
  exact ha (dotProduct_star_self_eq_zero.mp he)

theorem of_metric_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (e : Fin m ≃ ι) (G : SimpleGraph ι) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ i, G.degree i = 4)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (hH : H.PosDef)
    (v : ι → Fin 4 → ℝ) (hnz : ∀ i, v i ≠ 0)
    (hedge : ∀ i j, dotProduct (v i) (H *ᵥ v j) = 0 ↔ G.Adj i j)
    (hli : ∀ d : ℕ, d ≤ 3 → ∀ f : Fin d → ι, Function.Injective f →
      LinearIndependent ℝ (fun q => v (f q)))
    (hspan : ∀ f : Fin 5 → ι, Function.Injective f →
      span ℝ (Set.range fun q => v (f q)) = ⊤) : Seed m := by
  classical
  obtain ⟨F,hF⟩ := P14MetricRealization.exists_coordinates H hH
  let w : Fin m → Fin 4 → ℂ := fun i => P14RealComplex.embed (F (v (e i)))
  let G' := G.comap e
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  have hp (i j : Fin m) : pair (w i) (w j) = 0 ↔ G'.Adj i j := by
    change (∑ r, star (P14RealComplex.embed (F (v (e i))) r) *
      P14RealComplex.embed (F (v (e j))) r) = 0 ↔ G.Adj (e i) (e j)
    rw [P14RealComplex.pair]
    change ((dotProduct (F (v (e i))) (F (v (e j))) : ℝ) : ℂ) = 0 ↔ _
    rw [hF, Complex.ofReal_eq_zero, hedge]
  have hg : orthGraph w = G' := by
    ext i j
    simp only [orthGraph, SimpleGraph.fromRel_adj, hp]
    constructor
    · rintro ⟨_,h | h⟩
      · exact h
      · exact h.symm
    · intro h; exact ⟨h.ne, Or.inl h⟩
  refine ⟨w, (fun i => G'.neighborFinset i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h
    apply hnz (e i)
    apply F.injective
    apply P14RealComplex.embed_injective
    simpa [w] using h
  · intro i j
    rw [SimpleGraph.mem_neighborFinset]
    exact hp i j
  · intro i
    rw [SimpleGraph.card_neighborFinset_eq_degree, ← iso.degree_eq]
    exact hdeg (e i)
  · rw [hg]
    exact iso.connected_iff.mpr hconn
  · intro S hS
    let es : (S : Set (Fin m)) ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
    let f : Fin S.card → ι := fun q => e (es.symm q).val
    have hf : Function.Injective f := e.injective.comp
      (Subtype.val_injective.comp es.symm.injective)
    have hr := (hli S.card hS f hf).map' F.toLinearMap F.ker
    have hc := P14RealComplex.independent (fun q => F (v (f q))) hr
    have ht := hc.comp es es.injective
    simpa [w, f, Function.comp_def] using ht
  · intro S hS a ha
    let es : (S : Set (Fin m)) ≃ Fin 5 := Fintype.equivFinOfCardEq (by simpa using hS)
    let f : Fin 5 → ι := fun q => e (es.symm q).val
    have hf : Function.Injective f := e.injective.comp
      (Subtype.val_injective.comp es.symm.injective)
    have hr : span ℝ (Set.range fun q => F (v (f q))) = ⊤ := by
      have hm := congrArg (Submodule.map F.toLinearMap) (hspan f hf)
      simpa [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.map_top,
        LinearMap.range_eq_top.mpr F.surjective] using hm
    have hc := P14RealComplex.spanning (fun q => F (v (f q))) hr
    obtain ⟨q,hq⟩ := spanning_survivor _ hc a ha
    exact ⟨(es.symm q).val, (es.symm q).property, hq⟩

end P14SeedInterface
end


/- Source: elliptic_audit/OddRepairAlgebra.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Exact polynomial identities used in the odd-half-order cusp repair.
The trigonometric hypotheses are stated algebraically here; no numerical
approximation or unproved trigonometric assertion is used. -/

namespace P14OddRepairAlgebra

noncomputable section

abbrev Vec3 := Fin 3 → ℝ

def g (a b : ℝ) (v w : Vec3) : ℝ :=
  4*a*b*v 0*w 0 - 4*(a+b)*v 1*w 1 + 2*v 0*w 2 + 2*v 2*w 0

def curveEven (w : ℝ) : Vec3 := ![1,w,2*w^2-1]
def q (a c : ℝ) : Vec3 := ![1,-c,a]
def p (a b c : ℝ) : Vec3 := ![1,-c*(2*a-1),2*a*b-a]
def h (a b c : ℝ) : Vec3 := ![1,-2*a*c/(a+b),a*(2*a-2*b+1)]

theorem q_norm (a b c : ℝ) (hc : c^2=(a+1)/2) :
    g a b (q a c) (q a c) = 2*(1-a)*(a-b) := by
  simp only [g, q, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  calc
    _ = 4*a*b-4*(a+b)*c^2+4*a := by ring
    _ = _ := by rw [hc]; ring

theorem pq_inner (a b c : ℝ) (hb : b=2*a^2-1) (hc : c^2=(a+1)/2) :
    g a b (p a b c) (q a c) = -2*(a-b)^2 := by
  simp only [g, p, q, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  calc
    _ = 8*a*b - 4*(a+b)*c^2*(2*a-1) := by ring
    _ = -2*(a-b)^2 := by rw [hc, hb]; ring

theorem h_factor (a b c w : ℝ) (hab : a+b≠0) (hc : c^2=(a+1)/2) :
    g a b (curveEven w) (h a b c) = 4*(w+c)*(w+c*(2*a-1)) := by
  simp only [g, curveEven, h, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  nlinarith [hc]

theorem h_norm (a b c : ℝ) (hab : a+b≠0) (hc : c^2=(a+1)/2) :
    g a b (h a b c) (h a b c) = -4*a*(a-b)*(1-b)/(a+b) := by
  simp only [g, h, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  rw [hc]
  ring

theorem p_full_norm (a b c : ℝ) (hb : b=2*a^2-1) (hc : c^2=(a+1)/2) :
    g a b (p a b c) (p a b c) +
      4*(a-b)*(1-c^2*(2*a-1)^2) =
        4*(1-a)*(2*a*b-a-b) := by
  simp only [g, p, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  calc
    _ = 12*a*b - 4*b - 8*a*c^2*(2*a-1)^2 := by ring
    _ = _ := by rw [hc, hb]; ring

theorem p_norm_factor (a b c : ℝ) (hb : b=2*a^2-1) (hc : c^2=(a+1)/2) :
    g a b (p a b c) (p a b c) =
      -2*(1-a)^2*(8*a^3+20*a^2+10*a-1) := by
  simp only [g, p, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  calc
    _ = 12*a*b-4*a-4*(a+b)*c^2*(2*a-1)^2 := by ring
    _ = _ := by rw [hc,hb]; ring

theorem p_norm_neg (a b c : ℝ) (hb : b=2*a^2-1) (hc : c^2=(a+1)/2)
    (ha : 1/2<a) (ha1 : a<1) : g a b (p a b c) (p a b c)<0 := by
  rw [p_norm_factor a b c hb hc]
  have hap : 0<a := by linarith
  have hp : 0<8*a^3+20*a^2+10*a-1 := by
    nlinarith [pow_pos hap 3, sq_nonneg a]
  have hs : 0<(1-a)^2 := sq_pos_of_ne_zero (by linarith)
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hs) hp

theorem repair_sine_product (a b : ℝ) :
    4*(a-b)*((a-b)/2) = 2*(a-b)^2 := by ring

theorem q_sine_norm (a b : ℝ) :
    4*(a-b)*((1-a)/2) = 2*(1-a)*(a-b) := by ring

theorem metric_parameters (γ τ : ℝ) (ht : γ^2-1<τ^2) :
    let x := γ/(1+τ^2)
    let y := γ*τ/(1+τ^2)
    x^2+y^2=γ*x ∧ 0<1-x^2-y^2 := by
  dsimp
  have hden : 0 < 1+τ^2 := by positivity
  have hcircle : (γ/(1+τ^2))^2+(γ*τ/(1+τ^2))^2=γ*(γ/(1+τ^2)) := by
    field_simp
  refine ⟨hcircle, ?_⟩
  rw [sub_sub, hcircle]
  have heq : 1-γ*(γ/(1+τ^2)) = (1+τ^2-γ^2)/(1+τ^2) := by
    field_simp
  rw [heq]
  apply div_pos _ hden
  linarith

end
end P14OddRepairAlgebra


/- Source: elliptic_audit/LorentzMetric.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The positive self-dual metric in standard Lorentz coordinates.
The basis change from the trigonometric cusp form is a separate step. -/

namespace P14LorentzMetric

noncomputable section
open Matrix

abbrev Vec := Fin 4 → ℝ
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

def denominator (x y : ℝ) : ℝ := 1-x^2-y^2

def form (v w : Vec) : ℝ :=
  v 0*w 0-v 1*w 1-v 2*w 2+v 3*w 3

def orbit (x y : ℝ) (v : Vec) : Vec :=
  let z := (v 0-x*v 1-y*v 2)/denominator x y
  ![-v 0+2*z, -v 1+2*x*z, -v 2+2*y*z, v 3]

def metric (x y : ℝ) : Mat :=
  let R := denominator x y
  ![![-1+2/R, -2*x/R, -2*y/R, 0],
    ![-2*x/R, 1+2*x^2/R, 2*x*y/R, 0],
    ![-2*y/R, 2*x*y/R, 1+2*y^2/R, 0],
    ![0, 0, 0, 1]]

def diagonal : Mat := Matrix.diagonal ![1,-1,-1,1]

theorem orbit_involutive (x y : ℝ) (hR : denominator x y≠0) :
    Function.Involutive (orbit x y) := by
  intro v
  have hd : 1-x^2-y^2≠0 := hR
  ext i
  fin_cases i <;> simp [orbit, denominator] <;> field_simp [hd] <;> ring

theorem orbit_form_symm (x y : ℝ) (v w : Vec) :
    form (orbit x y v) w = form v (orbit x y w) := by
  simp [orbit, form]
  ring

theorem metric_pairing (x y : ℝ) (v w : Vec) :
    v ⬝ᵥ (metric x y *ᵥ w) = form v (orbit x y w) := by
  simp [metric, form, orbit, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

/-- A sum-of-squares certificate for the metric's strict positivity. -/
theorem positive_certificate (x y : ℝ) (hR : denominator x y≠0) (v : Vec) :
    form v (orbit x y v) =
      ((1+x^2+y^2)*v 0-2*(x*v 1+y*v 2))^2 /
        ((1+x^2+y^2)*denominator x y) +
      (denominator x y*(v 1^2+v 2^2)+2*(y*v 1-x*v 2)^2) /
        (1+x^2+y^2) + v 3^2 := by
  have hC : (1+x^2+y^2)≠0 := ne_of_gt (by positivity)
  simp [form, orbit]
  field_simp
  dsimp [denominator]
  ring

theorem metric_pairing_pos (x y : ℝ) (hR : 0<denominator x y)
    (v : Vec) (hv : v≠0) : 0<form v (orbit x y v) := by
  rw [positive_certificate x y (ne_of_gt hR)]
  have hC : 0<1+x^2+y^2 := by positivity
  have htop : 0 ≤ ((1+x^2+y^2)*v 0-2*(x*v 1+y*v 2))^2 /
      ((1+x^2+y^2)*denominator x y) := div_nonneg (sq_nonneg _) (le_of_lt (mul_pos hC hR))
  have hmid : 0 ≤ (denominator x y*(v 1^2+v 2^2)+2*(y*v 1-x*v 2)^2) /
      (1+x^2+y^2) := by positivity
  by_contra hn
  have hzero : (denominator x y*(v 1^2+v 2^2)+2*(y*v 1-x*v 2)^2) /
      (1+x^2+y^2) = 0 := by nlinarith [sq_nonneg (v 3)]
  have hnum := (div_eq_zero_iff.mp hzero).resolve_right (ne_of_gt hC)
  have hv12 : v 1^2+v 2^2 = 0 := by
    have hs : 0≤v 1^2+v 2^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith [sq_nonneg (y*v 1-x*v 2)]
  have hv1 : v 1=0 := by nlinarith [sq_nonneg (v 2)]
  have hv2 : v 2=0 := by nlinarith [sq_nonneg (v 1)]
  have hv3 : v 3=0 := by nlinarith
  have htzero : ((1+x^2+y^2)*v 0-2*(x*v 1+y*v 2))^2 /
      ((1+x^2+y^2)*denominator x y)=0 := by nlinarith [sq_nonneg (v 3)]
  have ht := (div_eq_zero_iff.mp htzero).resolve_right (ne_of_gt (mul_pos hC hR))
  have hv0 : v 0=0 := by
    simp only [hv1, hv2, mul_zero, add_zero, sub_zero, sq_eq_zero_iff] at ht
    exact (mul_eq_zero.mp ht).resolve_left (ne_of_gt hC)
  apply hv
  ext i
  fin_cases i <;> simp [hv0, hv1, hv2, hv3]

theorem metric_posDef (x y : ℝ) (hR : 0<denominator x y) :
    (metric x y).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    change star (metric x y j i) = metric x y i j
    fin_cases i <;> fin_cases j <;> simp [metric]
  · intro v hv
    simpa only [star_trivial, metric_pairing] using metric_pairing_pos x y hR v hv

theorem diagonal_sq : diagonal * diagonal = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, Matrix.mul_apply, Fin.sum_univ_succ]

theorem diagonal_metric_mulVec (x y : ℝ) (v : Vec) :
    (diagonal * metric x y) *ᵥ v = orbit x y v := by
  rw [← Matrix.mulVec_mulVec]
  ext i
  fin_cases i <;> simp [diagonal, metric, orbit, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem metric_selfDual (x y : ℝ) (hR : denominator x y≠0) :
    diagonal * (metric x y)⁻¹ * diagonal = metric x y := by
  have hsq : (diagonal * metric x y) * (diagonal * metric x y) = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec, diagonal_metric_mulVec,
      diagonal_metric_mulVec, Matrix.one_mulVec]
    exact orbit_involutive x y hR v
  have hinv : (metric x y)⁻¹ = diagonal * metric x y * diagonal := by
    apply Matrix.inv_eq_left_inv
    simpa only [mul_assoc] using hsq
  rw [hinv]
  calc
    _ = (diagonal * diagonal) * metric x y * (diagonal * diagonal) := by
      simp only [mul_assoc]
    _ = _ := by rw [diagonal_sq]; simp

theorem inverse_metric_mul_diagonal (x y : ℝ) (hR : denominator x y≠0) (v : Vec) :
    ((metric x y)⁻¹ * diagonal) *ᵥ v = orbit x y v := by
  have hd : diagonal * (metric x y)⁻¹ * diagonal = metric x y := metric_selfDual x y hR
  have hid : (metric x y)⁻¹ * diagonal = diagonal * metric x y := by
    calc
      _ = diagonal * (diagonal * (metric x y)⁻¹ * diagonal) := by
        simp only [← mul_assoc, diagonal_sq, one_mul]
      _ = _ := by rw [hd]
  rw [hid, diagonal_metric_mulVec]

/-- On the repair conic, both sign choices of the two desired pairings vanish. -/
theorem repair_pairing (γ x y t Q ε : ℝ)
    (hcircle : x^2+y^2=γ*x) (hR : denominator x y≠0) (hε : ε^2=1) :
    form ![t,γ*t,0,-ε*t]
      (orbit x y ![Q,0,0,ε*Q]) = 0 := by
  simp [form, orbit]
  have heq : 1-γ*x = denominator x y := by dsimp [denominator]; linarith
  calc
    _ = t*Q*((2*(1-γ*x)/denominator x y)-1-ε^2) := by ring
    _ = 0 := by rw [heq, hε]; field_simp; ring

end
end P14LorentzMetric


/- Source: grouping_audit/LorentzAnnihilator.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Exact real algebra for the Lorentz-orbit annihilator calculation.
This file classifies quadratic identities; identifying vanishing on the
geometric orbit with such an identity is a separate geometric step. -/

namespace P14LorentzAnnihilator

def A (v0 v1 v2 S l0 l1 l2 l3 : ℝ) : ℝ :=
  -l0*v0-l1*v1-l2*v2+l3*S

def numerator (v0 v1 v2 S l0 l1 l2 l3 x y : ℝ) : ℝ :=
  A v0 v1 v2 S l0 l1 l2 l3 * (1-x^2-y^2) +
    2*(l0+l1*x+l2*y)*(v0-v1*x-v2*y)

def conic (γ x y : ℝ) : ℝ := x^2+y^2-γ*x

def Coefficients (γ v0 v1 v2 S l0 l1 l2 l3 lam : ℝ) : Prop :=
  A v0 v1 v2 S l0 l1 l2 l3 + 2*l0*v0 = 0 ∧
  2*(l1*v0-l0*v1) = -lam*γ ∧
  2*(l2*v0-l0*v2) = 0 ∧
  -A v0 v1 v2 S l0 l1 l2 l3 - 2*l1*v1 = lam ∧
  -2*(l1*v2+l2*v1) = 0 ∧
  -A v0 v1 v2 S l0 l1 l2 l3 - 2*l2*v2 = lam

def Nontrivial (l0 l1 l2 l3 : ℝ) : Prop := l0 ≠ 0 ∨ l1 ≠ 0 ∨ l2 ≠ 0 ∨ l3 ≠ 0

/-- The six equations are exactly the coefficients of the quadratic identity. -/
theorem coefficients_iff_identity (γ v0 v1 v2 S l0 l1 l2 l3 lam : ℝ) :
    Coefficients γ v0 v1 v2 S l0 l1 l2 l3 lam ↔
      ∀ x y, numerator v0 v1 v2 S l0 l1 l2 l3 x y = lam*conic γ x y := by
  constructor
  · rintro ⟨h0,hx,hy,hxx,hxy,hyy⟩ x y
    dsimp [numerator, conic]
    linear_combination h0 + x*hx + y*hy + x^2*hxx + x*y*hxy + y^2*hyy
  · intro h
    have h00 := h 0 0
    have h10 := h 1 0
    have hn0 := h (-1) 0
    have h01 := h 0 1
    have h0n := h 0 (-1)
    have h11 := h 1 1
    dsimp [numerator,conic] at h00 h10 hn0 h01 h0n h11
    dsimp [Coefficients]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

/-- The diagonal and mixed quadratic coefficients force one horizontal vector to vanish. -/
lemma horizontal_dichotomy (l1 l2 v1 v2 : ℝ)
    (hd : l1*v1-l2*v2 = 0) (hc : l1*v2+l2*v1 = 0) :
    (l1 = 0 ∧ l2 = 0) ∨ (v1 = 0 ∧ v2 = 0) := by
  have hp : (l1^2+l2^2)*(v1^2+v2^2) = 0 := by
    calc
      _ = (l1*v1-l2*v2)^2 + (l1*v2+l2*v1)^2 := by ring
      _ = 0 := by rw [hd,hc]; norm_num
  rcases mul_eq_zero.mp hp with hl | hv
  · exact Or.inl ⟨by nlinarith [sq_nonneg l2], by nlinarith [sq_nonneg l1]⟩
  · exact Or.inr ⟨by nlinarith [sq_nonneg v2], by nlinarith [sq_nonneg v1]⟩

lemma horizontal_of_coefficients {γ v0 v1 v2 S l0 l1 l2 l3 lam : ℝ}
    (h : Coefficients γ v0 v1 v2 S l0 l1 l2 l3 lam) :
    (l1 = 0 ∧ l2 = 0) ∨ (v1 = 0 ∧ v2 = 0) := by
  obtain ⟨h0,hx,hy,hxx,hxy,hyy⟩ := h
  apply horizontal_dichotomy l1 l2 v1 v2
  · nlinarith [hxx,hyy]
  · nlinarith [hxy]

theorem only_exceptional {γ v0 v1 v2 S l0 l1 l2 l3 lam : ℝ}
    (hS : S ≠ 0) (hl : Nontrivial l0 l1 l2 l3)
    (h : Coefficients γ v0 v1 v2 S l0 l1 l2 l3 lam) :
    (v1 = 0 ∧ v2 = 0) ∨ (v2 = 0 ∧ v1 = γ*v0) := by
  rcases horizontal_of_coefficients h with ⟨hl1,hl2⟩ | hv
  · subst l1 l2
    obtain ⟨h0,hx,hy,hxx,hxy,hyy⟩ := h
    have hl0 : l0 ≠ 0 := by
      intro he
      have hp : l3*S = 0 := by simpa [A,he] using h0
      have hl3 := (mul_eq_zero.mp hp).resolve_right hS
      simp [Nontrivial,he,hl3] at hl
    have hv2 : v2 = 0 := by
      apply (mul_eq_zero.mp (show l0*v2 = 0 by nlinarith [hy])).resolve_left hl0
    have hlam : lam = 2*l0*v0 := by nlinarith [h0,hxx]
    have hv1 : v1 = γ*v0 := by
      have hp : l0*(v1-γ*v0) = 0 := by
        rw [hlam] at hx
        linear_combination (-1/2 : ℝ)*hx
      exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hl0)
    exact Or.inr ⟨hv2,hv1⟩
  · exact Or.inl hv

theorem axis_witness (γ v0 S : ℝ) :
    Coefficients γ v0 0 0 S S (-γ*S) 0 (-v0) (2*S*v0) := by
  dsimp [Coefficients,A]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem tilted_witness (γ v0 S : ℝ) :
    Coefficients γ v0 (γ*v0) 0 S S 0 0 (-v0) (2*S*v0) := by
  dsimp [Coefficients,A]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Exact existence classification. No hypothesis on γ or the even component is needed. -/
theorem exists_nontrivial_iff (γ v0 v1 v2 S : ℝ) (hS : S ≠ 0) :
    (∃ l0 l1 l2 l3 lam : ℝ,
      Nontrivial l0 l1 l2 l3 ∧ Coefficients γ v0 v1 v2 S l0 l1 l2 l3 lam) ↔
      (v1 = 0 ∧ v2 = 0) ∨ (v2 = 0 ∧ v1 = γ*v0) := by
  constructor
  · rintro ⟨l0,l1,l2,l3,lam,hl,h⟩
    exact only_exceptional hS hl h
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨S,-γ*S,0,-v0,2*S*v0,Or.inl hS,axis_witness γ v0 S⟩
    · exact ⟨S,0,0,-v0,2*S*v0,Or.inl hS,tilted_witness γ v0 S⟩

/-- The full annihilator line in the axial exceptional case. -/
theorem axis_coefficients_iff (γ v0 S l0 l1 l2 l3 lam : ℝ) (hv0 : v0 ≠ 0) :
    Coefficients γ v0 0 0 S l0 l1 l2 l3 lam ↔
      l1 = -γ*l0 ∧ l2 = 0 ∧ l3*S = -l0*v0 ∧ lam = 2*l0*v0 := by
  constructor
  · rintro ⟨h0,hx,hy,hxx,hxy,hyy⟩
    have hl2 : l2 = 0 :=
      (mul_eq_zero.mp (show l2*v0 = 0 by nlinarith [hy])).resolve_right hv0
    have hlam : lam = 2*l0*v0 := by nlinarith [h0,hxx]
    have hl1 : l1 = -γ*l0 := by
      have hp : (l1+γ*l0)*v0 = 0 := by
        rw [hlam] at hx
        linear_combination (1/2 : ℝ)*hx
      simpa only [neg_mul] using eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hp).resolve_right hv0)
    refine ⟨hl1,hl2,?_,hlam⟩
    dsimp [A] at h0
    nlinarith [h0]
  · rintro ⟨rfl,rfl,h3,rfl⟩
    dsimp [Coefficients,A]
    constructor
    · nlinarith [h3]
    constructor
    · ring
    constructor
    · ring
    constructor
    · nlinarith [h3]
    constructor
    · ring
    · nlinarith [h3]

/-- The full annihilator line in the tilted exceptional case. -/
theorem tilted_coefficients_iff (γ v0 S l0 l1 l2 l3 lam : ℝ)
    (hγ : γ ≠ 0) (hv0 : v0 ≠ 0) :
    Coefficients γ v0 (γ*v0) 0 S l0 l1 l2 l3 lam ↔
      l1 = 0 ∧ l2 = 0 ∧ l3*S = -l0*v0 ∧ lam = 2*l0*v0 := by
  constructor
  · intro h
    have hl12 : l1 = 0 ∧ l2 = 0 := by
      rcases horizontal_of_coefficients h with hl | hv
      · exact hl
      · exact False.elim ((mul_ne_zero hγ hv0) hv.1)
    obtain ⟨h0,hx,hy,hxx,hxy,hyy⟩ := h
    obtain ⟨rfl,rfl⟩ := hl12
    refine ⟨rfl,rfl,?_,?_⟩
    · dsimp [A] at h0
      nlinarith [h0]
    · nlinarith [h0,hxx]
  · rintro ⟨rfl,rfl,h3,rfl⟩
    dsimp [Coefficients,A]
    constructor
    · nlinarith [h3]
    constructor
    · ring
    constructor
    · ring
    constructor
    · nlinarith [h3]
    constructor
    · ring
    · nlinarith [h3]

/-- If S=0 and v2≠0, the only annihilator is the unchanged fourth coordinate. -/
theorem sine_zero_coefficients_iff (γ v0 v1 v2 l0 l1 l2 l3 lam : ℝ) (hv2 : v2 ≠ 0) :
    Coefficients γ v0 v1 v2 0 l0 l1 l2 l3 lam ↔
      l0 = 0 ∧ l1 = 0 ∧ l2 = 0 ∧ lam = 0 := by
  constructor
  · intro h
    have hl12 : l1 = 0 ∧ l2 = 0 := by
      rcases horizontal_of_coefficients h with hl | hv
      · exact hl
      · exact False.elim (hv2 hv.2)
    obtain ⟨h0,hx,hy,hxx,hxy,hyy⟩ := h
    obtain ⟨rfl,rfl⟩ := hl12
    have hl0 : l0 = 0 :=
      (mul_eq_zero.mp (show l0*v2 = 0 by nlinarith [hy])).resolve_right hv2
    subst l0
    refine ⟨rfl,rfl,rfl,?_⟩
    simpa [A] using hxx.symm
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    simp [Coefficients,A]

end P14LorentzAnnihilator


/- Source: grouping_audit/LorentzOrbit.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Exact finite interpolation on the positive-denominator arc of the conic.
The five samples have rational parameters ±γ, ±2γ, 3γ. No limit point,
analytic density argument, or numerical certificate is used. -/

namespace P14LorentzOrbit

open P14LorentzAnnihilator

def quadratic (a b c d e f x y : ℝ) : ℝ :=
  a+b*x+c*y+d*x^2+e*x*y+f*y^2

lemma quadratic_three_roots {a b c x1 x2 x3 : ℝ}
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (h1 : a+b*x1+c*x1^2 = 0) (h2 : a+b*x2+c*x2^2 = 0)
    (h3 : a+b*x3+c*x3^2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hr12 : b+c*(x1+x2) = 0 := by
    have hp : (x1-x2)*(b+c*(x1+x2)) = 0 := by linear_combination h1-h2
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr h12)
  have hr13 : b+c*(x1+x3) = 0 := by
    have hp : (x1-x3)*(b+c*(x1+x3)) = 0 := by linear_combination h1-h3
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr h13)
  have hc : c = 0 := by
    have hp : c*(x2-x3) = 0 := by linear_combination hr12-hr13
    exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr h23)
  have hb : b = 0 := by simpa [hc] using hr12
  exact ⟨by simpa [hb,hc] using h1,hb,hc⟩

lemma five_point_interpolation {γ a b c d e f x1 y1 x2 y2 x3 y3 : ℝ}
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (hc1 : x1^2+y1^2 = γ*x1) (hc2 : x2^2+y2^2 = γ*x2)
    (hc3 : x3^2+y3^2 = γ*x3)
    (h1p : quadratic a b c d e f x1 y1 = 0)
    (h1m : quadratic a b c d e f x1 (-y1) = 0)
    (h2p : quadratic a b c d e f x2 y2 = 0)
    (h2m : quadratic a b c d e f x2 (-y2) = 0)
    (h3p : quadratic a b c d e f x3 y3 = 0) :
    a = 0 ∧ c = 0 ∧ e = 0 ∧ d = f ∧ b = -γ*f := by
  dsimp [quadratic] at h1p h1m h2p h2m h3p
  have ho1 : c+e*x1 = 0 := by
    have hp : y1*(c+e*x1) = 0 := by linear_combination (1/2 : ℝ)*(h1p-h1m)
    exact (mul_eq_zero.mp hp).resolve_left hy1
  have ho2 : c+e*x2 = 0 := by
    have hp : y2*(c+e*x2) = 0 := by linear_combination (1/2 : ℝ)*(h2p-h2m)
    exact (mul_eq_zero.mp hp).resolve_left hy2
  have he : e = 0 := by
    have hp : e*(x1-x2) = 0 := by linear_combination ho1-ho2
    exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr h12)
  have hc : c = 0 := by simpa [he] using ho1
  have h1 : a+(b+γ*f)*x1+(d-f)*x1^2 = 0 := by
    rw [hc,he] at h1p
    linear_combination h1p-f*hc1
  have h2 : a+(b+γ*f)*x2+(d-f)*x2^2 = 0 := by
    rw [hc,he] at h2p
    linear_combination h2p-f*hc2
  have h3 : a+(b+γ*f)*x3+(d-f)*x3^2 = 0 := by
    rw [hc,he] at h3p
    linear_combination h3p-f*hc3
  obtain ⟨ha,hb,hd⟩ := quadratic_three_roots h12 h13 h23 h1 h2 h3
  refine ⟨ha,hc,he,sub_eq_zero.mp hd,?_⟩
  simpa only [neg_mul] using eq_neg_of_add_eq_zero_left hb

noncomputable def px (γ t : ℝ) : ℝ := γ/(1+t^2)
noncomputable def py (γ t : ℝ) : ℝ := γ*t/(1+t^2)

lemma param_conic (γ t : ℝ) : (px γ t)^2+(py γ t)^2 = γ*(px γ t) := by
  have hd : (1+t^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  dsimp [px,py]
  field_simp [hd]

lemma param_positive (γ t : ℝ) (hsq : γ^2 ≤ t^2) : 0 < 1-γ*(px γ t) := by
  have hd : (0 : ℝ) < 1+t^2 := by positivity
  have he : 1-γ*(px γ t) = (1+t^2-γ^2)/(1+t^2) := by
    dsimp [px]
    field_simp [ne_of_gt hd]
  rw [he]
  exact div_pos (by linarith) hd

lemma param_x_ne {γ t1 t2 : ℝ} (hγ : γ ≠ 0) (ht : t1^2 ≠ t2^2) :
    px γ t1 ≠ px γ t2 := by
  intro he
  have hd1 : (1+t1^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hd2 : (1+t2^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hp := (div_eq_div_iff hd1 hd2).mp he
  have h := mul_left_cancel₀ hγ hp
  exact ht (by linarith)

lemma param_y_ne {γ t : ℝ} (hγ : γ ≠ 0) (ht : t ≠ 0) : py γ t ≠ 0 :=
  div_ne_zero (mul_ne_zero hγ ht) (ne_of_gt (by positivity))

/-- Vanishing on the positive arc forces exactly a scalar multiple of the conic. -/
theorem positive_conic_quadratic {γ a b c d e f : ℝ} (hγ : γ ≠ 0)
    (h : ∀ x y : ℝ, x^2+y^2 = γ*x → 0 < 1-γ*x →
      quadratic a b c d e f x y = 0) :
    a = 0 ∧ c = 0 ∧ e = 0 ∧ d = f ∧ b = -γ*f := by
  have hsq : 0 < γ^2 := sq_pos_of_ne_zero hγ
  have h12 : px γ γ ≠ px γ (2*γ) := param_x_ne hγ (by nlinarith)
  have h13 : px γ γ ≠ px γ (3*γ) := param_x_ne hγ (by nlinarith)
  have h23 : px γ (2*γ) ≠ px γ (3*γ) := param_x_ne hγ (by nlinarith)
  have hp1 := param_positive γ γ (le_refl _)
  have hp2 := param_positive γ (2*γ) (by nlinarith)
  have hp3 := param_positive γ (3*γ) (by nlinarith)
  have hc1 := param_conic γ γ
  have hc2 := param_conic γ (2*γ)
  have hc3 := param_conic γ (3*γ)
  apply five_point_interpolation h12 h13 h23 (param_y_ne hγ hγ)
    (param_y_ne hγ (mul_ne_zero (by norm_num) hγ)) hc1 hc2 hc3
  · exact h _ _ hc1 hp1
  · exact h _ _ (by nlinarith [hc1]) hp1
  · exact h _ _ hc2 hp2
  · exact h _ _ (by nlinarith [hc2]) hp2
  · exact h _ _ hc3 hp3

/-- Evaluation of the linear functional on the Lorentz orbit point, with S unchanged. -/
noncomputable def orbitPair (γ v0 v1 v2 S l0 l1 l2 l3 x y : ℝ) : ℝ :=
  l0*(-v0+2*(v0-x*v1-y*v2)/(1-γ*x)) +
  l1*(-v1+2*x*(v0-x*v1-y*v2)/(1-γ*x)) +
  l2*(-v2+2*y*(v0-x*v1-y*v2)/(1-γ*x)) + l3*S

def Annihilates (γ v0 v1 v2 S l0 l1 l2 l3 : ℝ) : Prop :=
  ∀ x y, x^2+y^2 = γ*x → 0 < 1-γ*x → orbitPair γ v0 v1 v2 S l0 l1 l2 l3 x y = 0

lemma denominator_identity (γ v0 v1 v2 S l0 l1 l2 l3 x y : ℝ)
    (hc : x^2+y^2 = γ*x) (hd : 1-γ*x ≠ 0) :
    (1-γ*x)*orbitPair γ v0 v1 v2 S l0 l1 l2 l3 x y =
      numerator v0 v1 v2 S l0 l1 l2 l3 x y := by
  have he : 1-x^2-y^2 = 1-γ*x := by linarith
  dsimp [numerator]
  rw [he]
  dsimp [orbitPair,A]
  field_simp [hd]
  ring

lemma orbitPair_zero_iff (γ v0 v1 v2 S l0 l1 l2 l3 x y : ℝ)
    (hc : x^2+y^2 = γ*x) (hd : 1-γ*x ≠ 0) :
    orbitPair γ v0 v1 v2 S l0 l1 l2 l3 x y = 0 ↔
      numerator v0 v1 v2 S l0 l1 l2 l3 x y = 0 := by
  rw [← denominator_identity γ v0 v1 v2 S l0 l1 l2 l3 x y hc hd]
  constructor
  · intro h
    rw [h,mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hd

/-- Actual annihilation on the positive arc is equivalent to the exact coefficient equations. -/
theorem annihilates_iff_coefficients (γ v0 v1 v2 S l0 l1 l2 l3 : ℝ) (hγ : γ ≠ 0) :
    Annihilates γ v0 v1 v2 S l0 l1 l2 l3 ↔
      ∃ lam, Coefficients γ v0 v1 v2 S l0 l1 l2 l3 lam := by
  constructor
  · intro h
    let av := A v0 v1 v2 S l0 l1 l2 l3
    have hq : ∀ x y : ℝ, x^2+y^2 = γ*x → 0 < 1-γ*x →
        quadratic (av+2*l0*v0) (2*(l1*v0-l0*v1)) (2*(l2*v0-l0*v2))
          (-av-2*l1*v1) (-2*(l1*v2+l2*v1)) (-av-2*l2*v2) x y = 0 := by
      intro x y hc hd
      have hp := (orbitPair_zero_iff γ v0 v1 v2 S l0 l1 l2 l3 x y hc (ne_of_gt hd)).mp
        (h x y hc hd)
      have he : quadratic (av+2*l0*v0) (2*(l1*v0-l0*v1)) (2*(l2*v0-l0*v2))
          (-av-2*l1*v1) (-2*(l1*v2+l2*v1)) (-av-2*l2*v2) x y =
          numerator v0 v1 v2 S l0 l1 l2 l3 x y := by
        dsimp [quadratic,numerator,av]
        ring
      exact he.trans hp
    obtain ⟨h0,hy,hxy,hxx,hx⟩ := positive_conic_quadratic hγ hq
    refine ⟨-av-2*l2*v2,h0,?_,hy,hxx,hxy,rfl⟩
    calc
      _ = -γ*(-av-2*l2*v2) := hx
      _ = -(-av-2*l2*v2)*γ := by ring
  · rintro ⟨lam,h⟩ x y hc hd
    apply (orbitPair_zero_iff γ v0 v1 v2 S l0 l1 l2 l3 x y hc (ne_of_gt hd)).mpr
    rw [(coefficients_iff_identity γ v0 v1 v2 S l0 l1 l2 l3 lam).mp h x y]
    have he : conic γ x y = 0 := by dsimp [conic]; linarith
    rw [he,mul_zero]

/-- Classification of nontrivial real annihilators for the actual positive-denominator orbit. -/
theorem exists_annihilator_iff (γ v0 v1 v2 S : ℝ) (hγ : γ ≠ 0) (hS : S ≠ 0) :
    (∃ l0 l1 l2 l3 : ℝ, Nontrivial l0 l1 l2 l3 ∧
      Annihilates γ v0 v1 v2 S l0 l1 l2 l3) ↔
      (v1 = 0 ∧ v2 = 0) ∨ (v2 = 0 ∧ v1 = γ*v0) := by
  rw [← exists_nontrivial_iff γ v0 v1 v2 S hS]
  constructor
  · rintro ⟨l0,l1,l2,l3,hl,h⟩
    obtain ⟨lam,hc⟩ := (annihilates_iff_coefficients γ v0 v1 v2 S l0 l1 l2 l3 hγ).mp h
    exact ⟨l0,l1,l2,l3,lam,hl,hc⟩
  · rintro ⟨l0,l1,l2,l3,lam,hl,hc⟩
    exact ⟨l0,l1,l2,l3,hl,
      (annihilates_iff_coefficients γ v0 v1 v2 S l0 l1 l2 l3 hγ).mpr ⟨lam,hc⟩⟩

theorem axis_annihilator_iff (γ v0 S l0 l1 l2 l3 : ℝ) (hγ : γ ≠ 0) (hv0 : v0 ≠ 0) :
    Annihilates γ v0 0 0 S l0 l1 l2 l3 ↔
      l1 = -γ*l0 ∧ l2 = 0 ∧ l3*S = -l0*v0 := by
  rw [annihilates_iff_coefficients γ v0 0 0 S l0 l1 l2 l3 hγ]
  constructor
  · rintro ⟨lam,hc⟩
    obtain ⟨h1,h2,h3,_⟩ := (axis_coefficients_iff γ v0 S l0 l1 l2 l3 lam hv0).mp hc
    exact ⟨h1,h2,h3⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨2*l0*v0,(axis_coefficients_iff γ v0 S l0 l1 l2 l3 _ hv0).mpr ⟨h1,h2,h3,rfl⟩⟩

theorem tilted_annihilator_iff (γ v0 S l0 l1 l2 l3 : ℝ) (hγ : γ ≠ 0) (hv0 : v0 ≠ 0) :
    Annihilates γ v0 (γ*v0) 0 S l0 l1 l2 l3 ↔
      l1 = 0 ∧ l2 = 0 ∧ l3*S = -l0*v0 := by
  rw [annihilates_iff_coefficients γ v0 (γ*v0) 0 S l0 l1 l2 l3 hγ]
  constructor
  · rintro ⟨lam,hc⟩
    obtain ⟨h1,h2,h3,_⟩ :=
      (tilted_coefficients_iff γ v0 S l0 l1 l2 l3 lam hγ hv0).mp hc
    exact ⟨h1,h2,h3⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨2*l0*v0,
      (tilted_coefficients_iff γ v0 S l0 l1 l2 l3 _ hγ hv0).mpr ⟨h1,h2,h3,rfl⟩⟩

theorem sine_zero_annihilator_iff (γ v0 v1 v2 l0 l1 l2 l3 : ℝ)
    (hγ : γ ≠ 0) (hv2 : v2 ≠ 0) :
    Annihilates γ v0 v1 v2 0 l0 l1 l2 l3 ↔ l0 = 0 ∧ l1 = 0 ∧ l2 = 0 := by
  rw [annihilates_iff_coefficients γ v0 v1 v2 0 l0 l1 l2 l3 hγ]
  constructor
  · rintro ⟨lam,hc⟩
    obtain ⟨h0,h1,h2,_⟩ :=
      (sine_zero_coefficients_iff γ v0 v1 v2 l0 l1 l2 l3 lam hv2).mp hc
    exact ⟨h0,h1,h2⟩
  · rintro ⟨h0,h1,h2⟩
    exact ⟨0,(sine_zero_coefficients_iff γ v0 v1 v2 l0 l1 l2 l3 0 hv2).mpr
      ⟨h0,h1,h2,rfl⟩⟩

end P14LorentzOrbit


/- Source: grouping_audit/LorentzParametric.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The finite-parameter orbit interface, avoiding the conic origin entirely. -/

namespace P14LorentzParametric

open P14LorentzAnnihilator P14LorentzOrbit

lemma px_neg (γ t : ℝ) : px γ (-t) = px γ t := by simp [px]
lemma py_neg (γ t : ℝ) : py γ (-t) = -py γ t := by
  dsimp [py]
  rw [neg_sq,mul_neg,neg_div]

lemma param_positive_of_allowed (γ t : ℝ) (ht : γ^2-1 < t^2) :
    0 < 1-γ*px γ t := by
  have hd : (0 : ℝ) < 1+t^2 := by positivity
  have he : 1-γ*px γ t = (1+t^2-γ^2)/(1+t^2) := by
    dsimp [px]
    field_simp [ne_of_gt hd]
  rw [he]
  exact div_pos (by linarith) hd

theorem parametric_quadratic {γ a b c d e f : ℝ} (hγ : γ ≠ 0)
    (h : ∀ t : ℝ, γ^2-1 < t^2 → quadratic a b c d e f (px γ t) (py γ t) = 0) :
    a = 0 ∧ c = 0 ∧ e = 0 ∧ d = f ∧ b = -γ*f := by
  have hsq : 0 < γ^2 := sq_pos_of_ne_zero hγ
  have h12 : px γ γ ≠ px γ (2*γ) := param_x_ne hγ (by nlinarith)
  have h13 : px γ γ ≠ px γ (3*γ) := param_x_ne hγ (by nlinarith)
  have h23 : px γ (2*γ) ≠ px γ (3*γ) := param_x_ne hγ (by nlinarith)
  apply five_point_interpolation h12 h13 h23 (param_y_ne hγ hγ)
    (param_y_ne hγ (mul_ne_zero (by norm_num) hγ))
    (param_conic γ γ) (param_conic γ (2*γ)) (param_conic γ (3*γ))
  · exact h γ (by nlinarith)
  · simpa only [px_neg,py_neg] using h (-γ) (by nlinarith)
  · exact h (2*γ) (by nlinarith)
  · simpa only [px_neg,py_neg] using h (-(2*γ)) (by nlinarith)
  · exact h (3*γ) (by nlinarith)

def ParamAnnihilates (γ v0 v1 v2 S l0 l1 l2 l3 : ℝ) : Prop :=
  ∀ t, γ^2-1 < t^2 → orbitPair γ v0 v1 v2 S l0 l1 l2 l3 (px γ t) (py γ t) = 0

theorem param_annihilates_iff_coefficients (γ v0 v1 v2 S l0 l1 l2 l3 : ℝ)
    (hγ : γ ≠ 0) :
    ParamAnnihilates γ v0 v1 v2 S l0 l1 l2 l3 ↔
      ∃ lam, Coefficients γ v0 v1 v2 S l0 l1 l2 l3 lam := by
  constructor
  · intro h
    let av := A v0 v1 v2 S l0 l1 l2 l3
    have hq : ∀ t : ℝ, γ^2-1 < t^2 →
        quadratic (av+2*l0*v0) (2*(l1*v0-l0*v1)) (2*(l2*v0-l0*v2))
          (-av-2*l1*v1) (-2*(l1*v2+l2*v1)) (-av-2*l2*v2) (px γ t) (py γ t) = 0 := by
      intro t ht
      have hp := (orbitPair_zero_iff γ v0 v1 v2 S l0 l1 l2 l3 (px γ t) (py γ t)
        (param_conic γ t) (ne_of_gt (param_positive_of_allowed γ t ht))).mp (h t ht)
      have he : quadratic (av+2*l0*v0) (2*(l1*v0-l0*v1)) (2*(l2*v0-l0*v2))
          (-av-2*l1*v1) (-2*(l1*v2+l2*v1)) (-av-2*l2*v2) (px γ t) (py γ t) =
          numerator v0 v1 v2 S l0 l1 l2 l3 (px γ t) (py γ t) := by
        dsimp [quadratic,numerator,av]
        ring
      exact he.trans hp
    obtain ⟨h0,hy,hxy,hxx,hx⟩ := parametric_quadratic hγ hq
    refine ⟨-av-2*l2*v2,h0,?_,hy,hxx,hxy,rfl⟩
    calc
      _ = -γ*(-av-2*l2*v2) := hx
      _ = -(-av-2*l2*v2)*γ := by ring
  · intro h t ht
    exact ((annihilates_iff_coefficients γ v0 v1 v2 S l0 l1 l2 l3 hγ).mpr h)
      (px γ t) (py γ t) (param_conic γ t) (param_positive_of_allowed γ t ht)

theorem param_annihilates_iff_positive_conic (γ v0 v1 v2 S l0 l1 l2 l3 : ℝ)
    (hγ : γ ≠ 0) :
    ParamAnnihilates γ v0 v1 v2 S l0 l1 l2 l3 ↔ Annihilates γ v0 v1 v2 S l0 l1 l2 l3 := by
  rw [param_annihilates_iff_coefficients γ v0 v1 v2 S l0 l1 l2 l3 hγ,
    annihilates_iff_coefficients γ v0 v1 v2 S l0 l1 l2 l3 hγ]

theorem exists_param_annihilator_iff (γ v0 v1 v2 S : ℝ) (hγ : γ ≠ 0) (hS : S ≠ 0) :
    (∃ l0 l1 l2 l3 : ℝ, Nontrivial l0 l1 l2 l3 ∧
      ParamAnnihilates γ v0 v1 v2 S l0 l1 l2 l3) ↔
      (v1 = 0 ∧ v2 = 0) ∨ (v2 = 0 ∧ v1 = γ*v0) := by
  simp_rw [param_annihilates_iff_positive_conic γ v0 v1 v2 S _ _ _ _ hγ]
  exact exists_annihilator_iff γ v0 v1 v2 S hγ hS

end P14LorentzParametric


/- Source: cusp_assembly/LorentzPolynomial.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
namespace P14LorentzPolynomial
open Polynomial P14LorentzMetric P14LorentzOrbit

def A : Polynomial ℝ := 1 + X^2
def B (γ : ℝ) : Polynomial ℝ := A - C (γ^2)
def D (γ : ℝ) : Polynomial ℝ := A * B γ

def linearNumerator (γ : ℝ) (v : Vec) : Polynomial ℝ :=
  A * C (v 0) - C (γ * v 1) - C (γ * v 2) * X

def numerator (γ : ℝ) (v : Vec) : Fin 4 → Polynomial ℝ :=
  ![A * (-B γ * C (v 0) + 2 * linearNumerator γ v),
    -D γ * C (v 1) + C (2*γ) * linearNumerator γ v,
    -D γ * C (v 2) + C (2*γ) * X * linearNumerator γ v,
    D γ * C (v 3)]

def paramOrbit (γ t : ℝ) (v : Vec) : Vec := orbit (px γ t) (py γ t) v

lemma denominator_eq (γ t : ℝ) :
    denominator (px γ t) (py γ t) = (1+t^2-γ^2)/(1+t^2) := by
  have hd : (1+t^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  dsimp [denominator, px, py]
  field_simp
  ring

lemma D_positive (γ t : ℝ) (ht : γ^2-1 < t^2) : 0 < (D γ).eval t := by
  simp only [D, B, A, eval_mul, eval_sub, eval_add, eval_one, eval_pow, eval_X, eval_C]
  exact mul_pos (by positivity) (by linarith)

lemma eval_numerator (γ t : ℝ) (ht : γ^2-1 < t^2) (v : Vec) :
    (fun j => (numerator γ v j).eval t) = (D γ).eval t • paramOrbit γ t v := by
  have hA : (1+t^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hB : (1+t^2-γ^2 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  unfold paramOrbit orbit
  rw [denominator_eq]
  ext j
  fin_cases j <;>
    simp [numerator, D, B, A, linearNumerator, px, py] <;>
    field_simp <;> ring

def mixed {ι : Type*} (γ t : ℝ) (v : ι → Vec) : ι ⊕ ι → Vec :=
  Sum.elim v (fun i => paramOrbit γ t (v i))

def mixedPolynomial {ι : Type*} (γ : ℝ) (v : ι → Vec) : ι ⊕ ι → Fin 4 → Polynomial ℝ :=
  Sum.elim (fun i j => D γ * C (v i j)) (fun i => numerator γ (v i))

lemma eval_mixed {ι : Type*} (γ t : ℝ) (ht : γ^2-1 < t^2) (v : ι → Vec) (i : ι ⊕ ι) :
    (fun j => (mixedPolynomial γ v i j).eval t) = (D γ).eval t • mixed γ t v i := by
  rcases i with i | i
  · ext j; simp [mixedPolynomial, mixed]
  · exact eval_numerator γ t ht (v i)

def pairingPolynomial (γ : ℝ) (v w : Vec) : Polynomial ℝ :=
  C (v 0) * numerator γ w 0 - C (v 1) * numerator γ w 1 -
    C (v 2) * numerator γ w 2 + C (v 3) * numerator γ w 3

lemma eval_pairing (γ t : ℝ) (ht : γ^2-1 < t^2) (v w : Vec) :
    (pairingPolynomial γ v w).eval t = (D γ).eval t * form v (paramOrbit γ t w) := by
  have hn (j : Fin 4) := congrFun (eval_numerator γ t ht w) j
  simp only [Pi.smul_apply, smul_eq_mul] at hn
  simp only [pairingPolynomial, eval_add, eval_sub, eval_mul, eval_C, hn, form]
  ring

lemma pairing_ne_zero (γ : ℝ) (v w : Vec)
    (h : ∃ t : ℝ, γ^2-1 < t^2 ∧ form v (paramOrbit γ t w) ≠ 0) :
    pairingPolynomial γ v w ≠ 0 := by
  obtain ⟨t,ht,hne⟩ := h
  intro hz
  have he := eval_pairing γ t ht v w
  rw [hz, eval_zero] at he
  exact mul_ne_zero (ne_of_gt (D_positive γ t ht)) hne he.symm

end P14LorentzPolynomial
end


/- Source: elliptic_audit/LorentzSpan.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Exact orbit subspaces from the checked parametric annihilator classifier. -/

namespace P14LorentzSpan

noncomputable section
open Matrix P14LorentzMetric P14LorentzOrbit P14LorentzParametric

abbrev Vec := Fin 4 → ℝ
abbrev Param (γ : ℝ) := {τ : ℝ // γ^2-1<τ^2}

def J (γ : ℝ) (τ : Param γ) : Vec →ₗ[ℝ] Vec :=
  (diagonal * metric (px γ τ) (py γ τ)).mulVecLin

theorem J_apply (γ : ℝ) (τ : Param γ) (v : Vec) :
    J γ τ v=orbit (px γ τ) (py γ τ) v := diagonal_metric_mulVec _ _ _

theorem denominator_positive (γ : ℝ) (τ : Param γ) :
    0<denominator (px γ τ) (py γ τ) := by
  have hc := param_conic γ (τ : ℝ)
  have hp := param_positive_of_allowed γ (τ : ℝ) τ.property
  dsimp [denominator]
  linarith

theorem J_involutive (γ : ℝ) (τ : Param γ) : Function.Involutive (J γ τ) := by
  intro v
  rw [J_apply,J_apply]
  exact orbit_involutive _ _ (ne_of_gt (denominator_positive γ τ)) v

theorem metric_cross_pairing (γ : ℝ) (τ : Param γ) (v w : Vec) :
    v ⬝ᵥ (metric (px γ τ) (py γ τ) *ᵥ J γ τ w)=form v w := by
  rw [metric_pairing,← J_apply,J_involutive γ τ w]

theorem metric_same_pairing (γ : ℝ) (τ : Param γ) (v w : Vec) :
    J γ τ v ⬝ᵥ (metric (px γ τ) (py γ τ) *ᵥ J γ τ w)=
      v ⬝ᵥ (metric (px γ τ) (py γ τ) *ᵥ w) := by
  rw [metric_cross_pairing,metric_pairing,J_apply]
  exact orbit_form_symm _ _ _ _

def orbitSpan (γ : ℝ) (v : Vec) : Submodule ℝ Vec :=
  Submodule.span ℝ (Set.range fun τ : Param γ => J γ τ v)

def functional (l : Vec) : Module.Dual ℝ Vec where
  toFun v := l 0*v 0+l 1*v 1+l 2*v 2+l 3*v 3
  map_add' v w := by simp; ring
  map_smul' a v := by simp; ring

def coeff (ℓ : Module.Dual ℝ Vec) : Vec :=
  ![ℓ ![1,0,0,0],ℓ ![0,1,0,0],ℓ ![0,0,1,0],ℓ ![0,0,0,1]]

theorem functional_coeff (ℓ : Module.Dual ℝ Vec) : functional (coeff ℓ)=ℓ := by
  apply LinearMap.ext
  intro v
  have he : v=v 0 • ![1,0,0,0]+v 1 • ![0,1,0,0]+
      v 2 • ![0,0,1,0]+v 3 • ![0,0,0,1] := by
    ext i
    fin_cases i <;> simp
  change coeff ℓ 0*v 0+coeff ℓ 1*v 1+coeff ℓ 2*v 2+coeff ℓ 3*v 3=ℓ v
  conv_rhs => rw [he,map_add,map_add,map_add,map_smul,map_smul,map_smul,map_smul]
  simp [coeff]
  ring

theorem coeff_functional (l : Vec) : coeff (functional l)=l := by
  ext i
  fin_cases i <;> simp [coeff,functional]

theorem functional_smul (a : ℝ) (l : Vec) : functional (a • l)=a • functional l := by
  ext v
  simp [functional]
  ring

theorem functional_eq_zero (ℓ : Module.Dual ℝ Vec)
    (h0 : coeff ℓ 0=0) (h1 : coeff ℓ 1=0) (h2 : coeff ℓ 2=0) (h3 : coeff ℓ 3=0) : ℓ=0 := by
  rw [← functional_coeff ℓ]
  ext v
  simp [functional,h0,h1,h2,h3]

theorem eval_J (γ : ℝ) (τ : Param γ) (v : Vec) (ℓ : Module.Dual ℝ Vec) :
    ℓ (J γ τ v)=orbitPair γ (v 0) (v 1) (v 2) (v 3)
      (coeff ℓ 0) (coeff ℓ 1) (coeff ℓ 2) (coeff ℓ 3) (px γ τ) (py γ τ) := by
  have hc := param_conic γ (τ : ℝ)
  have he : denominator (px γ τ) (py γ τ)=1-γ*px γ τ := by
    dsimp [denominator]
    linarith
  conv_lhs => rw [J_apply,← functional_coeff ℓ]
  simp [functional,orbit,orbitPair,he]
  ring

theorem annihilator_iff (γ : ℝ) (v : Vec) (ℓ : Module.Dual ℝ Vec) :
    ℓ ∈ (orbitSpan γ v).dualAnnihilator ↔
      ParamAnnihilates γ (v 0) (v 1) (v 2) (v 3)
        (coeff ℓ 0) (coeff ℓ 1) (coeff ℓ 2) (coeff ℓ 3) := by
  rw [Submodule.mem_dualAnnihilator]
  change (orbitSpan γ v ≤ LinearMap.ker ℓ) ↔ _
  rw [orbitSpan,Submodule.span_le]
  constructor
  · intro h τ hτ
    have he := h (Set.mem_range_self (⟨τ,hτ⟩ : Param γ))
    exact (eval_J γ ⟨τ,hτ⟩ v ℓ).symm.trans he
  · intro h w hw
    obtain ⟨τ,rfl⟩ := hw
    change ℓ (J γ τ v)=0
    rw [eval_J]
    exact h τ τ.property

theorem subspace_eq_ker_of_annihilator (W : Submodule ℝ Vec) (φ : Module.Dual ℝ Vec)
    (h : ∀ ℓ, ℓ ∈ W.dualAnnihilator ↔ ∃ a : ℝ, ℓ=a • φ) : W=LinearMap.ker φ := by
  ext v
  constructor
  · intro hv
    have hφ : φ ∈ W.dualAnnihilator := (h φ).2 ⟨1,by simp⟩
    exact (Submodule.mem_dualAnnihilator φ).1 hφ v hv
  · intro hv
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W v).1
    intro ℓ hℓ
    obtain ⟨a,rfl⟩ := (h ℓ).1 hℓ
    change a*φ v=0
    rw [show φ v=0 from hv,mul_zero]

theorem ker_finrank (φ : Module.Dual ℝ Vec) (hφ : φ≠0) :
    Module.finrank ℝ (LinearMap.ker φ)=3 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  have h4 : Module.finrank ℝ Vec=4 := by simp [Vec]
  omega

theorem generic_span (γ : ℝ) (v : Vec) (hγ : γ≠0) (h2 : v 2≠0) (h3 : v 3≠0) :
    orbitSpan γ v=⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro ℓ hℓ
  change ℓ=0
  have hp := (annihilator_iff γ v ℓ).1 hℓ
  have hn : ¬ P14LorentzAnnihilator.Nontrivial (coeff ℓ 0) (coeff ℓ 1) (coeff ℓ 2) (coeff ℓ 3) := by
    intro hnon
    have he := (exists_param_annihilator_iff γ (v 0) (v 1) (v 2) (v 3) hγ h3).1
      ⟨coeff ℓ 0,coeff ℓ 1,coeff ℓ 2,coeff ℓ 3,hnon,hp⟩
    rcases he with he | he
    · exact h2 he.2
    · exact h2 he.1
  simp only [P14LorentzAnnihilator.Nontrivial,not_or,not_not] at hn
  exact functional_eq_zero ℓ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

theorem eq_smul_functional_iff (ℓ : Module.Dual ℝ Vec) (a : ℝ) (l : Vec) :
    ℓ=a • functional l ↔ coeff ℓ=a • l := by
  constructor
  · intro h
    rw [h,← functional_smul,coeff_functional]
  · intro h
    rw [← functional_coeff ℓ,h,functional_smul]

theorem axis_span (γ v0 S : ℝ) (hγ : γ≠0) (hv0 : v0≠0) (hS : S≠0) :
    orbitSpan γ ![v0,0,0,S] = LinearMap.ker (functional ![1,-γ,0,-v0/S]) := by
  apply subspace_eq_ker_of_annihilator
  intro ℓ
  simp only [annihilator_iff,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons]
  rw [param_annihilates_iff_positive_conic _ _ _ _ _ _ _ _ _ hγ,
    axis_annihilator_iff _ _ _ _ _ _ _ hγ hv0]
  constructor
  · rintro ⟨h1,h2,h3⟩
    refine ⟨coeff ℓ 0,(eq_smul_functional_iff _ _ _).2 ?_⟩
    have hc3 : coeff ℓ 3=coeff ℓ 0*(-v0/S) := by
      calc
        _ = -(coeff ℓ 0*v0)/S := (eq_div_iff hS).2 (by nlinarith [h3])
        _ = _ := by ring
    ext i
    fin_cases i <;> simp [h1,h2,hc3]
    ring
  · rintro ⟨a,hℓ⟩
    have hc := (eq_smul_functional_iff _ _ _).1 hℓ
    rw [hc]
    simp
    field_simp
    simp

theorem tilted_span (γ v0 S : ℝ) (hγ : γ≠0) (hv0 : v0≠0) (hS : S≠0) :
    orbitSpan γ ![v0,γ*v0,0,S] = LinearMap.ker (functional ![1,0,0,-v0/S]) := by
  apply subspace_eq_ker_of_annihilator
  intro ℓ
  simp only [annihilator_iff,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons]
  rw [param_annihilates_iff_positive_conic _ _ _ _ _ _ _ _ _ hγ,
    tilted_annihilator_iff _ _ _ _ _ _ _ hγ hv0]
  constructor
  · rintro ⟨h1,h2,h3⟩
    refine ⟨coeff ℓ 0,(eq_smul_functional_iff _ _ _).2 ?_⟩
    have hc3 : coeff ℓ 3=coeff ℓ 0*(-v0/S) := by
      calc
        _ = -(coeff ℓ 0*v0)/S := (eq_div_iff hS).2 (by nlinarith [h3])
        _ = _ := by ring
    ext i
    fin_cases i <;> simp [h1,h2,hc3]
  · rintro ⟨a,hℓ⟩
    have hc := (eq_smul_functional_iff _ _ _).1 hℓ
    rw [hc]
    simp
    field_simp

theorem sine_zero_span (γ v0 v1 v2 : ℝ) (hγ : γ≠0) (hv2 : v2≠0) :
    orbitSpan γ ![v0,v1,v2,0] = LinearMap.ker (functional ![0,0,0,1]) := by
  apply subspace_eq_ker_of_annihilator
  intro ℓ
  simp only [annihilator_iff,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons]
  rw [param_annihilates_iff_positive_conic _ _ _ _ _ _ _ _ _ hγ,
    sine_zero_annihilator_iff _ _ _ _ _ _ _ _ hγ hv2]
  constructor
  · rintro ⟨h0,h1,h2⟩
    refine ⟨coeff ℓ 3,(eq_smul_functional_iff _ _ _).2 ?_⟩
    ext i
    fin_cases i <;> simp [h0,h1,h2]
  · rintro ⟨a,hℓ⟩
    have hc := (eq_smul_functional_iff _ _ _).1 hℓ
    rw [hc]
    simp

theorem axis_rank (γ v0 S : ℝ) (hγ : γ≠0) (hv0 : v0≠0) (hS : S≠0) :
    Module.finrank ℝ (orbitSpan γ ![v0,0,0,S])=3 := by
  rw [axis_span γ v0 S hγ hv0 hS]
  apply ker_finrank
  intro he
  have h := congrArg (fun f : Module.Dual ℝ Vec => f ![1,0,0,0]) he
  norm_num [functional,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.tail_cons,Matrix.head_cons] at h

theorem tilted_rank (γ v0 S : ℝ) (hγ : γ≠0) (hv0 : v0≠0) (hS : S≠0) :
    Module.finrank ℝ (orbitSpan γ ![v0,γ*v0,0,S])=3 := by
  rw [tilted_span γ v0 S hγ hv0 hS]
  apply ker_finrank
  intro he
  have h := congrArg (fun f : Module.Dual ℝ Vec => f ![1,0,0,0]) he
  norm_num [functional,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.tail_cons,Matrix.head_cons] at h

theorem sine_zero_rank (γ v0 v1 v2 : ℝ) (hγ : γ≠0) (hv2 : v2≠0) :
    Module.finrank ℝ (orbitSpan γ ![v0,v1,v2,0])=3 := by
  rw [sine_zero_span γ v0 v1 v2 hγ hv2]
  apply ker_finrank
  intro he
  have h := congrArg (fun f : Module.Dual ℝ Vec => f ![0,0,0,1]) he
  norm_num [functional,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.tail_cons,Matrix.head_cons] at h

def lorentzFunctional (v : Vec) : Module.Dual ℝ Vec :=
  functional ![v 0,-v 1,-v 2,v 3]

theorem lorentzFunctional_apply (v w : Vec) : lorentzFunctional v w=form v w := by
  simp [lorentzFunctional,functional,form]
  ring

/-- The axis orbit is the D-orthogonal hyperplane of its repair partner. -/
theorem axis_repair_span (γ Q t ε : ℝ) (hγ : γ≠0) (hQ : Q≠0) (ht : t≠0) (hε : ε^2=1) :
    orbitSpan γ ![Q,0,0,ε*Q] =
      LinearMap.ker (lorentzFunctional ![t,γ*t,0,-ε*t]) := by
  have hεn : ε≠0 := by intro he; simp [he] at hε
  rw [axis_span γ Q (ε*Q) hγ hQ (mul_ne_zero hεn hQ)]
  have hfrac : -Q/(ε*Q)= -ε := by field_simp; nlinarith [hε]
  rw [hfrac]
  have he : lorentzFunctional ![t,γ*t,0,-ε*t]=t • functional ![1,-γ,0,-ε] := by
    apply LinearMap.ext
    intro w
    simp [lorentzFunctional,functional]
    ring
  rw [he,LinearMap.ker_smul _ t ht]

/-- The tilted orbit is the D-orthogonal hyperplane of its repair partner. -/
theorem tilted_repair_span (γ Q t ε : ℝ) (hγ : γ≠0) (hQ : Q≠0) (ht : t≠0) (hε : ε^2=1) :
    orbitSpan γ ![t,γ*t,0,-ε*t] =
      LinearMap.ker (lorentzFunctional ![Q,0,0,ε*Q]) := by
  have hεn : ε≠0 := by intro he; simp [he] at hε
  rw [tilted_span γ t (-ε*t) hγ ht (mul_ne_zero (neg_ne_zero.mpr hεn) ht)]
  have hfrac : -t/(-ε*t)=ε := by field_simp; nlinarith [hε]
  rw [hfrac]
  have he : lorentzFunctional ![Q,0,0,ε*Q]=Q • functional ![1,0,0,ε] := by
    apply LinearMap.ext
    intro w
    simp [lorentzFunctional,functional]
    ring
  rw [he,LinearMap.ker_smul _ Q hQ]

theorem sine_zero_span_mem (γ v0 v1 v2 : ℝ) (hγ : γ≠0) (hv2 : v2≠0) (w : Vec) :
    w ∈ orbitSpan γ ![v0,v1,v2,0] ↔ w 3=0 := by
  rw [sine_zero_span γ v0 v1 v2 hγ hv2]
  change functional ![0,0,0,1] w=0 ↔ _
  simp [functional]

theorem generic_rank (γ : ℝ) (v : Vec) (hγ : γ≠0) (h2 : v 2≠0) (h3 : v 3≠0) :
    Module.finrank ℝ (orbitSpan γ v)=4 := by
  rw [generic_span γ v hγ h2 h3]
  simp [Vec]

end
end P14LorentzSpan


/- Source: grouping_audit/OrbitRanks.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Pointwise rank witnesses for a common orbit family. Polynomial avoidance
is a separate step: the parameters in these witnesses need not coincide. -/

noncomputable section
open Submodule Function

namespace P14OrbitRanks

variable {E I T : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

abbrev orbitSpan (v : I → E) (J : T → E →ₗ[ℝ] E) (i : I) : Submodule ℝ E :=
  span ℝ (Set.range fun t => J t (v i))

lemma orbit_le_iff (v : I → E) (J : T → E →ₗ[ℝ] E) (i : I) (W : Submodule ℝ E) :
    orbitSpan v J i ≤ W ↔ ∀ t, J t (v i) ∈ W := by
  simp [orbitSpan, Submodule.span_le, Set.range_subset_iff]

lemma escape_two (v : I → E) (J : T → E →ₗ[ℝ] E) (i : I)
    (hO : 3 ≤ Module.finrank ℝ (orbitSpan v J i))
    (W : Submodule ℝ E) (hW : Module.finrank ℝ W ≤ 2) :
    ∃ t, J t (v i) ∉ W := by
  by_contra! h
  have hm := Submodule.finrank_mono ((orbit_le_iff v J i W).mpr h)
  omega

lemma orbit_eq_three (v : I → E) (J : T → E →ₗ[ℝ] E) (i : I)
    (hO : 3 ≤ Module.finrank ℝ (orbitSpan v J i))
    (W : Submodule ℝ E) (hW : Module.finrank ℝ W = 3)
    (h : ∀ t, J t (v i) ∈ W) : orbitSpan v J i = W := by
  have hle := (orbit_le_iff v J i W).mpr h
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hm := Submodule.finrank_mono hle
  omega

lemma escape_three_pair (v : I → E) (J : T → E →ₗ[ℝ] E) (i j : I)
    (hi : 3 ≤ Module.finrank ℝ (orbitSpan v J i))
    (hj : 3 ≤ Module.finrank ℝ (orbitSpan v J j))
    (hdist : Module.finrank ℝ (orbitSpan v J i) = 3 →
      Module.finrank ℝ (orbitSpan v J j) = 3 → orbitSpan v J i ≠ orbitSpan v J j)
    (W : Submodule ℝ E) (hW : Module.finrank ℝ W = 3) :
    ∃ t, J t (v i) ∉ W ∨ J t (v j) ∉ W := by
  by_contra! h
  have he_i := orbit_eq_three v J i hi W hW (fun t => (h t).1)
  have he_j := orbit_eq_three v J j hj W hW (fun t => (h t).2)
  exact hdist (he_i ▸ hW) (he_j ▸ hW) (he_i.trans he_j.symm)

lemma escape_three_four (v : I → E) (J : T → E →ₗ[ℝ] E) (i : I)
    (hi : 3 ≤ Module.finrank ℝ (orbitSpan v J i))
    (hcap : Module.finrank ℝ (orbitSpan v J i) = 3 →
      ∀ a : Fin 4 → I, Injective a → ¬ ∀ q, v (a q) ∈ orbitSpan v J i)
    (W : Submodule ℝ E) (hW : Module.finrank ℝ W = 3)
    (a : Fin 4 → I) (ha : Injective a) (haW : ∀ q, v (a q) ∈ W) :
    ∃ t, J t (v i) ∉ W := by
  by_contra! h
  have he := orbit_eq_three v J i hi W hW h
  exact hcap (he ▸ hW) a ha (he ▸ haW)

lemma spanning_of_hyperplane_escape (hE : Module.finrank ℝ E = 4)
    (W : Submodule ℝ E) (hW : Module.finrank ℝ W = 3) (z : E) (hz : z ∉ W) :
    W ⊔ span ℝ {z} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [Submodule.finrank_sup_span_singleton hz, hW, hE]

lemma mixed_two_one (v : I → E) (J : T → E →ₗ[ℝ] E)
    (a : Fin 2 → I) (ha : LinearIndependent ℝ (v ∘ a)) (i : I)
    (hi : 3 ≤ Module.finrank ℝ (orbitSpan v J i)) :
    ∃ t, LinearIndependent ℝ (Fin.cons (J t (v i)) (v ∘ a)) := by
  obtain ⟨t,ht⟩ := escape_two v J i hi (span ℝ (Set.range (v ∘ a)))
    (by simpa using (finrank_span_eq_card ha).le)
  exact ⟨t,ha.finCons ht⟩

lemma mixed_three_two (hE : Module.finrank ℝ E = 4)
    (v : I → E) (J : T → E →ₗ[ℝ] E)
    (a : Fin 3 → I) (ha : LinearIndependent ℝ (v ∘ a)) (i j : I)
    (hi : 3 ≤ Module.finrank ℝ (orbitSpan v J i))
    (hj : 3 ≤ Module.finrank ℝ (orbitSpan v J j))
    (hdist : Module.finrank ℝ (orbitSpan v J i) = 3 →
      Module.finrank ℝ (orbitSpan v J j) = 3 → orbitSpan v J i ≠ orbitSpan v J j) :
    ∃ t, span ℝ (Set.range (Sum.elim (v ∘ a) ![J t (v i),J t (v j)])) = ⊤ := by
  let W := span ℝ (Set.range (v ∘ a))
  have hW : Module.finrank ℝ W = 3 := by simpa [W] using finrank_span_eq_card ha
  obtain ⟨t,ht⟩ := escape_three_pair v J i j hi hj hdist W hW
  refine ⟨t,?_⟩
  apply top_unique
  rcases ht with ht | ht
  · rw [← spanning_of_hyperplane_escape hE W hW _ ht]
    apply sup_le
    · exact Submodule.span_mono (fun z ⟨q,hq⟩ => ⟨Sum.inl q,hq⟩)
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact Submodule.subset_span ⟨Sum.inr 0,rfl⟩
  · rw [← spanning_of_hyperplane_escape hE W hW _ ht]
    apply sup_le
    · exact Submodule.span_mono (fun z ⟨q,hq⟩ => ⟨Sum.inl q,hq⟩)
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact Submodule.subset_span ⟨Sum.inr 1,rfl⟩

lemma mixed_four_one (hE : Module.finrank ℝ E = 4) [Nonempty T]
    (v : I → E) (J : T → E →ₗ[ℝ] E) (a : Fin 4 → I) (ha : Injective a)
    (ha3 : LinearIndependent ℝ (fun q : Fin 3 => v (a q.castSucc))) (i : I)
    (hi : 3 ≤ Module.finrank ℝ (orbitSpan v J i))
    (hcap : Module.finrank ℝ (orbitSpan v J i) = 3 →
      ∀ a : Fin 4 → I, Injective a → ¬ ∀ q, v (a q) ∈ orbitSpan v J i) :
    ∃ t, span ℝ (Set.range (Fin.cons (J t (v i)) (v ∘ a))) = ⊤ := by
  let W := span ℝ (Set.range (v ∘ a))
  have h3W : span ℝ (Set.range (fun q : Fin 3 => v (a q.castSucc))) ≤ W :=
    Submodule.span_mono (fun z ⟨q,hq⟩ => ⟨q.castSucc,hq⟩)
  have hlo : 3 ≤ Module.finrank ℝ W := by
    have hm := Submodule.finrank_mono h3W
    have he : Module.finrank ℝ (span ℝ (Set.range (fun q : Fin 3 => v (a q.castSucc)))) = 3 := by
      simpa using finrank_span_eq_card ha3
    omega
  have hhi : Module.finrank ℝ W ≤ 4 := by simpa [hE] using Submodule.finrank_le W
  have hall : ∀ t, W ≤ span ℝ (Set.range (Fin.cons (J t (v i)) (v ∘ a))) := by
    intro t
    exact Submodule.span_mono (fun z ⟨q,hq⟩ => ⟨q.succ, by simpa using hq⟩)
  by_cases hW4 : Module.finrank ℝ W = 4
  · refine ⟨Classical.choice inferInstance, top_unique ?_⟩
    have he : W = ⊤ := Submodule.eq_top_of_finrank_eq (hW4.trans hE.symm)
    simpa [he] using hall (Classical.choice inferInstance)
  · have hW3 : Module.finrank ℝ W = 3 := by omega
    obtain ⟨t,ht⟩ := escape_three_four v J i hi hcap W hW3 a ha
      (fun q => Submodule.subset_span ⟨q,rfl⟩)
    refine ⟨t,top_unique ?_⟩
    rw [← spanning_of_hyperplane_escape hE W hW3 _ ht]
    apply sup_le (hall t)
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Submodule.subset_span ⟨0,rfl⟩

end P14OrbitRanks
end


/- Source: grouping_audit/OrbitSelections.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
open Submodule Function

namespace P14OrbitSelections
open P14OrbitRanks

variable {E I T : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

def mixed {p q : ℕ} (v : I → E) (J : E ≃ₗ[ℝ] E) (a : Fin p → I) (b : Fin q → I) :
    Fin p ⊕ Fin q → E := Sum.elim (v ∘ a) (J ∘ v ∘ b)

lemma mixed_swap {p q : ℕ} (v : I → E) (J : E ≃ₗ[ℝ] E)
    (hJ : Involutive J) (a : Fin p → I) (b : Fin q → I) :
    J ∘ mixed v J b a ∘ (Equiv.sumComm (Fin p) (Fin q)) = mixed v J a b := by
  funext z
  cases z with
  | inl z => exact hJ (v (a z))
  | inr z => rfl

lemma span_map_equiv {A : Type*} (v : A → E) (J : E ≃ₗ[ℝ] E) :
    span ℝ (Set.range (J ∘ v)) = (span ℝ (Set.range v)).map J.toLinearMap := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma span_reindex {A B : Type*} (v : A → E) (e : B ≃ A) :
    span ℝ (Set.range (v ∘ e)) = span ℝ (Set.range v) := by
  rw [e.surjective.range_comp]

lemma independent_swap {p q : ℕ} (v : I → E) (J : E ≃ₗ[ℝ] E)
    (hJ : Involutive J) (a : Fin p → I) (b : Fin q → I)
    (h : LinearIndependent ℝ (mixed v J b a)) :
    LinearIndependent ℝ (mixed v J a b) := by
  rw [← mixed_swap v J hJ a b]
  exact (h.map' J.toLinearMap J.ker).comp (Equiv.sumComm _ _) (Equiv.sumComm _ _).injective

lemma spanning_swap {p q : ℕ} (v : I → E) (J : E ≃ₗ[ℝ] E)
    (hJ : Involutive J) (a : Fin p → I) (b : Fin q → I)
    (h : span ℝ (Set.range (mixed v J b a)) = ⊤) :
    span ℝ (Set.range (mixed v J a b)) = ⊤ := by
  rw [← mixed_swap v J hJ a b, ← comp_assoc, span_reindex, span_map_equiv, h]
  simpa only [Submodule.map_top] using LinearMap.range_eq_top.mpr J.surjective

lemma mixed_zero_independent {p : ℕ} (v : I → E) (J : E ≃ₗ[ℝ] E)
    (a : Fin p → I) (b : Fin 0 → I) (ha : LinearIndependent ℝ (v ∘ a)) :
    LinearIndependent ℝ (mixed v J a b) := by
  simpa [mixed] using ha.sum_type (linearIndependent_empty_type :
    LinearIndependent ℝ (J ∘ v ∘ b)) (by simp)

lemma mixed_zero_spanning {p : ℕ} (v : I → E) (J : E ≃ₗ[ℝ] E)
    (a : Fin p → I) (b : Fin 0 → I) (ha : span ℝ (Set.range (v ∘ a)) = ⊤) :
    span ℝ (Set.range (mixed v J a b)) = ⊤ := by
  simpa [mixed, Set.Sum.elim_range, Submodule.span_union] using ha

lemma mixed_two_one' (v : I → E) (J : T → E ≃ₗ[ℝ] E)
    (a : Fin 2 → I) (b : Fin 1 → I) (ha : LinearIndependent ℝ (v ∘ a))
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i)) :
    ∃ t, LinearIndependent ℝ (mixed v (J t) a b) := by
  obtain ⟨t,ht⟩ := escape_two v (fun t => (J t).toLinearMap) (b 0) (hO _)
    (span ℝ (Set.range (v ∘ a))) (by simpa using (finrank_span_eq_card ha).le)
  have hnz : J t (v (b 0)) ≠ 0 := fun he => ht (he ▸ Submodule.zero_mem _)
  have hb : LinearIndependent ℝ (J t ∘ v ∘ b) :=
    (linearIndependent_unique_iff).mpr hnz
  refine ⟨t,ha.sum_type hb ?_⟩
  simpa [Set.range_unique, comp_def, Fin.default_eq_zero] using Submodule.disjoint_span_singleton_of_notMem ht

lemma mixed_four_one' [Nonempty T] (hE : Module.finrank ℝ E = 4)
    (v : I → E) (J : T → E ≃ₗ[ℝ] E) (a : Fin 4 → I) (b : Fin 1 → I)
    (ha : Injective a) (ha3 : LinearIndependent ℝ (fun q : Fin 3 => v (a q.castSucc)))
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i))
    (hcap : ∀ i, Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      ∀ a : Fin 4 → I, Injective a → ¬ ∀ q, v (a q) ∈ orbitSpan v (fun t => (J t).toLinearMap) i) :
    ∃ t, span ℝ (Set.range (mixed v (J t) a b)) = ⊤ := by
  obtain ⟨t,ht⟩ := mixed_four_one hE v (fun t => (J t).toLinearMap) a ha ha3
    (b 0) (hO _) (hcap _)
  refine ⟨t,?_⟩
  have hr : Set.range (mixed v (J t) a b) =
      Set.range (Fin.cons (J t (v (b 0))) (v ∘ a)) := by
    simp [mixed, Set.Sum.elim_range, Fin.range_cons, Set.range_unique, Set.union_comm]
  rwa [hr]

theorem three_split [Nonempty T] (v : I → E) (J : T → E ≃ₗ[ℝ] E)
    (hJ : ∀ t, Involutive (J t))
    (hpure : ∀ d, d ≤ 3 → ∀ a : Fin d → I, Injective a → LinearIndependent ℝ (v ∘ a))
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i))
    {p q : ℕ} (hpq : p+q=3) (a : Fin p → I) (b : Fin q → I)
    (ha : Injective a) (hb : Injective b) :
    ∃ t, LinearIndependent ℝ (mixed v (J t) a b) := by
  have hdom : ∀ {p q : ℕ}, p+q=3 → q≤p → ∀ (a : Fin p → I) (b : Fin q → I),
      Injective a → Injective b → ∃ t, LinearIndependent ℝ (mixed v (J t) a b) := by
    intro p q hpq hqp a b ha hb
    have hc : (p=3 ∧ q=0) ∨ (p=2 ∧ q=1) := by omega
    rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨Classical.choice inferInstance,mixed_zero_independent v _ a b (hpure 3 le_rfl a ha)⟩
    · exact mixed_two_one' v J a b (hpure 2 (by omega) a ha) hO
  by_cases hqp : q≤p
  · exact hdom hpq hqp a b ha hb
  · obtain ⟨t,ht⟩ := hdom (by omega : q+p=3) (by omega) b a hb ha
    exact ⟨t,independent_swap v (J t) (hJ t) a b ht⟩

theorem five_split [Nonempty T] (hE : Module.finrank ℝ E = 4)
    (v : I → E) (J : T → E ≃ₗ[ℝ] E) (hJ : ∀ t, Involutive (J t))
    (hpure3 : ∀ a : Fin 3 → I, Injective a → LinearIndependent ℝ (v ∘ a))
    (hpure5 : ∀ a : Fin 5 → I, Injective a → span ℝ (Set.range (v ∘ a)) = ⊤)
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i))
    (hdist : ∀ i j, i ≠ j →
      Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) j) = 3 →
      orbitSpan v (fun t => (J t).toLinearMap) i ≠ orbitSpan v (fun t => (J t).toLinearMap) j)
    (hcap : ∀ i, Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      ∀ a : Fin 4 → I, Injective a → ¬ ∀ q, v (a q) ∈ orbitSpan v (fun t => (J t).toLinearMap) i)
    {p q : ℕ} (hpq : p+q=5) (a : Fin p → I) (b : Fin q → I)
    (ha : Injective a) (hb : Injective b) :
    ∃ t, span ℝ (Set.range (mixed v (J t) a b)) = ⊤ := by
  have hdom : ∀ {p q : ℕ}, p+q=5 → q≤p → ∀ (a : Fin p → I) (b : Fin q → I),
      Injective a → Injective b → ∃ t, span ℝ (Set.range (mixed v (J t) a b)) = ⊤ := by
    intro p q hpq hqp a b ha hb
    have hc : (p=5 ∧ q=0) ∨ (p=4 ∧ q=1) ∨ (p=3 ∧ q=2) := by omega
    rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨Classical.choice inferInstance,mixed_zero_spanning v _ a b (hpure5 a ha)⟩
    · exact mixed_four_one' hE v J a b ha
        (hpure3 (a ∘ Fin.castSucc) (ha.comp (Fin.castSucc_injective _))) hO hcap
    · obtain ⟨t,ht⟩ := mixed_three_two hE v (fun t => (J t).toLinearMap) a (hpure3 a ha)
        (b 0) (b 1) (hO _) (hO _) (hdist _ _ (fun he => by simpa using hb he))
      refine ⟨t,?_⟩
      have he : ![J t (v (b 0)), J t (v (b 1))] = J t ∘ v ∘ b := by
        funext z
        fin_cases z <;> rfl
      change span ℝ (Set.range (Sum.elim (v ∘ a) ![J t (v (b 0)),J t (v (b 1))])) = ⊤ at ht
      simpa only [he,mixed] using ht
  by_cases hqp : q≤p
  · exact hdom hpq hqp a b ha hb
  · obtain ⟨t,ht⟩ := hdom (by omega : q+p=5) (by omega) b a hb ha
    exact ⟨t,spanning_swap v (J t) (hJ t) a b ht⟩

def leftIndex {d : ℕ} (f : Fin d → I ⊕ I) (i : {i // (f i).isLeft}) : I :=
  (f i.val).getLeft i.property

def rightIndex {d : ℕ} (f : Fin d → I ⊕ I) (i : {i // ¬ (f i).isLeft}) : I :=
  (f i.val).getRight (by simpa using i.property)

lemma leftIndex_injective {d : ℕ} (f : Fin d → I ⊕ I) (hf : Injective f) :
    Injective (leftIndex f) := by
  intro i j hij
  apply Subtype.ext
  apply hf
  simpa only [leftIndex, Sum.inl_getLeft] using congrArg (Sum.inl : I → I ⊕ I) hij

lemma rightIndex_injective {d : ℕ} (f : Fin d → I ⊕ I) (hf : Injective f) :
    Injective (rightIndex f) := by
  intro i j hij
  apply Subtype.ext
  apply hf
  simpa only [rightIndex, Sum.inr_getRight] using congrArg (Sum.inr : I → I ⊕ I) hij

lemma partition_card {d : ℕ} (f : Fin d → I ⊕ I) :
    Fintype.card {i // (f i).isLeft} + Fintype.card {i // ¬ (f i).isLeft} = d := by
  classical
  simpa using Fintype.card_congr (Equiv.sumCompl (fun i => (f i).isLeft))

def partitionEquiv {d : ℕ} (f : Fin d → I ⊕ I) :
    Fin (Fintype.card {i // (f i).isLeft}) ⊕ Fin (Fintype.card {i // ¬ (f i).isLeft}) ≃ Fin d :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl (fun i => (f i).isLeft))

lemma partition_family {d : ℕ} (v : I → E) (J : E ≃ₗ[ℝ] E) (f : Fin d → I ⊕ I) :
    mixed v J (leftIndex f ∘ (Fintype.equivFin _).symm)
      (rightIndex f ∘ (Fintype.equivFin _).symm) =
      (Sum.elim v (J ∘ v)) ∘ f ∘ partitionEquiv f := by
  funext i
  cases i with
  | inl i =>
    let j : {i // (f i).isLeft} := (Fintype.equivFin _).symm i
    change v ((f j.val).getLeft j.property) = Sum.elim v (J ∘ v) (f j.val)
    conv_rhs => rw [← Sum.inl_getLeft (f j.val) j.property]
    rfl
  | inr i =>
    let j : {i // ¬ (f i).isLeft} := (Fintype.equivFin _).symm i
    change J (v ((f j.val).getRight _)) = Sum.elim v (J ∘ v) (f j.val)
    conv_rhs => rw [← Sum.inr_getRight (f j.val) (by simpa using j.property)]
    rfl

theorem three_selections [Nonempty T] (v : I → E) (J : T → E ≃ₗ[ℝ] E)
    (hJ : ∀ t, Involutive (J t))
    (hpure : ∀ d, d ≤ 3 → ∀ a : Fin d → I, Injective a → LinearIndependent ℝ (v ∘ a))
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i))
    (f : Fin 3 → I ⊕ I) (hf : Injective f) :
    ∃ t, LinearIndependent ℝ ((Sum.elim v (J t ∘ v)) ∘ f) := by
  obtain ⟨t,ht⟩ := three_split v J hJ hpure hO (partition_card f)
    (leftIndex f ∘ (Fintype.equivFin _).symm) (rightIndex f ∘ (Fintype.equivFin _).symm)
    ((leftIndex_injective f hf).comp (Fintype.equivFin _).symm.injective)
    ((rightIndex_injective f hf).comp (Fintype.equivFin _).symm.injective)
  rw [partition_family] at ht
  refine ⟨t,?_⟩
  simpa [comp_def] using ht.comp (partitionEquiv f).symm (partitionEquiv f).symm.injective

theorem five_selections [Nonempty T] (hE : Module.finrank ℝ E = 4)
    (v : I → E) (J : T → E ≃ₗ[ℝ] E) (hJ : ∀ t, Involutive (J t))
    (hpure3 : ∀ a : Fin 3 → I, Injective a → LinearIndependent ℝ (v ∘ a))
    (hpure5 : ∀ a : Fin 5 → I, Injective a → span ℝ (Set.range (v ∘ a)) = ⊤)
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i))
    (hdist : ∀ i j, i ≠ j →
      Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) j) = 3 →
      orbitSpan v (fun t => (J t).toLinearMap) i ≠ orbitSpan v (fun t => (J t).toLinearMap) j)
    (hcap : ∀ i, Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      ∀ a : Fin 4 → I, Injective a → ¬ ∀ q, v (a q) ∈ orbitSpan v (fun t => (J t).toLinearMap) i)
    (f : Fin 5 → I ⊕ I) (hf : Injective f) :
    ∃ t, span ℝ (Set.range ((Sum.elim v (J t ∘ v)) ∘ f)) = ⊤ := by
  obtain ⟨t,ht⟩ := five_split hE v J hJ hpure3 hpure5 hO hdist hcap (partition_card f)
    (leftIndex f ∘ (Fintype.equivFin _).symm) (rightIndex f ∘ (Fintype.equivFin _).symm)
    ((leftIndex_injective f hf).comp (Fintype.equivFin _).symm.injective)
    ((rightIndex_injective f hf).comp (Fintype.equivFin _).symm.injective)
  rw [partition_family, ← comp_assoc, span_reindex] at ht
  exact ⟨t,ht⟩

lemma small_of_three [Fintype I] (v : I → E) (hcard : 3 ≤ Fintype.card I)
    (hthree : ∀ a : Fin 3 → I, Injective a → LinearIndependent ℝ (v ∘ a)) :
    ∀ d, d ≤ 3 → ∀ a : Fin d → I, Injective a → LinearIndependent ℝ (v ∘ a) := by
  intro d hd a ha
  let e := Fintype.equivFin I
  have hdn : d ≤ Fintype.card I := hd.trans hcard
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE hdn) (e ∘ a) (Fin.castLE_injective _) (e.injective.comp ha)
  have hbig := hthree (e.symm ∘ σ ∘ Fin.castLE hcard)
    (e.symm.injective.comp (σ.injective.comp (Fin.castLE_injective _)))
  have hres := hbig.comp (Fin.castLE hd) (Fin.castLE_injective _)
  have he : (v ∘ (e.symm ∘ σ ∘ Fin.castLE hcard)) ∘ Fin.castLE hd = v ∘ a := by
    funext i
    change v (e.symm (σ (Fin.castLE hdn i))) = v (a i)
    rw [hσ i]
    simp [comp_def]
  rwa [he] at hres

end P14OrbitSelections
end


/- Source: grouping_audit/PolynomialGenericity.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! A finite family of pointwise polynomial rank witnesses has one common
real parameter, arbitrarily large, at which all witnesses hold. -/

noncomputable section
open Polynomial Submodule Function
open scoped BigOperators

namespace P14PolynomialGenericity

abbrev Space (k : ℕ) := EuclideanSpace ℝ (Fin k)

def rowEval {k : ℕ} (p : Fin k → Polynomial ℝ) (t : ℝ) : Space k :=
  WithLp.toLp 2 (fun j => (p j).eval t)

def gramPolynomial {k n : ℕ} (p : Fin n → Fin k → Polynomial ℝ) : Polynomial ℝ :=
  Matrix.det (Matrix.of fun i j => ∑ q, p i q * p j q)

lemma eval_gramPolynomial {k n : ℕ} (p : Fin n → Fin k → Polynomial ℝ) (t : ℝ) :
    (gramPolynomial p).eval t = (Matrix.gram ℝ (fun i => rowEval (p i) t)).det := by
  change (Polynomial.evalRingHom t) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.gram_apply, rowEval, PiLp.inner_apply, mul_comm, Polynomial.eval_finsetSum]

lemma gramPolynomial_ne_zero {k n : ℕ} (p : Fin n → Fin k → Polynomial ℝ)
    (h : ∃ t, LinearIndependent ℝ (fun i => rowEval (p i) t)) :
    gramPolynomial p ≠ 0 := by
  obtain ⟨t,ht⟩ := h
  intro he
  have hh := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr ht
  rw [← eval_gramPolynomial, he, Polynomial.eval_zero] at hh
  exact hh rfl

theorem avoid_finitely_many {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℝ) (hp : ∀ i, p i ≠ 0) (bound : ℝ) :
    ∃ t, bound < t ∧ ∀ i, (p i).eval t ≠ 0 := by
  classical
  let P := ∏ i, p i
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  obtain ⟨b,hb⟩ := Polynomial.exists_max_root P hP
  let t := max b bound + 1
  have hbt : b < t := by dsimp [t]; linarith [le_max_left b bound]
  have hbound : bound < t := by dsimp [t]; linarith [le_max_right b bound]
  have hPt : P.eval t ≠ 0 := fun he => (not_le_of_gt hbt) (hb t he)
  refine ⟨t,hbound,?_⟩
  have hpall : ∏ i, (p i).eval t ≠ 0 := by simpa [P, Polynomial.eval_prod] using hPt
  exact fun i => (Finset.prod_ne_zero_iff.mp hpall) i (Finset.mem_univ _)

theorem simultaneous_independent {ι κ : Type*} [Fintype ι] [Fintype κ]
    {k : ℕ} (n : ι → ℕ) (p : (i : ι) → Fin (n i) → Fin k → Polynomial ℝ)
    (hwitness : ∀ i, ∃ t, LinearIndependent ℝ (fun j => rowEval (p i j) t))
    (extra : κ → Polynomial ℝ) (hextra : ∀ i, extra i ≠ 0) (bound : ℝ) :
    ∃ t, bound < t ∧
      (∀ i, LinearIndependent ℝ (fun j => rowEval (p i j) t)) ∧
      ∀ i, (extra i).eval t ≠ 0 := by
  let tests : ι ⊕ κ → Polynomial ℝ := Sum.elim (fun i => gramPolynomial (p i)) extra
  have htests : ∀ i, tests i ≠ 0 := by
    intro i
    cases i with
    | inl i => exact gramPolynomial_ne_zero (p i) (hwitness i)
    | inr i => exact hextra i
  obtain ⟨t,ht,htests⟩ := avoid_finitely_many tests htests bound
  refine ⟨t,ht,?_,fun i => htests (Sum.inr i)⟩
  intro i
  apply Matrix.det_gram_ne_zero_iff_linearIndependent.mp
  rw [← eval_gramPolynomial]
  exact htests (Sum.inl i)

lemma independent_subfamily_of_spanning {k : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → Space k) (hv : span ℝ (Set.range v) = ⊤) :
    ∃ e : Fin k → ι, Injective e ∧ LinearIndependent ℝ (v ∘ e) := by
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli,hspan,hv]
    simp [Space]
  let eκ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨a ∘ eκ,ha.comp eκ.injective,hli.comp eκ eκ.injective⟩

theorem simultaneous_three_five {I κ : Type*} [Fintype I] [Fintype κ]
    (p : I → Fin 4 → Polynomial ℝ)
    (hthree : ∀ a : Fin 3 → I, Injective a →
      ∃ t, LinearIndependent ℝ (fun q => rowEval (p (a q)) t))
    (hfive : ∀ a : Fin 5 → I, Injective a →
      ∃ t, span ℝ (Set.range (fun q => rowEval (p (a q)) t)) = ⊤)
    (extra : κ → Polynomial ℝ) (hextra : ∀ i, extra i ≠ 0) (bound : ℝ) :
    ∃ t, bound < t ∧
      (∀ a : Fin 3 → I, Injective a → LinearIndependent ℝ (fun q => rowEval (p (a q)) t)) ∧
      (∀ a : Fin 5 → I, Injective a → span ℝ (Set.range (fun q => rowEval (p (a q)) t)) = ⊤) ∧
      ∀ i, (extra i).eval t ≠ 0 := by
  classical
  let A := {a : Fin 3 → I // Injective a}
  let B := {a : Fin 5 → I // Injective a}
  have hb : ∀ b : B, ∃ e : Fin 4 → Fin 5, ∃ t,
      LinearIndependent ℝ (fun q => rowEval (p (b.val (e q))) t) := by
    intro b
    obtain ⟨t,ht⟩ := hfive b.val b.property
    obtain ⟨e,he,hli⟩ := independent_subfamily_of_spanning _ ht
    exact ⟨e,t,hli⟩
  choose e et het using hb
  let n : A ⊕ B → ℕ := Sum.elim (fun _ => 3) (fun _ => 4)
  let rows : (i : A ⊕ B) → Fin (n i) → Fin 4 → Polynomial ℝ :=
    fun i => match i with
    | Sum.inl a => fun q => p (a.val q)
    | Sum.inr b => fun q => p (b.val (e b q))
  have hw : ∀ i, ∃ t, LinearIndependent ℝ (fun j => rowEval (rows i j) t) := by
    intro i
    cases i with
    | inl a => exact hthree a.val a.property
    | inr b => exact ⟨et b,het b⟩
  obtain ⟨t,ht,hli,hex⟩ := simultaneous_independent n rows hw extra hextra bound
  refine ⟨t,ht,fun a ha => hli (Sum.inl ⟨a,ha⟩),?_,hex⟩
  intro a ha
  let b : B := ⟨a,ha⟩
  have hs : span ℝ (Set.range (fun q => rowEval (p (a (e b q))) t)) = ⊤ :=
    (hli (Sum.inr b)).span_eq_top_of_card_eq_finrank' (by simp [Space,n]; rfl)
  apply top_unique
  rw [← hs]
  exact Submodule.span_mono (fun z ⟨q,hq⟩ => ⟨e b q,hq⟩)

lemma independent_scale_iff {E A : Type*} [AddCommGroup E] [Module ℝ E]
    (v : A → E) (c : ℝ) (hc : c ≠ 0) :
    LinearIndependent ℝ (fun i => c • v i) ↔ LinearIndependent ℝ v := by
  exact LinearIndependent.units_smul_iff v (fun _ => Units.mk0 c hc)

lemma span_scale {E A : Type*} [AddCommGroup E] [Module ℝ E]
    (v : A → E) (c : ℝ) (hc : c ≠ 0) :
    span ℝ (Set.range (fun i => c • v i)) = span ℝ (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨i,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro z ⟨i,rfl⟩
    have h := Submodule.smul_mem (span ℝ (Set.range (fun i => c • v i))) c⁻¹
      (Submodule.subset_span ⟨i,rfl⟩)
    simpa [smul_smul,hc] using h

end P14PolynomialGenericity
end


/- Source: grouping_audit/RationalOrbitGenericity.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Assembly of pointwise orbit geometry with finite polynomial avoidance.
The common denominator and polynomial row identity remain explicit inputs. -/

noncomputable section
open Function Submodule

namespace P14RationalOrbitGenericity
open P14OrbitRanks P14OrbitSelections P14PolynomialGenericity

lemma span_map_coordinates {E F A : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (v : A → E) (e : E ≃ₗ[ℝ] F) :
    span ℝ (Set.range (e ∘ v)) = (span ℝ (Set.range v)).map e.toLinearMap := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem proof {I K : Type*} [Fintype I] [Fintype K]
    (allowed : Set ℝ) (bound : ℝ) (hupper : ∀ t, bound < t → t ∈ allowed)
    (v : I → Space 4) (J : allowed → Space 4 ≃ₗ[ℝ] Space 4)
    (hJ : ∀ t, Involutive (J t))
    (hpure : ∀ d, d ≤ 3 → ∀ a : Fin d → I, Injective a → LinearIndependent ℝ (v ∘ a))
    (hpure5 : ∀ a : Fin 5 → I, Injective a → span ℝ (Set.range (v ∘ a)) = ⊤)
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i))
    (hdist : ∀ i j, i ≠ j →
      Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) j) = 3 →
      orbitSpan v (fun t => (J t).toLinearMap) i ≠ orbitSpan v (fun t => (J t).toLinearMap) j)
    (hcap : ∀ i, Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      ∀ a : Fin 4 → I, Injective a → ¬ ∀ q, v (a q) ∈ orbitSpan v (fun t => (J t).toLinearMap) i)
    (p : I ⊕ I → Fin 4 → Polynomial ℝ) (den : ℝ → ℝ)
    (hden : ∀ t : allowed, den t ≠ 0)
    (hrows : ∀ (t : allowed) i, rowEval (p i) t = den t • Sum.elim v (J t ∘ v) i)
    (extra : K → Polynomial ℝ) (hextra : ∀ i, extra i ≠ 0) :
    ∃ t : allowed, bound < t.val ∧
      (∀ a : Fin 3 → I ⊕ I, Injective a →
        LinearIndependent ℝ ((Sum.elim v (J t ∘ v)) ∘ a)) ∧
      (∀ a : Fin 5 → I ⊕ I, Injective a →
        span ℝ (Set.range ((Sum.elim v (J t ∘ v)) ∘ a)) = ⊤) ∧
      ∀ i, (extra i).eval t.val ≠ 0 := by
  classical
  let : Nonempty allowed := ⟨⟨bound+1,hupper _ (by linarith)⟩⟩
  have hthree : ∀ a : Fin 3 → I ⊕ I, Injective a →
      ∃ t, LinearIndependent ℝ (fun q => rowEval (p (a q)) t) := by
    intro a ha
    obtain ⟨t,ht⟩ := three_selections v J hJ hpure hO a ha
    refine ⟨t.val,?_⟩
    simp_rw [hrows t]
    exact (independent_scale_iff _ _ (hden t)).mpr ht
  have hfive : ∀ a : Fin 5 → I ⊕ I, Injective a →
      ∃ t, span ℝ (Set.range (fun q => rowEval (p (a q)) t)) = ⊤ := by
    intro a ha
    obtain ⟨t,ht⟩ := five_selections (by simp [Space]) v J hJ
      (hpure 3 le_rfl) hpure5 hO hdist hcap a ha
    refine ⟨t.val,?_⟩
    simp_rw [hrows t]
    rw [span_scale _ _ (hden t)]
    exact ht
  obtain ⟨t,ht,h3,h5,hex⟩ := simultaneous_three_five p hthree hfive extra hextra bound
  let t' : allowed := ⟨t,hupper t ht⟩
  refine ⟨t',ht,?_,?_,hex⟩
  · intro a ha
    have h := h3 a ha
    change LinearIndependent ℝ (fun q => rowEval (p (a q)) t') at h
    simp_rw [hrows t'] at h
    exact (independent_scale_iff _ _ (hden t')).mp h
  · intro a ha
    have h := h5 a ha
    change span ℝ (Set.range (fun q => rowEval (p (a q)) t')) = ⊤ at h
    simp_rw [hrows t'] at h
    rw [span_scale _ _ (hden t')] at h
    exact h


theorem proof_coordinates {E I K : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [Fintype I] [Fintype K]
    (e : E ≃ₗ[ℝ] Space 4)
    (allowed : Set ℝ) (bound : ℝ) (hupper : ∀ t, bound < t → t ∈ allowed)
    (v : I → E) (J : allowed → E ≃ₗ[ℝ] E)
    (hJ : ∀ t, Involutive (J t))
    (hpure : ∀ d, d ≤ 3 → ∀ a : Fin d → I, Injective a → LinearIndependent ℝ (v ∘ a))
    (hpure5 : ∀ a : Fin 5 → I, Injective a → span ℝ (Set.range (v ∘ a)) = ⊤)
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i))
    (hdist : ∀ i j, i ≠ j →
      Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) j) = 3 →
      orbitSpan v (fun t => (J t).toLinearMap) i ≠ orbitSpan v (fun t => (J t).toLinearMap) j)
    (hcap : ∀ i, Module.finrank ℝ (orbitSpan v (fun t => (J t).toLinearMap) i) = 3 →
      ∀ a : Fin 4 → I, Injective a → ¬ ∀ q, v (a q) ∈ orbitSpan v (fun t => (J t).toLinearMap) i)
    (p : I ⊕ I → Fin 4 → Polynomial ℝ) (den : ℝ → ℝ)
    (hden : ∀ t : allowed, den t ≠ 0)
    (hrows : ∀ (t : allowed) i, rowEval (p i) t = den t • e (Sum.elim v (J t ∘ v) i))
    (extra : K → Polynomial ℝ) (hextra : ∀ i, extra i ≠ 0) :
    ∃ t : allowed, bound < t.val ∧
      (∀ a : Fin 3 → I ⊕ I, Injective a →
        LinearIndependent ℝ ((Sum.elim v (J t ∘ v)) ∘ a)) ∧
      (∀ a : Fin 5 → I ⊕ I, Injective a →
        span ℝ (Set.range ((Sum.elim v (J t ∘ v)) ∘ a)) = ⊤) ∧
      ∀ i, (extra i).eval t.val ≠ 0 := by
  classical
  let : Nonempty allowed := ⟨⟨bound+1,hupper _ (by linarith)⟩⟩
  have hthree : ∀ a : Fin 3 → I ⊕ I, Injective a →
      ∃ t, LinearIndependent ℝ (fun q => rowEval (p (a q)) t) := by
    intro a ha
    obtain ⟨t,ht⟩ := three_selections v J hJ hpure hO a ha
    refine ⟨t.val,?_⟩
    simp_rw [hrows t]
    exact (independent_scale_iff _ _ (hden t)).mpr (ht.map' e.toLinearMap e.ker)
  have hfive : ∀ a : Fin 5 → I ⊕ I, Injective a →
      ∃ t, span ℝ (Set.range (fun q => rowEval (p (a q)) t)) = ⊤ := by
    intro a ha
    obtain ⟨t,ht⟩ := five_selections (e.finrank_eq.trans (by simp [Space])) v J hJ
      (hpure 3 le_rfl) hpure5 hO hdist hcap a ha
    refine ⟨t.val,?_⟩
    simp_rw [hrows t]
    rw [span_scale _ _ (hden t)]
    change span ℝ (Set.range (e ∘ ((Sum.elim v (J t ∘ v)) ∘ a))) = ⊤
    rw [span_map_coordinates,ht]
    simpa only [Submodule.map_top] using LinearMap.range_eq_top.mpr e.surjective
  obtain ⟨t,ht,h3,h5,hex⟩ := simultaneous_three_five p hthree hfive extra hextra bound
  let t' : allowed := ⟨t,hupper t ht⟩
  refine ⟨t',ht,?_,?_,hex⟩
  · intro a ha
    have h := h3 a ha
    change LinearIndependent ℝ (fun q => rowEval (p (a q)) t') at h
    simp_rw [hrows t'] at h
    exact LinearIndependent.of_comp e.toLinearMap ((independent_scale_iff _ _ (hden t')).mp h)
  · intro a ha
    have h := h5 a ha
    change span ℝ (Set.range (fun q => rowEval (p (a q)) t')) = ⊤ at h
    simp_rw [hrows t'] at h
    rw [span_scale _ _ (hden t')] at h
    change span ℝ (Set.range (e ∘ ((Sum.elim v (J t' ∘ v)) ∘ a))) = ⊤ at h
    rw [span_map_coordinates] at h
    exact Submodule.map_eq_top_iff.mp h

end P14RationalOrbitGenericity
end


/- Source: cusp_assembly/LorentzSeedAssembly.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
namespace P14LorentzSeedAssembly
open Matrix Submodule P14LorentzMetric P14LorentzOrbit

def JE (γ : ℝ) (t : P14LorentzSpan.Param γ) : Vec ≃ₗ[ℝ] Vec :=
  LinearEquiv.ofBijective (P14LorentzSpan.J γ t)
    (P14LorentzSpan.J_involutive γ t).bijective

lemma JE_apply (γ : ℝ) (t : P14LorentzSpan.Param γ) (v : Vec) :
    JE γ t v = P14LorentzSpan.J γ t v := rfl

/-- A seed witness that retains its particular graph for complement factorization. -/
def MetricSeed (N : ℕ) (hN : 3 ≤ N) : Prop :=
  ∃ H : Mat, H.PosDef ∧ ∃ v : P14OddGraph.Vertex N → Vec,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, dotProduct (v i) (H *ᵥ v j) = 0 ↔ (P14OddGraph.graph N hN).Adj i j) ∧
    (∀ d, d ≤ 3 → ∀ f : Fin d → P14OddGraph.Vertex N, Function.Injective f →
      LinearIndependent ℝ (v ∘ f)) ∧
    (∀ f : Fin 5 → P14OddGraph.Vertex N, Function.Injective f →
      span ℝ (Set.range (v ∘ f)) = ⊤)

theorem to_seed (N : ℕ) (hN : 3 ≤ N) (h : MetricSeed N hN) :
    P14SeedInterface.Seed (4*N+2) := by
  classical
  obtain ⟨H,hH,v,hv,hedge,hsmall,h5⟩ := h
  let e : Fin (4*N+2) ≃ P14OddGraph.Vertex N :=
    (Fintype.equivFinOfCardEq (by simp [P14OddGraph.Vertex, P14OddGraph.Cyclic]; omega)).symm
  exact P14SeedInterface.of_metric_family e (P14OddGraph.graph N hN)
    (P14OddGraph.graph_connected N hN) (P14OddGraph.graph_degree N hN)
    H hH v hv hedge hsmall h5

theorem metric_of_geometry (N : ℕ) (hN : 3 ≤ N) (γ : ℝ)
    (u : P14OddGraph.Cyclic N → Vec) (hnz : ∀ i, u i ≠ 0)
    (hpure : ∀ d, d ≤ 3 → ∀ a : Fin d → P14OddGraph.Cyclic N,
      Function.Injective a → LinearIndependent ℝ (u ∘ a))
    (hpure5 : ∀ a : Fin 5 → P14OddGraph.Cyclic N, Function.Injective a →
      span ℝ (Set.range (u ∘ a)) = ⊤)
    (hO : ∀ i, 3 ≤ Module.finrank ℝ (P14LorentzSpan.orbitSpan γ (u i)))
    (hdist : ∀ i j, i ≠ j →
      Module.finrank ℝ (P14LorentzSpan.orbitSpan γ (u i)) = 3 →
      Module.finrank ℝ (P14LorentzSpan.orbitSpan γ (u j)) = 3 →
      P14LorentzSpan.orbitSpan γ (u i) ≠ P14LorentzSpan.orbitSpan γ (u j))
    (hcap : ∀ i, Module.finrank ℝ (P14LorentzSpan.orbitSpan γ (u i)) = 3 →
      ∀ a : Fin 4 → P14OddGraph.Cyclic N, Function.Injective a →
      ¬ ∀ q, u (a q) ∈ P14LorentzSpan.orbitSpan γ (u i))
    (hcross : ∀ i j, form (u i) (u j) = 0 ↔ j ∈ P14OddGraph.cross N i)
    (hsame : ∀ i j, (∀ t : P14LorentzSpan.Param γ,
      form (u i) (P14LorentzSpan.J γ t (u j)) = 0) ↔ j ∈ P14OddGraph.within N i) :
    MetricSeed N hN := by
  classical
  let allowed : Set ℝ := {t | γ^2-1 < t^2}
  let K := {p : P14OddGraph.Cyclic N × P14OddGraph.Cyclic N //
    p.2 ∉ P14OddGraph.within N p.1}
  let extra : K → Polynomial ℝ := fun k =>
    P14LorentzPolynomial.pairingPolynomial γ (u k.val.1) (u k.val.2)
  have hextra : ∀ k, extra k ≠ 0 := by
    intro k
    have hn : ¬ ∀ t : P14LorentzSpan.Param γ,
        form (u k.val.1) (P14LorentzSpan.J γ t (u k.val.2)) = 0 :=
      fun h => k.property ((hsame _ _).mp h)
    obtain ⟨t,ht⟩ := not_forall.mp hn
    apply P14LorentzPolynomial.pairing_ne_zero
    refine ⟨t,t.property,?_⟩
    simpa only [P14LorentzPolynomial.paramOrbit, ← P14LorentzSpan.J_apply] using ht
  let coords : Vec ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (WithLp.linearEquiv 2 ℝ Vec).symm
  have hupper : ∀ t : ℝ, γ^2+1 < t → t ∈ allowed := by
    intro t ht
    change γ^2-1 < t^2
    nlinarith [sq_nonneg γ, sq_nonneg (t-1)]
  have hden : ∀ t : allowed, (P14LorentzPolynomial.D γ).eval (t : ℝ) ≠ 0 :=
    fun t => ne_of_gt (P14LorentzPolynomial.D_positive γ t t.property)
  have hmixed (t : allowed) (i : P14OddGraph.Vertex N) :
      P14LorentzPolynomial.mixed γ t u i = Sum.elim u (JE γ t ∘ u) i := by
    rcases i with i | i
    · rfl
    · exact (P14LorentzSpan.J_apply γ t (u i)).symm
  have hrows (t : allowed) (i : P14OddGraph.Vertex N) :
      P14PolynomialGenericity.rowEval (P14LorentzPolynomial.mixedPolynomial γ u i) t =
        (P14LorentzPolynomial.D γ).eval (t : ℝ) • coords (Sum.elim u (JE γ t ∘ u) i) := by
    change coords (fun j => (P14LorentzPolynomial.mixedPolynomial γ u i j).eval (t : ℝ)) = _
    rw [P14LorentzPolynomial.eval_mixed γ t t.property, map_smul, hmixed]
  obtain ⟨t,_,h3,h5,hex⟩ := P14RationalOrbitGenericity.proof_coordinates
    coords allowed (γ^2+1) hupper u (JE γ)
    (fun t => P14LorentzSpan.J_involutive γ t) hpure hpure5 hO hdist hcap
    (P14LorentzPolynomial.mixedPolynomial γ u) (fun t => (P14LorentzPolynomial.D γ).eval (t : ℝ))
    hden hrows extra hextra
  have hs (i j : P14OddGraph.Cyclic N) :
      form (u i) (P14LorentzSpan.J γ t (u j)) = 0 ↔ j ∈ P14OddGraph.within N i := by
    constructor
    · intro h
      by_contra hn
      have he := hex (⟨(i,j),hn⟩ : K)
      change (P14LorentzPolynomial.pairingPolynomial γ (u i) (u j)).eval (t : ℝ) ≠ 0 at he
      rw [P14LorentzPolynomial.eval_pairing γ t t.property] at he
      have hz : form (u i) (P14LorentzPolynomial.paramOrbit γ t (u j)) = 0 := by
        simpa only [P14LorentzPolynomial.paramOrbit, ← P14LorentzSpan.J_apply] using h
      exact he (by rw [hz, mul_zero])
    · intro h; exact (hsame i j).mpr h t
  let v : P14OddGraph.Vertex N → Vec := Sum.elim u (JE γ t ∘ u)
  let H := metric (px γ t) (py γ t)
  have hH : H.PosDef := metric_posDef _ _ (P14LorentzSpan.denominator_positive γ t)
  have hv : ∀ i, v i ≠ 0 := by
    rintro (i | i)
    · exact hnz i
    · exact (JE γ t).map_ne_zero_iff.mpr (hnz i)
  have hedge : ∀ i j, dotProduct (v i) (H *ᵥ v j) = 0 ↔ (P14OddGraph.graph N hN).Adj i j := by
    rintro (i | i) (j | j)
    · change dotProduct (u i) (metric (px γ t) (py γ t) *ᵥ u j) = 0 ↔ _
      rw [metric_pairing, ← P14LorentzSpan.J_apply]
      exact hs i j
    · change dotProduct (u i) (metric (px γ t) (py γ t) *ᵥ P14LorentzSpan.J γ t (u j)) = 0 ↔ _
      rw [P14LorentzSpan.metric_cross_pairing]
      exact hcross i j
    · change dotProduct (P14LorentzSpan.J γ t (u i)) (metric (px γ t) (py γ t) *ᵥ u j) = 0 ↔ _
      rw [metric_pairing, ← P14LorentzSpan.J_apply, P14LorentzSpan.J_apply γ t (u i),
        orbit_form_symm, ← P14LorentzSpan.J_apply, P14LorentzSpan.J_involutive γ t (u j)]
      exact hcross i j
    · change dotProduct (P14LorentzSpan.J γ t (u i))
        (metric (px γ t) (py γ t) *ᵥ P14LorentzSpan.J γ t (u j)) = 0 ↔ _
      rw [P14LorentzSpan.metric_same_pairing, metric_pairing, ← P14LorentzSpan.J_apply]
      exact hs i j
  have hcard : 3 ≤ Fintype.card (P14OddGraph.Vertex N) := by
    simp [P14OddGraph.Vertex, P14OddGraph.Cyclic]
    omega
  have hsmall := P14OrbitSelections.small_of_three v hcard h3
  exact ⟨H,hH,v,hv,hedge,hsmall,h5⟩

end P14LorentzSeedAssembly
end


/- Source: literature/TrigClutchReused.lean. Reused authorship is retained in the source comments and artifact citations. -/
/- Attributed verbatim proof reuse from woshuajolk, Jig p14 s75
   ClutchedVandermondeRanks. Only the namespace is changed.
   Extracted from cusp_assembly/Reused.lean; no new rank theorem is claimed here. -/

namespace P14TrigClutchReused

open Matrix

noncomputable def clutch (k : ℕ) (tau z : ℂ) : Fin k → ℂ := fun q =>
  if q.val = 0 then 1 + tau * z ^ k else z ^ q.val

lemma clutch_kminus1_independent {k n : ℕ} (hk : 2 ≤ k)
    (tau : ℂ) (z : Fin n → ℂ) (hz : Function.Injective z)
    (hnz : ∀ i, z i ≠ 0) (f : Fin (k - 1) → Fin n)
    (hf : Function.Injective f) :
    LinearIndependent ℂ (fun i => clutch k tau (z (f i))) := by
  let D : (Fin k → ℂ) →ₗ[ℂ] (Fin (k - 1) → ℂ) :=
    LinearMap.pi (fun q => LinearMap.proj (R := ℂ)
      (⟨q.val + 1, by omega⟩ : Fin k))
  let A : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ :=
    fun i q => z (f i) ^ (q.val + 1)
  have hA : A = Matrix.diagonal (fun i => z (f i)) *
      Matrix.vandermonde (z ∘ f) := by
    ext i q
    simp [A, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vandermonde_apply,
      pow_succ']
  have hdet : A.det ≠ 0 := by
    rw [hA, Matrix.det_mul, Matrix.det_diagonal]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hnz (f i))
    · exact Matrix.det_vandermonde_ne_zero_iff.mpr (hz.comp hf)
  have hrows : LinearIndependent ℂ (fun i => A i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  apply LinearIndependent.of_comp D
  have hDA : (fun i => D (clutch k tau (z (f i)))) = fun i => A i := by
    funext i q
    simp [D, A, clutch]
  change LinearIndependent ℂ (fun i => D (clutch k tau (z (f i))))
  rw [hDA]
  exact hrows

lemma clutch_kplus1_spanning {k n : ℕ} (hk : 2 ≤ k)
    (tau : ℂ) (z : Fin n → ℂ) (hz : Function.Injective z)
    (f : Fin (k + 1) → Fin n) (hf : Function.Injective f) :
    Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) = ⊤ := by
  classical
  by_contra htop
  have hlt : Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) < ⊤ :=
    lt_top_iff_ne_top.mpr htop
  obtain ⟨phi, hphi, hker⟩ :=
    (Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i)))).exists_le_ker_of_lt_top hlt
  let b : Module.Basis (Fin k) ℂ (Fin k → ℂ) := Pi.basisFun ℂ (Fin k)
  let term : Fin k → _root_.Polynomial ℂ := fun q =>
    Polynomial.C (phi (b q)) *
      if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
      else Polynomial.X ^ q.val
  let P : _root_.Polynomial ℂ := ∑ q, term q
  have hphi_clutch (w : ℂ) :
      phi (clutch k tau w) = ∑ q, clutch k tau w q * phi (b q) := by
    conv_lhs => rw [← b.sum_repr (clutch k tau w)]
    simp [b, Pi.basisFun_repr]
  have hPeval (w : ℂ) : P.eval w = phi (clutch k tau w) := by
    rw [hphi_clutch]
    change Polynomial.eval w (∑ q, term q) = _
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [term, Polynomial.eval_mul, Polynomial.eval_C]
    by_cases hq0 : q.val = 0
    · rw [if_pos hq0]
      simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [show clutch k tau w q = 1 + tau * w ^ k by simp [clutch, hq0]]
      ring
    · rw [if_neg hq0]
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      rw [show clutch k tau w q = w ^ q.val by simp [clutch, hq0]]
      ring
  have hPdeg : P.natDegree ≤ k := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q hq
    simp only [term]
    by_cases hq0 : q.val = 0
    · rw [if_pos hq0]
      calc
        (Polynomial.C (phi (b q)) *
            (1 + Polynomial.C tau * Polynomial.X ^ k)).natDegree
            ≤ (Polynomial.C (phi (b q))).natDegree +
              (1 + Polynomial.C tau * Polynomial.X ^ k).natDegree :=
                Polynomial.natDegree_mul_le
        _ ≤ 0 + k := by
          apply Nat.add_le_add
          · simp
          · apply Polynomial.natDegree_add_le_of_degree_le
            · simp
            · exact Polynomial.natDegree_mul_le.trans (by simp)
        _ = k := Nat.zero_add k
    · rw [if_neg hq0]
      calc
        (Polynomial.C (phi (b q)) * Polynomial.X ^ q.val).natDegree
            ≤ (Polynomial.C (phi (b q))).natDegree +
              (Polynomial.X ^ q.val).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + q.val := by simp
        _ ≤ k := by omega
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (hz.comp hf)
    · intro i
      rw [hPeval]
      apply LinearMap.mem_ker.mp
      apply hker
      exact Submodule.subset_span (Set.mem_range_self i)
    · simpa using Nat.lt_succ_of_le hPdeg
  apply hphi
  apply b.ext
  intro q
  have hcoeff : P.coeff q.val = phi (b q) := by
    change (∑ s, term s).coeff q.val = phi (b q)
    rw [Polynomial.finsetSum_coeff]
    calc
      ∑ s, (term s).coeff q.val = (term q).coeff q.val := by
        apply Finset.sum_eq_single q
        · intro s hs hsq
          have hsqval : s.val ≠ q.val := fun h => hsq (Fin.ext h)
          by_cases hs0 : s.val = 0
          · have hq0 : q.val ≠ 0 := fun h => hsq (Fin.ext (hs0.trans h.symm))
            have hqk : q.val ≠ k := Nat.ne_of_lt q.isLt
            change (Polynomial.C (phi (b s)) *
              (if s.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
                else Polynomial.X ^ s.val)).coeff q.val = 0
            rw [if_pos hs0, Polynomial.coeff_C_mul, Polynomial.coeff_add,
              Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow]
            simp [hq0, hqk]
          · change (Polynomial.C (phi (b s)) *
              (if s.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
                else Polynomial.X ^ s.val)).coeff q.val = 0
            rw [if_neg hs0, Polynomial.coeff_C_mul_X_pow]
            simp [Ne.symm hsqval]
        · simp
      _ = phi (b q) := by
        by_cases hq0 : q.val = 0
        · have hk0 : k ≠ 0 := by omega
          change (Polynomial.C (phi (b q)) *
            (if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
              else Polynomial.X ^ q.val)).coeff q.val = phi (b q)
          rw [if_pos hq0, Polynomial.coeff_C_mul, Polynomial.coeff_add,
            Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow]
          simp [hq0, hk0, Ne.symm hk0]
        · change (Polynomial.C (phi (b q)) *
            (if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
              else Polynomial.X ^ q.val)).coeff q.val = phi (b q)
          rw [if_neg hq0, Polynomial.coeff_C_mul_X_pow]
          simp
  rw [hPzero] at hcoeff
  simpa using hcoeff.symm

theorem proof :
  ∀ (k n : ℕ), 2 ≤ k → ∀ (tau : ℂ) (z : Fin n → ℂ),
    Function.Injective z →
      ((∀ (_hnz : ∀ i, z i ≠ 0) (f : Fin (k - 1) → Fin n),
          Function.Injective f →
            LinearIndependent ℂ (fun i => clutch k tau (z (f i)))) ∧
       (∀ (f : Fin (k + 1) → Fin n), Function.Injective f →
          Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) = ⊤)) := by
  intro k n hk tau z hz
  constructor
  · intro hnz f hf
    exact clutch_kminus1_independent hk tau z hz hnz f hf
  · intro f hf
    exact clutch_kplus1_spanning hk tau z hz f hf

end P14TrigClutchReused


/- Source: literature/TrigCurveRanks.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Real trigonometric curve `(1, Re z, Im z, Re(z²))` in complex four-space.
The pure rank argument is a fixed linear change and nonzero row scaling of
woshuajolk's clutched Vandermonde rank theorem, Jig p14 s75. -/

noncomputable section
open Matrix Complex ComplexConjugate Submodule
namespace P14TrigCurveRanks

abbrev Vec := Fin 4 → ℂ

def curve (z : ℂ) : Vec := ![1, (z.re : ℂ), (z.im : ℂ), ((z ^ 2).re : ℂ)]

def T : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 2;
     0, 1, -I, 0;
     1, 0, 0, 0;
     0, 1, I, 0]

lemma det_T : T.det = 4 * I := by
  have hm : T.submatrix Fin.succ (3 : Fin 4).succAbove =
      (!![0, 1, -I; 1, 0, 0; 0, 1, I] : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  have h0 : T 0 0 = 0 := rfl
  have h1 : T 0 1 = 0 := rfl
  have h2 : T 0 2 = 0 := rfl
  have h3 : T 0 3 = 2 := rfl
  rw [h0, h1, h2, h3]
  simp only [mul_zero, zero_mul, zero_add, hm]
  norm_num [Matrix.det_fin_three]
  change -(2 * (-I + 0 * 0 + (-I) * 1)) = 4 * I
  ring

lemma det_T_ne_zero : T.det ≠ 0 := by
  rw [det_T]
  exact mul_ne_zero (by norm_num) I_ne_zero

lemma T_injective : Function.Injective T.mulVec :=
  Matrix.mulVec_injective_iff_isUnit.mpr
    (T.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr det_T_ne_zero))

lemma T_surjective : Function.Surjective T.mulVec :=
  Matrix.mulVec_surjective_iff_isUnit.mpr
    (T.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr det_T_ne_zero))

lemma curve_nonzero (z : ℂ) : curve z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [curve] at h0

lemma curve_real (z : ℂ) : star (curve z) = curve z := by
  ext i
  fin_cases i <;> simp [curve]

lemma curve_injective : Function.Injective curve := by
  intro z w h
  have hr := congrFun h 1
  have hi := congrFun h 2
  change (z.re : ℂ) = (w.re : ℂ) at hr
  change (z.im : ℂ) = (w.im : ℂ) at hi
  apply Complex.ext
  · exact_mod_cast hr
  · exact_mod_cast hi

lemma projective_injective (z w c : ℂ) (h : c • curve z = curve w) : c = 1 ∧ z = w := by
  have hc := congrFun h 0
  have hc1 : c = 1 := by simpa [curve] using hc
  refine ⟨hc1, curve_injective ?_⟩
  simpa [hc1] using h

lemma unit_mul_conj {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

lemma unit_nonzero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

lemma re_sub_I_im (z : ℂ) : (z.re : ℂ) - I * z.im = conj z := by
  apply Complex.ext <;> simp

lemma double_re (z : ℂ) : 2 * (z.re : ℂ) = z + conj z := by
  apply Complex.ext <;> simp
  ring

lemma T_curve (z : ℂ) : T.mulVec (curve z) = ![z ^ 2 + (conj z) ^ 2, conj z, 1, z] := by
  ext i
  fin_cases i <;> simp [T, curve, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · have hp : conj (z ^ 2) = (conj z) ^ 2 := (starRingEnd ℂ).map_pow z 2
    exact (double_re (z ^ 2)).trans (congrArg (fun w => z ^ 2 + w) hp)
  · simpa only [sub_eq_add_neg, neg_mul] using re_sub_I_im z
  · simpa only [mul_comm] using Complex.re_add_im z

lemma clutch_relation {z : ℂ} (hz : ‖z‖ = 1) :
    z ^ 2 • T.mulVec (curve z) = P14TrigClutchReused.clutch 4 1 z := by
  have hu := unit_mul_conj hz
  rw [T_curve]
  ext i
  fin_cases i <;> simp [P14TrigClutchReused.clutch, Pi.smul_apply, smul_eq_mul]
  · calc
      z ^ 2 * (z ^ 2 + conj z ^ 2) = z ^ 4 + (z * conj z) ^ 2 := by ring
      _ = 1 + z ^ 4 := by rw [hu]; ring
  · calc
      z ^ 2 * conj z = z * (z * conj z) := by ring
      _ = z := by rw [hu]; ring
  · ring

/-- Every three distinct unit-circle nodes give independent trigonometric rows. -/
theorem three_independent {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) (hunit : ∀ i, ‖z i‖ = 1)
    (f : Fin 3 → Fin n) (hf : Function.Injective f) :
    LinearIndependent ℂ (fun i => curve (z (f i))) := by
  have hc := P14TrigClutchReused.clutch_kminus1_independent (k := 4) (by decide)
    1 z hz (fun i => unit_nonzero (hunit i)) f hf
  let w : Fin 3 → ℂˣ := fun i => Units.mk0 (z (f i) ^ 2)
    (pow_ne_zero 2 (unit_nonzero (hunit (f i))))
  have hrel : (fun i => P14TrigClutchReused.clutch 4 1 (z (f i))) =
      w • (fun i => T.mulVec (curve (z (f i)))) := by
    funext i
    exact (clutch_relation (hunit (f i))).symm
  rw [hrel] at hc
  apply LinearIndependent.of_comp T.mulVecLin
  exact (LinearIndependent.units_smul_iff _ w).mp hc

/-- Every five distinct unit-circle nodes span complex four-space. -/
theorem five_spanning {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) (hunit : ∀ i, ‖z i‖ = 1)
    (f : Fin 5 → Fin n) (hf : Function.Injective f) :
    span ℂ (Set.range fun i => curve (z (f i))) = ⊤ := by
  have hc := P14TrigClutchReused.clutch_kplus1_spanning (k := 4) (by decide) 1 z hz f hf
  apply Submodule.map_injective_of_injective (f := T.mulVecLin) T_injective
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr T_surjective]
  apply top_unique
  rw [← hc]
  apply span_le.mpr
  rintro v ⟨i, rfl⟩
  dsimp only
  rw [← clutch_relation (hunit (f i))]
  apply Submodule.smul_mem
  exact Submodule.mem_map_of_mem (subset_span (Set.mem_range_self i))

/-- Selection form for any index type, without a finiteness requirement on the ambient family. -/
theorem three_independent_any {ι : Type*} (z : ι → ℂ)
    (hz : Function.Injective z) (hunit : ∀ i, ‖z i‖ = 1)
    (f : Fin 3 → ι) (hf : Function.Injective f) :
    LinearIndependent ℂ (fun i => curve (z (f i))) := by
  exact three_independent (z ∘ f) (hz.comp hf) (fun i => hunit (f i)) id Function.injective_id

theorem five_spanning_any {ι : Type*} (z : ι → ℂ)
    (hz : Function.Injective z) (hunit : ∀ i, ‖z i‖ = 1)
    (f : Fin 5 → ι) (hf : Function.Injective f) :
    span ℂ (Set.range fun i => curve (z (f i))) = ⊤ := by
  exact five_spanning (z ∘ f) (hz.comp hf) (fun i => hunit (f i)) id Function.injective_id

end P14TrigCurveRanks
end


/- Source: literature/OddTrigSigns.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
namespace P14OddTrig

open Real

def alpha (N : ℕ) : ℝ := 2 * π / (2 * N + 1)

lemma alpha_range {N : ℕ} (hN : 3 ≤ N) : 0 < alpha N ∧ alpha N < π / 3 := by
  have hn : (0 : ℝ) < 2 * N + 1 := by positivity
  constructor
  · exact div_pos (by positivity) hn
  · rw [alpha, div_lt_div_iff₀ hn (by norm_num : (0 : ℝ) < 3)]
    have hNc : (3 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [pi_pos]

lemma parameter_signs {u : ℝ} (hu : 0 < u) (hup : u < π / 3) :
    1 / 2 < cos u ∧ cos u < 1 ∧ cos (2 * u) < cos u ∧ 0 < cos u + cos (2 * u) := by
  have hp := pi_pos
  have hhalf : 1 / 2 < cos u := by
    have h := cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hu) (show π/3 ≤ π by linarith) hup
    simpa only [cos_pi_div_three] using h
  have hlt : cos u < 1 := by
    have h := cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num)
      (show u ≤ π by linarith) hu
    simpa only [cos_zero] using h
  have hba : cos (2*u) < cos u :=
    cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hu) (by linarith) (by linarith)
  have hb : -(1/2 : ℝ) < cos (2*u) := by
    have h := cos_lt_cos_of_nonneg_of_le_pi (show 0 ≤ 2*u by linarith)
      (show π-π/3 ≤ π by linarith) (show 2*u < π-π/3 by linarith)
    simpa only [cos_pi_sub, cos_pi_div_three] using h
  exact ⟨hhalf, hlt, hba, by linarith⟩

lemma grid_parameter_signs {N : ℕ} (hN : 3 ≤ N) :
    1 / 2 < cos (alpha N) ∧ cos (alpha N) < 1 ∧
    cos (2 * alpha N) < cos (alpha N) ∧ 0 < cos (alpha N) + cos (2 * alpha N) :=
  parameter_signs (alpha_range hN).1 (alpha_range hN).2

lemma half_square (u : ℝ) : cos (u/2)^2 = (cos u + 1)/2 := by
  have h := cos_two_mul (u/2)
  rw [show 2*(u/2)=u by ring] at h
  linarith

lemma triple_half (u : ℝ) : cos (3*u/2) = cos (u/2)*(2*cos u-1) := by
  have h := cos_three_mul (u/2)
  rw [show 3*(u/2)=3*u/2 by ring] at h
  have hc := half_square u
  rw [h, pow_succ, hc]
  ring

lemma triple_cos (u : ℝ) : cos (3*u) = 2*cos u*cos (2*u)-cos u := by
  rw [cos_three_mul, cos_two_mul]
  ring

lemma half_sine_square (u : ℝ) : sin (u/2)^2 = (1-cos u)/2 := by
  have h := cos_two_mul_eq_one_sub (u/2)
  rw [show 2*(u/2)=u by ring] at h
  linarith

lemma half_sine_product (u : ℝ) : sin (u/2)*sin (3*u/2) = (cos u-cos (2*u))/2 := by
  have h := two_mul_sin_mul_sin (u/2) (3*u/2)
  rw [show u/2-3*u/2 = -u by ring, show u/2+3*u/2=2*u by ring, cos_neg] at h
  linarith

lemma half_cos_positive {u : ℝ} (hu : 0 < u) (hup : u < π / 3) :
    0 < cos (u/2) ∧ 0 < cos (3*u/2) ∧ 0 < sin (u/2) ∧ 0 < sin (3*u/2) := by
  have hp := pi_pos
  exact ⟨cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩,
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩,
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)⟩

lemma triple_cos_lt_double {u : ℝ} (hu : 0 < u) (hup : u < Real.pi / 3) :
    Real.cos (3*u) < Real.cos (2*u) :=
  Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

lemma repair_sine_norm (u : ℝ) :
    4*(Real.cos u-Real.cos (2*u))*Real.sin (u/2)^2 =
      2*(1-Real.cos u)*(Real.cos u-Real.cos (2*u)) := by
  rw [half_sine_square]
  ring

lemma repair_sine_product (u : ℝ) :
    4*(Real.cos u-Real.cos (2*u))*Real.sin (u/2)*Real.sin (3*u/2) =
      2*(Real.cos u-Real.cos (2*u))^2 := by
  rw [mul_assoc, half_sine_product]
  ring

end P14OddTrig
end


/- Source: literature/OddTrigGrid.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
open ComplexConjugate
namespace P14OddTrig

abbrev Index (N : ℕ) := Fin (2 * N + 1)
abbrev Cyclic (N : ℕ) := ZMod (2 * N + 1)

instance odd_neZero (N : ℕ) : NeZero (2 * N + 1) := ⟨by omega⟩

/-- Shifted indexing: the zero angle is at index 1. -/
def angle {N : ℕ} (i : Index N) : ℝ := ((i.val : ℝ) - 1) * alpha N

def node {N : ℕ} (i : Index N) : ℂ := ZMod.stdAddChar ((i.val : Cyclic N) - 1)

lemma node_injective (N : ℕ) : Function.Injective (node (N := N)) := by
  intro i j h
  have he := ZMod.injective_stdAddChar h
  have hi : (i.val : Cyclic N) = j.val := by linear_combination he
  have hv := congrArg ZMod.val hi
  apply Fin.ext
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hv

lemma node_unit {N : ℕ} (i : Index N) : ‖node i‖ = 1 :=
  Circle.norm_coe (ZMod.toCircle ((i.val : Cyclic N) - 1))

lemma node_exp {N : ℕ} (i : Index N) : node i = Complex.exp ((angle i : ℂ) * Complex.I) := by
  have he : (i.val : Cyclic N) - 1 = (((i.val : ℤ) - 1 : ℤ) : Cyclic N) := by push_cast; rfl
  rw [node, he, ZMod.stdAddChar_coe]
  congr 1
  simp only [angle, alpha]
  push_cast
  ring

lemma node_re {N : ℕ} (i : Index N) : (node i).re = Real.cos (angle i) := by
  rw [node_exp]
  simp [Complex.exp_re]

lemma node_im {N : ℕ} (i : Index N) : (node i).im = Real.sin (angle i) := by
  rw [node_exp]
  simp [Complex.exp_im]

lemma curve_trig {N : ℕ} (i : Index N) :
    P14TrigCurveRanks.curve (node i) =
      ![1, (Real.cos (angle i) : ℂ), (Real.sin (angle i) : ℂ),
        (Real.cos (2 * angle i) : ℂ)] := by
  ext q
  fin_cases q <;> simp [P14TrigCurveRanks.curve, node_re, node_im, pow_two,
    Complex.mul_re, Real.cos_two_mul']

lemma char_conj {N : ℕ} (x : Cyclic N) :
    ZMod.stdAddChar (-x) = conj (ZMod.stdAddChar x) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
  simpa only [Circle.coe_inv] using Circle.coe_inv_eq_conj (ZMod.toCircle x)

lemma unit_re_eq_iff {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    z.re = w.re ↔ z = w ∨ z = conj w := by
  constructor
  · intro hr
    have hzn : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq z
      rw [hz] at h
      simpa only [Complex.normSq_apply, sq, one_mul] using h
    have hwn : w.re ^ 2 + w.im ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq w
      rw [hw] at h
      simpa only [Complex.normSq_apply, sq, one_mul] using h
    have hs : z.im ^ 2 = w.im ^ 2 := by
      rw [hr] at hzn
      linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hi | hi
    · exact Or.inl (Complex.ext hr hi)
    · exact Or.inr (Complex.ext (by simpa using hr) (by simpa using hi))
  · rintro (h | h)
    · exact congrArg Complex.re h
    · simpa using congrArg Complex.re h

lemma node_conj_iff {N : ℕ} (i j : Index N) :
    node i = conj (node j) ↔ (i.val : Cyclic N) + j.val = 2 := by
  change ZMod.stdAddChar ((i.val : Cyclic N) - 1) =
    conj (ZMod.stdAddChar ((j.val : Cyclic N) - 1)) ↔ _
  rw [← char_conj, ZMod.injective_stdAddChar.eq_iff]
  constructor <;> intro h <;> linear_combination h

lemma node_re_eq_iff {N : ℕ} (i j : Index N) :
    (node i).re = (node j).re ↔ i = j ∨ (i.val : Cyclic N) + j.val = 2 := by
  rw [unit_re_eq_iff (node_unit i) (node_unit j), (node_injective N).eq_iff, node_conj_iff]

lemma double_inverse (N : ℕ) : (2 : Cyclic N) * (N + 1) = 1 := by
  have h := ZMod.natCast_self (2 * N + 1)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  linear_combination h

lemma sine_zero_iff {N : ℕ} (hN : 3 ≤ N) (i : Index N) :
    Real.sin (angle i) = 0 ↔ i.val = 1 := by
  rw [← node_im]
  constructor
  · intro hsin
    have hc : node i = conj (node i) := by
      apply Complex.ext <;> simp [hsin]
    have hd := (node_conj_iff i i).mp hc
    have hd' : 2 * (i.val : Cyclic N) = 2 := by linear_combination hd
    have hmul := congrArg (fun x : Cyclic N => (N + 1) * x) hd'
    have hh : ((N : Cyclic N) + 1) * 2 = 1 := by simpa [mul_comm] using double_inverse N
    simp only [← mul_assoc, hh, one_mul] at hmul
    have hv := congrArg ZMod.val hmul
    have hcast : (1 : Cyclic N) = ((1 : ℕ) : Cyclic N) := by norm_num
    rw [hcast, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt (by omega : 1 < 2 * N + 1)] at hv
    exact hv
  · intro hi
    simp [node, hi]

lemma cast_sum_two_iff {N : ℕ} (i j : Index N) (hj : 2 < j.val) :
    (i.val : Cyclic N) + j.val = 2 ↔ i.val + j.val = 2 * N + 3 := by
  have hi := i.isLt
  have hjb := j.isLt
  have hn : 2 < 2 * N + 1 := by omega
  constructor
  · intro h
    have hc : (((i.val + j.val : ℕ) : Cyclic N)) = ((2 : ℕ) : Cyclic N) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using h
    have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
    change (i.val + j.val) % (2 * N + 1) = 2 % (2 * N + 1) at hm
    rw [Nat.mod_eq_of_lt hn] at hm
    by_cases hs : i.val + j.val < 2 * N + 1
    · rw [Nat.mod_eq_of_lt hs] at hm
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : 2 * N + 1 ≤ i.val + j.val),
        Nat.mod_eq_of_lt (by omega : i.val + j.val - (2 * N + 1) < 2 * N + 1)] at hm
      omega
  · intro h
    rw [← Nat.cast_add, h, show 2*N+3=(2*N+1)+2 by omega, Nat.cast_add,
      ZMod.natCast_self]
    norm_num

lemma angle_pminus {N : ℕ} (i : Index N) (hi : i.val = N) :
    angle i = Real.pi - 3 * alpha N / 2 := by
  have hn : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
  simp only [angle, hi, alpha]
  field_simp
  ring

lemma angle_qminus {N : ℕ} (i : Index N) (hi : i.val = N + 1) :
    angle i = Real.pi - alpha N / 2 := by
  have hn : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
  simp only [angle, hi, alpha]
  push_cast
  field_simp
  ring

lemma angle_qplus {N : ℕ} (i : Index N) (hi : i.val = N + 2) :
    angle i = Real.pi + alpha N / 2 := by
  have hn : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
  simp only [angle, hi, alpha]
  push_cast
  field_simp
  ring

lemma angle_pplus {N : ℕ} (i : Index N) (hi : i.val = N + 3) :
    angle i = Real.pi + 3 * alpha N / 2 := by
  have hn : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
  simp only [angle, hi, alpha]
  push_cast
  field_simp
  ring

lemma cosine_half_iff {N : ℕ} (hN : 3 ≤ N) (i : Index N) :
    Real.cos (angle i) = -Real.cos (alpha N / 2) ↔
      i.val = N + 1 ∨ i.val = N + 2 := by
  let j : Index N := ⟨N + 1, by omega⟩
  have hj : 2 < j.val := by dsimp [j]; omega
  have hangle : Real.cos (angle j) = -Real.cos (alpha N / 2) := by
    rw [angle_qminus j rfl, Real.cos_pi_sub]
  rw [← hangle, ← node_re i, ← node_re j, node_re_eq_iff, cast_sum_two_iff i j hj]
  simp only [Fin.ext_iff]
  dsimp [j]
  omega

lemma cosine_three_half_iff {N : ℕ} (hN : 3 ≤ N) (i : Index N) :
    Real.cos (angle i) = -Real.cos (3 * alpha N / 2) ↔
      i.val = N ∨ i.val = N + 3 := by
  let j : Index N := ⟨N, by omega⟩
  have hj : 2 < j.val := by dsimp [j]; omega
  have hangle : Real.cos (angle j) = -Real.cos (3 * alpha N / 2) := by
    rw [angle_pminus j rfl, Real.cos_pi_sub]
  rw [← hangle, ← node_re i, ← node_re j, node_re_eq_iff, cast_sum_two_iff i j hj]
  simp only [Fin.ext_iff]
  dsimp [j]
  omega

lemma cosine_defects_iff {N : ℕ} (hN : 3 ≤ N) (i : Index N) :
    (Real.cos (angle i) = -Real.cos (alpha N / 2) ∨
      Real.cos (angle i) = -Real.cos (3 * alpha N / 2)) ↔
      i.val = N ∨ i.val = N + 1 ∨ i.val = N + 2 ∨ i.val = N + 3 := by
  rw [cosine_half_iff hN, cosine_three_half_iff hN]
  tauto

end P14OddTrig
end


/- Source: literature/OddTrigKernel.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
open ComplexConjugate
namespace P14OddTrig

lemma char_unit {N : ℕ} (x : Cyclic N) : ‖ZMod.stdAddChar x‖ = 1 :=
  Circle.norm_coe (ZMod.toCircle x)

lemma char_re_eq_iff {N : ℕ} (x y : Cyclic N) :
    (ZMod.stdAddChar x).re = (ZMod.stdAddChar y).re ↔ x = y ∨ x = -y := by
  rw [unit_re_eq_iff (char_unit x) (char_unit y), ← char_conj,
    ZMod.injective_stdAddChar.eq_iff, ZMod.injective_stdAddChar.eq_iff]

lemma char_int_exp {N : ℕ} (m : ℤ) :
    ZMod.stdAddChar (m : Cyclic N) = Complex.exp (((m : ℝ) * alpha N : ℝ) * Complex.I) := by
  rw [ZMod.stdAddChar_coe]
  congr 1
  simp only [alpha]
  push_cast
  ring

lemma char_int_re {N : ℕ} (m : ℤ) :
    (ZMod.stdAddChar (m : Cyclic N)).re = Real.cos ((m : ℝ) * alpha N) := by
  rw [char_int_exp]
  simp [Complex.exp_re]

lemma cos_int_eq_iff {N : ℕ} (m l : ℤ) :
    Real.cos ((m : ℝ) * alpha N) = Real.cos ((l : ℝ) * alpha N) ↔
      (m : Cyclic N) = l ∨ (m : Cyclic N) = -(l : Cyclic N) := by
  rw [← char_int_re, ← char_int_re, char_re_eq_iff]

lemma cosine_difference_iff {N : ℕ} (i j : Index N) :
    Real.cos (angle j - angle i) = Real.cos (alpha N) ↔
      (j.val : Cyclic N) = i.val + 1 ∨ (j.val : Cyclic N) = i.val - 1 := by
  have h := cos_int_eq_iff (N := N) ((j.val : ℤ) - i.val) 1
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, one_mul] at h
  have he : ((j.val : ℝ) - i.val) * alpha N = angle j - angle i := by
    simp only [angle]
    ring
  rw [he] at h
  constructor
  · intro hc
    rcases h.mp hc with hp | hm
    · exact Or.inl (by linear_combination hp)
    · exact Or.inr (by linear_combination hm)
  · rintro (hp | hm)
    · exact h.mpr (Or.inl (by linear_combination hp))
    · exact h.mpr (Or.inr (by linear_combination hm))

lemma cosine_sum_iff {N : ℕ} (i j : Index N) :
    Real.cos (angle j + angle i) = Real.cos (2 * alpha N) ↔
      (j.val : Cyclic N) = -(i.val : Cyclic N) ∨
      (j.val : Cyclic N) = -(i.val : Cyclic N) + 4 := by
  have h := cos_int_eq_iff (N := N) ((i.val : ℤ) + j.val - 2) 2
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_ofNat] at h
  have he : ((i.val : ℝ) + j.val - 2) * alpha N = angle j + angle i := by
    simp only [angle]
    ring
  rw [he] at h
  constructor
  · intro hc
    rcases h.mp hc with hp | hm
    · exact Or.inr (by linear_combination hp)
    · exact Or.inl (by linear_combination hm)
  · rintro (hm | hp)
    · exact h.mpr (Or.inr (by linear_combination hm))
    · exact h.mpr (Or.inl (by linear_combination hp))

/-- Exact normalized cross-zero graph on two copies of the same shifted odd grid. -/
theorem kernel_zero_iff {N : ℕ} (i j : Index N) :
    4 * (Real.cos (angle j - angle i) - Real.cos (alpha N)) *
      (Real.cos (angle j + angle i) - Real.cos (2 * alpha N)) = 0 ↔
      (j.val : Cyclic N) = i.val + 1 ∨ (j.val : Cyclic N) = i.val - 1 ∨
      (j.val : Cyclic N) = -(i.val : Cyclic N) ∨
      (j.val : Cyclic N) = -(i.val : Cyclic N) + 4 := by
  rw [mul_eq_zero, mul_eq_zero]
  simp only [show (4 : ℝ) ≠ 0 by norm_num, false_or, sub_eq_zero,
    cosine_difference_iff, cosine_sum_iff]
  tauto

/-- The factor defining the third Lorentz coordinate vanishes at precisely four nodes. -/
theorem cosine_factor_zero_iff {N : ℕ} (hN : 3 ≤ N) (i : Index N) :
    (Real.cos (angle i) + Real.cos (alpha N / 2)) *
      (Real.cos (angle i) + Real.cos (3 * alpha N / 2)) = 0 ↔
      i.val = N ∨ i.val = N + 1 ∨ i.val = N + 2 ∨ i.val = N + 3 := by
  rw [mul_eq_zero, add_eq_zero_iff_eq_neg, add_eq_zero_iff_eq_neg]
  exact cosine_defects_iff hN i

lemma sine_zero_not_defect {N : ℕ} (hN : 3 ≤ N) (i : Index N)
    (hs : Real.sin (angle i) = 0) :
    (Real.cos (angle i) + Real.cos (alpha N / 2)) *
      (Real.cos (angle i) + Real.cos (3 * alpha N / 2)) ≠ 0 := by
  rw [sine_zero_iff hN] at hs
  rw [ne_eq, cosine_factor_zero_iff hN]
  omega

/-- Scalar form of the symmetric cusp matrix identity, valid for arbitrary real parameters. -/
theorem symmetric_kernel (a b u v : ℝ) :
    4*a*b - 4*(a+b)*Real.cos u*Real.cos v +
      4*(a-b)*Real.sin u*Real.sin v + 2*Real.cos (2*u) + 2*Real.cos (2*v) =
      4*(Real.cos (v-u)-a)*(Real.cos (v+u)-b) := by
  have hu : Real.sin u ^ 2 = 1 - Real.cos u ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq u]
  have hv : Real.sin v ^ 2 = 1 - Real.cos v ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq v]
  have hp : (Real.cos u * Real.cos v)^2 - (Real.sin u * Real.sin v)^2 =
      (Real.cos (2*u)+Real.cos (2*v))/2 := by
    rw [mul_pow, mul_pow, hu, hv, Real.cos_two_mul, Real.cos_two_mul]
    ring
  rw [Real.cos_sub, Real.cos_add]
  linear_combination -4*hp

end P14OddTrig
end


/- Source: literature/OddPlaneIncidence.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
open scoped BigOperators Classical
open P14OddTrig
namespace P14OddPlaneIncidence

abbrev Vec := Fin 4 → ℝ

def realCurve {N : ℕ} (i : Index N) : Vec :=
  ![1, Real.cos (angle i), Real.sin (angle i), Real.cos (2 * angle i)]

def kernelValue {N : ℕ} (i j : Index N) : ℝ :=
  4 * (Real.cos (angle j - angle i) - Real.cos (alpha N)) *
    (Real.cos (angle j + angle i) - Real.cos (2 * alpha N))

def cuspFunctional {N : ℕ} (j : Index N) : Vec →ₗ[ℝ] ℝ where
  toFun w := (4*Real.cos (alpha N)*Real.cos (2*alpha N)+2*Real.cos (2*angle j))*w 0
    - 4*(Real.cos (alpha N)+Real.cos (2*alpha N))*Real.cos (angle j)*w 1
    + 4*(Real.cos (alpha N)-Real.cos (2*alpha N))*Real.sin (angle j)*w 2 + 2*w 3
  map_add' w v := by simp only [Pi.add_apply]; ring
  map_smul' c w := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def cuspPlane {N : ℕ} (j : Index N) : Submodule ℝ Vec := (cuspFunctional j).ker

def sineFunctional : Vec →ₗ[ℝ] ℝ := LinearMap.proj 2

def sinePlane : Submodule ℝ Vec := sineFunctional.ker

lemma cusp_on_curve {N : ℕ} (i j : Index N) :
    cuspFunctional j (realCurve i) = kernelValue i j := by
  have h := symmetric_kernel (Real.cos (alpha N)) (Real.cos (2*alpha N)) (angle i) (angle j)
  dsimp [cuspFunctional, realCurve, kernelValue]
  convert h using 1; ring

lemma sine_on_curve {N : ℕ} (i : Index N) : sineFunctional (realCurve i) = Real.sin (angle i) := rfl

def coord (N : ℕ) : Index N ≃ Cyclic N where
  toFun i := (i.val : Cyclic N)
  invFun x := ⟨x.val, ZMod.val_lt x⟩
  left_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv x := ZMod.natCast_zmod_val x

def defectIndex (N : ℕ) (t : Fin 4) : Index N := (coord N).symm (P14OddGraph.defect N t)

lemma defectIndex_val {N : ℕ} (hN : 3 ≤ N) (t : Fin 4) :
    (defectIndex N t).val = N + t.val := by
  change (P14OddGraph.defect N t).val = N + t.val
  rw [P14OddGraph.defect, ← Nat.cast_add, ZMod.val_natCast_of_lt (by omega)]

lemma kernel_mem_cross {N : ℕ} (i j : Index N) :
    kernelValue i j = 0 ↔ coord N i ∈ P14OddGraph.cross N (coord N j) := by
  rw [← P14OddGraph.cross_symm N (coord N i) (coord N j)]
  rw [kernelValue, kernel_zero_iff]
  simp only [P14OddGraph.cross, Finset.mem_insert, Finset.mem_singleton]
  change (_ ∨ _ ∨ _ ∨ _) ↔
    ((j.val : Cyclic N) = i.val - 1 ∨ (j.val : Cyclic N) = i.val + 1 ∨
      (j.val : Cyclic N) = -(i.val : Cyclic N) ∨ (j.val : Cyclic N) = -(i.val : Cyclic N) + 4)
  tauto

lemma mem_cuspPlane_curve {N : ℕ} (i j : Index N) :
    realCurve i ∈ cuspPlane j ↔ coord N i ∈ P14OddGraph.cross N (coord N j) := by
  change cuspFunctional j (realCurve i) = 0 ↔ _
  rw [cusp_on_curve, kernel_mem_cross]

lemma mem_sinePlane_curve {N : ℕ} (hN : 3 ≤ N) (i : Index N) :
    realCurve i ∈ sinePlane ↔ i.val = 1 := by
  change sineFunctional (realCurve i) = 0 ↔ _
  rw [sine_on_curve, sine_zero_iff hN]

/-- Exact incidence count for each of the four repaired kernel hyperplanes. -/
theorem cusp_incidence_card {N : ℕ} (hN : 3 ≤ N) (t : Fin 4) :
    (Finset.univ.filter (fun i : Index N =>
      realCurve i ∈ cuspPlane (defectIndex N t))).card = 3 := by
  classical
  have he : (Finset.univ.filter (fun i : Index N =>
      realCurve i ∈ cuspPlane (defectIndex N t))) =
      (P14OddGraph.cross N (P14OddGraph.defect N t)).map (coord N).symm.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_cuspPlane_curve,
      Finset.mem_map_equiv, Equiv.symm_symm, defectIndex, Equiv.apply_symm_apply]
  rw [he, Finset.card_map, P14OddGraph.cross_card N hN]
  exact if_pos ⟨t, rfl⟩

/-- The fifth exceptional hyperplane contains only the zero-angle pure point. -/
theorem sine_incidence_card {N : ℕ} (hN : 3 ≤ N) :
    (Finset.univ.filter (fun i : Index N => realCurve i ∈ sinePlane)).card = 1 := by
  classical
  have he : (Finset.univ.filter (fun i : Index N => realCurve i ∈ sinePlane)) =
      {⟨1, by omega⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_sinePlane_curve hN,
      Finset.mem_singleton, Fin.ext_iff]
  rw [he, Finset.card_singleton]

lemma no_four_of_incidence {N : ℕ} (S : Submodule ℝ Vec)
    (hcard : (Finset.univ.filter (fun i : Index N => realCurve i ∈ S)).card < 4)
    (f : Fin 4 → Index N) (hf : Function.Injective f) :
    ¬ ∀ q, realCurve (f q) ∈ S := by
  classical
  intro h
  have hs : Finset.univ.image f ⊆ Finset.univ.filter (fun i : Index N => realCurve i ∈ S) := by
    intro i hi
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h q⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hc
  omega

theorem cusp_no_four {N : ℕ} (hN : 3 ≤ N) (t : Fin 4)
    (f : Fin 4 → Index N) (hf : Function.Injective f) :
    ¬ ∀ q, realCurve (f q) ∈ cuspPlane (defectIndex N t) := by
  apply no_four_of_incidence _ _ f hf
  rw [cusp_incidence_card hN t]
  omega

theorem sine_no_four {N : ℕ} (hN : 3 ≤ N)
    (f : Fin 4 → Index N) (hf : Function.Injective f) :
    ¬ ∀ q, realCurve (f q) ∈ sinePlane := by
  apply no_four_of_incidence _ _ f hf
  rw [sine_incidence_card hN]
  omega

/-- A common nonzero normalization recovers a functional from its kernel. -/
lemma functional_eq_of_ker_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : V →ₗ[ℝ] ℝ) (e : V) (c : ℝ) (hc : c ≠ 0)
    (hf : f e = c) (hg : g e = c) (hker : f.ker = g.ker) : f = g := by
  ext w
  have hm : w - (f w / c) • e ∈ f.ker := by
    change f (w - (f w / c) • e) = 0
    simp [map_sub, map_smul, hf, hc]
  rw [hker] at hm
  change g (w - (f w / c) • e) = 0 at hm
  simp [map_sub, map_smul, hg, hc] at hm
  linarith

lemma cusp_normalized {N : ℕ} (j : Index N) :
    cuspFunctional j ![0,0,0,1] = 2 := by
  simp [cuspFunctional]

/-- All grid kernel hyperplanes are distinct, not merely the four defect planes. -/
theorem cuspPlane_injective {N : ℕ} (hN : 3 ≤ N) :
    Function.Injective (@cuspPlane N) := by
  intro i j hij
  have hfg : cuspFunctional i = cuspFunctional j :=
    functional_eq_of_ker_eq _ _ ![0,0,0,1] 2 (by norm_num)
      (cusp_normalized i) (cusp_normalized j) hij
  have hc := congrArg (fun f : Vec →ₗ[ℝ] ℝ => f ![0,1,0,0]) hfg
  have hs := congrArg (fun f : Vec →ₗ[ℝ] ℝ => f ![0,0,1,0]) hfg
  simp only [cuspFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
    mul_zero, mul_one, zero_sub, add_zero] at hc hs
  obtain ⟨_, _, hba, hab⟩ := grid_parameter_signs hN
  have hcos : Real.cos (angle i) = Real.cos (angle j) := by
    nlinarith
  have hsin : Real.sin (angle i) = Real.sin (angle j) := by
    nlinarith
  apply node_injective N
  apply Complex.ext
  · simpa only [node_re] using hcos
  · simpa only [node_im] using hsin

theorem sinePlane_ne_cuspPlane {N : ℕ} (j : Index N) :
    sinePlane ≠ cuspPlane j := by
  intro h
  have hm : ![0,0,0,1] ∈ sinePlane := by
    change sineFunctional ![0,0,0,1] = 0
    rfl
  rw [h] at hm
  change cuspFunctional j ![0,0,0,1] = 0 at hm
  rw [cusp_normalized] at hm
  norm_num at hm

lemma defectIndex_injective {N : ℕ} (hN : 3 ≤ N) :
    Function.Injective (defectIndex N) :=
  (coord N).symm.injective.comp (P14OddGraph.defect_injective N hN)

/-- The five exceptional planes form an injective family. -/
def exceptionalPlane {N : ℕ} : Option (Fin 4) → Submodule ℝ Vec
  | none => sinePlane
  | some t => cuspPlane (defectIndex N t)

theorem exceptionalPlane_injective {N : ℕ} (hN : 3 ≤ N) :
    Function.Injective (@exceptionalPlane N) := by
  intro i j heq
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact False.elim (sinePlane_ne_cuspPlane _ heq)
  | some i =>
    cases j with
    | none => exact False.elim (sinePlane_ne_cuspPlane _ heq.symm)
    | some j =>
      congr 1
      exact defectIndex_injective hN (cuspPlane_injective hN heq)

theorem exceptional_no_four {N : ℕ} (hN : 3 ≤ N) (t : Option (Fin 4))
    (f : Fin 4 → Index N) (hf : Function.Injective f) :
    ¬ ∀ q, realCurve (f q) ∈ exceptionalPlane (N := N) t := by
  cases t with
  | none => exact sine_no_four hN f hf
  | some t => exact cusp_no_four hN t f hf

end P14OddPlaneIncidence
end


/- Source: elliptic_audit/LorentzFrame.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Explicit normalization of one timelike and two spacelike vectors.
This supplies the coordinate equivalence needed to transfer the repaired
cusp kernel to the standard Lorentz metric. -/

namespace P14LorentzFrame

noncomputable section
open LinearMap LinearMap.BilinForm

abbrev Vec := Fin 3 → ℝ

def frame (p q h : Vec) (rQ t s rL : ℝ) : Fin 3 → Vec :=
  ![rQ⁻¹ • q, s⁻¹ • (p-t • (rQ⁻¹ • q)), rL⁻¹ • h]

theorem frame_gram (B : LinearMap.BilinForm ℝ Vec) (p q h : Vec) (rQ t s rL : ℝ)
    (hsym : ∀ v w, B v w=B w v) (hQ : rQ≠0) (hs : s≠0) (hL : rL≠0)
    (hqq : B q q=rQ^2) (hpq : B p q=t*rQ) (hpp : B p p=t^2-s^2)
    (hhq : B h q=0) (hhp : B h p=0) (hhh : B h h= -rL^2) :
    ∀ i j, B (frame p q h rQ t s rL i) (frame p q h rQ t s rL j) =
      if i=j then (if i=0 then 1 else -1) else 0 := by
  have hqp : B q p=t*rQ := (hsym q p).trans hpq
  have hqh : B q h=0 := (hsym q h).trans hhq
  have hph : B p h=0 := (hsym p h).trans hhp
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, sub_right,
      hqq, hpq, hqp, hpp, hhq, hqh, hhp, hph, hhh] <;>
    field_simp <;> ring_nf <;> simp

theorem coordinates_of_frame (B : LinearMap.BilinForm ℝ Vec) (F : Fin 3 → Vec)
    (hF : ∀ i j, B (F i) (F j) = if i=j then (if i=0 then 1 else -1) else 0) :
    ∃ U : Vec ≃ₗ[ℝ] Vec,
      (∀ i j, U (F i) j = if i=j then 1 else 0) ∧
      (∀ v w, B v w = U v 0*U w 0-U v 1*U w 1-U v 2*U w 2) := by
  classical
  have hli : LinearIndependent ℝ F := by
    apply linearIndependent_of_iIsOrtho (B := B)
    · intro i j hij
      change B (F i) (F j)=0
      rw [hF, if_neg hij]
    · intro i
      rw [hF, if_pos rfl]
      split <;> norm_num
  let b : Module.Basis (Fin 3) ℝ Vec :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [Vec])
  have hb : ∀ i, b i=F i := by
    intro i
    simp [b]
  refine ⟨b.equivFun, ?_, ?_⟩
  · intro i j
    rw [← hb i]
    exact b.equivFun_self i j
  · intro v w
    calc
      B v w = B (∑ i, b.equivFun v i • F i) (∑ j, b.equivFun w j • F j) := by
        simp_rw [← hb]
        rw [b.sum_equivFun, b.sum_equivFun]
      _ = _ := by
        simp [Fin.sum_univ_succ, add_right, hF]
        ring

/-- Coordinates with the exact exceptional vectors and h-coordinate functional. -/
theorem exists_coordinates (B : LinearMap.BilinForm ℝ Vec) (p q h : Vec) (rQ t s rL : ℝ)
    (hsym : ∀ v w, B v w=B w v) (hQ : rQ≠0) (hs : s≠0) (hL : rL≠0)
    (hqq : B q q=rQ^2) (hpq : B p q=t*rQ) (hpp : B p p=t^2-s^2)
    (hhq : B h q=0) (hhp : B h p=0) (hhh : B h h= -rL^2) :
    ∃ U : Vec ≃ₗ[ℝ] Vec,
      (∀ v w, B v w=U v 0*U w 0-U v 1*U w 1-U v 2*U w 2) ∧
      U q=![rQ,0,0] ∧ U p=![t,s,0] ∧ U h=![0,0,rL] ∧
      (∀ v, U v 2= -B h v/rL) := by
  let F := frame p q h rQ t s rL
  obtain ⟨U,hU,hform⟩ := coordinates_of_frame B F
    (frame_gram B p q h rQ t s rL hsym hQ hs hL hqq hpq hpp hhq hhp hhh)
  have hq : q=rQ • F 0 := by
    simp [F,frame,hQ]
  have hp : p=t • F 0+s • F 1 := by
    simp [F,frame,hs]
  have hh : h=rL • F 2 := by
    simp [F,frame,hL]
  have hUq : U q=![rQ,0,0] := by
    rw [hq, map_smul]
    ext i
    fin_cases i <;> simp [hU]
  have hUp : U p=![t,s,0] := by
    rw [hp,map_add,map_smul,map_smul]
    ext i
    fin_cases i <;> simp [hU]
  have hUh : U h=![0,0,rL] := by
    rw [hh,map_smul]
    ext i
    fin_cases i <;> simp [hU]
  refine ⟨U,hform,hUq,hUp,hUh,?_⟩
  intro v
  rw [hform,hUh]
  simp
  field_simp

end
end P14LorentzFrame


/- Source: elliptic_audit/CuspLorentzFrame.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The explicit cusp even-coordinate form has the normalized Lorentz frame.
All assumptions are polynomial identities and strict signs; the trigonometric
grid module supplies them uniformly for odd half-orders at least seven. -/

namespace P14CuspLorentzFrame

noncomputable section
open P14OddRepairAlgebra

def evenMatrix (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![4*a*b,0,2], ![0,-4*(a+b),0], ![2,0,0]]

def evenBilin (a b : ℝ) : LinearMap.BilinForm ℝ Vec3 := (evenMatrix a b).toBilin'

theorem evenBilin_apply (a b : ℝ) (v w : Vec3) : evenBilin a b v w = g a b v w := by
  rw [evenBilin, Matrix.toBilin'_apply']
  simp [evenMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, g]
  ring

theorem g_symm (a b : ℝ) (v w : Vec3) : g a b v w=g a b w v := by
  dsimp [g]
  ring

structure FrameData (a b c : ℝ) where
  rQ : ℝ
  rL : ℝ
  t : ℝ
  s : ℝ
  gamma : ℝ
  U : Vec3 ≃ₗ[ℝ] Vec3
  rQ_pos : 0<rQ
  rL_pos : 0<rL
  t_neg : t<0
  s_gt : -t<s
  gamma_lt : gamma< -1
  s_eq : s=gamma*t
  rQ_sq : rQ^2=2*(1-a)*(a-b)
  rL_sq : rL^2=4*a*(a-b)*(1-b)/(a+b)
  t_mul_rQ : t*rQ= -2*(a-b)^2
  form_eq : ∀ v w, g a b v w=U v 0*U w 0-U v 1*U w 1-U v 2*U w 2
  q_coords : U (q a c)=![rQ,0,0]
  p_coords : U (p a b c)=![t,s,0]
  h_coords : U (h a b c)=![0,0,rL]
  third_coordinate : ∀ w, U (curveEven w) 2= -4*(w+c)*(w+c*(2*a-1))/rL

theorem exists_frame (a b c : ℝ) (hb : b=2*a^2-1) (hc : c^2=(a+1)/2)
    (ha : 1/2<a) (ha1 : a<1) (hab : 0<a+b) (hba : b<a) : Nonempty (FrameData a b c) := by
  have hap : 0<a := by linarith
  have habn := ne_of_gt hab
  have hQ : 0<2*(1-a)*(a-b) := by positivity
  have hL : 0<4*a*(a-b)*(1-b)/(a+b) := by
    apply div_pos _ hab
    have hb1 : b<1 := lt_trans hba ha1
    positivity
  let rQ := Real.sqrt (2*(1-a)*(a-b))
  let rL := Real.sqrt (4*a*(a-b)*(1-b)/(a+b))
  have hrQ : 0<rQ := Real.sqrt_pos.2 hQ
  have hrL : 0<rL := Real.sqrt_pos.2 hL
  have hrQ2 : rQ^2=2*(1-a)*(a-b) := Real.sq_sqrt (le_of_lt hQ)
  have hrL2 : rL^2=4*a*(a-b)*(1-b)/(a+b) := Real.sq_sqrt (le_of_lt hL)
  let t := -2*(a-b)^2/rQ
  have ht : t<0 := div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero (by linarith))) hrQ
  have htQ : t*rQ= -2*(a-b)^2 := by dsimp [t]; field_simp
  have hpneg := p_norm_neg a b c hb hc ha ha1
  let s := Real.sqrt (t^2-g a b (p a b c) (p a b c))
  have hsp : 0<s := Real.sqrt_pos.2 (by nlinarith [sq_nonneg t])
  have hs2 : s^2=t^2-g a b (p a b c) (p a b c) :=
    Real.sq_sqrt (by nlinarith [sq_nonneg t])
  have hsgt : -t<s := by nlinarith
  let gamma := s/t
  have hgamma : gamma< -1 := (div_lt_iff_of_neg ht).2 (by linarith)
  have hseq : s=gamma*t := by dsimp [gamma]; field_simp [ne_of_lt ht]
  have hqq : evenBilin a b (q a c) (q a c)=rQ^2 := by
    rw [evenBilin_apply,q_norm a b c hc,hrQ2]
  have hpq : evenBilin a b (p a b c) (q a c)=t*rQ := by
    rw [evenBilin_apply,pq_inner a b c hb hc,htQ]
  have hpp : evenBilin a b (p a b c) (p a b c)=t^2-s^2 := by
    rw [evenBilin_apply,hs2]
    ring
  have hhq : evenBilin a b (h a b c) (q a c)=0 := by
    rw [evenBilin_apply,g_symm]
    have heq : q a c=curveEven (-c) := by
      ext i
      fin_cases i <;> simp [q,curveEven]
      nlinarith [hc]
    rw [heq,h_factor a b c (-c) habn hc]
    ring
  have hhp : evenBilin a b (h a b c) (p a b c)=0 := by
    rw [evenBilin_apply,g_symm]
    have heq : p a b c=curveEven (-c*(2*a-1)) := by
      ext i
      fin_cases i <;> simp [p,curveEven]
      calc
        _ = 2*((a+1)/2)*(2*a-1)^2-1 := by rw [hb]; ring
        _ = _ := by rw [mul_pow,hc]; ring
    rw [heq,h_factor a b c (-c*(2*a-1)) habn hc]
    ring
  have hhh : evenBilin a b (h a b c) (h a b c)= -rL^2 := by
    rw [evenBilin_apply,h_norm a b c habn hc,hrL2]
    ring
  obtain ⟨U,hform,hUq,hUp,hUh,hcoord⟩ := P14LorentzFrame.exists_coordinates
    (evenBilin a b) (p a b c) (q a c) (h a b c) rQ t s rL
    (fun v w => by simp only [evenBilin_apply]; exact g_symm a b v w)
    (ne_of_gt hrQ) (ne_of_gt hsp) (ne_of_gt hrL) hqq hpq hpp hhq hhp hhh
  refine ⟨⟨rQ,rL,t,s,gamma,U,hrQ,hrL,ht,hsgt,hgamma,hseq,hrQ2,hrL2,htQ,
    ?_,hUq,hUp,hUh,?_⟩⟩
  · intro v w
    simpa only [evenBilin_apply] using hform v w
  · intro w
    rw [hcoord,evenBilin_apply,g_symm,h_factor a b c w habn hc]
    ring

end
end P14CuspLorentzFrame


/- Source: elliptic_audit/LorentzCoordinateLift.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Extending the three even coordinates by the rescaled sine coordinate. -/

namespace P14LorentzCoordinateLift

noncomputable section
abbrev Vec3 := Fin 3 → ℝ
abbrev Vec4 := Fin 4 → ℝ

def even (v : Vec4) : Vec3 := ![v 0,v 1,v 3]

theorem even_add (v w : Vec4) : even (v+w)=even v+even w := by
  ext i
  fin_cases i <;> simp [even]

theorem even_smul (a : ℝ) (v : Vec4) : even (a • v)=a • even v := by
  ext i
  fin_cases i <;> simp [even]

def liftMap (U : Vec3 ≃ₗ[ℝ] Vec3) (rD : ℝ) : Vec4 →ₗ[ℝ] Vec4 where
  toFun v := ![U (even v) 0,U (even v) 1,U (even v) 2,rD*v 2]
  map_add' v w := by
    rw [even_add,map_add]
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' a v := by
    rw [even_smul,map_smul]
    ext i
    fin_cases i <;> simp [mul_left_comm]

theorem liftMap_injective (U : Vec3 ≃ₗ[ℝ] Vec3) (rD : ℝ) (hD : rD≠0) :
    Function.Injective (liftMap U rD) := by
  intro v w heq
  have hev : U (even v)=U (even w) := by
    ext i
    fin_cases i
    · simpa [liftMap] using congrFun heq 0
    · simpa [liftMap] using congrFun heq 1
    · simpa [liftMap] using congrFun heq 2
  have he := U.injective hev
  have hsin : v 2=w 2 := by
    apply mul_left_cancel₀ hD
    simpa [liftMap] using congrFun heq 3
  ext i
  fin_cases i
  · simpa [even] using congrFun he 0
  · simpa [even] using congrFun he 1
  · exact hsin
  · simpa [even] using congrFun he 2

def liftEquiv (U : Vec3 ≃ₗ[ℝ] Vec3) (rD : ℝ) (hD : rD≠0) : Vec4 ≃ₗ[ℝ] Vec4 :=
  LinearEquiv.ofBijective (liftMap U rD)
    ⟨liftMap_injective U rD hD,
      LinearMap.injective_iff_surjective.mp (liftMap_injective U rD hD)⟩

theorem liftEquiv_apply (U : Vec3 ≃ₗ[ℝ] Vec3) (rD : ℝ) (hD : rD≠0) (v : Vec4) :
    liftEquiv U rD hD v = ![U (even v) 0,U (even v) 1,U (even v) 2,rD*v 2] := rfl

theorem lift_form (a b c : ℝ) (F : P14CuspLorentzFrame.FrameData a b c)
    (rD : ℝ) (hD : rD≠0) (hD2 : rD^2=4*(a-b)) (v w : Vec4) :
    P14LorentzMetric.form (liftEquiv F.U rD hD v) (liftEquiv F.U rD hD w) =
      P14OddRepairAlgebra.g a b (even v) (even w)+4*(a-b)*v 2*w 2 := by
  rw [F.form_eq]
  simp [liftEquiv_apply,P14LorentzMetric.form]
  calc
    _ = rD^2*v 2*w 2 := by ring
    _ = _ := by rw [hD2]

theorem curve_coordinates (U : Vec3 ≃ₗ[ℝ] Vec3) (rD : ℝ) (hD : rD≠0)
    (w S : ℝ) :
    liftEquiv U rD hD ![1,w,S,2*w^2-1] =
      ![U (P14OddRepairAlgebra.curveEven w) 0,
        U (P14OddRepairAlgebra.curveEven w) 1,
        U (P14OddRepairAlgebra.curveEven w) 2,rD*S] := by
  simp [liftEquiv_apply,even,P14OddRepairAlgebra.curveEven]

theorem q_coordinates (a b c : ℝ) (F : P14CuspLorentzFrame.FrameData a b c)
    (rD : ℝ) (hD : rD≠0) (S : ℝ) :
    liftEquiv F.U rD hD ![1,-c,S,a] = ![F.rQ,0,0,rD*S] := by
  simp only [liftEquiv_apply,even,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons]
  change ![F.U (P14OddRepairAlgebra.q a c) 0,F.U (P14OddRepairAlgebra.q a c) 1,
    F.U (P14OddRepairAlgebra.q a c) 2,rD*S]=_
  rw [F.q_coords]
  rfl

theorem p_coordinates (a b c : ℝ) (F : P14CuspLorentzFrame.FrameData a b c)
    (rD : ℝ) (hD : rD≠0) (S : ℝ) :
    liftEquiv F.U rD hD ![1,-c*(2*a-1),S,2*a*b-a] = ![F.t,F.s,0,rD*S] := by
  simp only [liftEquiv_apply,even,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons]
  change ![F.U (P14OddRepairAlgebra.p a b c) 0,F.U (P14OddRepairAlgebra.p a b c) 1,
    F.U (P14OddRepairAlgebra.p a b c) 2,rD*S]=_
  rw [F.p_coords]
  rfl

theorem special_sine_scales (a b c : ℝ) (F : P14CuspLorentzFrame.FrameData a b c)
    (rD sh s3h : ℝ) (hrD : 0<rD) (hrD2 : rD^2=4*(a-b)) (hsh : 0<sh)
    (hsh2 : sh^2=(1-a)/2) (hprod : sh*s3h=(a-b)/2) :
    rD*sh=F.rQ ∧ rD*s3h= -F.t := by
  have hsq : (rD*sh)^2=F.rQ^2 := by
    rw [mul_pow,hrD2,hsh2,F.rQ_sq]
    ring
  have hq : rD*sh=F.rQ := by nlinarith [F.rQ_pos,mul_pos hrD hsh]
  refine ⟨hq,?_⟩
  apply mul_left_cancel₀ (ne_of_gt F.rQ_pos)
  calc
    F.rQ*(rD*s3h) = rD^2*(sh*s3h) := by rw [← hq]; ring
    _ = 2*(a-b)^2 := by rw [hrD2,hprod]; ring
    _ = F.rQ * -F.t := by nlinarith [F.t_mul_rQ]

end
end P14LorentzCoordinateLift


/- Source: literature/OddGridFrame.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The shifted odd trigonometric grid in the checked Lorentz coordinates. -/
noncomputable section
open scoped Classical
open P14OddTrig P14OddPlaneIncidence
namespace P14OddGridFrame

abbrev Vec := Fin 4 → ℝ

def a (N : ℕ) : ℝ := Real.cos (alpha N)
def b (N : ℕ) : ℝ := Real.cos (2*alpha N)
def c (N : ℕ) : ℝ := Real.cos (alpha N/2)

abbrev Frame (N : ℕ) := P14CuspLorentzFrame.FrameData (a N) (b N) (c N)

theorem frame_nonempty {N : ℕ} (hN : 3 ≤ N) : Nonempty (Frame N) := by
  obtain ⟨ha,ha1,hba,hab⟩ := grid_parameter_signs hN
  exact P14CuspLorentzFrame.exists_frame (a N) (b N) (c N)
    (Real.cos_two_mul (alpha N)) (half_square (alpha N)) ha ha1 hab hba

def frame {N : ℕ} (hN : 3 ≤ N) : Frame N := Classical.choice (frame_nonempty hN)

def rD (N : ℕ) : ℝ := Real.sqrt (4*(a N-b N))

lemma rD_pos {N : ℕ} (hN : 3 ≤ N) : 0 < rD N := by
  apply Real.sqrt_pos.mpr
  have := (grid_parameter_signs hN).2.2.1
  dsimp [a,b] at *
  linarith

lemma rD_sq {N : ℕ} (hN : 3 ≤ N) : rD N^2 = 4*(a N-b N) := by
  apply Real.sq_sqrt
  have := (grid_parameter_signs hN).2.2.1
  dsimp [a,b] at *
  linarith

def lift {N : ℕ} (hN : 3 ≤ N) (F : Frame N) : Vec ≃ₗ[ℝ] Vec :=
  P14LorentzCoordinateLift.liftEquiv F.U (rD N) (ne_of_gt (rD_pos hN))

def vector {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) : Vec :=
  lift hN F (realCurve i)

lemma realCurve_embed {N : ℕ} (i : Index N) :
    P14RealComplex.embed (realCurve i) = P14TrigCurveRanks.curve (node i) := by
  rw [curve_trig]
  ext q
  fin_cases q <;> simp [P14RealComplex.embed,realCurve]

lemma realCurve_nonzero {N : ℕ} (i : Index N) : realCurve i ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [realCurve] at this

lemma realCurve_injective (N : ℕ) : Function.Injective (@realCurve N) := by
  intro i j heq
  apply node_injective N
  apply Complex.ext
  · have he := congrFun heq 1
    simpa [realCurve,node_re] using he
  · have he := congrFun heq 2
    simpa [realCurve,node_im] using he

lemma realCurve_three {N : ℕ} (f : Fin 3 → Index N) (hf : Function.Injective f) :
    LinearIndependent ℝ (fun q => realCurve (f q)) := by
  apply P14RealComplex.independent_of_complex
  simp_rw [realCurve_embed]
  exact P14TrigCurveRanks.three_independent (node (N := N)) (node_injective N)
    node_unit f hf

lemma realCurve_five {N : ℕ} (f : Fin 5 → Index N) (hf : Function.Injective f) :
    Submodule.span ℝ (Set.range fun q => realCurve (f q)) = ⊤ := by
  apply P14RealComplex.spanning_of_complex
  simp_rw [realCurve_embed]
  exact P14TrigCurveRanks.five_spanning (node (N := N)) (node_injective N)
    node_unit f hf

lemma vector_nonzero {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) :
    vector hN F i ≠ 0 := by
  intro hi
  apply realCurve_nonzero i
  apply (lift hN F).injective
  simpa only [vector,map_zero] using hi

lemma vector_three {N : ℕ} (hN : 3 ≤ N) (F : Frame N)
    (f : Fin 3 → Index N) (hf : Function.Injective f) :
    LinearIndependent ℝ (fun q => vector hN F (f q)) :=
  (realCurve_three f hf).map' (lift hN F).toLinearMap (LinearMap.ker_eq_bot.mpr (lift hN F).injective)

lemma vector_five {N : ℕ} (hN : 3 ≤ N) (F : Frame N)
    (f : Fin 5 → Index N) (hf : Function.Injective f) :
    Submodule.span ℝ (Set.range fun q => vector hN F (f q)) = ⊤ := by
  have hm := congrArg (Submodule.map (lift hN F).toLinearMap) (realCurve_five f hf)
  rw [Submodule.map_span, Submodule.map_top,
    LinearMap.range_eq_top.mpr (lift hN F).surjective] at hm
  simpa only [← Set.range_comp,Function.comp_def,LinearEquiv.coe_coe,vector] using hm

lemma vector_form {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i j : Index N) :
    P14LorentzMetric.form (vector hN F i) (vector hN F j) = kernelValue i j := by
  rw [vector,vector,lift,P14LorentzCoordinateLift.lift_form _ _ _ F _ _ (rD_sq hN)]
  rw [← cusp_on_curve]
  simp [P14OddRepairAlgebra.g,P14LorentzCoordinateLift.even,realCurve,cuspFunctional,a,b]
  ring

lemma vector_form_zero {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i j : Index N) :
    P14LorentzMetric.form (vector hN F i) (vector hN F j) = 0 ↔
      coord N i ∈ P14OddGraph.cross N (coord N j) := by
  rw [vector_form,kernel_mem_cross]

lemma vector_third {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) :
    vector hN F i 2 = -4*(Real.cos (angle i)+c N)*
      (Real.cos (angle i)+c N*(2*a N-1))/F.rL := by
  change F.U (P14LorentzCoordinateLift.even (realCurve i)) 2 = _
  have he : P14LorentzCoordinateLift.even (realCurve i) =
      P14OddRepairAlgebra.curveEven (Real.cos (angle i)) := by
    simp [P14LorentzCoordinateLift.even,realCurve,P14OddRepairAlgebra.curveEven,
      Real.cos_two_mul]
  rw [he,F.third_coordinate]

lemma vector_fourth {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) :
    vector hN F i 3 = rD N*Real.sin (angle i) := rfl

lemma vector_third_zero {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) :
    vector hN F i 2 = 0 ↔ ∃ t : Fin 4, i = defectIndex N t := by
  rw [vector_third,div_eq_zero_iff,or_iff_left (ne_of_gt F.rL_pos)]
  have he : -4*(Real.cos (angle i)+c N)*(Real.cos (angle i)+c N*(2*a N-1)) =
      -4*((Real.cos (angle i)+Real.cos (alpha N/2))*
        (Real.cos (angle i)+Real.cos (3*alpha N/2))) := by
    rw [triple_half]
    dsimp [a,c]
    ring
  rw [he,mul_eq_zero,or_iff_right (by norm_num : (-4:ℝ)≠0),cosine_factor_zero_iff hN]
  constructor
  · rintro (hi | hi | hi | hi)
    · exact ⟨0,Fin.ext (hi.trans (defectIndex_val hN 0).symm)⟩
    · exact ⟨1,Fin.ext (hi.trans (defectIndex_val hN 1).symm)⟩
    · exact ⟨2,Fin.ext (hi.trans (defectIndex_val hN 2).symm)⟩
    · exact ⟨3,Fin.ext (hi.trans (defectIndex_val hN 3).symm)⟩
  · rintro ⟨t,rfl⟩
    rw [defectIndex_val hN]
    fin_cases t <;> simp

lemma vector_fourth_zero {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) :
    vector hN F i 3 = 0 ↔ i.val=1 := by
  rw [vector_fourth,mul_eq_zero,or_iff_right (ne_of_gt (rD_pos hN)),sine_zero_iff hN]

lemma sine_scales {N : ℕ} (hN : 3 ≤ N) (F : Frame N) :
    rD N*Real.sin (alpha N/2)=F.rQ ∧ rD N*Real.sin (3*alpha N/2)= -F.t := by
  obtain ⟨_,_,hs,_⟩ := half_cos_positive (alpha_range hN).1 (alpha_range hN).2
  exact P14LorentzCoordinateLift.special_sine_scales _ _ _ F (rD N)
    (Real.sin (alpha N/2)) (Real.sin (3*alpha N/2)) (rD_pos hN) (rD_sq hN)
    hs (half_sine_square (alpha N)) (half_sine_product (alpha N))

lemma curve_pi_sub {N : ℕ} (i : Index N) (u : ℝ) (hi : angle i=Real.pi-u) :
    realCurve i = ![1,-Real.cos u,Real.sin u,Real.cos (2*u)] := by
  ext q
  fin_cases q <;> simp [realCurve,hi,Real.cos_two_mul]

lemma curve_pi_add {N : ℕ} (i : Index N) (u : ℝ) (hi : angle i=Real.pi+u) :
    realCurve i = ![1,-Real.cos u,-Real.sin u,Real.cos (2*u)] := by
  ext q
  fin_cases q <;> simp [realCurve,hi,Real.cos_two_mul,Real.cos_add,Real.sin_add]

lemma vector_qminus {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N)
    (hi : i.val=N+1) : vector hN F i = ![F.rQ,0,0,F.rQ] := by
  rw [vector,curve_pi_sub i (alpha N/2) (angle_qminus i hi),
    show 2*(alpha N/2)=alpha N by ring]
  change P14LorentzCoordinateLift.liftEquiv F.U (rD N) _
    ![1,-c N,Real.sin (alpha N/2),a N]=_
  rw [P14LorentzCoordinateLift.q_coordinates _ _ _ F, (sine_scales hN F).1]

lemma vector_qplus {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N)
    (hi : i.val=N+2) : vector hN F i = ![F.rQ,0,0,-F.rQ] := by
  rw [vector,curve_pi_add i (alpha N/2) (angle_qplus i hi),
    show 2*(alpha N/2)=alpha N by ring]
  change P14LorentzCoordinateLift.liftEquiv F.U (rD N) _
    ![1,-c N,-Real.sin (alpha N/2),a N]=_
  rw [P14LorentzCoordinateLift.q_coordinates _ _ _ F,mul_neg,(sine_scales hN F).1]

lemma vector_pminus {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N)
    (hi : i.val=N) : vector hN F i = ![F.t,F.s,0,-F.t] := by
  rw [vector,curve_pi_sub i (3*alpha N/2) (angle_pminus i hi),
    show 2*(3*alpha N/2)=3*alpha N by ring,triple_half,triple_cos]
  change P14LorentzCoordinateLift.liftEquiv F.U (rD N) _
    ![1,-(c N*(2*a N-1)),Real.sin (3*alpha N/2),2*a N*b N-a N]=_
  rw [← neg_mul,P14LorentzCoordinateLift.p_coordinates _ _ _ F,(sine_scales hN F).2]

lemma vector_pplus {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N)
    (hi : i.val=N+3) : vector hN F i = ![F.t,F.s,0,F.t] := by
  rw [vector,curve_pi_add i (3*alpha N/2) (angle_pplus i hi),
    show 2*(3*alpha N/2)=3*alpha N by ring,triple_half,triple_cos]
  change P14LorentzCoordinateLift.liftEquiv F.U (rD N) _
    ![1,-(c N*(2*a N-1)),-Real.sin (3*alpha N/2),2*a N*b N-a N]=_
  rw [← neg_mul,P14LorentzCoordinateLift.p_coordinates _ _ _ F,mul_neg,
    (sine_scales hN F).2,neg_neg]

lemma vector_defects {N : ℕ} (hN : 3 ≤ N) (F : Frame N) :
    (fun t : Fin 4 => vector hN F (defectIndex N t)) =
      ![![F.t,F.s,0,-F.t],![F.rQ,0,0,F.rQ],
        ![F.rQ,0,0,-F.rQ],![F.t,F.s,0,F.t]] := by
  funext t
  fin_cases t
  · exact vector_pminus hN F _ (by simpa using defectIndex_val hN 0)
  · exact vector_qminus hN F _ (defectIndex_val hN 1)
  · exact vector_qplus hN F _ (defectIndex_val hN 2)
  · exact vector_pplus hN F _ (defectIndex_val hN 3)

lemma vector_fourth_zero_third_ne {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N)
    (hzero : vector hN F i 3=0) : vector hN F i 2≠0 := by
  rw [vector_fourth_zero hN F] at hzero
  intro ht
  obtain ⟨t,hit⟩ := (vector_third_zero hN F i).1 ht
  have := congrArg Fin.val hit
  rw [defectIndex_val hN] at this
  omega

lemma form_lift_curve {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (w : Vec) (j : Index N) :
    P14LorentzMetric.form (lift hN F w) (vector hN F j)=cuspFunctional j w := by
  rw [vector,lift,P14LorentzCoordinateLift.lift_form _ _ _ F _ _ (rD_sq hN)]
  simp [P14OddRepairAlgebra.g,P14LorentzCoordinateLift.even,realCurve,cuspFunctional,a,b]
  ring

/-- The original cusp plane transported through the invertible Lorentz lift. -/
def kernelPlane {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (j : Index N) : Submodule ℝ Vec :=
  (cuspPlane j).map (lift hN F).toLinearMap

def fourthPlane {N : ℕ} (hN : 3 ≤ N) (F : Frame N) : Submodule ℝ Vec :=
  sinePlane.map (lift hN F).toLinearMap

lemma mem_kernelPlane {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (j : Index N) (w : Vec) :
    w ∈ kernelPlane hN F j ↔ P14LorentzMetric.form w (vector hN F j)=0 := by
  obtain ⟨v,rfl⟩ := (lift hN F).surjective w
  rw [kernelPlane,Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply]
  change cuspFunctional j v=0 ↔ _
  rw [form_lift_curve]

lemma mem_fourthPlane {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (w : Vec) :
    w ∈ fourthPlane hN F ↔ w 3=0 := by
  obtain ⟨v,rfl⟩ := (lift hN F).surjective w
  rw [fourthPlane,Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply]
  change v 2=0 ↔ rD N*v 2=0
  simp only [mul_eq_zero,or_iff_right (ne_of_gt (rD_pos hN))]

lemma kernelPlane_injective {N : ℕ} (hN : 3 ≤ N) (F : Frame N) :
    Function.Injective (kernelPlane hN F) :=
  (Submodule.map_injective_of_injective (lift hN F).injective).comp (cuspPlane_injective hN)

lemma fourthPlane_ne_kernelPlane {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (j : Index N) :
    fourthPlane hN F ≠ kernelPlane hN F j := by
  intro he
  exact sinePlane_ne_cuspPlane j
    (Submodule.map_injective_of_injective (lift hN F).injective he)

lemma kernelPlane_no_four {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (t : Fin 4)
    (f : Fin 4 → Index N) (hf : Function.Injective f) :
    ¬ ∀ q, vector hN F (f q) ∈ kernelPlane hN F (defectIndex N t) := by
  simpa only [vector,kernelPlane,
    Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply] using cusp_no_four hN t f hf

lemma fourthPlane_no_four {N : ℕ} (hN : 3 ≤ N) (F : Frame N)
    (f : Fin 4 → Index N) (hf : Function.Injective f) :
    ¬ ∀ q, vector hN F (f q) ∈ fourthPlane hN F := by
  simpa only [vector,fourthPlane,
    Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply] using sine_no_four hN f hf

end P14OddGridFrame
end


/- Source: literature/OddOrbitGrid.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Exact orbit geometry of the shifted odd grid, including its five deficient
hyperplanes and the universal repair pairing relation. -/
noncomputable section
open scoped Classical
open P14OddTrig P14OddPlaneIncidence P14OddGridFrame P14LorentzSpan
namespace P14OddOrbitGrid

abbrev Vec := Fin 4 → ℝ

def O {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) : Submodule ℝ Vec :=
  orbitSpan F.gamma (vector hN F i)

lemma gamma_ne {N : ℕ} (F : Frame N) : F.gamma ≠ 0 := by
  have := F.gamma_lt
  linarith

lemma form_comm (v w : Vec) : P14LorentzMetric.form v w=P14LorentzMetric.form w v := by
  dsimp [P14LorentzMetric.form]
  ring

lemma kernelPlane_eq_ker {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (j : Index N) :
    kernelPlane hN F j = LinearMap.ker (lorentzFunctional (vector hN F j)) := by
  ext w
  rw [mem_kernelPlane]
  change _ ↔ lorentzFunctional (vector hN F j) w=0
  rw [lorentzFunctional_apply,form_comm]

lemma lorentzFunctional_ne_zero (v : Vec) (hv : v≠0) : lorentzFunctional v≠0 := by
  intro he
  apply hv
  have h0 := congrArg (fun f : Module.Dual ℝ Vec => f ![1,0,0,0]) he
  have h1 := congrArg (fun f : Module.Dual ℝ Vec => f ![0,1,0,0]) he
  have h2 := congrArg (fun f : Module.Dual ℝ Vec => f ![0,0,1,0]) he
  have h3 := congrArg (fun f : Module.Dual ℝ Vec => f ![0,0,0,1]) he
  simp [lorentzFunctional,functional] at h0 h1 h2 h3
  ext q
  fin_cases q <;> simp [h0,h1,h2,h3]

lemma kernelPlane_rank {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (j : Index N) :
    Module.finrank ℝ (kernelPlane hN F j)=3 := by
  rw [kernelPlane_eq_ker]
  exact ker_finrank _ (lorentzFunctional_ne_zero _ (vector_nonzero hN F j))

lemma fourthPlane_rank {N : ℕ} (hN : 3 ≤ N) (F : Frame N) :
    Module.finrank ℝ (fourthPlane hN F)=3 := by
  have he : fourthPlane hN F=LinearMap.ker (functional ![0,0,0,1]) := by
    ext w
    rw [mem_fourthPlane]
    change _ ↔ functional ![0,0,0,1] w=0
    simp [functional]
  rw [he]
  apply ker_finrank
  intro heq
  have he0 := congrArg (fun f : Module.Dual ℝ Vec => f ![0,0,0,1]) heq
  norm_num [functional,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.tail_cons,Matrix.head_cons] at he0

/-- Each of the four defect orbits is precisely its repair partner's kernel. -/
theorem defect_orbit {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (t : Fin 4) :
    O hN F (defectIndex N t)=kernelPlane hN F (defectIndex N (P14OddGraph.pair t)) := by
  rw [O,kernelPlane_eq_ker]
  have hQ := ne_of_gt F.rQ_pos
  have ht := ne_of_lt F.t_neg
  fin_cases t
  · change orbitSpan F.gamma (vector hN F (defectIndex N 0))=
      LinearMap.ker (lorentzFunctional (vector hN F (defectIndex N 1)))
    rw [vector_pminus hN F _ (by simpa using defectIndex_val hN 0),
      vector_qminus hN F _ (defectIndex_val hN 1)]
    simpa only [F.s_eq,one_mul,neg_mul,neg_one_mul] using
      tilted_repair_span F.gamma F.rQ F.t 1 (gamma_ne F) hQ ht (by norm_num)
  · change orbitSpan F.gamma (vector hN F (defectIndex N 1))=
      LinearMap.ker (lorentzFunctional (vector hN F (defectIndex N 0)))
    rw [vector_qminus hN F _ (defectIndex_val hN 1),
      vector_pminus hN F _ (by simpa using defectIndex_val hN 0)]
    simpa only [F.s_eq,one_mul,neg_mul,neg_one_mul] using
      axis_repair_span F.gamma F.rQ F.t 1 (gamma_ne F) hQ ht (by norm_num)
  · change orbitSpan F.gamma (vector hN F (defectIndex N 2))=
      LinearMap.ker (lorentzFunctional (vector hN F (defectIndex N 3)))
    rw [vector_qplus hN F _ (defectIndex_val hN 2),
      vector_pplus hN F _ (defectIndex_val hN 3)]
    simpa only [F.s_eq,neg_one_mul,neg_neg,one_mul] using
      axis_repair_span F.gamma F.rQ F.t (-1) (gamma_ne F) hQ ht (by norm_num)
  · change orbitSpan F.gamma (vector hN F (defectIndex N 3))=
      LinearMap.ker (lorentzFunctional (vector hN F (defectIndex N 2)))
    rw [vector_pplus hN F _ (defectIndex_val hN 3),
      vector_qplus hN F _ (defectIndex_val hN 2)]
    simpa only [F.s_eq,neg_one_mul,neg_neg,one_mul] using
      tilted_repair_span F.gamma F.rQ F.t (-1) (gamma_ne F) hQ ht (by norm_num)

lemma zero_orbit {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) (hi : i.val=1) :
    O hN F i=fourthPlane hN F := by
  have h3 := (vector_fourth_zero hN F i).2 hi
  have h2 := vector_fourth_zero_third_ne hN F i h3
  have he : vector hN F i = ![vector hN F i 0,vector hN F i 1,vector hN F i 2,0] := by
    ext q
    fin_cases q <;> simp [h3]
  ext w
  rw [mem_fourthPlane,O,he]
  exact sine_zero_span_mem _ _ _ _ (gamma_ne F) h2 w

lemma generic_orbit {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N)
    (hi : i.val≠1) (hd : ¬ ∃ t : Fin 4, i=defectIndex N t) : O hN F i=⊤ := by
  exact generic_span _ _ (gamma_ne F)
    (fun h => hd ((vector_third_zero hN F i).1 h))
    (fun h => hi ((vector_fourth_zero hN F i).1 h))

lemma orbit_classification {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) :
    (i.val=1 ∧ O hN F i=fourthPlane hN F) ∨
    (∃ t : Fin 4, i=defectIndex N t ∧
      O hN F i=kernelPlane hN F (defectIndex N (P14OddGraph.pair t))) ∨ O hN F i=⊤ := by
  by_cases hi : i.val=1
  · exact Or.inl ⟨hi,zero_orbit hN F i hi⟩
  · by_cases hd : ∃ t : Fin 4, i=defectIndex N t
    · obtain ⟨t,rfl⟩ := hd
      exact Or.inr (Or.inl ⟨t,rfl,defect_orbit hN F t⟩)
    · exact Or.inr (Or.inr (generic_orbit hN F i hi hd))

/-- Uniform orbit rank lower bound required by mixed-selection interpolation. -/
theorem orbit_rank_ge {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N) :
    3 ≤ Module.finrank ℝ (O hN F i) := by
  rcases orbit_classification hN F i with ⟨_,he⟩ | ⟨t,_,he⟩ | he
  · rw [he,fourthPlane_rank]
  · rw [he,kernelPlane_rank]
  · rw [he]
    norm_num [Vec]

lemma rank_three_classification {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N)
    (hr : Module.finrank ℝ (O hN F i)=3) :
    (i.val=1 ∧ O hN F i=fourthPlane hN F) ∨
    (∃ t : Fin 4, i=defectIndex N t ∧
      O hN F i=kernelPlane hN F (defectIndex N (P14OddGraph.pair t))) := by
  rcases orbit_classification hN F i with h | h | he
  · exact Or.inl h
  · exact Or.inr h
  · rw [he] at hr
    norm_num [Vec] at hr

/-- Distinct grid indices with rank-three orbits have different orbit hyperplanes. -/
theorem rank_three_distinct {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i j : Index N)
    (hij : i≠j) (hi : Module.finrank ℝ (O hN F i)=3)
    (hj : Module.finrank ℝ (O hN F j)=3) : O hN F i≠O hN F j := by
  intro he
  rcases rank_three_classification hN F i hi with ⟨hiv,hei⟩ | ⟨ti,rfl,hei⟩
  · rcases rank_three_classification hN F j hj with ⟨hjv,hej⟩ | ⟨tj,rfl,hej⟩
    · exact hij (Fin.ext (hiv.trans hjv.symm))
    · exact fourthPlane_ne_kernelPlane hN F _ (hei.symm.trans (he.trans hej))
  · rcases rank_three_classification hN F j hj with ⟨hjv,hej⟩ | ⟨tj,rfl,hej⟩
    · exact fourthPlane_ne_kernelPlane hN F _ (hej.symm.trans (he.symm.trans hei))
    · have hpair := defectIndex_injective hN
        (kernelPlane_injective hN F (hei.symm.trans (he.trans hej)))
      have ht := P14OddGraph.pair_involutive.injective hpair
      exact hij (congrArg (defectIndex N) ht)

/-- No rank-three orbit contains four distinct pure grid points. -/
theorem rank_three_no_four {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i : Index N)
    (hi : Module.finrank ℝ (O hN F i)=3) (f : Fin 4 → Index N)
    (hf : Function.Injective f) : ¬ ∀ q, vector hN F (f q) ∈ O hN F i := by
  rcases rank_three_classification hN F i hi with ⟨_,he⟩ | ⟨t,_,he⟩
  · rw [he]
    exact fourthPlane_no_four hN F f hf
  · rw [he]
    exact kernelPlane_no_four hN F (P14OddGraph.pair t) f hf

lemma universal_pairing_iff_le {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i j : Index N) :
    (∀ τ : Param F.gamma,
      P14LorentzMetric.form (vector hN F i) (J F.gamma τ (vector hN F j))=0) ↔
      O hN F j ≤ kernelPlane hN F i := by
  rw [O,orbitSpan,Submodule.span_le]
  constructor
  · intro h w hw
    obtain ⟨τ,rfl⟩ := hw
    change J F.gamma τ (vector hN F j) ∈ kernelPlane hN F i
    rw [mem_kernelPlane,form_comm]
    exact h τ
  · intro h τ
    have hm : J F.gamma τ (vector hN F j) ∈ kernelPlane hN F i := h (Set.mem_range_self τ)
    rw [mem_kernelPlane,form_comm] at hm
    exact hm

/-- Universal same-half annihilation is exactly the prescribed repair relation. -/
theorem universal_pairing_iff_repair {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i j : Index N) :
    (∀ τ : Param F.gamma,
      P14LorentzMetric.form (vector hN F i) (J F.gamma τ (vector hN F j))=0) ↔
      ∃ t : Fin 4, j=defectIndex N t ∧ i=defectIndex N (P14OddGraph.pair t) := by
  rw [universal_pairing_iff_le]
  constructor
  · intro hle
    have hge := orbit_rank_ge hN F j
    have hr := Submodule.finrank_mono hle
    rw [kernelPlane_rank] at hr
    have hthree : Module.finrank ℝ (O hN F j)=3 := by omega
    have he : O hN F j=kernelPlane hN F i :=
      Submodule.eq_of_le_of_finrank_eq hle (hthree.trans (kernelPlane_rank hN F i).symm)
    rcases rank_three_classification hN F j hthree with ⟨_,hj⟩ | ⟨t,hj,hplane⟩
    · exact False.elim (fourthPlane_ne_kernelPlane hN F i (hj.symm.trans he))
    · exact ⟨t,hj,kernelPlane_injective hN F (he.symm.trans hplane)⟩
  · rintro ⟨t,rfl,rfl⟩
    rw [defect_orbit]

/-- Graph-indexed version, matching the canonical normalized odd graph. -/
theorem universal_pairing_iff_within {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i j : Index N) :
    (∀ τ : Param F.gamma,
      P14LorentzMetric.form (vector hN F i) (J F.gamma τ (vector hN F j))=0) ↔
      coord N i ∈ P14OddGraph.within N (coord N j) := by
  rw [universal_pairing_iff_repair,P14OddGraph.mem_within]
  constructor
  · rintro ⟨t,rfl,rfl⟩
    exact ⟨t,by simp [defectIndex],by simp [defectIndex]⟩
  · rintro ⟨t,hj,hi⟩
    refine ⟨t,?_,?_⟩
    · apply (coord N).injective
      simpa [defectIndex] using hj
    · apply (coord N).injective
      simpa [defectIndex] using hi

/-- Every unprescribed same-half pair is nonzero at some allowed parameter. -/
theorem exists_pairing_ne {N : ℕ} (hN : 3 ≤ N) (F : Frame N) (i j : Index N)
    (hij : coord N i ∉ P14OddGraph.within N (coord N j)) :
    ∃ τ : Param F.gamma,
      P14LorentzMetric.form (vector hN F i) (J F.gamma τ (vector hN F j))≠0 := by
  by_contra! h
  exact hij ((universal_pairing_iff_within hN F i j).1 h)

end P14OddOrbitGrid
end


/- Source: cusp_assembly/OddSeedFinal.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
namespace P14OddSeedFinal
open P14OddGridFrame P14OddOrbitGrid

/-- The specific metric and graph witness used by the complement construction. -/
theorem metric (N : ℕ) (hN : 3 ≤ N) : P14LorentzSeedAssembly.MetricSeed N hN := by
  classical
  let F := frame hN
  let e := P14OddPlaneIncidence.coord N
  let u : P14OddGraph.Cyclic N → P14LorentzMetric.Vec := fun i => vector hN F (e.symm i)
  have h3 (a : Fin 3 → P14OddGraph.Cyclic N) (ha : Function.Injective a) :
      LinearIndependent ℝ (u ∘ a) :=
    vector_three hN F (e.symm ∘ a) (e.symm.injective.comp ha)
  have hcard : 3 ≤ Fintype.card (P14OddGraph.Cyclic N) := by
    simp [P14OddGraph.Cyclic]
    omega
  apply P14LorentzSeedAssembly.metric_of_geometry N hN F.gamma u
  · intro i; exact vector_nonzero hN F (e.symm i)
  · exact P14OrbitSelections.small_of_three u hcard h3
  · intro a ha
    exact vector_five hN F (e.symm ∘ a) (e.symm.injective.comp ha)
  · intro i; exact orbit_rank_ge hN F (e.symm i)
  · intro i j hij hi hj
    exact rank_three_distinct hN F (e.symm i) (e.symm j)
      (fun h => hij (e.symm.injective h)) hi hj
  · intro i hi a ha
    exact rank_three_no_four hN F (e.symm i) hi (e.symm ∘ a) (e.symm.injective.comp ha)
  · intro i j
    have h := vector_form_zero hN F (e.symm i) (e.symm j)
    have he : P14LorentzMetric.form (u i) (u j) = 0 ↔ i ∈ P14OddGraph.cross N j := by
      simpa [u,e] using h
    exact he.trans (P14OddGraph.cross_symm N j i)
  · intro i j
    have h := universal_pairing_iff_within hN F (e.symm i) (e.symm j)
    have he : (∀ t : P14LorentzSpan.Param F.gamma,
        P14LorentzMetric.form (u i) (P14LorentzSpan.J F.gamma t (u j)) = 0) ↔
        i ∈ P14OddGraph.within N j := by
      simpa [u,e] using h
    exact he.trans (P14OddGraph.within_symm N j i)

/-- Connected exact 4-regular tight 5-spanning complex seeds at every order 4N+2, N≥3. -/
theorem proof (N : ℕ) (hN : 3 ≤ N) : P14SeedInterface.Seed (4*N+2) :=
  P14LorentzSeedAssembly.to_seed N hN (metric N hN)

end P14OddSeedFinal
end


/- Source: grouping_audit/QubitMatching.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Explicit qubit vectors for any perfect matching on `Fin m`.
The integer determinant/elimination argument is adapted from the verified
Jig p14 `MinUPB2244/Circulant.lean` construction, now uniformly in the matching.
-/

namespace P14QubitMatching

noncomputable section

def vectorsZ {m : ℕ} (F : Fin m → Fin m) (i : Fin m) : Fin 2 → ℤ :=
  if i < F i then ![1, (i.val : ℤ) + 1]
  else ![-((F i).val : ℤ) - 1, 1]

def vectors {m : ℕ} (F : Fin m → Fin m) (i : Fin m) :
    EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun r => (vectorsZ F i r : ℂ))

def det2Z (x y : Fin 2 → ℤ) : ℤ := x 0 * y 1 - x 1 * y 0

lemma nonzero {m : ℕ} (F : Fin m → Fin m) (i : Fin m) : vectors F i ≠ 0 := by
  intro h
  by_cases hi : i < F i
  · have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 0) h
    simp [vectors, vectorsZ, hi] at h0
  · have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) h
    simp [vectors, vectorsZ, hi] at h1

lemma matching_dotZ {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Involutive F) (hfix : ∀ i, F i ≠ i) (i : Fin m) :
    vectorsZ F i 0 * vectorsZ F (F i) 0 +
      vectorsZ F i 1 * vectorsZ F (F i) 1 = 0 := by
  by_cases hi : i < F i
  · have hj : ¬ F i < i := not_lt_of_gt hi
    simp [vectorsZ, hi, hj, hF i]
  · have hj : F i < i := lt_of_le_of_ne (le_of_not_gt hi) (hfix i)
    simp [vectorsZ, hi, hj, hF i]

lemma matching_orthogonal {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Involutive F) (hfix : ∀ i, F i ≠ i) (i : Fin m) :
    inner ℂ (vectors F i) (vectors F (F i)) = 0 := by
  have h := matching_dotZ F hF hfix i
  have hc : (vectorsZ F i 0 : ℂ) * (vectorsZ F (F i) 0 : ℂ) +
      (vectorsZ F i 1 : ℂ) * (vectorsZ F (F i) 1 : ℂ) = 0 := by
    exact_mod_cast h
  simpa [vectors, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, star_intCast, mul_comm] using hc

lemma determinant_ne_zero {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {i j : Fin m} (hij : i ≠ j) :
    det2Z (vectorsZ F i) (vectorsZ F j) ≠ 0 := by
  have hv : (i.val : ℤ) ≠ (j.val : ℤ) := by
    intro h
    apply hij
    apply Fin.ext
    exact_mod_cast h
  have hw : ((F i).val : ℤ) ≠ ((F j).val : ℤ) := by
    intro h
    apply hij
    apply hF
    apply Fin.ext
    exact_mod_cast h
  by_cases hi : i < F i <;> by_cases hj : j < F j
  · simp [vectorsZ, det2Z, hi, hj]
    omega
  · have hp : 0 ≤ (i.val : ℤ) * (F j).val := mul_nonneg (by positivity) (by positivity)
    simp only [vectorsZ, hi, hj, if_true, if_false, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, det2Z]
    nlinarith
  · have hp : 0 ≤ ((F i).val : ℤ) * j.val := mul_nonneg (by positivity) (by positivity)
    simp only [vectorsZ, hi, hj, if_true, if_false, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, det2Z]
    nlinarith
  · simp [vectorsZ, det2Z, hi, hj]
    omega

lemma determinant_complex_ne_zero {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {i j : Fin m} (hij : i ≠ j) :
    vectors F i 0 * vectors F j 1 - vectors F i 1 * vectors F j 0 ≠ 0 := by
  have h := determinant_ne_zero F hF hij
  change (vectorsZ F i 0 : ℂ) * (vectorsZ F j 1 : ℂ) -
    (vectorsZ F i 1 : ℂ) * (vectorsZ F j 0 : ℂ) ≠ 0
  exact_mod_cast h

lemma pair_independent {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {i j : Fin m} (hij : i ≠ j) :
    LinearIndependent ℂ ![vectors F i, vectors F j] := by
  rw [linearIndependent_fin2]
  refine ⟨nonzero F j, ?_⟩
  intro c hc
  have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 0) hc
  have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) hc
  change c * vectors F j 0 = vectors F i 0 at h0
  change c * vectors F j 1 = vectors F i 1 at h1
  apply determinant_complex_ne_zero F hF hij
  rw [← h0, ← h1]
  ring

lemma exact_independent {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) (f : Fin 2 → Fin m) (hf : Function.Injective f) :
    LinearIndependent ℂ (fun q => vectors F (f q)) := by
  have h := pair_independent F hF (hf.ne (by decide : (0 : Fin 2) ≠ 1))
  convert h using 1
  ext q
  fin_cases q <;> rfl

/-- The exact finite-set spanning interface used by `P14UPBAssembly.SpansEvery`. -/
lemma spans_every_two {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) (S : Finset (Fin m)) (hS : S.card = 2) :
    Submodule.span ℂ (Set.range fun i : (S : Set (Fin m)) => vectors F i.1) = ⊤ := by
  let e : (S : Set (Fin m)) ≃ Fin 2 := Fintype.equivFinOfCardEq (by simpa using hS)
  let f : Fin 2 → Fin m := fun q => (e.symm q).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hli := (exact_independent F hF f hf).comp e e.injective
  have hs : LinearIndependent ℂ (fun i : (S : Set (Fin m)) => vectors F i.1) := by
    simpa [f, Function.comp_def] using hli
  apply hs.span_eq_top_of_card_eq_finrank'
  simpa [finrank_euclideanSpace_fin] using hS

lemma killed_pair_zero {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {i j : Fin m} (hij : i ≠ j)
    {a : EuclideanSpace ℂ (Fin 2)}
    (hi : inner ℂ (vectors F i) a = 0)
    (hj : inner ℂ (vectors F j) a = 0) : a = 0 := by
  have h0 : vectors F i 0 * a 0 + vectors F i 1 * a 1 = 0 := by
    simpa [vectors, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, star_intCast, mul_comm] using hi
  have h1 : vectors F j 0 * a 0 + vectors F j 1 * a 1 = 0 := by
    simpa [vectors, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, star_intCast, mul_comm] using hj
  have hd := determinant_complex_ne_zero F hF hij
  ext r
  fin_cases r
  · apply (mul_eq_zero.mp ?_).resolve_left hd
    calc
      (vectors F i 0 * vectors F j 1 - vectors F i 1 * vectors F j 0) * a 0 =
          vectors F j 1 * (vectors F i 0 * a 0 + vectors F i 1 * a 1) -
            vectors F i 1 * (vectors F j 0 * a 0 + vectors F j 1 * a 1) := by ring
      _ = 0 := by rw [h0, h1]; ring
  · apply (mul_eq_zero.mp ?_).resolve_left hd
    calc
      (vectors F i 0 * vectors F j 1 - vectors F i 1 * vectors F j 0) * a 1 =
          vectors F i 0 * (vectors F j 0 * a 0 + vectors F j 1 * a 1) -
            vectors F j 0 * (vectors F i 0 * a 0 + vectors F i 1 * a 1) := by ring
      _ = 0 := by rw [h0, h1]; ring

lemma killing_bound {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Injective F) {a : EuclideanSpace ℂ (Fin 2)} (ha : a ≠ 0)
    (S : Finset (Fin m)) (hS : ∀ i ∈ S, inner ℂ (vectors F i) a = 0) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  by_contra hij
  exact ha (killed_pair_zero F hF hij (hS i hi) (hS j hj))

/-- Uniform qubit realization with the properties used in the UPB assembly. -/
theorem realization {m : ℕ} (F : Fin m → Fin m)
    (hF : Function.Involutive F) (hfix : ∀ i, F i ≠ i) :
    ∃ z : Fin m → EuclideanSpace ℂ (Fin 2),
      (∀ i, z i ≠ 0) ∧
      (∀ i, inner ℂ (z i) (z (F i)) = 0) ∧
      (∀ i j, i ≠ j → LinearIndependent ℂ ![z i, z j]) ∧
      (∀ a, a ≠ 0 → ∀ S : Finset (Fin m),
        (∀ i ∈ S, inner ℂ (z i) a = 0) → S.card ≤ 1) := by
  exact ⟨vectors F, nonzero F, matching_orthogonal F hF hfix,
    fun _ _ h => pair_independent F hF.injective h,
    fun _ h S hS => killing_bound F hF.injective h S hS⟩

end

end P14QubitMatching


/- Source: elliptic_audit/UPBAssembly.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-!
Reusable final gluing for the problem-14 UPB constructions.

The finite budget argument is adapted from the existing green submission
`Submissions/UPBFromDegreeBudget/Budget.lean` (s3), and span induction from
`Submissions/UPBIffNoDeficientCover/DeficientCover.lean` (s52).
This file supplies a Euclidean spanning-to-budget interface and the s56 specialization.
It does not assert the missing graph decomposition or local vector existence.
-/

noncomputable section
open scoped BigOperators

namespace P14UPBAssembly

abbrev Space (k : ℕ) := EuclideanSpace ℂ (Fin k)

/-- Every subfamily with exactly `s` members spans the ambient space. -/
def SpansEvery {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (v : V → Space k) (s : ℕ) : Prop :=
  ∀ S : Finset V, S.card = s →
    Submodule.span ℂ (Set.range fun i : (S : Set V) => v i.1) = ⊤

/-- The span-induction argument already used by the green deficient-cover theorem. -/
lemma span_inner_right_eq_zero {k : ℕ} {s : Set (Space k)} {a x : Space k}
    (hgen : ∀ y ∈ s, inner ℂ y a = 0)
    (hx : x ∈ Submodule.span ℂ s) : inner ℂ x a = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | smul c x _ hx => simp [inner_smul_left, hx]

/-- A nonzero vector kills at most `c` members of a `(c+1)`-spanning family. -/
theorem killing_bound {V : Type*} [Fintype V] [DecidableEq V] {k c : ℕ}
    (v : V → Space k) (hspan : SpansEvery v (c + 1))
    (a : Space k) (ha : a ≠ 0) (S : Finset V)
    (hkill : ∀ i ∈ S, inner ℂ (v i) a = 0) : S.card ≤ c := by
  by_contra hbad
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (show c + 1 ≤ S.card by omega)
  have haSpan : a ∈ Submodule.span ℂ
      (Set.range fun i : (T : Set V) => v i.1) := by
    rw [hspan T hT]
    exact Submodule.mem_top
  have hself : inner ℂ a a = 0 := span_inner_right_eq_zero (by
    rintro _ ⟨i, rfl⟩
    exact hkill i.1 (hTS i.2)) haSpan
  exact ha (inner_self_eq_zero.mp hself)

/-- Dimension-sized independent subfamilies give the required spanning interface. -/
theorem spansEvery_of_independent {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (v : V → Space k)
    (h : ∀ S : Finset V, S.card = k →
      LinearIndependent ℂ (fun i : (S : Set V) => v i.1)) : SpansEvery v k := by
  intro S hS
  apply (h S hS).span_eq_top_of_card_eq_finrank'
  simpa [finrank_euclideanSpace_fin] using hS

/-- Existing s3 finite budget argument, generalized to arbitrary finite index types. -/
theorem finite_budget {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (d c : J → ℕ) (v : V → (j : J) → Space (d j))
    (hbudget : (∑ j, c j) < Fintype.card V)
    (hkill : ∀ j (a : Space (d j)), a ≠ 0 →
      ∀ S : Finset V, (∀ i ∈ S, inner ℂ (v i j) a = 0) → S.card ≤ c j) :
    ∀ a : (j : J) → Space (d j), (∀ j, a j ≠ 0) →
      ∃ i, ∀ j, inner ℂ (v i j) (a j) ≠ 0 := by
  classical
  intro a ha
  by_contra hsurvivor
  push Not at hsurvivor
  choose f hf using hsurvivor
  let S : J → Finset V := fun j => Finset.univ.filter (fun i => f i = j)
  have hScap : ∀ j, (S j).card ≤ c j := by
    intro j
    apply hkill j (a j) (ha j)
    intro i hi
    have hfi : f i = j := (Finset.mem_filter.mp hi).2
    rw [← hfi]
    exact hf i
  have hcard : Fintype.card V = ∑ j, (S j).card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := f)
      (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset J))
      (fun _ _ => Finset.mem_univ _)
    simpa [S] using h
  have hle : Fintype.card V ≤ ∑ j, c j := by
    calc
      Fintype.card V = ∑ j, (S j).card := hcard
      _ ≤ ∑ j, c j := Finset.sum_le_sum (fun j _ => hScap j)
  exact (Nat.not_lt_of_ge hle) hbudget

theorem survivor_of_spanning {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (d c : J → ℕ) (v : V → (j : J) → Space (d j))
    (hbudget : (∑ j, c j) < Fintype.card V)
    (hspan : ∀ j, SpansEvery (fun i => v i j) (c j + 1)) :
    ∀ a : (j : J) → Space (d j), (∀ j, a j ≠ 0) →
      ∃ i, ∀ j, inner ℂ (v i j) (a j) ≠ 0 :=
  finite_budget d c v hbudget (fun j a ha S hS =>
    killing_bound (fun i => v i j) (hspan j) a ha S hS)

/-- Convenient input form for matrix and Vandermonde constructions. -/
theorem spansEvery_of_exact_independent {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (v : V → Space k)
    (h : ∀ f : Fin k → V, Function.Injective f →
      LinearIndependent ℂ (fun q => v (f q))) : SpansEvery v k := by
  apply spansEvery_of_independent
  intro S hS
  let e : (S : Set V) ≃ Fin k := Fintype.equivFinOfCardEq (by simpa using hS)
  let f : Fin k → V := fun q => (e.symm q).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hli := (h f hf).comp e e.injective
  simpa [f, Function.comp_def] using hli

theorem exact_independent_of_spansEvery {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (v : V → Space k) (h : SpansEvery v k)
    (f : Fin k → V) (hf : Function.Injective f) :
    LinearIndependent ℂ (fun q => v (f q)) := by
  classical
  let S : Finset V := Finset.univ.image f
  have hS : S.card = k := by simp [S, Finset.card_image_of_injective _ hf]
  have hs := h S hS
  have heq : Set.range (fun i : (S : Set V) => v i.1) = Set.range (fun q => v (f q)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp i.2
      exact ⟨q, congrArg v hq⟩
    · rintro ⟨q, rfl⟩
      exact ⟨⟨f q, Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩⟩, rfl⟩
  rw [heq] at hs
  apply linearIndependent_of_top_le_span_of_card_le_finrank hs.ge
  simp

theorem spansEvery_pullback {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {k : ℕ} (v : V → Space k)
    (h : SpansEvery v k) (f : W → V) (hf : Function.Injective f) :
    SpansEvery (fun w => v (f w)) k := by
  apply spansEvery_of_exact_independent
  intro g hg
  exact exact_independent_of_spansEvery v h (f ∘ g) (hf.comp hg)

/-- The survivor clause of s56: budget `t + 3 + k < t + k + 4`. -/
theorem two_four_survivor {V : Type*} [Fintype V] [DecidableEq V] {k t : ℕ}
    (z : V → Fin t → Space 2) (y : V → Space 4) (x : V → Space k)
    (hcard : Fintype.card V = t + k + 4)
    (hz : ∀ q, SpansEvery (fun i => z i q) 2)
    (hy : SpansEvery y 4) (hx : SpansEvery x (k + 1)) :
    ∀ az : Fin t → Space 2, ∀ ay : Space 4, ∀ ax : Space k,
      (∀ q, az q ≠ 0) → ay ≠ 0 → ax ≠ 0 →
      ∃ i, (∀ q, inner ℂ (z i q) (az q) ≠ 0) ∧
        inner ℂ (y i) ay ≠ 0 ∧ inner ℂ (x i) ax ≠ 0 := by
  classical
  intro az ay ax haz hay hax
  let J := (Fin t ⊕ Unit) ⊕ Unit
  let d : J → ℕ := Sum.elim (Sum.elim (fun _ => 2) (fun _ => 4)) (fun _ => k)
  let c : J → ℕ := Sum.elim (Sum.elim (fun _ => 1) (fun _ => 3)) (fun _ => k)
  let v : V → (j : J) → Space (d j) := fun i j => match j with
    | .inl (.inl q) => z i q
    | .inl (.inr _) => y i
    | .inr _ => x i
  let a : (j : J) → Space (d j) := fun j => match j with
    | .inl (.inl q) => az q
    | .inl (.inr _) => ay
    | .inr _ => ax
  have hb : (∑ j, c j) < Fintype.card V := by
    simp [c, J, Fintype.sum_sum_type, hcard]
    omega
  have hs : ∀ j, SpansEvery (fun i => v i j) (c j + 1) := by
    rintro ((q | u) | u)
    · exact hz q
    · exact hy
    · exact hx
  have ha : ∀ j, a j ≠ 0 := by
    rintro ((q | u) | u)
    · exact haz q
    · exact hay
    · exact hax
  obtain ⟨i, hi⟩ := survivor_of_spanning d c v hb hs a ha
  exact ⟨i, fun q => hi (.inl (.inl q)), hi (.inl (.inr ())), hi (.inr ())⟩

end P14UPBAssembly
end


/- Source: literature/OddComplementPath.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The explicit Hamiltonian-path relabeling used in the odd complement trade.
The path in the union of the near-factors centred at 0 and 1 is
`0, 2, -2, 4, -4, ..., 2*N, -2*N`.
This file only concerns finite cyclic arithmetic. -/

noncomputable section

namespace P14OddComplementPath

open P14OddGraph

def finCyclic (N : ℕ) : Fin (2*N+1) ≃ Cyclic N where
  toFun t := t.val
  invFun x := ⟨x.val, ZMod.val_lt x⟩
  left_inv t := Fin.ext (ZMod.val_natCast_of_lt t.isLt)
  right_inv x := ZMod.natCast_zmod_val x

@[simp] lemma finCyclic_apply (N : ℕ) (t : Fin (2*N+1)) :
    finCyclic N t = (t.val : Cyclic N) := rfl

def zig (N : ℕ) (t : Fin (2*N+1)) : Fin (2*N+1) :=
  if h0 : t.val = 0 then ⟨0, by omega⟩
  else if h2 : t.val % 2 = 0 then ⟨2*N+1-t.val, by omega⟩
  else ⟨t.val+1, by omega⟩

def zag (N : ℕ) (x : Fin (2*N+1)) : Fin (2*N+1) :=
  if h0 : x.val = 0 then ⟨0, by omega⟩
  else if h2 : x.val % 2 = 0 then ⟨x.val-1, by omega⟩
  else ⟨2*N+1-x.val, by omega⟩

lemma zag_zig (N : ℕ) (t : Fin (2*N+1)) : zag N (zig N t) = t := by
  by_cases h0 : t.val = 0
  · apply Fin.ext
    simp [zig, zag, h0]
  by_cases h2 : t.val % 2 = 0
  · have hp : 2*N+1-t.val ≠ 0 := by omega
    have ho : (2*N+1-t.val) % 2 ≠ 0 := by omega
    apply Fin.ext
    simp [zig, zag, h0, h2, hp, ho]; omega
  · have hp : t.val+1 ≠ 0 := by omega
    have he : (t.val+1) % 2 = 0 := by omega
    apply Fin.ext
    simp [zig, zag, h0, h2, he]

lemma zig_zag (N : ℕ) (t : Fin (2*N+1)) : zig N (zag N t) = t := by
  by_cases h0 : t.val = 0
  · apply Fin.ext
    simp [zig, zag, h0]
  by_cases h2 : t.val % 2 = 0
  · have hp : t.val-1 ≠ 0 := by omega
    have ho : (t.val-1) % 2 ≠ 0 := by omega
    apply Fin.ext
    simp [zig, zag, h0, h2, hp, ho]; omega
  · have hp : 2*N+1-t.val ≠ 0 := by omega
    have he : (2*N+1-t.val) % 2 = 0 := by omega
    apply Fin.ext
    simp [zig, zag, h0, h2, hp, he]; omega

def zigEquiv (N : ℕ) : Equiv.Perm (Fin (2*N+1)) where
  toFun := zig N
  invFun := zag N
  left_inv := zag_zig N
  right_inv := zig_zag N

def reflection (N : ℕ) (c : Cyclic N) : Equiv.Perm (Cyclic N) where
  toFun x := c-x
  invFun x := c-x
  left_inv x := by ring
  right_inv x := by ring

def relabel (N : ℕ) : Equiv.Perm (Cyclic N) :=
  (((finCyclic N).symm.trans (zigEquiv N).symm).trans (finCyclic N)).trans
    (reflection N (N+1))

lemma relabel_zig (N : ℕ) (t : Fin (2*N+1)) :
    relabel N (finCyclic N (zig N t)) = (N+1 : Cyclic N) - t.val := by
  change (N+1 : Cyclic N) -
    finCyclic N ((zigEquiv N).symm ((finCyclic N).symm (finCyclic N (zig N t)))) = _
  rw [Equiv.symm_apply_apply]
  change (N+1 : Cyclic N) - finCyclic N ((zigEquiv N).symm (zigEquiv N t)) = _
  simp

lemma zig_cast (N : ℕ) (t : Fin (2*N+1)) :
    finCyclic N (zig N t) =
      if t.val % 2 = 0 then -(t.val : Cyclic N) else t.val+1 := by
  have hn : ((2*N+1 : ℕ) : Cyclic N) = 0 := ZMod.natCast_self _
  by_cases h0 : t.val = 0
  · simp [zig, h0]
  by_cases h2 : t.val % 2 = 0
  · simp only [zig, h0, ↓reduceDIte, h2, finCyclic_apply, ↓reduceIte]
    rw [Nat.cast_sub (by omega), hn, zero_sub]
  · simp [zig, h0, h2]

lemma zig_successor_sum (N : ℕ) (s t : Fin (2*N+1)) (hst : t.val = s.val+1) :
    finCyclic N (zig N s) + finCyclic N (zig N t) = 0 ∨
      finCyclic N (zig N s) + finCyclic N (zig N t) = 2 := by
  rw [zig_cast, zig_cast]
  by_cases hs : s.val % 2 = 0
  · have ht : t.val % 2 ≠ 0 := by omega
    simp only [hs, ht, ↓reduceIte]
    right
    rw [hst, Nat.cast_add, Nat.cast_one]
    ring
  · have ht : t.val % 2 = 0 := by omega
    simp only [hs, ht, ↓reduceIte]
    left
    rw [hst, Nat.cast_add, Nat.cast_one]
    ring

lemma relabel_zero (N : ℕ) : relabel N 0 = (N+1 : Cyclic N) := by
  have h := relabel_zig N ⟨0, by omega⟩
  simpa [zig] using h

lemma relabel_one (N : ℕ) : relabel N 1 = (N+2 : Cyclic N) := by
  let t : Fin (2*N+1) := ⟨2*N, by omega⟩
  have hz : finCyclic N (zig N t) = 1 := by
    rw [zig_cast]
    have ht : t.val % 2 = 0 := by dsimp [t]; omega
    simp only [ht, ↓reduceIte]
    have hd := double_inverse N
    dsimp [t]
    push_cast
    linear_combination -hd
  have h := relabel_zig N t
  rw [hz] at h
  have hd := double_inverse N
  dsimp [t] at h
  push_cast at h
  linear_combination h - hd

lemma cycle_step (N : ℕ) (s t : Fin (2*N+1))
    (hst : (t.val : Cyclic N) = (s.val : Cyclic N)+1) :
    ((N+1 : Cyclic N)-s.val) + ((N+1 : Cyclic N)-t.val) = 2 ∨
      finCyclic N (zig N s) + finCyclic N (zig N t) = 0 ∨
      finCyclic N (zig N s) + finCyclic N (zig N t) = 2 := by
  have hv := congrArg ZMod.val hst
  have hcast : ((s.val : Cyclic N)+1).val = (s.val+1) % (2*N+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ZMod.val_natCast (2*N+1) (s.val+1)
  rw [ZMod.val_natCast_of_lt t.isLt, hcast] at hv
  by_cases hs : s.val+1 < 2*N+1
  · have htv : t.val = s.val+1 := by rwa [Nat.mod_eq_of_lt hs] at hv
    exact Or.inr (zig_successor_sum N s t htv)
  · have hsl : s.val = 2*N := by omega
    have ht0 : t.val = 0 := by rw [hsl] at hv; simpa using hv
    left
    rw [hsl, ht0]
    push_cast
    ring

/-- A cycle edge under the path relabeling is either the one deleted edge,
or belongs to one of the two near-factors centred at 0 and 1. -/
theorem relabel_cycle (N : ℕ) (u v : Cyclic N)
    (h : relabel N v = relabel N u-1 ∨ relabel N v = relabel N u+1) :
    relabel N u + relabel N v = 2 ∨ u+v = 0 ∨ u+v = 2 := by
  obtain ⟨s, rfl⟩ := ((zigEquiv N).trans (finCyclic N)).surjective u
  obtain ⟨t, rfl⟩ := ((zigEquiv N).trans (finCyclic N)).surjective v
  change relabel N (finCyclic N (zig N t)) =
    relabel N (finCyclic N (zig N s))-1 ∨
    relabel N (finCyclic N (zig N t)) =
    relabel N (finCyclic N (zig N s))+1 at h
  change relabel N (finCyclic N (zig N s)) +
    relabel N (finCyclic N (zig N t)) = 2 ∨
    finCyclic N (zig N s) + finCyclic N (zig N t) = 0 ∨
    finCyclic N (zig N s) + finCyclic N (zig N t) = 2
  rw [relabel_zig, relabel_zig] at h ⊢
  rcases h with h | h
  · exact cycle_step N s t (by linear_combination -h)
  · have he := cycle_step N t s (by linear_combination h)
    simpa only [add_comm] using he

end P14OddComplementPath
end


/- Source: literature/OddComplement.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Explicit one-factorization of the complement of `P14OddGraph.graph`.
The factors are modified cross reflections, together with a transported
round-robin trade. No graph factorization existence theorem is used. -/

noncomputable section
open Function

namespace P14OddComplement

open P14OddGraph P14OddComplementPath

def label {N : ℕ} : Vertex N → Cyclic N := Sum.elim id id

def hole (N : ℕ) (c : Cyclic N) : Cyclic N := (N+1)*(c-1)

lemma double_hole (N : ℕ) (c : Cyclic N) : 2*hole N c = c-1 := by
  dsimp [hole]
  rw [← mul_assoc, double_inverse, one_mul]

lemma hole_sum (N : ℕ) (c : Cyclic N) : hole N c + (hole N c+1) = c := by
  linear_combination double_hole N c

lemma one_ne_zero (N : ℕ) (hN : 3 ≤ N) : (1 : Cyclic N) ≠ 0 :=
  natCast_ne_zero N 1 (by omega) (by omega)

lemma two_ne_zero (N : ℕ) (hN : 3 ≤ N) : (2 : Cyclic N) ≠ 0 :=
  natCast_ne_zero N 2 (by omega) (by omega)

lemma four_ne_zero (N : ℕ) (hN : 3 ≤ N) : (4 : Cyclic N) ≠ 0 :=
  natCast_ne_zero N 4 (by omega) (by omega)

lemma two_ne_four (N : ℕ) (hN : 3 ≤ N) : (2 : Cyclic N) ≠ 4 := by
  intro h
  apply two_ne_zero N hN
  linear_combination -h

lemma hole_ne (N : ℕ) (hN : 3 ≤ N) (c : Cyclic N) : hole N c ≠ hole N c+1 := by
  intro h
  apply one_ne_zero N hN
  linear_combination -h

def modified (N : ℕ) (c : Cyclic N) : Vertex N → Vertex N
  | .inl x => if x = hole N c then .inl (hole N c+1)
      else if x = hole N c+1 then .inl (hole N c) else .inr (c-x)
  | .inr x => if x = hole N c then .inr (hole N c+1)
      else if x = hole N c+1 then .inr (hole N c) else .inl (c-x)

lemma reflected_hole (N : ℕ) (c x : Cyclic N) :
    (c-x = hole N c ↔ x = hole N c+1) ∧
    (c-x = hole N c+1 ↔ x = hole N c) := by
  have hs := hole_sum N c
  constructor <;> constructor <;> intro h <;> linear_combination -hs - h

theorem modified_involutive (N : ℕ) (hN : 3 ≤ N) (c : Cyclic N) :
    Involutive (modified N c) := by
  intro v
  have hab := hole_ne N hN c
  cases v with
  | inl x =>
    by_cases ha : x = hole N c
    · subst x; simp [modified, hab.symm]
    by_cases hb : x = hole N c+1
    · subst x; simp [modified, hab.symm]
    have hr := reflected_hole N c x
    simp [modified, ha, hb, hr, sub_sub_cancel]
  | inr x =>
    by_cases ha : x = hole N c
    · subst x; simp [modified, hab.symm]
    by_cases hb : x = hole N c+1
    · subst x; simp [modified, hab.symm]
    have hr := reflected_hole N c x
    simp [modified, ha, hb, hr, sub_sub_cancel]

theorem modified_fixed_free (N : ℕ) (hN : 3 ≤ N) (c : Cyclic N) (v : Vertex N) :
    modified N c v ≠ v := by
  have hab := hole_ne N hN c
  cases v <;> dsimp only [modified] <;> split_ifs <;> simp_all

lemma modified_sum (N : ℕ) (c : Cyclic N) (v : Vertex N) :
    label v + label (modified N c v) = c := by
  cases v <;> dsimp only [modified] <;> split_ifs <;>
    simp_all only [label, Sum.elim_inl, Sum.elim_inr, id_eq]
  all_goals first | exact hole_sum N c | simpa only [add_comm] using hole_sum N c | ring

lemma modified_parameter_injective (N : ℕ) (v : Vertex N) :
    Injective (fun c => modified N c v) := by
  intro c d h
  change modified N c v = modified N d v at h
  have hc := modified_sum N c v
  have hd := modified_sum N d v
  rw [h] at hc
  exact hc.symm.trans hd

/-- Two odd near-factors are made perfect by joining their unique holes. -/
def nearStitch (N : ℕ) (r : Cyclic N) : Vertex N → Vertex N
  | .inl x => if x = r then .inr r else .inl (2*r-x)
  | .inr x => if x = r then .inl r else .inr (2*r-x)

lemma nearStitch_involutive (N : ℕ) (r : Cyclic N) :
    Involutive (nearStitch N r) := by
  intro v
  have he (x : Cyclic N) : 2*r-x = r ↔ x = r := by
    constructor <;> intro h <;> linear_combination -h
  cases v <;> simp only [nearStitch] <;> split_ifs <;> simp_all

lemma nearStitch_fixed_free (N : ℕ) (r : Cyclic N) (v : Vertex N) :
    nearStitch N r v ≠ v := by
  have he (x : Cyclic N) (hx : x ≠ r) : 2*r-x ≠ x := by
    intro h
    apply hx
    apply double_injective N
    linear_combination -h
  cases v <;> simp only [nearStitch] <;> split_ifs <;> simp_all

lemma nearStitch_parameter_injective (N : ℕ) (v : Vertex N) :
    Injective (fun r => nearStitch N r v) := by
  intro r s h
  cases v <;> simp only [nearStitch] at h <;> split_ifs at h <;> simp_all
  all_goals apply double_injective N; linear_combination h

def glued (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (r : Cyclic N) : Vertex N → Vertex N
  | .inl x => if x = φ r then .inr (ψ r) else .inl (φ (2*r-φ.symm x))
  | .inr x => if x = ψ r then .inl (φ r) else .inr (ψ (2*r-ψ.symm x))

lemma glued_conjugate (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (r : Cyclic N)
    (v : Vertex N) :
    glued N φ ψ r v =
      Equiv.sumCongr φ ψ (nearStitch N r ((Equiv.sumCongr φ ψ).symm v)) := by
  have heφ (x : Cyclic N) : φ.symm x = r ↔ x = φ r := by
    exact φ.symm_apply_eq
  have heψ (x : Cyclic N) : ψ.symm x = r ↔ x = ψ r := by
    exact ψ.symm_apply_eq
  cases v <;> simp [glued, nearStitch, heφ, heψ]
  all_goals split_ifs <;> rfl

lemma glued_involutive (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (r : Cyclic N) :
    Involutive (glued N φ ψ r) := by
  intro v
  rw [glued_conjugate, glued_conjugate, Equiv.symm_apply_apply,
    nearStitch_involutive, Equiv.apply_symm_apply]

lemma glued_fixed_free (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (r : Cyclic N)
    (v : Vertex N) : glued N φ ψ r v ≠ v := by
  intro h
  have he := congrArg (Equiv.sumCongr φ ψ).symm h
  rw [glued_conjugate, Equiv.symm_apply_apply] at he
  exact nearStitch_fixed_free N r _ he

lemma glued_parameter_injective (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (v : Vertex N) :
    Injective (fun r => glued N φ ψ r v) := by
  intro r s h
  have he := congrArg (Equiv.sumCongr φ ψ).symm h
  simp only [glued_conjugate, Equiv.symm_apply_apply] at he
  exact nearStitch_parameter_injective N _ he

lemma glued_left_same (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (r x y : Cyclic N)
    (h : glued N φ ψ r (.inl x) = .inl y) : φ.symm x + φ.symm y = 2*r := by
  by_cases hx : x = φ r
  · simp [glued, hx] at h
  · have he : φ (2*r-φ.symm x) = y := by simpa [glued, hx] using h
    rw [← he, Equiv.symm_apply_apply]
    ring

lemma glued_right_same (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (r x y : Cyclic N)
    (h : glued N φ ψ r (.inr x) = .inr y) : ψ.symm x + ψ.symm y = 2*r := by
  by_cases hx : x = ψ r
  · simp [glued, hx] at h
  · have he : ψ (2*r-ψ.symm x) = y := by simpa [glued, hx] using h
    rw [← he, Equiv.symm_apply_apply]
    ring

lemma glued_left_cross (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (r x y : Cyclic N)
    (h : glued N φ ψ r (.inl x) = .inr y) : x = φ r ∧ y = ψ r := by
  by_cases hx : x = φ r
  · have he : ψ r = y := by simpa [glued, hx] using h
    exact ⟨hx, he.symm⟩
  · simp [glued, hx] at h

lemma glued_right_cross (N : ℕ) (φ ψ : Equiv.Perm (Cyclic N)) (r x y : Cyclic N)
    (h : glued N φ ψ r (.inr x) = .inl y) : x = ψ r ∧ y = φ r := by
  by_cases hx : x = ψ r
  · have he : φ r = y := by simpa [glued, hx] using h
    exact ⟨hx, he.symm⟩
  · simp [glued, hx] at h

def rightRelabel (N : ℕ) : Equiv.Perm (Cyclic N) :=
  (relabel N).trans (reflection N 2)

@[simp] lemma rightRelabel_apply (N : ℕ) (u : Cyclic N) :
    rightRelabel N u = 2-relabel N u := rfl

lemma rightRelabel_cycle (N : ℕ) (u v : Cyclic N)
    (h : rightRelabel N v = rightRelabel N u-1 ∨
      rightRelabel N v = rightRelabel N u+1) :
    rightRelabel N u + rightRelabel N v = 2 ∨ u+v = 0 ∨ u+v = 2 := by
  have he : relabel N v = relabel N u-1 ∨ relabel N v = relabel N u+1 := by
    simp only [rightRelabel_apply] at h
    rcases h with h | h
    · right; linear_combination -h
    · left; linear_combination -h
  rcases relabel_cycle N u v he with he | he
  · left
    simp only [rightRelabel_apply]
    linear_combination -he
  · exact Or.inr he

def traded (N : ℕ) (r : Cyclic N) : Vertex N → Vertex N :=
  glued N (relabel N) (rightRelabel N) r

lemma cycle_same_sum (N : ℕ) (φ : Equiv.Perm (Cyclic N))
    (hφ : ∀ u v, φ v = φ u-1 ∨ φ v = φ u+1 →
      φ u+φ v = 2 ∨ u+v = 0 ∨ u+v = 2)
    (r x y : Cyclic N) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hs : φ.symm x + φ.symm y = 2*r) (hxy : y = x-1 ∨ y = x+1) :
    x+y = 2 := by
  have hh := hφ (φ.symm x) (φ.symm y) (by simpa using hxy)
  simp only [Equiv.apply_symm_apply] at hh
  rcases hh with h | h | h
  · exact h
  · exfalso
    apply hr0
    apply double_injective N
    linear_combination h - hs
  · exfalso
    apply hr1
    apply double_injective N
    linear_combination h - hs

lemma traded_same_sum (N : ℕ) (r x y : Cyclic N) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hxy : y = x-1 ∨ y = x+1)
    (h : traded N r (.inl x) = .inl y ∨ traded N r (.inr x) = .inr y) :
    x+y = 2 := by
  rcases h with h | h
  · exact cycle_same_sum N (relabel N) (relabel_cycle N) r x y hr0 hr1
      (glued_left_same N _ _ r x y h) hxy
  · exact cycle_same_sum N (rightRelabel N) (rightRelabel_cycle N) r x y hr0 hr1
      (glued_right_same N _ _ r x y h) hxy

lemma traded_cross_sum (N : ℕ) (r x y : Cyclic N)
    (h : traded N r (.inl x) = .inr y ∨ traded N r (.inr x) = .inl y) : x+y = 2 := by
  rcases h with h | h
  · obtain ⟨rfl, rfl⟩ := glued_left_cross N _ _ r x y h
    simp [rightRelabel_apply]
  · obtain ⟨rfl, rfl⟩ := glued_right_cross N _ _ r x y h
    simp [rightRelabel_apply]

lemma traded_cross_not_translate (N : ℕ) (r x y : Cyclic N)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (h : traded N r (.inl x) = .inr y ∨ traded N r (.inr x) = .inl y) :
    y ≠ x-1 ∧ y ≠ x+1 := by
  have hx : x = relabel N r ∨ y = relabel N r := by
    rcases h with h | h
    · exact Or.inl (glued_left_cross N _ _ r x y h).1
    · exact Or.inr (glued_right_cross N _ _ r x y h).2
  have hs := traded_cross_sum N r x y h
  have h0 : relabel N r ≠ (N+1 : Cyclic N) := by
    rw [← relabel_zero N]
    exact fun he => hr0 ((relabel N).injective he)
  have h1 : relabel N r ≠ (N+2 : Cyclic N) := by
    rw [← relabel_one N]
    exact fun he => hr1 ((relabel N).injective he)
  have hd := double_inverse N
  constructor <;> intro ht <;> rcases hx with hx | hx
  · apply h1; apply double_injective N; linear_combination hs - ht - hd - 2*hx
  · apply h0; apply double_injective N; linear_combination hs + ht - hd - 2*hx
  · apply h0; apply double_injective N; linear_combination hs - ht - hd - 2*hx
  · apply h1; apply double_injective N; linear_combination hs + ht - hd - 2*hx

lemma within_cycle (N : ℕ) (x y : Cyclic N) (h : y ∈ within N x) :
    y = x-1 ∨ y = x+1 := by
  obtain ⟨t, rfl, rfl⟩ := (mem_within N x y).mp h
  fin_cases t
  · right; norm_num [defect, pair]
  · left; norm_num [defect, pair]
  · right; norm_num [defect, pair]; ring
  · left; norm_num [defect, pair]; ring

lemma within_sum (N : ℕ) (x y : Cyclic N) (h : y ∈ within N x) : x+y = 0 ∨ x+y = 4 := by
  obtain ⟨t, rfl, rfl⟩ := (mem_within N x y).mp h
  have hd := double_inverse N
  fin_cases t
  · left; norm_num [defect, pair]; linear_combination hd
  · left; norm_num [defect, pair]; linear_combination hd
  · right; norm_num [defect, pair]; linear_combination hd
  · right; norm_num [defect, pair]; linear_combination hd

lemma not_within (N : ℕ) (x y : Cyclic N) (h0 : x+y ≠ 0) (h4 : x+y ≠ 4) :
    y ∉ within N x := by
  intro h
  exact (within_sum N x y h).elim h0 h4

lemma not_cross (N : ℕ) (x y : Cyclic N) (h0 : x+y ≠ 0) (h4 : x+y ≠ 4)
    (hm : y ≠ x-1) (hp : y ≠ x+1) : y ∉ cross N x := by
  simp only [cross, Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h | h | h)
  · exact hm h
  · exact hp h
  · apply h0; linear_combination h
  · apply h4; linear_combination h

lemma modified_left_same (N : ℕ) (c x y : Cyclic N)
    (h : modified N c (.inl x) = .inl y) :
    (x = hole N c ∧ y = hole N c+1) ∨ (x = hole N c+1 ∧ y = hole N c) := by
  simp only [modified] at h
  split_ifs at h <;> simp_all

lemma modified_right_same (N : ℕ) (c x y : Cyclic N)
    (h : modified N c (.inr x) = .inr y) :
    (x = hole N c ∧ y = hole N c+1) ∨ (x = hole N c+1 ∧ y = hole N c) := by
  simp only [modified] at h
  split_ifs at h <;> simp_all

lemma modified_same_cycle (N : ℕ) (c x y : Cyclic N)
    (h : modified N c (.inl x) = .inl y ∨ modified N c (.inr x) = .inr y) :
    y = x-1 ∨ y = x+1 := by
  have he : (x = hole N c ∧ y = hole N c+1) ∨
      (x = hole N c+1 ∧ y = hole N c) := by
    rcases h with h | h
    · exact modified_left_same N c x y h
    · exact modified_right_same N c x y h
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr rfl
  · left; ring

lemma modified_left_cross (N : ℕ) (c x y : Cyclic N)
    (h : modified N c (.inl x) = .inr y) :
    x ≠ hole N c ∧ x ≠ hole N c+1 ∧ y = c-x := by
  simp only [modified] at h
  split_ifs at h; simp_all

lemma modified_right_cross (N : ℕ) (c x y : Cyclic N)
    (h : modified N c (.inr x) = .inl y) :
    x ≠ hole N c ∧ x ≠ hole N c+1 ∧ y = c-x := by
  simp only [modified] at h
  split_ifs at h; simp_all

lemma modified_cross_not_translate (N : ℕ) (c x y : Cyclic N)
    (h : modified N c (.inl x) = .inr y ∨ modified N c (.inr x) = .inl y) :
    y ≠ x-1 ∧ y ≠ x+1 := by
  have he : x ≠ hole N c ∧ x ≠ hole N c+1 ∧ y = c-x := by
    rcases h with h | h
    · exact modified_left_cross N c x y h
    · exact modified_right_cross N c x y h
  obtain ⟨ha, hb, rfl⟩ := he
  have hd := double_hole N c
  constructor <;> intro ht
  · apply hb; apply double_injective N; linear_combination -ht - hd
  · apply ha; apply double_injective N; linear_combination -ht - hd

lemma modified_nonedge_of_eq (N : ℕ) (hN : 3 ≤ N) (c : Cyclic N)
    (hc0 : c ≠ 0) (hc4 : c ≠ 4) (v w : Vertex N) (he : modified N c v = w) :
    ¬(graph N hN).Adj v w := by
  have hs := modified_sum N c v
  rw [he] at hs
  have h0 : label v + label w ≠ 0 := fun h => hc0 (hs.symm.trans h)
  have h4 : label v + label w ≠ 4 := fun h => hc4 (hs.symm.trans h)
  rcases v with x | x <;> rcases w with y | y
  · exact not_within N x y h0 h4
  · obtain ⟨hm, hp⟩ := modified_cross_not_translate N c x y (Or.inl he)
    exact not_cross N x y h0 h4 hm hp
  · obtain ⟨hm, hp⟩ := modified_cross_not_translate N c x y (Or.inr he)
    exact not_cross N x y h0 h4 hm hp
  · exact not_within N x y h0 h4

lemma traded_nonedge_of_eq (N : ℕ) (hN : 3 ≤ N) (r : Cyclic N)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (v w : Vertex N) (he : traded N r v = w) :
    ¬(graph N hN).Adj v w := by
  have h2 := two_ne_zero N hN
  have h24 := two_ne_four N hN
  rcases v with x | x <;> rcases w with y | y
  · intro hg
    have hc := within_cycle N x y hg
    have hs := traded_same_sum N r x y hr0 hr1 hc (Or.inl he)
    exact not_within N x y (by simpa [hs] using h2) (by simpa [hs] using h24) hg
  · have hs := traded_cross_sum N r x y (Or.inl he)
    obtain ⟨hm, hp⟩ := traded_cross_not_translate N r x y hr0 hr1 (Or.inl he)
    exact not_cross N x y (by simpa [hs] using h2) (by simpa [hs] using h24) hm hp
  · have hs := traded_cross_sum N r x y (Or.inr he)
    obtain ⟨hm, hp⟩ := traded_cross_not_translate N r x y hr0 hr1 (Or.inr he)
    exact not_cross N x y (by simpa [hs] using h2) (by simpa [hs] using h24) hm hp
  · intro hg
    have hc := within_cycle N x y hg
    have hs := traded_same_sum N r x y hr0 hr1 hc (Or.inr he)
    exact not_within N x y (by simpa [hs] using h2) (by simpa [hs] using h24) hg

lemma modified_ne_traded (N : ℕ) (c r : Cyclic N) (hc : c ≠ 2)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (v : Vertex N) : modified N c v ≠ traded N r v := by
  intro he
  have hs := modified_sum N c v
  have hw : ∀ w : Vertex N, modified N c v = w → traded N r v = w → label v+label w = 2 := by
    intro w hm ht
    rcases v with x | x <;> rcases w with y | y
    · exact traded_same_sum N r x y hr0 hr1
        (modified_same_cycle N c x y (Or.inl hm)) (Or.inl ht)
    · exact traded_cross_sum N r x y (Or.inl ht)
    · exact traded_cross_sum N r x y (Or.inr ht)
    · exact traded_same_sum N r x y hr0 hr1
        (modified_same_cycle N c x y (Or.inr hm)) (Or.inr ht)
  exact hc (hs.symm.trans (hw _ rfl he.symm))

abbrev CrossIndex (N : ℕ) := {c : Cyclic N // c ∉ ({0,2,4} : Finset (Cyclic N))}
abbrev RoundIndex (N : ℕ) := {r : Cyclic N // r ∉ ({0,1} : Finset (Cyclic N))}
abbrev Factor (N : ℕ) := CrossIndex N ⊕ RoundIndex N

def matching (N : ℕ) : Factor N → Vertex N → Vertex N
  | .inl c => modified N c.val
  | .inr r => traded N r.val

lemma crossIndex_conditions (N : ℕ) (c : CrossIndex N) :
    c.val ≠ 0 ∧ c.val ≠ 2 ∧ c.val ≠ 4 := by
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using c.property

lemma roundIndex_conditions (N : ℕ) (r : RoundIndex N) : r.val ≠ 0 ∧ r.val ≠ 1 := by
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using r.property

theorem factor_card (N : ℕ) (hN : 3 ≤ N) : Fintype.card (Factor N) = 4*N-3 := by
  classical
  have h1 := one_ne_zero N hN
  have h2 := two_ne_zero N hN
  have h4 := four_ne_zero N hN
  have h24 := two_ne_four N hN
  have hc : ({0,2,4} : Finset (Cyclic N)).card = 3 := by
    simp [h24, Ne.symm h2, Ne.symm h4]
  have hr : ({0,1} : Finset (Cyclic N)).card = 2 := by
    simp [Ne.symm h1]
  simp only [Factor, Fintype.card_sum, CrossIndex, RoundIndex, Fintype.card_subtype_compl,
    ZMod.card, Fintype.card_coe, hc, hr]
  omega

theorem matching_involutive (N : ℕ) (hN : 3 ≤ N) (q : Factor N) :
    Involutive (matching N q) := by
  cases q with
  | inl c => exact modified_involutive N hN c.val
  | inr r => exact glued_involutive N _ _ r.val

theorem matching_fixed_free (N : ℕ) (hN : 3 ≤ N) (q : Factor N) (v : Vertex N) :
    matching N q v ≠ v := by
  cases q with
  | inl c => exact modified_fixed_free N hN c.val v
  | inr r => exact glued_fixed_free N _ _ r.val v

theorem matching_nonedge (N : ℕ) (hN : 3 ≤ N) (q : Factor N) (v : Vertex N) :
    ¬(graph N hN).Adj v (matching N q v) := by
  cases q with
  | inl c =>
    obtain ⟨h0, h2, h4⟩ := crossIndex_conditions N c
    exact modified_nonedge_of_eq N hN c.val h0 h4 v _ rfl
  | inr r =>
    obtain ⟨h0, h1⟩ := roundIndex_conditions N r
    exact traded_nonedge_of_eq N hN r.val h0 h1 v _ rfl

theorem matching_parameter_injective (N : ℕ) (v : Vertex N) :
    Injective (fun q : Factor N => matching N q v) := by
  intro q t h
  rcases q with c | r <;> rcases t with d | s
  · exact congrArg Sum.inl (Subtype.ext (modified_parameter_injective N v h))
  · obtain ⟨h0, h2, h4⟩ := crossIndex_conditions N c
    obtain ⟨h0', h1⟩ := roundIndex_conditions N s
    exact False.elim (modified_ne_traded N c.val s.val h2 h0' h1 v h)
  · obtain ⟨h0, h2, h4⟩ := crossIndex_conditions N d
    obtain ⟨h0', h1⟩ := roundIndex_conditions N r
    exact False.elim (modified_ne_traded N d.val r.val h2 h0' h1 v h.symm)
  · exact congrArg Sum.inr (Subtype.ext (glued_parameter_injective N _ _ v h))

/-- Every edge of the graph complement belongs to exactly one explicit factor. -/
theorem matching_exact_cover (N : ℕ) (hN : 3 ≤ N) (v w : Vertex N) :
    (graph N hN)ᶜ.Adj v w ↔ ∃! q : Factor N, matching N q v = w := by
  classical
  let G := graph N hN
  let f : Factor N → Gᶜ.neighborSet v := fun q =>
    ⟨matching N q v, (show Gᶜ.Adj v (matching N q v) from
      ⟨(matching_fixed_free N hN q v).symm, matching_nonedge N hN q v⟩)⟩
  have hi : Injective f := by
    intro q t h
    exact matching_parameter_injective N v (congrArg Subtype.val h)
  have hc : Fintype.card (Gᶜ.neighborSet v) = Fintype.card (Factor N) := by
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.degree_compl,
      factor_card N hN]
    simp only [G, graph_degree N hN, Vertex, Fintype.card_sum, ZMod.card]
    omega
  have hsurj : Surjective f := by
    by_contra hn
    have hh := Fintype.card_lt_of_injective_not_surjective f hi hn
    omega
  constructor
  · intro h
    obtain ⟨q, hq⟩ := hsurj ⟨w, h⟩
    refine ⟨q, congrArg Subtype.val hq, ?_⟩
    intro t ht
    apply matching_parameter_injective N v
    exact ht.trans (congrArg Subtype.val hq).symm
  · rintro ⟨q, rfl, _⟩
    exact (f q).property

/-- The index is normalized for the qubit assembly: there are exactly `4*N-3`
perfect matchings, with no loops, no seed edge, and exact complement coverage. -/
theorem complement_factors (N : ℕ) (hN : 3 ≤ N) :
    ∃ F : Fin (4*N-3) → Vertex N → Vertex N,
      (∀ q, Involutive (F q)) ∧
      (∀ q v, F q v ≠ v) ∧
      (∀ v w, (graph N hN)ᶜ.Adj v w ↔ ∃! q, F q v = w) := by
  classical
  let e : Fin (4*N-3) ≃ Factor N := (Fintype.equivFinOfCardEq (factor_card N hN)).symm
  refine ⟨fun q => matching N (e q), fun q => matching_involutive N hN (e q),
    fun q v => matching_fixed_free N hN (e q) v, ?_⟩
  intro v w
  rw [matching_exact_cover N hN v w]
  exact e.existsUnique_congr_right.symm

end P14OddComplement
end


/- Source: cusp_assembly/QuarticUPB.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Assembly for a quartic seed whose complement has a specified matching cover.
The existing matching realization and finite budget proofs do all the work.
No assertion that an arbitrary seed has such a cover is made here. -/

noncomputable section
namespace P14QuarticUPB
open P14UPBAssembly
open scoped BigOperators

def HasUPB (m t : ℕ) : Prop :=
  ∃ z : Fin m → Fin t → Space 2, ∃ x : Fin m → Space 4,
    (∀ i q, z i q ≠ 0) ∧ (∀ i, x i ≠ 0) ∧
    (∀ i j, i ≠ j →
      (∃ q, inner ℂ (z i q) (z j q) = 0) ∨ inner ℂ (x i) (x j) = 0) ∧
    (∀ az : Fin t → Space 2, ∀ ax : Space 4,
      (∀ q, az q ≠ 0) → ax ≠ 0 →
      ∃ i, (∀ q, inner ℂ (z i q) (az q) ≠ 0) ∧ inner ℂ (x i) ax ≠ 0)

theorem from_rows {m t : ℕ} (hm : m = t + 5)
    (x : Fin m → Space 4) (hx : ∀ i, x i ≠ 0) (hspan : SpansEvery x 5)
    (F : Fin t → Fin m → Fin m) (hF : ∀ q, Function.Involutive (F q))
    (hfix : ∀ q i, F q i ≠ i)
    (hcover : ∀ i j, i ≠ j → inner ℂ (x i) (x j) = 0 ∨ ∃ q, F q i = j) :
    HasUPB m t := by
  classical
  let z : Fin m → Fin t → Space 2 := fun i q => P14QubitMatching.vectors (F q) i
  refine ⟨z, x, fun i q => P14QubitMatching.nonzero (F q) i, hx, ?_, ?_⟩
  · intro i j hij
    rcases hcover i j hij with h | ⟨q, hq⟩
    · exact Or.inr h
    · refine Or.inl ⟨q, ?_⟩
      simpa [z, hq] using P14QubitMatching.matching_orthogonal (F q) (hF q) (hfix q) i
  · intro az ax haz hax
    let J := Fin t ⊕ Unit
    let d : J → ℕ := Sum.elim (fun _ => 2) (fun _ => 4)
    let c : J → ℕ := Sum.elim (fun _ => 1) (fun _ => 4)
    let v : Fin m → (j : J) → Space (d j) := fun i j => match j with
      | .inl q => z i q
      | .inr _ => x i
    let a : (j : J) → Space (d j) := fun j => match j with
      | .inl q => az q
      | .inr _ => ax
    have hb : (∑ j, c j) < Fintype.card (Fin m) := by
      simp [c, J, Fintype.sum_sum_type, hm]
    have hk : ∀ j (b : Space (d j)), b ≠ 0 →
        ∀ S : Finset (Fin m), (∀ i ∈ S, inner ℂ (v i j) b = 0) → S.card ≤ c j := by
      rintro (q | u) b hb S hS
      · exact P14QubitMatching.killing_bound (F q) (hF q).injective hb S hS
      · exact P14UPBAssembly.killing_bound x hspan b hb S hS
    have ha : ∀ j, a j ≠ 0 := by
      rintro (q | u)
      · exact haz q
      · exact hax
    obtain ⟨i, hi⟩ := finite_budget d c v hb hk a ha
    exact ⟨i, fun q => hi (.inl q), hi (.inr ())⟩

end P14QuarticUPB

namespace P14OddQuarticRows
open Matrix Submodule P14UPBAssembly

/-- Retain the exact graph while turning the positive real metric into complex rows. -/
theorem rows (N : ℕ) (hN : 3 ≤ N)
    (e : Fin (4*N+2) ≃ P14OddGraph.Vertex N) :
    ∃ x : Fin (4*N+2) → Space 4,
      (∀ i, x i ≠ 0) ∧ SpansEvery x 5 ∧
      (∀ i j, inner ℂ (x i) (x j) = 0 ↔ (P14OddGraph.graph N hN).Adj (e i) (e j)) := by
  classical
  obtain ⟨H,hH,v,hv,hedge,_,h5⟩ := P14OddSeedFinal.metric N hN
  obtain ⟨F,hF⟩ := P14MetricRealization.exists_coordinates H hH
  let C : (Fin 4 → ℂ) ≃ₗ[ℂ] Space 4 := (WithLp.linearEquiv 2 ℂ (Fin 4 → ℂ)).symm
  let w : Fin (4*N+2) → Fin 4 → ℂ := fun i => P14RealComplex.embed (F (v (e i)))
  let x : Fin (4*N+2) → Space 4 := fun i => C (w i)
  have hp (i j : Fin (4*N+2)) :
      inner ℂ (x i) (x j) = ((dotProduct (v (e i)) (H *ᵥ v (e j)) : ℝ) : ℂ) := by
    have he := P14RealComplex.pair (F (v (e i))) (F (v (e j)))
    have he' := he.trans (congrArg (fun r : ℝ => (r : ℂ)) (hF (v (e i)) (v (e j))))
    simpa [x,C,w,PiLp.inner_apply,RCLike.inner_apply,mul_comm] using he'
  refine ⟨x,?_,?_,?_⟩
  · intro i hi
    apply hv (e i)
    apply F.injective
    apply P14RealComplex.embed_injective
    have hw : w i = 0 := C.map_eq_zero_iff.mp hi
    simpa [w] using hw
  · intro S hS
    let es : Fin 5 ≃ (S : Set (Fin (4*N+2))) :=
      (Fintype.equivFinOfCardEq (by simpa using hS)).symm
    let f : Fin 5 → P14OddGraph.Vertex N := fun q => e (es q).val
    have hf : Function.Injective f := e.injective.comp
      (Subtype.val_injective.comp es.injective)
    have hr : span ℝ (Set.range fun q => F (v (f q))) = ⊤ := by
      have hm := congrArg (Submodule.map F.toLinearMap) (h5 f hf)
      simpa [Submodule.map_span,← Set.range_comp,Function.comp_def,Submodule.map_top,
        LinearMap.range_eq_top.mpr F.surjective] using hm
    have hc := P14RealComplex.spanning (fun q => F (v (f q))) hr
    have hm := congrArg (Submodule.map C.toLinearMap) hc
    have ht : span ℂ (Set.range fun q => x (es q).val) = ⊤ := by
      simpa [x,w,f,Submodule.map_span,← Set.range_comp,Function.comp_def,Submodule.map_top,
        LinearMap.range_eq_top.mpr C.surjective] using hm
    have he : Set.range (fun q => x (es q).val) =
        Set.range (fun i : (S : Set (Fin (4*N+2))) => x i.val) := by
      ext y
      constructor
      · rintro ⟨q,rfl⟩; exact ⟨es q,rfl⟩
      · rintro ⟨i,rfl⟩; exact ⟨es.symm i,by simp⟩
    rwa [he] at ht
  · intro i j
    rw [hp,Complex.ofReal_eq_zero]
    exact hedge (e i) (e j)

end P14OddQuarticRows
end


/- Source: cusp_assembly/OddQuarticUPB.lean. Reused authorship is retained in the source comments and artifact citations. -/
noncomputable section
namespace P14OddQuarticUPB

/-- Actual UPBs on `4N−3` qubits and one quart, with `4N+2` states. -/
theorem proof (N : ℕ) (hN : 3 ≤ N) :
    P14QuarticUPB.HasUPB (4*N+2) (4*N-3) := by
  classical
  let e : Fin (4*N+2) ≃ P14OddGraph.Vertex N :=
    (Fintype.equivFinOfCardEq (by simp [P14OddGraph.Vertex,P14OddGraph.Cyclic]; omega)).symm
  obtain ⟨x,hx,hspan,hedge⟩ := P14OddQuarticRows.rows N hN e
  obtain ⟨F,hF,hfix,hcover⟩ := P14OddComplement.complement_factors N hN
  let Q : Fin (4*N-3) → Fin (4*N+2) → Fin (4*N+2) :=
    fun q i => e.symm (F q (e i))
  have hQ : ∀ q, Function.Involutive (Q q) := by
    intro q i
    simp only [Q,e.apply_symm_apply]
    rw [hF q (e i),e.symm_apply_apply]
  have hQfix : ∀ q i, Q q i ≠ i := by
    intro q i hi
    apply hfix q (e i)
    have he := congrArg e hi
    simpa only [Q,e.apply_symm_apply] using he
  apply P14QuarticUPB.from_rows (by omega) x hx hspan Q hQ hQfix
  intro i j hij
  by_cases h : (P14OddGraph.graph N hN).Adj (e i) (e j)
  · exact Or.inl ((hedge i j).mpr h)
  · obtain ⟨q,hq,_⟩ := (hcover (e i) (e j)).mp ⟨e.injective.ne hij,h⟩
    exact Or.inr ⟨q,by simp only [Q,hq,e.symm_apply_apply]⟩

end P14OddQuarticUPB
end

theorem proof : ∀ N : ℕ, 3 ≤ N → P14QuarticUPB.HasUPB (4*N+2) (4*N-3) :=
  P14OddQuarticUPB.proof

end Submissions.QuarticUPBTwoModFour.Assembly
