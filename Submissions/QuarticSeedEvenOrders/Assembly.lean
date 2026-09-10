import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
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
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
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

namespace Submissions.QuarticSeedEvenOrders.Assembly

/- Source: literature/CrossComplement.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Direct factorization of the complement of the elliptic cross graph.
The parity argument extends the existing s60 proof to all even and odd offsets.
No graph matching existence theorem is needed. -/

noncomputable section
open Function

namespace P14CrossComplement

abbrev Class (N : ℕ) := Fin N ⊕ Fin N
abbrev Vertex (N : ℕ) := ZMod (2 * N) ⊕ ZMod (2 * N)

def peer {N : ℕ} : Class N → ZMod (2 * N) → ZMod (2 * N)
  | .inl c, i => i + (2 * c.val : ℕ)
  | .inr d, i => -i + (2 * d.val + 1 : ℕ)

def back {N : ℕ} : Class N → ZMod (2 * N) → ZMod (2 * N)
  | .inl c, j => j - (2 * c.val : ℕ)
  | .inr d, j => -j + (2 * d.val + 1 : ℕ)

lemma back_peer {N : ℕ} (a : Class N) (i : ZMod (2 * N)) :
    back a (peer a i) = i := by
  cases a <;> dsimp only [back, peer] <;> ring

lemma peer_back {N : ℕ} (a : Class N) (i : ZMod (2 * N)) :
    peer a (back a i) = i := by
  cases a <;> dsimp only [back, peer] <;> ring

lemma peer_cross_ne {N : ℕ} (hN : 0 < N)
    (i : ZMod (2 * N)) (c d : Fin N) :
    peer (.inl c) i ≠ peer (.inr d) i := by
  have : NeZero (2 * N) := ⟨by omega⟩
  intro h
  have h' : i + i + (2 * c.val : ℕ) = (2 * d.val + 1 : ℕ) := by
    change i + (2 * c.val : ℕ) = -i + (2 * d.val + 1 : ℕ) at h
    linear_combination h
  rw [← ZMod.natCast_zmod_val i] at h'
  have hcast : ((2 * i.val + 2 * c.val : ℕ) : ZMod (2 * N)) =
      (2 * d.val + 1 : ℕ) := by
    simpa [Nat.cast_add, Nat.cast_mul, two_mul] using h'
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hm2 := hm.of_dvd (by omega : 2 ∣ 2 * N)
  simp [Nat.ModEq] at hm2

theorem peer_injective {N : ℕ} (hN : 0 < N) (i : ZMod (2 * N)) :
    Injective (fun a : Class N => peer a i) := by
  intro a b hab
  cases a with
  | inl c =>
    cases b with
    | inl c' =>
      have he : ((2 * c.val : ℕ) : ZMod (2 * N)) = (2 * c'.val : ℕ) :=
        add_left_cancel hab
      have hm := (ZMod.natCast_eq_natCast_iff (2 * c.val) (2 * c'.val) (2 * N)).mp
        he
      have hv := hm.eq_of_lt_of_lt (by omega) (by omega)
      exact congrArg Sum.inl (Fin.ext (by omega))
    | inr d => exact False.elim (peer_cross_ne hN i c d hab)
  | inr d =>
    cases b with
    | inl c => exact False.elim (peer_cross_ne hN i c d hab.symm)
    | inr d' =>
      have he : ((2 * d.val + 1 : ℕ) : ZMod (2 * N)) = (2 * d'.val + 1 : ℕ) :=
        add_left_cancel hab
      have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
      have hv := hm.eq_of_lt_of_lt (by omega) (by omega)
      exact congrArg Sum.inr (Fin.ext (by omega))

theorem peer_bijective {N : ℕ} (hN : 0 < N) (i : ZMod (2 * N)) :
    Bijective (fun a : Class N => peer a i) := by
  have : NeZero (2 * N) := ⟨by omega⟩
  refine ⟨peer_injective hN i, ?_⟩
  by_contra h
  have hc := Fintype.card_lt_of_injective_not_surjective _ (peer_injective hN i) h
  simp only [Class, Fintype.card_sum, Fintype.card_fin, ZMod.card] at hc
  omega

def matchVertex {N : ℕ} (a : Class N) : Vertex N → Vertex N
  | .inl i => .inr (peer a i)
  | .inr j => .inl (back a j)

theorem matchVertex_involutive {N : ℕ} (a : Class N) :
    Involutive (matchVertex a) := by
  intro v
  cases v <;> simp [matchVertex, peer_back, back_peer]

theorem matchVertex_ne {N : ℕ} (a : Class N) (v : Vertex N) :
    matchVertex a v ≠ v := by cases v <;> simp [matchVertex]

def selected {r N : ℕ} (hN : r + 2 ≤ N) : Class r → Class N
  | .inl c => .inl ⟨c.val, by omega⟩
  | .inr d => .inr ⟨d.val + if d.val + 1 = r then 1 else 0, by split <;> omega⟩

theorem selected_injective {r N : ℕ} (hN : r + 2 ≤ N) :
    Injective (selected hN) := by
  intro a b hab
  cases a with
  | inl c =>
    cases b with
    | inl c' =>
      have h := congrArg Fin.val (Sum.inl.inj hab)
      exact congrArg Sum.inl (Fin.ext h)
    | inr d => cases hab
  | inr d =>
    cases b with
    | inl c => cases hab
    | inr d' =>
      have h := congrArg Fin.val (Sum.inr.inj hab)
      change d.val + (if d.val + 1 = r then 1 else 0) =
        d'.val + (if d'.val + 1 = r then 1 else 0) at h
      exact congrArg Sum.inr (Fin.ext (by split_ifs at h <;> omega))

def CrossAdj {r N : ℕ} (i j : ZMod (2 * N)) : Prop :=
  (∃ c : Fin r, j = i + (2 * c.val : ℕ)) ∨
  (∃ d : Fin r, j = -i + (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ))

theorem crossAdj_iff_selected {r N : ℕ} (hN : r + 2 ≤ N)
    (i j : ZMod (2 * N)) :
    CrossAdj (r := r) i j ↔ ∃ a : Class r, peer (selected hN a) i = j := by
  constructor
  · rintro (⟨c, hc⟩ | ⟨d, hd⟩)
    · exact ⟨.inl c, hc.symm⟩
    · refine ⟨.inr d, ?_⟩
      simp only [peer, selected]
      rw [hd]
      congr 1
      split_ifs <;> norm_num
      all_goals ring
  · rintro ⟨a, ha⟩
    cases a with
    | inl c => exact Or.inl ⟨c, ha.symm⟩
    | inr d =>
      refine Or.inr ⟨d, ?_⟩
      rw [← ha]
      simp only [peer, selected]
      congr 1
      split_ifs <;> norm_num
      all_goals ring

abbrev Unused {r N : ℕ} (hN : r + 2 ≤ N) :=
  {a : Class N // a ∉ Set.range (selected hN)}

theorem unused_card {r N : ℕ} (hN : r + 2 ≤ N) :
    Fintype.card (Unused hN) = 2 * N - 2 * r := by
  classical
  have hcard : Fintype.card (Set.range (selected hN)) = 2 * r := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ (selected_injective hN))]
    simp [Class, two_mul]
  change Fintype.card {a : Class N // ¬ a ∈ Set.range (selected hN)} = _
  rw [Fintype.card_subtype_compl, hcard]
  simp [Class, two_mul]

/-- Every non-seed cross edge belongs to exactly one unused matching. -/
theorem complement_unique {r N : ℕ} (hN : r + 2 ≤ N)
    (i j : ZMod (2 * N)) :
    ¬ CrossAdj (r := r) i j ↔ ∃! a : Unused hN, peer a.val i = j := by
  classical
  have hpos : 0 < N := by omega
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (peer_bijective hpos i).surjective j
    have hn : a ∉ Set.range (selected hN) := by
      rintro ⟨b, hb⟩
      apply h
      rw [crossAdj_iff_selected hN]
      exact ⟨b, hb ▸ ha⟩
    refine ⟨⟨a, hn⟩, ha, ?_⟩
    intro b hb
    exact Subtype.ext (peer_injective hpos i (hb.trans ha.symm))
  · rintro ⟨a, ha, _⟩ hadj
    obtain ⟨b, hb⟩ := (crossAdj_iff_selected hN i j).mp hadj
    apply a.property
    exact ⟨b, peer_injective hpos i (hb.trans ha.symm)⟩

def peerEquiv {N : ℕ} (a : Class N) : Equiv.Perm (ZMod (2 * N)) where
  toFun := peer a
  invFun := back a
  left_inv := back_peer a
  right_inv := peer_back a

/-- A finite-indexed family of permutations, one for each unused matching.
Every cross edge outside the seed occurs in exactly one of these matchings. -/
theorem complement_permutations {r N : ℕ} (hN : r + 2 ≤ N) :
    ∃ F : Fin (2 * N - 2 * r) → Equiv.Perm (ZMod (2 * N)),
      ∀ i j, ¬ CrossAdj (r := r) i j ↔ ∃! t, F t i = j := by
  classical
  let e : Fin (2 * N - 2 * r) ≃ Unused hN :=
    (Fintype.equivFinOfCardEq (unused_card hN)).symm
  refine ⟨fun t => peerEquiv (e t).val, ?_⟩
  intro i j
  rw [complement_unique hN]
  exact e.existsUnique_congr_right.symm

end P14CrossComplement
end


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


/- Source: cusp_assembly/CuspSeedGraph.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The degree-four connected graph already realized by the proved s55 row. -/

noncomputable section
namespace P14CuspSeedGraph
open P14CrossComplement

def neighbors {N : ℕ} (hN : 4 ≤ N) (i : Vertex N) : Finset (Vertex N) :=
  Finset.univ.image (fun a : Class 2 => matchVertex (selected hN a) i)

def graph {N : ℕ} (hN : 4 ≤ N) : SimpleGraph (Vertex N) where
  Adj i j := j ∈ neighbors hN i
  symm := by
    constructor
    intro i j h
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp h
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_univ _,?_⟩
    rw [← ha]
    exact matchVertex_involutive _ i
  loopless := by
    constructor
    intro i h
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp h
    exact matchVertex_ne _ i ha

instance {N : ℕ} (hN : 4 ≤ N) : DecidableRel (graph hN).Adj := by
  classical
  exact fun _ _ => inferInstance

lemma match_injective {N : ℕ} (hN : 0 < N) (v : Vertex N) :
    Function.Injective (fun a : Class N => matchVertex a v) := by
  intro a b hab
  cases v with
  | inl i => exact peer_injective hN i (Sum.inr.inj hab)
  | inr j =>
    have he : back a j = back b j := Sum.inl.inj hab
    apply peer_injective hN (back a j)
    change peer a (back a j) = peer b (back a j)
    rw [peer_back,he,peer_back]

theorem degree {N : ℕ} [NeZero (2*N)] (hN : 4 ≤ N) (i : Vertex N) :
    (graph hN).degree i = 4 := by
  have he : (graph hN).neighborFinset i = neighbors hN i := by
    ext j
    rw [SimpleGraph.mem_neighborFinset]
    rfl
  rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
  have hi : Function.Injective (fun a : Class 2 => matchVertex (selected hN a) i) :=
    (match_injective (by omega) i).comp (selected_injective hN)
  rw [neighbors,Finset.card_image_of_injective _ hi]
  simp [Class]

lemma cross_iff {N : ℕ} (hN : 4 ≤ N) (i j : ZMod (2*N)) :
    (graph hN).Adj (.inl i) (.inr j) ↔ CrossAdj (r := 2) i j := by
  rw [crossAdj_iff_selected hN]
  change (Sum.inr j ∈ Finset.univ.image
    (fun a : Class 2 => Sum.inr (peer (selected hN a) i))) ↔ _
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Sum.inr.injEq]

lemma same_left {N : ℕ} (hN : 4 ≤ N) (i j : ZMod (2*N)) :
    ¬ (graph hN).Adj (.inl i) (.inl j) := by
  intro h
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp h
  change Sum.inr (peer (selected hN a) i) = Sum.inl j at ha
  cases ha

lemma same_right {N : ℕ} (hN : 4 ≤ N) (i j : ZMod (2*N)) :
    ¬ (graph hN).Adj (.inr i) (.inr j) := by
  intro h
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp h
  change Sum.inl (back (selected hN a) i) = Sum.inr j at ha
  cases ha

theorem connected {N : ℕ} [NeZero (2*N)] (hN : 4 ≤ N) :
    (graph hN).Connected := by
  let G := graph hN
  have h0 (i : ZMod (2*N)) : G.Adj (.inl i) (.inr i) := by
    apply (cross_iff hN i i).mpr
    exact Or.inl ⟨⟨0,by decide⟩,by simp⟩
  have h2 (i : ZMod (2*N)) : G.Adj (.inl i) (.inr (i+2)) := by
    apply (cross_iff hN i (i+2)).mpr
    exact Or.inl ⟨⟨1,by decide⟩,by simp⟩
  have h1 : G.Reachable (.inl 0) (.inl 1) := by
    have h : G.Adj (.inl 0) (.inr 1) := by
      apply (cross_iff hN 0 1).mpr
      exact Or.inr ⟨⟨0,by decide⟩,by simp⟩
    exact h.reachable.trans (h0 1).symm.reachable
  have hstep (i : ZMod (2*N)) : G.Reachable (.inl i) (.inl (i+2)) :=
    (h2 i).reachable.trans (h0 (i+2)).symm.reachable
  have hnat (a : ZMod (2*N)) : ∀ t : ℕ,
      G.Reachable (.inl a) (.inl (a+2*(t : ZMod (2*N)))) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h := ih.trans (hstep (a+2*(t : ZMod (2*N))))
      simpa only [Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_assoc] using h
  have hleft (i : ZMod (2*N)) : G.Reachable (.inl 0) (.inl i) := by
    have hv : i.val = 2*(i.val/2) ∨ i.val = 1+2*(i.val/2) := by omega
    rcases hv with hv | hv
    · have he : (2 : ZMod (2*N)) * (i.val/2 : ℕ) = i := by
        simpa only [Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] using
          (congrArg (fun t : ℕ => (t : ZMod (2*N))) hv).symm
      simpa only [zero_add,he] using hnat 0 (i.val/2)
    · have he : (1 : ZMod (2*N)) + 2*(i.val/2 : ℕ) = i := by
        simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,ZMod.natCast_zmod_val] using
          (congrArg (fun t : ℕ => (t : ZMod (2*N))) hv).symm
      exact h1.trans (by simpa only [he] using hnat 1 (i.val/2))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨.inl 0,?_⟩
  rintro (i | i)
  · exact hleft i
  · exact (hleft i).trans (h0 i).reachable

end P14CuspSeedGraph
end


/- Source: cusp_assembly/ComplexSeedInterface.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Reindex the existing exact complex seed obligations. -/

noncomputable section
namespace P14ComplexSeedInterface
open Submodule P14SeedInterface

theorem of_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (e : Fin m ≃ ι) (G : SimpleGraph ι) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ i, G.degree i = 4)
    (v : ι → Fin 4 → ℂ) (hnz : ∀ i, v i ≠ 0)
    (hedge : ∀ i j, pair (v i) (v j) = 0 ↔ G.Adj i j)
    (hli : ∀ d : ℕ, d ≤ 3 → ∀ f : Fin d → ι, Function.Injective f →
      LinearIndependent ℂ (fun q => v (f q)))
    (hspan : ∀ f : Fin 5 → ι, Function.Injective f →
      span ℂ (Set.range fun q => v (f q)) = ⊤) : Seed m := by
  classical
  let w : Fin m → Fin 4 → ℂ := fun i => v (e i)
  let G' := G.comap e
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  have hp (i j : Fin m) : pair (w i) (w j) = 0 ↔ G'.Adj i j := hedge (e i) (e j)
  have hg : orthGraph w = G' := by
    ext i j
    simp only [orthGraph, SimpleGraph.fromRel_adj, hp]
    constructor
    · rintro ⟨_,h | h⟩
      · exact h
      · exact h.symm
    · intro h; exact ⟨h.ne, Or.inl h⟩
  refine ⟨w, (fun i => G'.neighborFinset i), fun i => hnz (e i), ?_, ?_, ?_, ?_, ?_⟩
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
    have ht := (hli S.card hS f hf).comp es es.injective
    simpa [w, f, Function.comp_def] using ht
  · intro S hS a ha
    let es : (S : Set (Fin m)) ≃ Fin 5 := Fintype.equivFinOfCardEq (by simpa using hS)
    let f : Fin 5 → ι := fun q => e (es.symm q).val
    have hf : Function.Injective f := e.injective.comp
      (Subtype.val_injective.comp es.symm.injective)
    obtain ⟨q,hq⟩ := spanning_survivor _ (hspan f hf) a ha
    exact ⟨(es.symm q).val, (es.symm q).property, hq⟩

end P14ComplexSeedInterface
end


/- Source: cusp_assembly/Reused.lean. Reused authorship is retained in the source comments and artifact citations. -/
/- Reuses the kernel-checked Jig p14 proofs s75, s79, s80 and s81 by woshuajolk.
   Original verifier checkout: 2f467d409773c4471b81e08d26ed25c870836aa0.
   Only namespaces and imports of the reused source are changed. -/


namespace Submissions.CuspBilinearSeedFamilies.Assembly.CuspAllRankMinor

open scoped BigOperators

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

def CrossAdj {r N : ℕ} (i j : ZMod (2 * N)) : Prop :=
  (∃ c : Fin r, j = i + cOffset c) ∨
  (∃ d : Fin r, j = -i + dOffset d)

noncomputable def cuspProduct {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) : ℂ := by
  letI := h
  exact
    (∏ c : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c))) *
      (∏ d : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)))

lemma zeroPattern (r N : ℕ) (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    cuspProduct (r := r) h i j = 0 ↔ CrossAdj (r := r) i j := by
  letI := h
  simp only [cuspProduct, CrossAdj, mul_eq_zero, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero]
  simp only [ZMod.injective_stdAddChar.eq_iff]

def OffsetZ (r u : ℤ) : Prop :=
  (u % 2 = 1 ∧ 0 ≤ u ∧ u < 2 * r - 1) ∨ u = 2 * r + 1

def AdjQFZ (r N i j : ℤ) : Prop :=
  (i ≤ j ∧ (j - i) % 2 = 0 ∧ j - i < 2 * r) ∨
  (j < i ∧ (j + 2 * N - i) % 2 = 0 ∧ j + 2 * N - i < 2 * r) ∨
  OffsetZ r (j + i) ∨ OffsetZ r (j + i - 2 * N)

def rowZ (r N q : ℤ) : ℤ :=
  if q < r + 2 then q
  else if q - (r + 2) < 3 then 2 * N - r + 2 * (q - (r + 2))
  else 2 * N - r + (q - (r + 2)) + 2

def potentialZ (r q : ℤ) : ℤ :=
  if q < r + 2 then q
  else if q - (r + 2) < 3 then r - 2 * (q - (r + 2))
  else r - (q - (r + 2)) - 2

def colZ (r q : ℤ) : ℤ :=
  if q < r then 2 * r - 1 - q
  else if q = r then r - 4
  else if q = r + 1 then r - 2
  else if q - (r + 2) < 3 then r - 1 - 2 * (q - (r + 2))
  else r - (q - (r + 2)) - 3

def rankZ (r q : ℤ) : ℤ :=
  if q < r + 2 then
    if q < 2 then q
    else if r % 2 = 0 then
      if q % 2 = 1 then q
      else if q = r then 2 * r - 2
      else if q + 2 = r then 2 * r - 1
      else r + 1 + q
    else
      if q % 2 = 0 then r - 4 + q
      else if q = r then 2 * r - 2
      else if q + 2 = r then 2 * r - 1
      else q
  else
    let u := potentialZ r q
    if u % 2 = 0 then u
    else if r % 2 = 0 then r + 1 + u
    else r - 4 + u

set_option maxHeartbeats 10000000 in
lemma support_potential {r N q s : ℤ} (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (hq0 : 0 ≤ q) (hq : q < 2 * r) (hs0 : 0 ≤ s) (hs : s < 2 * r)
    (hnon : ¬ AdjQFZ r N (rowZ r N q) (colZ r s)) :
    q = s ∨ rankZ r s < rankZ r q := by
  by_contra hbad
  push Not at hbad
  apply hnon
  simp only [AdjQFZ, OffsetZ, rowZ, colZ, rankZ, potentialZ] at *
  split_ifs at * <;> omega

set_option maxHeartbeats 10000000 in
lemma diagonal_nonadj {r N q : ℤ} (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (hq0 : 0 ≤ q) (hq : q < 2 * r) :
    ¬ AdjQFZ r N (rowZ r N q) (colZ r q) := by
  simp only [AdjQFZ, OffsetZ, rowZ, colZ]
  split_ifs <;> omega

lemma direct_translate {r N i j : ℕ} (hij : i ≤ j)
    (heven : ((j : ℤ) - i) % 2 = 0) (hsmall : (j : ℤ) - i < 2 * r) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  have hevenN : (j - i) % 2 = 0 := by omega
  let a := (j - i) / 2
  have ha : a < r := by
    dsimp [a]
    omega
  left
  refine ⟨⟨a, ha⟩, ?_⟩
  have hj : j = i + 2 * a := by
    dsimp [a]
    omega
  simp only [cOffset]
  rw [hj]
  simp

lemma wrapped_translate {r N i j : ℕ} (hi : i < 2 * N) (hji : j < i)
    (heven : (((j + 2 * N : ℕ) : ℤ) - i) % 2 = 0)
    (hsmall : ((j + 2 * N : ℕ) : ℤ) - i < 2 * r) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  have hevenN : (j + 2 * N - i) % 2 = 0 := by omega
  let a := (j + 2 * N - i) / 2
  have ha : a < r := by
    dsimp [a]
    omega
  have heq : j + 2 * N = i + 2 * a := by
    dsimp [a]
    omega
  left
  refine ⟨⟨a, ha⟩, ?_⟩
  simp only [cOffset]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) heq
  simpa using hz

lemma direct_anti_regular {r N i j : ℕ}
    (hodd : (((j + i : ℕ) : ℤ) % 2) = 1)
    (hsmall : (j + i : ℤ) < 2 * r - 1) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  have hoddN : (j + i) % 2 = 1 := by omega
  let b := (j + i - 1) / 2
  have hb : b + 1 < r := by
    dsimp [b]
    omega
  have hsum : j + i = 2 * b + 1 := by
    dsimp [b]
    omega
  right
  refine ⟨⟨b, by omega⟩, ?_⟩
  have hif : ¬ b + 1 = r := by omega
  simp only [dOffset, hif, if_false, Nat.add_zero]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) hsum
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
  linear_combination hz

lemma direct_anti_special {r N i j : ℕ} (hr : 1 ≤ r)
    (hsum : j + i = 2 * r + 1) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  right
  let d : Fin r := ⟨r - 1, by omega⟩
  refine ⟨d, ?_⟩
  have hd : d.val + 1 = r := by
    dsimp [d]
    omega
  simp only [dOffset, hd, if_true]
  dsimp [d]
  have hoff : 2 * (r - 1) + 1 + 2 = 2 * r + 1 := by omega
  rw [hoff]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) hsum
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
  linear_combination hz

lemma wrapped_anti_regular {r N i j : ℕ} (hle : 2 * N ≤ j + i)
    (hodd : (((j + i : ℕ) : ℤ) - 2 * N) % 2 = 1)
    (hsmall : ((j + i : ℕ) : ℤ) - 2 * N < 2 * r - 1) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  have hoddN : (j + i - 2 * N) % 2 = 1 := by omega
  let b := (j + i - 2 * N - 1) / 2
  have hb : b + 1 < r := by
    dsimp [b]
    omega
  have hsum : j + i = 2 * b + 1 + 2 * N := by
    dsimp [b]
    omega
  right
  refine ⟨⟨b, by omega⟩, ?_⟩
  have hif : ¬ b + 1 = r := by omega
  simp only [dOffset, hif, if_false, Nat.add_zero]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) hsum
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
  have hn : (2 : ZMod (2 * N)) * (N : ZMod (2 * N)) = 0 := by
    have hzmod : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := by simp
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hzmod
  linear_combination hz + hn

lemma wrapped_anti_special {r N i j : ℕ} (hr : 1 ≤ r)
    (hsum : j + i = 2 * r + 1 + 2 * N) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  right
  let d : Fin r := ⟨r - 1, by omega⟩
  refine ⟨d, ?_⟩
  have hd : d.val + 1 = r := by
    dsimp [d]
    omega
  simp only [dOffset, hd, if_true]
  dsimp [d]
  have hoff : 2 * (r - 1) + 1 + 2 = 2 * r + 1 := by omega
  rw [hoff]
  have hz := congrArg (fun x : ℕ => (x : ZMod (2 * N))) hsum
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
  have hn : (2 : ZMod (2 * N)) * (N : ZMod (2 * N)) = 0 := by
    have hzmod : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := by simp
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hzmod
  linear_combination hz + hn

lemma adjQF_crossAdj {r N i j : ℕ} (hr : 1 ≤ r) (hi : i < 2 * N)
    (h : AdjQFZ r N i j) :
    CrossAdj (r := r) (N := N) (i : ZMod (2 * N)) (j : ZMod (2 * N)) := by
  simp only [AdjQFZ, OffsetZ, Int.natCast_add, Int.natCast_mul] at h
  rcases h with h | h | h | h
  · exact direct_translate (by omega) h.2.1 h.2.2
  · exact wrapped_translate hi (by omega) h.2.1 h.2.2
  · rcases h with h | h
    · exact direct_anti_regular h.1 h.2.2
    · exact direct_anti_special hr (by omega)
  · rcases h with h | h
    · apply wrapped_anti_regular (by omega) h.1
      omega
    · exact wrapped_anti_special hr (by omega)

lemma crossAdj_adjQF {r N i j : ℕ} (hr : 1 ≤ r) (hN : r + 2 ≤ N)
    (hi : i < 2 * N) (hj : j < 2 * N)
    (h : CrossAdj (r := r) (N := N)
      (i : ZMod (2 * N)) (j : ZMod (2 * N))) :
    AdjQFZ r N i j := by
  rcases h with ⟨c, hc⟩ | ⟨d, hd⟩
  · have heq : (j : ZMod (2 * N)) = ((i + 2 * c.val : ℕ) : ZMod (2 * N)) := by
      simpa only [cOffset, Nat.cast_add] using hc
    have hmod := (ZMod.natCast_eq_natCast_iff' j (i + 2 * c.val) (2 * N)).mp heq
    have hc_lt : c.val < r := c.isLt
    simp only [AdjQFZ, OffsetZ]
    by_cases hw : i + 2 * c.val < 2 * N
    · left
      have hj_eq : j = i + 2 * c.val := by
        rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hw] at hmod
        exact hmod
      omega
    · right; left
      have hsum : i + 2 * c.val < 2 * (2 * N) := by omega
      have hj_eq : j + 2 * N = i + 2 * c.val := by
        rw [Nat.mod_eq_of_lt hj] at hmod
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hw)] at hmod
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
      omega
  · have hsumz :
        (j + i : ZMod (2 * N)) = dOffset (r := r) (N := N) d := by
      linear_combination hd
    let off : ℕ := 2 * d.val + 1 + if d.val + 1 = r then 2 else 0
    have heq : ((j + i : ℕ) : ZMod (2 * N)) = (off : ZMod (2 * N)) := by
      simpa only [off, dOffset, Nat.cast_add] using hsumz
    have hmod := (ZMod.natCast_eq_natCast_iff' (j + i) off (2 * N)).mp heq
    have hd_lt : d.val < r := d.isLt
    have hoff_lt : off < 2 * N := by
      simp only [off]
      split_ifs <;> omega
    have hoff_shape :
        (off % 2 = 1 ∧ off < 2 * r - 1) ∨ off = 2 * r + 1 := by
      simp only [off]
      split_ifs <;> omega
    simp only [AdjQFZ, OffsetZ]
    right; right
    by_cases hw : j + i < 2 * N
    · left
      have hji : j + i = off := by
        rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hoff_lt] at hmod
        exact hmod
      rcases hoff_shape with hs | hs
      · left; omega
      · right; omega
    · right
      have hsum : j + i < 2 * (2 * N) := by omega
      have hji : j + i = off + 2 * N := by
        rw [Nat.mod_eq_of_lt hoff_lt] at hmod
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hw)] at hmod
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
      rcases hoff_shape with hs | hs
      · left; omega
      · right; omega

def rowN (r N q : ℕ) : ℕ :=
  if q < r + 2 then q
  else if q - (r + 2) < 3 then 2 * N - r + 2 * (q - (r + 2))
  else 2 * N - r + (q - (r + 2)) + 2

def colN (r q : ℕ) : ℕ :=
  if q < r then 2 * r - 1 - q
  else if q = r then r - 4
  else if q = r + 1 then r - 2
  else if q - (r + 2) < 3 then r - 1 - 2 * (q - (r + 2))
  else r - (q - (r + 2)) - 3

lemma rowN_lt {r N q : ℕ} (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (hq : q < 2 * r) : rowN r N q < 2 * N := by
  simp only [rowN]
  split_ifs <;> omega

lemma colN_lt {r q : ℕ} (hr : 4 ≤ r) (hq : q < 2 * r) :
    colN r q < 2 * r := by
  simp only [colN]
  split_ifs <;> omega

lemma rowN_cast {r N q : ℕ} (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (hq : q < 2 * r) :
    (rowN r N q : ℤ) = rowZ r N q := by
  simp only [rowN, rowZ]
  split_ifs <;> omega

lemma colN_cast {r q : ℕ} (hr : 4 ≤ r) (hq : q < 2 * r) :
    (colN r q : ℤ) = colZ r q := by
  simp only [colN, colZ]
  split_ifs <;> omega

noncomputable def cuspMatrix (r N : ℕ) (h : NeZero (2 * N)) :
    Matrix (Fin (2 * r)) (Fin (2 * r)) ℂ := fun q s =>
  cuspProduct (r := r) h
    (rowN r N q.val : ZMod (2 * N))
    (colN r s.val : ZMod (2 * N))

lemma det_ne_zero_of_unique_matching {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (σ : Equiv.Perm n)
    (hσ : ∀ i, M (σ i) i ≠ 0)
    (hunique : ∀ τ : Equiv.Perm n, τ ≠ σ → ∃ i, M (τ i) i = 0) :
    M.det ≠ 0 := by
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_single σ]
  · apply (smul_ne_zero_iff_ne _).2
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hσ i)
  · intro τ hτ hne
    obtain ⟨i, hi⟩ := hunique τ hne
    have hp : ∏ j, M (τ j) j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hp, smul_zero]
  · simp

lemma det_ne_zero_of_potential {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (p : n → ℤ)
    (hdiag : ∀ i, M i i ≠ 0)
    (hoff : ∀ i j, M i j ≠ 0 → i = j ∨ p j < p i) :
    M.det ≠ 0 := by
  apply det_ne_zero_of_unique_matching M 1 hdiag
  intro τ hτ
  by_contra hall
  push Not at hall
  have hcases : ∀ i, τ i = i ∨ p i < p (τ i) := by
    intro i
    rcases hoff (τ i) i (hall i) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hle : ∀ i ∈ Finset.univ, p i ≤ p (τ i) := by
    intro i hi
    rcases hcases i with h | h
    · simp [h]
    · exact h.le
  have hstrict : ∃ i ∈ Finset.univ, p i < p (τ i) := by
    by_contra h
    push Not at h
    apply hτ
    ext i
    rcases hcases i with hi | hi
    · exact hi
    · exact False.elim (not_le_of_gt hi (h i (Finset.mem_univ i)))
  have hsum : ∑ i, p i < ∑ i, p (τ i) :=
    Finset.sum_lt_sum hle hstrict
  rw [← Equiv.sum_comp τ] at hsum
  exact (lt_irrefl _ hsum)

theorem proof (r N : ℕ) (hr : 4 ≤ r) (hN : r + 2 ≤ N)
    (h : NeZero (2 * N)) : (cuspMatrix r N h).det ≠ 0 := by
  apply det_ne_zero_of_potential (cuspMatrix r N h)
    (fun q => rankZ r q.val)
  · intro q hzero
    have hadj := (zeroPattern r N h
      (rowN r N q.val : ZMod (2 * N))
      (colN r q.val : ZMod (2 * N))).mp hzero
    have hqf := crossAdj_adjQF (by omega) hN
      (rowN_lt hr hN q.isLt)
      ((colN_lt hr q.isLt).trans (by omega)) hadj
    rw [rowN_cast hr hN q.isLt, colN_cast hr q.isLt] at hqf
    exact diagonal_nonadj (by exact_mod_cast hr) (by exact_mod_cast hN)
      (by positivity) (by exact_mod_cast q.isLt) hqf
  · intro q s hnz
    by_cases hqs : q = s
    · exact Or.inl hqs
    right
    have hnotcross : ¬ CrossAdj (r := r) (N := N)
        (rowN r N q.val : ZMod (2 * N))
        (colN r s.val : ZMod (2 * N)) := by
      intro hadj
      apply hnz
      exact (zeroPattern r N h _ _).mpr hadj
    have hnotqf : ¬ AdjQFZ r N (rowN r N q.val) (colN r s.val) := by
      intro hqf
      apply hnotcross
      exact adjQF_crossAdj (by omega) (rowN_lt hr hN q.isLt) hqf
    rw [rowN_cast hr hN q.isLt, colN_cast hr s.isLt] at hnotqf
    rcases support_potential (by exact_mod_cast hr) (by exact_mod_cast hN)
      (by positivity) (by exact_mod_cast q.isLt)
      (by positivity) (by exact_mod_cast s.isLt) hnotqf with h | h
    · exact False.elim (hqs (Fin.ext (by exact_mod_cast h)))
    · exact h


def row2 (q : Fin 4) : ℕ := q.val

def col2 (q : Fin 4) : ℕ := ![3, 2, 0, 4] q

def pot2 (q : Fin 4) : ℤ := ![2, 0, 0, 1] q

noncomputable def matrix2 (N : ℕ) (h : NeZero (2 * N)) :
    Matrix (Fin 4) (Fin 4) ℂ := fun q s =>
  cuspProduct (r := 2) h
    (row2 q : ZMod (2 * N)) (col2 s : ZMod (2 * N))

lemma row2_lt {N : ℕ} (hN : 4 ≤ N) (q : Fin 4) : row2 q < 2 * N := by
  simp [row2]
  omega

lemma col2_lt {N : ℕ} (hN : 4 ≤ N) (q : Fin 4) : col2 q < 2 * N := by
  fin_cases q <;> simp [col2] <;> omega

lemma diag2 {N : ℕ} (hN : 4 ≤ N) (q : Fin 4) :
    ¬ AdjQFZ 2 N (row2 q) (col2 q) := by
  fin_cases q <;> simp [AdjQFZ, OffsetZ, row2, col2] <;> omega

lemma support2 {N : ℕ} (hN : 4 ≤ N) (q s : Fin 4)
    (hnon : ¬ AdjQFZ 2 N (row2 q) (col2 s)) :
    q = s ∨ pot2 s < pot2 q := by
  fin_cases q <;> fin_cases s <;>
    simp [AdjQFZ, OffsetZ, row2, col2, pot2] at hnon ⊢ <;> omega

theorem minor2 (N : ℕ) (hN : 4 ≤ N) (h : NeZero (2 * N)) :
    (matrix2 N h).det ≠ 0 := by
  apply det_ne_zero_of_potential (matrix2 N h) pot2
  · intro q hzero
    have hadj := (zeroPattern 2 N h
      (row2 q : ZMod (2 * N)) (col2 q : ZMod (2 * N))).mp hzero
    have hqf := crossAdj_adjQF (r := 2) (N := N) (by omega) (by omega)
      (row2_lt hN q) (col2_lt hN q) hadj
    exact diag2 hN q hqf
  · intro q s hnz
    have hnotqf : ¬ AdjQFZ 2 N (row2 q) (col2 s) := by
      intro hqf
      apply hnz
      apply (zeroPattern 2 N h _ _).mpr
      exact adjQF_crossAdj (r := 2) (N := N) (by omega)
        (row2_lt hN q) hqf
    exact support2 hN q s hnotqf

def row3small (q : Fin 6) : ℕ := ![0, 1, 2, 3, 4, 7] q

def col3small (q : Fin 6) : ℕ := ![5, 4, 7, 1, 0, 2] q

def pot3small (q : Fin 6) : ℤ := ![0, 5, 4, 2, 3, 1] q

noncomputable def matrix3small (h : NeZero 10) :
    Matrix (Fin 6) (Fin 6) ℂ := fun q s =>
  cuspProduct (r := 3) (N := 5) h
    (row3small q : ZMod 10) (col3small s : ZMod 10)

lemma diag3small (q : Fin 6) :
    ¬ AdjQFZ 3 5 (row3small q) (col3small q) := by
  fin_cases q <;> simp [AdjQFZ, OffsetZ, row3small, col3small]

lemma support3small (q s : Fin 6)
    (hnon : ¬ AdjQFZ 3 5 (row3small q) (col3small s)) :
    q = s ∨ pot3small s < pot3small q := by
  fin_cases q <;> fin_cases s <;>
    simp [AdjQFZ, OffsetZ, row3small, col3small, pot3small] at hnon ⊢

theorem minor3small (h : NeZero 10) : (matrix3small h).det ≠ 0 := by
  apply det_ne_zero_of_potential (matrix3small h) pot3small
  · intro q hzero
    have hadj := (zeroPattern 3 5 h
      (row3small q : ZMod 10) (col3small q : ZMod 10)).mp hzero
    have hqf := crossAdj_adjQF (r := 3) (N := 5) (by omega) (by omega)
      (by fin_cases q <;> simp [row3small])
      (by fin_cases q <;> simp [col3small]) hadj
    exact diag3small q hqf
  · intro q s hnz
    have hnotqf : ¬ AdjQFZ 3 5 (row3small q) (col3small s) := by
      intro hqf
      apply hnz
      apply (zeroPattern 3 5 h _ _).mpr
      exact adjQF_crossAdj (r := 3) (N := 5) (by omega)
        (by fin_cases q <;> simp [row3small]) hqf
    exact support3small q s hnotqf

def row3large (N : ℕ) (q : Fin 6) : ℕ := ![0, 1, 2, 3, 4, 2 * N - 2] q

def col3large (q : Fin 6) : ℕ := ![5, 4, 3, 2, 0, 1] q

def pot3large (q : Fin 6) : ℤ := ![0, 0, 4, 2, 3, 1] q

noncomputable def matrix3large (N : ℕ) (h : NeZero (2 * N)) :
    Matrix (Fin 6) (Fin 6) ℂ := fun q s =>
  cuspProduct (r := 3) h
    (row3large N q : ZMod (2 * N)) (col3large s : ZMod (2 * N))

lemma row3large_lt {N : ℕ} (hN : 6 ≤ N) (q : Fin 6) :
    row3large N q < 2 * N := by
  fin_cases q <;> simp [row3large] <;> omega

lemma col3large_lt {N : ℕ} (hN : 6 ≤ N) (q : Fin 6) :
    col3large q < 2 * N := by
  fin_cases q <;> simp [col3large] <;> omega

lemma diag3large {N : ℕ} (hN : 6 ≤ N) (q : Fin 6) :
    ¬ AdjQFZ 3 N (row3large N q) (col3large q) := by
  fin_cases q <;> simp [AdjQFZ, OffsetZ, row3large, col3large] <;> omega

lemma support3large {N : ℕ} (hN : 6 ≤ N) (q s : Fin 6)
    (hnon : ¬ AdjQFZ 3 N (row3large N q) (col3large s)) :
    q = s ∨ pot3large s < pot3large q := by
  fin_cases q <;> fin_cases s <;>
    simp [AdjQFZ, OffsetZ, row3large, col3large, pot3large] at hnon ⊢ <;> omega

theorem minor3large (N : ℕ) (hN : 6 ≤ N) (h : NeZero (2 * N)) :
    (matrix3large N h).det ≠ 0 := by
  apply det_ne_zero_of_potential (matrix3large N h) pot3large
  · intro q hzero
    have hadj := (zeroPattern 3 N h
      (row3large N q : ZMod (2 * N))
      (col3large q : ZMod (2 * N))).mp hzero
    have hqf := crossAdj_adjQF (r := 3) (N := N) (by omega) (by omega)
      (row3large_lt hN q) (col3large_lt hN q) hadj
    exact diag3large hN q hqf
  · intro q s hnz
    have hnotqf : ¬ AdjQFZ 3 N (row3large N q) (col3large s) := by
      intro hqf
      apply hnz
      apply (zeroPattern 3 N h _ _).mpr
      exact adjQF_crossAdj (r := 3) (N := N) (by omega)
        (row3large_lt hN q) hqf
    exact support3large hN q s hnotqf

theorem allRank (r N : ℕ) (hr : 2 ≤ r) (hN : r + 2 ≤ N)
    (h : NeZero (2 * N)) :
    ∃ row col : Fin (2 * r) → ℕ,
      (∀ q, row q < 2 * N ∧ col q < 2 * N) ∧
      (Matrix.of fun q s => cuspProduct (r := r) h
        (row q : ZMod (2 * N)) (col s : ZMod (2 * N))).det ≠ 0 := by
  by_cases hr2 : r = 2
  · subst r
    refine ⟨row2, col2, ?_, ?_⟩
    · intro q
      exact ⟨row2_lt hN q, col2_lt hN q⟩
    · exact minor2 N hN h
  by_cases hr3 : r = 3
  · subst r
    by_cases hN5 : N = 5
    · subst N
      refine ⟨row3small, col3small, ?_, ?_⟩
      · intro q
        fin_cases q <;> simp [row3small, col3small]
      · exact minor3small h
    · have hN6 : 6 ≤ N := by omega
      refine ⟨row3large N, col3large, ?_, ?_⟩
      · intro q
        exact ⟨row3large_lt hN6 q, col3large_lt hN6 q⟩
      · exact minor3large N hN6 h
  · have hr4 : 4 ≤ r := by omega
    refine ⟨fun q => rowN r N q.val, fun q => colN r q.val, ?_, ?_⟩
    · intro q
      exact ⟨rowN_lt hr4 hN q.isLt,
        (colN_lt hr4 q.isLt).trans (by omega)⟩
    · exact proof r N hr4 hN h


end Submissions.CuspBilinearSeedFamilies.Assembly.CuspAllRankMinor



namespace Submissions.CuspBilinearSeedFamilies.Assembly.CuspBiClutchedFactorization

open Polynomial
open scoped BigOperators

noncomputable def clutch (k : ℕ) (tau z : ℂ) : Fin k → ℂ := fun q =>
  if q.val = 0 then 1 + tau * z ^ k else z ^ q.val

lemma polynomial_eq_folded {k : ℕ} (hk : 1 ≤ k) (tau : ℂ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ k) (htop : P.coeff k = tau * P.coeff 0) :
    P = Polynomial.ofFn k (fun q => P.coeff q.val) +
      Polynomial.C (tau * P.coeff 0) * Polynomial.X ^ k := by
  ext m
  by_cases hm : m < k
  · rw [Polynomial.coeff_add, Polynomial.ofFn_coeff_eq_val_of_lt _ hm,
      Polynomial.coeff_C_mul_X_pow]
    simp [Nat.ne_of_lt hm]
  · have hkm : k ≤ m := Nat.le_of_not_gt hm
    rw [Polynomial.coeff_add, Polynomial.ofFn_coeff_eq_zero_of_ge _ hkm,
      zero_add, Polynomial.coeff_C_mul_X_pow]
    by_cases hmk : m = k
    · subst m
      simp [htop]
    · have hzero : P.coeff m = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [hmk, hzero]

lemma eval_eq_clutch_sum {k : ℕ} (hk : 1 ≤ k) (tau z : ℂ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ k) (htop : P.coeff k = tau * P.coeff 0) :
    P.eval z = ∑ q : Fin k, P.coeff q.val * clutch k tau z q := by
  have hP := polynomial_eq_folded hk tau P hdeg htop
  conv_lhs => rw [hP]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, clutch]
  let q0 : Fin k := ⟨0, hk⟩
  have hsplit (f : Fin k → ℂ) :
      ∑ q, f q = f q0 + ∑ q ∈ Finset.univ.erase q0, f q := by
    exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ q0)).symm
  rw [hsplit (fun q => P.coeff q.val * z ^ q.val),
    hsplit (fun q => P.coeff q.val *
      (if q.val = 0 then 1 + tau * z ^ k else z ^ q.val))]
  simp only [q0, pow_zero, mul_one, if_pos]
  have hrest :
      ∑ q ∈ Finset.univ.erase q0, P.coeff q.val * z ^ q.val =
        ∑ q ∈ Finset.univ.erase q0,
          P.coeff q.val *
            (if q.val = 0 then 1 + tau * z ^ k else z ^ q.val) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : q ≠ q0 := by simpa using hq
    have hqv : q.val ≠ 0 := fun h => hq0 (Fin.ext (by simpa [q0] using h))
    simp [hqv]
  rw [← hrest]
  ring

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) := (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

noncomputable def cuspProduct {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) : ℂ := by
  letI := h
  exact
    (∏ c : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c))) *
      (∏ d : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)))

noncomputable def directPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar j) -
    C (ZMod.stdAddChar (cOffset (r := r) (N := N) c)) * X

noncomputable def antiPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar j) * X -
    C (ZMod.stdAddChar (dOffset (r := r) (N := N) d))

noncomputable def cuspPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) : ℂ[X] :=
  (∏ c : Fin r, directPoly (r := r) (N := N) j c) *
    (∏ d : Fin r, antiPoly (r := r) (N := N) j d)

lemma anti_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (d : Fin r) :
    (antiPoly j d).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar i *
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)) := by
  simp only [antiPoly, eval_sub, eval_mul, eval_C, eval_X]
  rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  have hi : ZMod.stdAddChar i ≠ 0 := by simp [ZMod.stdAddChar_apply]
  field_simp

lemma direct_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (c : Fin r) :
    (directPoly j c).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c) := by
  simp [directPoly, AddChar.map_add_eq_mul]
  ring

lemma cuspPoly_eval {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j := by
  letI := h
  simp only [cuspPoly, eval_mul, eval_prod, direct_eval, anti_eval, cuspProduct]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma char_ne_zero {N : ℕ} [NeZero N] (i : ZMod N) :
    ZMod.stdAddChar i ≠ 0 := by
  simp [ZMod.stdAddChar_apply]

lemma direct_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) : (directPoly j c).natDegree = 1 := by
  have hc : ZMod.stdAddChar (cOffset (r := r) (N := N) c) ≠ 0 :=
    char_ne_zero _
  have hterm :
      (C (ZMod.stdAddChar (cOffset (r := r) (N := N) c)) * X).natDegree = 1 := by
    rw [natDegree_mul]
    · simp
    · exact C_ne_zero.mpr hc
    · exact (X_ne_zero : (X : ℂ[X]) ≠ 0)
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans (by simp [directPoly, hterm])
  · simp [directPoly, char_ne_zero]

lemma anti_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) : (antiPoly j d).natDegree = 1 := by
  simp [antiPoly, char_ne_zero]

lemma direct_leadingCoeff {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) :
    (directPoly j c).leadingCoeff =
      -ZMod.stdAddChar (cOffset (r := r) (N := N) c) := by
  rw [← coeff_natDegree, direct_natDegree]
  simp [directPoly]

lemma anti_leadingCoeff {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) :
    (antiPoly j d).leadingCoeff = ZMod.stdAddChar j := by
  rw [← coeff_natDegree, anti_natDegree]
  simp [antiPoly]

lemma cuspPoly_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) : (cuspPoly (r := r) j).natDegree = 2 * r := by
  have hc (c : Fin r) : directPoly j c ≠ 0 := by
    intro hz
    have hdeg := direct_natDegree j c
    simp [hz] at hdeg
  have hd (d : Fin r) : antiPoly j d ≠ 0 := by
    intro hz
    have hdeg := anti_natDegree j d
    simp [hz] at hdeg
  have hcprod : (∏ c : Fin r, directPoly j c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => hc c)
  have hdprod : (∏ d : Fin r, antiPoly j d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun d _ => hd d)
  simp only [cuspPoly]
  rw [natDegree_mul hcprod hdprod,
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun c : Fin r => directPoly j c) (fun c _ => hc c),
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun d : Fin r => antiPoly j d) (fun d _ => hd d)]
  simp [direct_natDegree, anti_natDegree]
  omega

noncomputable def cLead (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  ∏ c : Fin r, -ZMod.stdAddChar (cOffset (N := N) c)

noncomputable def dConst (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  ∏ d : Fin r, -ZMod.stdAddChar (dOffset (N := N) d)

noncomputable def tauZ (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  cLead r N / dConst r N

lemma cLead_ne_zero (r N : ℕ) [NeZero (2 * N)] : cLead r N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro c hc
  simp [char_ne_zero]

lemma dConst_ne_zero (r N : ℕ) [NeZero (2 * N)] : dConst r N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro d hd
  simp [char_ne_zero]

lemma cuspPoly_coeff_zero {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff 0 = ZMod.stdAddChar j ^ r * dConst r N := by
  rw [coeff_zero_eq_eval_zero]
  simp only [cuspPoly, eval_mul, eval_prod, directPoly, antiPoly,
    eval_sub, eval_C, eval_mul, eval_X, mul_zero, sub_zero, zero_mul, zero_sub]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma cuspPoly_coeff_top {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff (2 * r) = cLead r N * ZMod.stdAddChar j ^ r := by
  rw [← cuspPoly_natDegree j, coeff_natDegree]
  simp only [cuspPoly, leadingCoeff_mul, Polynomial.leadingCoeff_prod,
    direct_leadingCoeff, anti_leadingCoeff, cLead]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma cuspPoly_boundary {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff (2 * r) =
      tauZ r N * (cuspPoly (r := r) j).coeff 0 := by
  rw [cuspPoly_coeff_top, cuspPoly_coeff_zero]
  unfold tauZ
  field_simp [dConst_ne_zero]

theorem cusp_left_clutch {r N : ℕ} (hr : 1 ≤ r) (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
      ∑ q : Fin (2 * r),
        (cuspPoly (r := r) j).coeff q.val *
          clutch (2 * r) (tauZ r N)
            (ZMod.stdAddChar i) q := by
  letI := h
  rw [← cuspPoly_eval h i j]
  apply eval_eq_clutch_sum
  · omega
  · rw [cuspPoly_natDegree]
  · exact cuspPoly_boundary j

noncomputable def rightDirect {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (c : Fin r) : ℂ[X] :=
  X - C (ZMod.stdAddChar (cOffset (r := r) (N := N) c) * ZMod.stdAddChar i)

noncomputable def rightAnti {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (d : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar i) * X -
    C (ZMod.stdAddChar (dOffset (r := r) (N := N) d))

noncomputable def rightPoly {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) : ℂ[X] :=
  (∏ c : Fin r, rightDirect (r := r) (N := N) i c) *
    (∏ d : Fin r, rightAnti (r := r) (N := N) i d)

lemma rightDirect_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (c : Fin r) :
    (rightDirect i c).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c) := by
  simp [rightDirect, AddChar.map_add_eq_mul]
  ring

lemma rightAnti_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (d : Fin r) :
    (rightAnti i d).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar i *
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)) := by
  simp only [rightAnti, eval_sub, eval_mul, eval_C, eval_X]
  rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  have hi : ZMod.stdAddChar i ≠ 0 := char_ne_zero i
  field_simp

lemma rightPoly_eval {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    (rightPoly (r := r) i).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j := by
  letI := h
  simp only [rightPoly, eval_mul, eval_prod, rightDirect_eval, rightAnti_eval,
    cuspProduct]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma rightDirect_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (c : Fin r) : (rightDirect i c).natDegree = 1 := by
  simpa only [rightDirect] using
    (natDegree_X_sub_C
      (ZMod.stdAddChar (cOffset (r := r) (N := N) c) * ZMod.stdAddChar i))

lemma rightAnti_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (d : Fin r) : (rightAnti i d).natDegree = 1 := by
  simp [rightAnti, char_ne_zero]

lemma rightPoly_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) : (rightPoly (r := r) i).natDegree = 2 * r := by
  have hc (c : Fin r) : rightDirect i c ≠ 0 := by
    intro hz
    have hdeg := rightDirect_natDegree i c
    simp [hz] at hdeg
  have hd (d : Fin r) : rightAnti i d ≠ 0 := by
    intro hz
    have hdeg := rightAnti_natDegree i d
    simp [hz] at hdeg
  have hcprod : (∏ c : Fin r, rightDirect i c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => hc c)
  have hdprod : (∏ d : Fin r, rightAnti i d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun d _ => hd d)
  simp only [rightPoly]
  rw [natDegree_mul hcprod hdprod,
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun c : Fin r => rightDirect i c) (fun c _ => hc c),
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun d : Fin r => rightAnti i d) (fun d _ => hd d)]
  simp [rightDirect_natDegree, rightAnti_natDegree]
  omega

noncomputable def tauX (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  (cLead r N * dConst r N)⁻¹

lemma rightPoly_coeff_zero {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff 0 =
      cLead r N * dConst r N * ZMod.stdAddChar i ^ r := by
  rw [coeff_zero_eq_eval_zero]
  simp only [rightPoly, eval_mul, eval_prod, rightDirect, rightAnti,
    eval_sub, eval_X, eval_C, zero_mul, zero_sub, mul_zero, cLead, dConst]
  simp_rw [show ∀ c : Fin r,
    -(ZMod.stdAddChar (cOffset (N := N) c) * ZMod.stdAddChar i) =
      (-ZMod.stdAddChar (cOffset (N := N) c)) * ZMod.stdAddChar i by
        intro c; ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma rightPoly_coeff_top {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff (2 * r) = ZMod.stdAddChar i ^ r := by
  rw [← rightPoly_natDegree i, coeff_natDegree]
  simp only [rightPoly, leadingCoeff_mul, Polynomial.leadingCoeff_prod]
  have hc : ∀ c : Fin r, (rightDirect i c).leadingCoeff = 1 := by
    intro c
    rw [← coeff_natDegree, rightDirect_natDegree]
    simp [rightDirect]
  have hd : ∀ d : Fin r, (rightAnti i d).leadingCoeff = ZMod.stdAddChar i := by
    intro d
    rw [← coeff_natDegree, rightAnti_natDegree]
    simp [rightAnti]
  simp_rw [hc, hd]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp

lemma rightPoly_boundary {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff (2 * r) =
      tauX r N * (rightPoly (r := r) i).coeff 0 := by
  rw [rightPoly_coeff_top, rightPoly_coeff_zero]
  unfold tauX
  field_simp [cLead_ne_zero r N, dConst_ne_zero r N]

theorem cusp_right_clutch {r N : ℕ} (hr : 1 ≤ r) (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
      ∑ q : Fin (2 * r),
        (rightPoly (r := r) i).coeff q.val *
          clutch (2 * r) (tauX r N)
            (ZMod.stdAddChar j) q := by
  letI := h
  rw [← rightPoly_eval h i j]
  apply eval_eq_clutch_sum
  · omega
  · rw [rightPoly_natDegree]
  · exact rightPoly_boundary i

theorem proof :
    ∀ (r N : ℕ), 1 ≤ r → ∀ h : NeZero (2 * N),
      ∃ (tauL tauR : ℂ)
        (L R : ZMod (2 * N) → Fin (2 * r) → ℂ),
        tauL ≠ 0 ∧ tauR ≠ 0 ∧
        ∀ i j : ZMod (2 * N),
          (ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
            ∑ q, L j q * clutch (2 * r) tauL (ZMod.stdAddChar i) q) ∧
          (ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
            ∑ q, R i q * clutch (2 * r) tauR (ZMod.stdAddChar j) q) := by
  intro r N hr h
  letI := h
  refine ⟨tauZ r N, tauX r N,
    fun j q => (cuspPoly (r := r) j).coeff q.val,
    fun i q => (rightPoly (r := r) i).coeff q.val, ?_, ?_, ?_⟩
  · exact div_ne_zero (cLead_ne_zero r N) (dConst_ne_zero r N)
  · exact inv_ne_zero (mul_ne_zero (cLead_ne_zero r N) (dConst_ne_zero r N))
  · intro i j
    exact ⟨cusp_left_clutch hr h i j, cusp_right_clutch hr h i j⟩

end Submissions.CuspBilinearSeedFamilies.Assembly.CuspBiClutchedFactorization


namespace Submissions.CuspBilinearSeedFamilies.Assembly.ClutchedVandermondeRanks

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

end Submissions.CuspBilinearSeedFamilies.Assembly.ClutchedVandermondeRanks


namespace Submissions.CuspBilinearSeedFamilies.Assembly.BifactorizationGlue

open scoped BigOperators

universe u v w

theorem proof
    {ι : Type u} {κ : Type v} {ϕ : Type w}
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ϕ ℂ)
    (D : Matrix ι κ ℂ) (X : Matrix κ ϕ ℂ)
    (C : Matrix ι ϕ ℂ)
    (f : κ → ι) (g : κ → ϕ)
    (hAB : C = A * B) (hDX : C = D * X)
    (hdet : (C.submatrix f g).det ≠ 0) :
    ∃ G : Matrix κ κ ℂ, G.det ≠ 0 ∧ C = A * (G * X) := by
  let Ar : Matrix κ κ ℂ := A.submatrix f id
  let Bs : Matrix κ κ ℂ := B.submatrix id g
  let Dr : Matrix κ κ ℂ := D.submatrix f id
  let Xs : Matrix κ κ ℂ := X.submatrix id g
  have hCselAB : C.submatrix f g = Ar * Bs := by
    rw [hAB]
    ext a b
    simp [Ar, Bs, Matrix.mul_apply]
  have hCselDX : C.submatrix f g = Dr * Xs := by
    rw [hDX]
    ext a b
    simp [Dr, Xs, Matrix.mul_apply]
  have hprodAB : Ar.det * Bs.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hCselAB]
    exact hdet
  have hprodDX : Dr.det * Xs.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hCselDX]
    exact hdet
  have hAr : IsUnit Ar.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodAB).1
  have hBs : IsUnit Bs.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodAB).2
  have hXs : IsUnit Xs.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodDX).2
  have hrows : Ar * B = Dr * X := by
    ext a j
    have hij := congrArg (fun M : Matrix ι ϕ ℂ => M (f a) j)
      (hAB.symm.trans hDX)
    simpa [Ar, Dr, Matrix.mul_apply] using hij
  have hselected : Ar * Bs = Dr * Xs := hCselAB.symm.trans hCselDX
  let G : Matrix κ κ ℂ := Bs * Xs⁻¹
  have hArG : Ar * G = Dr := by
    calc
      Ar * G = (Ar * Bs) * Xs⁻¹ := by simp [G, Matrix.mul_assoc]
      _ = (Dr * Xs) * Xs⁻¹ := by rw [hselected]
      _ = Dr := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Xs hXs, Matrix.mul_one]
  have hArEq : Ar * (G * X) = Ar * B := by
    calc
      Ar * (G * X) = (Ar * G) * X := (Matrix.mul_assoc Ar G X).symm
      _ = Dr * X := by rw [hArG]
      _ = Ar * B := hrows.symm
  have hB : G * X = B := by
    have hmul := congrArg (fun M : Matrix κ ϕ ℂ => Ar⁻¹ * M) hArEq
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Ar hAr] using hmul
  have hGunit : IsUnit G.det := by
    change IsUnit (Bs * Xs⁻¹).det
    rw [Matrix.det_mul]
    exact hBs.mul (Matrix.isUnit_nonsing_inv_det Xs hXs)
  refine ⟨G, isUnit_iff_ne_zero.mp hGunit, ?_⟩
  calc
    C = A * B := hAB
    _ = A * (G * X) := congrArg (fun Y : Matrix κ ϕ ℂ => A * Y) hB.symm

end Submissions.CuspBilinearSeedFamilies.Assembly.BifactorizationGlue


/- Source: cusp_assembly/PureLocal.lean. Reused authorship is retained in the source comments and artifact citations. -/
namespace Submissions.CuspBilinearSeedFamilies.Assembly

open scoped BigOperators

noncomputable section

theorem cusp_factorization (r N : ℕ) (hr : 2 ≤ r) (hN : r + 2 ≤ N)
    (h : NeZero (2 * N)) :
    ∃ (tauL tauR : ℂ) (G : Matrix (Fin (2 * r)) (Fin (2 * r)) ℂ),
      tauL ≠ 0 ∧ tauR ≠ 0 ∧ G.det ≠ 0 ∧
      ∀ i j : ZMod (2 * N),
        ZMod.stdAddChar i ^ r * CuspAllRankMinor.cuspProduct (r := r) h i j =
          ∑ q, ClutchedVandermondeRanks.clutch (2 * r) tauL (ZMod.stdAddChar i) q *
            (G.mulVec (ClutchedVandermondeRanks.clutch (2 * r) tauR
              (ZMod.stdAddChar j))) q := by
  letI := h
  obtain ⟨tauL, tauR, L, R, htL, htR, hfactor⟩ :=
    CuspBiClutchedFactorization.proof r N (by omega) h
  obtain ⟨row, col, hbounds, hminor⟩ := CuspAllRankMinor.allRank r N hr hN h
  let A : Matrix (ZMod (2 * N)) (Fin (2 * r)) ℂ :=
    fun i q => ClutchedVandermondeRanks.clutch (2 * r) tauL (ZMod.stdAddChar i) q
  let X : Matrix (Fin (2 * r)) (ZMod (2 * N)) ℂ :=
    fun q j => ClutchedVandermondeRanks.clutch (2 * r) tauR (ZMod.stdAddChar j) q
  let B : Matrix (Fin (2 * r)) (ZMod (2 * N)) ℂ := fun q j => L j q
  let D : Matrix (ZMod (2 * N)) (Fin (2 * r)) ℂ := Matrix.of R
  let C : Matrix (ZMod (2 * N)) (ZMod (2 * N)) ℂ :=
    fun i j => ZMod.stdAddChar i ^ r * CuspAllRankMinor.cuspProduct (r := r) h i j
  let f : Fin (2 * r) → ZMod (2 * N) := fun q => (row q : ZMod (2 * N))
  let g : Fin (2 * r) → ZMod (2 * N) := fun q => (col q : ZMod (2 * N))
  have hAB : C = A * B := by
    ext i j
    change C i j = ∑ q, A i q * B q j
    simpa [C, A, B, mul_comm,
      CuspAllRankMinor.cuspProduct, CuspAllRankMinor.cOffset, CuspAllRankMinor.dOffset,
      CuspBiClutchedFactorization.cuspProduct, CuspBiClutchedFactorization.cOffset,
      CuspBiClutchedFactorization.dOffset,
      ClutchedVandermondeRanks.clutch, CuspBiClutchedFactorization.clutch]
      using (hfactor i j).1
  have hRX : C = D * X := by
    ext i j
    change C i j = ∑ q, D i q * X q j
    simpa [C, D, X, Matrix.of_apply,
      CuspAllRankMinor.cuspProduct, CuspAllRankMinor.cOffset, CuspAllRankMinor.dOffset,
      CuspBiClutchedFactorization.cuspProduct, CuspBiClutchedFactorization.cOffset,
      CuspBiClutchedFactorization.dOffset,
      ClutchedVandermondeRanks.clutch, CuspBiClutchedFactorization.clutch]
      using (hfactor i j).2
  have hdet : (C.submatrix f g).det ≠ 0 := by
    have heq : C.submatrix f g =
        Matrix.diagonal (fun q => ZMod.stdAddChar (f q) ^ r) *
          (Matrix.of fun q s => CuspAllRankMinor.cuspProduct (r := r) h (f q) (g s)) := by
      ext q s
      rw [Matrix.diagonal_mul]
      rfl
    rw [heq, Matrix.det_mul, Matrix.det_diagonal]
    apply mul_ne_zero _ hminor
    apply Finset.prod_ne_zero_iff.mpr
    intro q _
    exact pow_ne_zero _ (CuspBiClutchedFactorization.char_ne_zero (f q))
  obtain ⟨G, hG, hC⟩ := BifactorizationGlue.proof A B D X C f g hAB hRX hdet
  refine ⟨tauL, tauR, G, htL, htR, hG, ?_⟩
  intro i j
  have hij := congrArg (fun M => M i j) hC
  change C i j = ∑ q, A i q * (∑ s, G q s * X s j) at hij
  simpa only [C, A, X, Matrix.mulVec, dotProduct] using hij

theorem conjugate_independent {k n : ℕ} {v : Fin n → Fin k → ℂ}
    (hv : LinearIndependent ℂ v) : LinearIndependent ℂ (fun i => star (v i)) := by
  let e := (starLinearEquiv ℂ : (Fin k → ℂ) ≃ₗ⋆[ℂ] (Fin k → ℂ))
  exact hv.map_of_surjective_injective (star : ℂ → ℂ) e.toAddEquiv.toAddMonoidHom
    (star_involutive.surjective) (by intro x hx; exact e.injective (by simpa using hx))
    (by intro c x; simp [e])

theorem conjugate_spanning {k n : ℕ} {v : Fin n → Fin k → ℂ}
    (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => star (v i)) = ⊤ := by
  let e := (starLinearEquiv ℂ : (Fin k → ℂ) ≃ₗ⋆[ℂ] (Fin k → ℂ))
  change Submodule.span ℂ (Set.range (e.toLinearMap ∘ v)) = ⊤
  rw [Set.range_comp, Submodule.span_image, hv]
  exact (Submodule.map_eq_top_iff (e := e)).mpr rfl

theorem matrix_spanning {k n : ℕ} {v : Fin n → Fin k → ℂ}
    (G : Matrix (Fin k) (Fin k) ℂ) (hG : G.det ≠ 0)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => G.mulVec (v i)) = ⊤ := by
  change Submodule.span ℂ (Set.range (G.mulVecLin ∘ v)) = ⊤
  rw [Set.range_comp, Submodule.span_image, hv, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    (Matrix.mulVec_surjective_iff_isUnit.mpr
      (G.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hG)))

/-- The cusp construction already supplies both pure rank conditions in all parameters.
The remaining seed obligation is the simultaneous rank condition on mixed subsets. -/
theorem proof (r N : ℕ) (hr : 2 ≤ r) (hN : r + 2 ≤ N) :
    ∃ x y : Fin (2 * N) → Fin (2 * r) → ℂ,
      (∀ i, x i ≠ 0 ∧ y i ≠ 0) ∧
      (∀ i j, (∑ q, star (x i q) * y j q) = 0 ↔
        CuspAllRankMinor.CrossAdj (r := r) (N := N)
          (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N))) ∧
      (∀ f : Fin (2 * r - 1) → Fin (2 * N), Function.Injective f →
        LinearIndependent ℂ (x ∘ f) ∧ LinearIndependent ℂ (y ∘ f)) ∧
      (∀ f : Fin (2 * r + 1) → Fin (2 * N), Function.Injective f →
        Submodule.span ℂ (Set.range (x ∘ f)) = ⊤ ∧
          Submodule.span ℂ (Set.range (y ∘ f)) = ⊤) := by
  have hN0 : 2 * N ≠ 0 := by omega
  letI : NeZero (2 * N) := ⟨hN0⟩
  obtain ⟨tauL, tauR, G, htL, htR, hG, hf⟩ := cusp_factorization r N hr hN inferInstance
  let z : Fin (2 * N) → ℂ := fun i => ZMod.stdAddChar (i.val : ZMod (2 * N))
  have hz : Function.Injective z := by
    intro a b hab
    apply Fin.ext
    have heq := ZMod.injective_stdAddChar hab
    have hv := congrArg ZMod.val heq
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hv
  have hnz : ∀ i, z i ≠ 0 := by
    intro i
    exact CuspBiClutchedFactorization.char_ne_zero _
  let u := fun i => ClutchedVandermondeRanks.clutch (2 * r) tauL (z i)
  let v := fun i => ClutchedVandermondeRanks.clutch (2 * r) tauR (z i)
  let x := fun i => star (u i)
  let y := fun i => G.mulVec (v i)
  have hu0 (i) : u i ≠ 0 := by
    intro hi
    have hcoord := congrFun hi (⟨1, by omega⟩ : Fin (2 * r))
    exact hnz i (by simpa [u, ClutchedVandermondeRanks.clutch] using hcoord)
  have hv0 (i) : v i ≠ 0 := by
    intro hi
    have hcoord := congrFun hi (⟨1, by omega⟩ : Fin (2 * r))
    exact hnz i (by simpa [v, ClutchedVandermondeRanks.clutch] using hcoord)
  have hGinj : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (G.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hG))
  refine ⟨x, y, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · simpa [x] using hu0 i
    · intro hzero
      apply hv0 i
      exact hGinj (by simpa [y] using hzero)
  · intro i j
    have heq := hf (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N))
    have hpair : (∑ q, star (x i q) * y j q) =
        z i ^ r * CuspAllRankMinor.cuspProduct (r := r) inferInstance
          (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N)) := by
      simpa [x, y, u, v, z] using heq.symm
    rw [hpair, mul_eq_zero]
    simp only [pow_ne_zero r (hnz i), false_or]
    exact CuspAllRankMinor.zeroPattern r N inferInstance _ _
  · intro f hfinj
    constructor
    · exact conjugate_independent
        (ClutchedVandermondeRanks.clutch_kminus1_independent (by omega) tauL z hz hnz f hfinj)
    · exact (ClutchedVandermondeRanks.clutch_kminus1_independent
        (by omega) tauR z hz hnz f hfinj).map' G.mulVecLin
          (LinearMap.ker_eq_bot.mpr hGinj)
  · intro f hfinj
    exact ⟨conjugate_spanning
      (ClutchedVandermondeRanks.clutch_kplus1_spanning (by omega) tauL z hz f hfinj),
      matrix_spanning G hG
        (ClutchedVandermondeRanks.clutch_kplus1_spanning (by omega) tauR z hz f hfinj)⟩

end
end Submissions.CuspBilinearSeedFamilies.Assembly


/- Source: literature/Maximal.lean. Reused authorship is retained in the source comments and artifact citations. -/
namespace Submissions.SubspaceMaximalTransversality.Maximal

open Submodule

noncomputable section

lemma exists_submodule_finrank_eq_of_le
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (d : ℕ) (hd : d ≤ Module.finrank ℂ U) :
    ∃ D : Submodule ℂ V, D ≤ U ∧ Module.finrank ℂ D = d := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hd
  let g : Fin d → V := fun i => (f i : V)
  have hg : LinearIndependent ℂ g :=
    hf.map' U.subtype U.ker_subtype
  refine ⟨Submodule.span ℂ (Set.range g), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).property
  · simpa [g] using (finrank_span_eq_card hg)

lemma exists_target_subspace
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Submodule ℂ V) (b : ℕ) (hbV : b ≤ Module.finrank ℂ V) :
    ∃ W' : Submodule ℂ V,
      Module.finrank ℂ W' = b ∧
      Module.finrank ℂ (U ⊔ W' : Submodule ℂ V) =
        min (Module.finrank ℂ V) (Module.finrank ℂ U + b) := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  have hdim : Module.finrank ℂ U + Module.finrank ℂ C = Module.finrank ℂ V :=
    Submodule.finrank_add_eq_of_isCompl hC
  by_cases hbC : b ≤ Module.finrank ℂ C
  · obtain ⟨D, hDC, hD⟩ := exists_submodule_finrank_eq_of_le C b hbC
    have hUD : Disjoint U D := hC.disjoint.mono_right hDC
    refine ⟨D, hD, ?_⟩
    have hsum : Module.finrank ℂ (U ⊔ D : Submodule ℂ V) =
        Module.finrank ℂ U + b := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq U D
      rw [hUD.eq_bot, finrank_bot, add_zero, hD] at h
      exact h
    rw [hsum, Nat.min_eq_right]
    omega
  · have hCb : Module.finrank ℂ C < b := Nat.lt_of_not_ge hbC
    have hsub : b - Module.finrank ℂ C ≤ Module.finrank ℂ U := by omega
    obtain ⟨A, hAU, hA⟩ :=
      exists_submodule_finrank_eq_of_le U (b - Module.finrank ℂ C) hsub
    have hCA : Disjoint C A := hC.symm.disjoint.mono_right hAU
    refine ⟨C ⊔ A, ?_, ?_⟩
    · have h := Submodule.finrank_sup_add_finrank_inf_eq C A
      rw [hCA.eq_bot, finrank_bot, add_zero, hA] at h
      omega
    · have htop : U ⊔ (C ⊔ A) = ⊤ := by
        simp [← sup_assoc, hC.codisjoint.eq_top]
      rw [htop, finrank_top, Nat.min_eq_left]
      omega

lemma exists_linearEquiv_map_eq_of_finrank_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W W' : Submodule ℂ V)
    (hrank : Module.finrank ℂ W = Module.finrank ℂ W') :
    ∃ g : V ≃ₗ[ℂ] V, W.map g.toLinearMap = W' := by
  let f : W ≃ₗ[ℂ] W' :=
    Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hfx : (f ⟨x, hx⟩ : V) ∈ W' := (f ⟨x, hx⟩).property
    simpa [hg ⟨x, hx⟩] using hfx
  · rw [g.finrank_map_eq, hrank]

theorem proof :
    ∀ k : ℕ, ∀ U W : Submodule ℂ (Fin k → ℂ),
      ∃ g : (Fin k → ℂ) ≃ₗ[ℂ] (Fin k → ℂ),
        Module.finrank ℂ
            (U ⊔ W.map g.toLinearMap : Submodule ℂ (Fin k → ℂ)) =
          min k (Module.finrank ℂ U + Module.finrank ℂ W) := by
  intro k U W
  have hVk : Module.finrank ℂ (Fin k → ℂ) = k := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hWk : Module.finrank ℂ W ≤ Module.finrank ℂ (Fin k → ℂ) :=
    Submodule.finrank_le W
  obtain ⟨W', hW', hUW'⟩ :=
    exists_target_subspace U (Module.finrank ℂ W) hWk
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' hW'.symm
  refine ⟨g, ?_⟩
  rw [hg, hUW', hVk]

end

end Submissions.SubspaceMaximalTransversality.Maximal


/- Source: literature/MixedRanks.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Rank witnesses used by the mixed Hermitian seed construction.
The imported transversality proof is the existing Jig s65 submission,
copied unchanged into this private preflight directory. -/

noncomputable section

open Submodule Function

namespace P14MixedRanks

abbrev Vec (k : ℕ) := Fin k → ℂ

lemma map_span_range {k : ℕ} {ι : Type*} (x : ι → Vec k)
    (g : Vec k ≃ₗ[ℂ] Vec k) :
    (span ℂ (Set.range x)).map g.toLinearMap =
      span ℂ (Set.range (g ∘ x)) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma span_sum_elim {k : ℕ} {ι κ : Type*} (x : ι → Vec k) (y : κ → Vec k) :
    span ℂ (Set.range (Sum.elim x y)) =
      span ℂ (Set.range x) ⊔ span ℂ (Set.range y) := by
  rw [Set.Sum.elim_range, Submodule.span_union]

theorem exists_equiv_sum_independent {k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Vec k) (y : κ → Vec k)
    (hx : LinearIndependent ℂ x) (hy : LinearIndependent ℂ y)
    (hsize : Fintype.card ι + Fintype.card κ ≤ k) :
    ∃ g : Vec k ≃ₗ[ℂ] Vec k,
      LinearIndependent ℂ (Sum.elim x (g ∘ y)) := by
  let U := span ℂ (Set.range x)
  let W := span ℂ (Set.range y)
  obtain ⟨g, hg⟩ := Submissions.SubspaceMaximalTransversality.Maximal.proof k U W
  have hU : Module.finrank ℂ U = Fintype.card ι := finrank_span_eq_card hx
  have hW : Module.finrank ℂ W = Fintype.card κ := finrank_span_eq_card hy
  rw [hU, hW, Nat.min_eq_right hsize] at hg
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U (W.map g.toLinearMap)
  rw [hg, hU, g.finrank_map_eq, hW] at hdim
  have hdis : Disjoint U (W.map g.toLinearMap) := by
    rw [disjoint_iff, ← Submodule.finrank_eq_zero]
    omega
  refine ⟨g, hx.sum_type (hy.map' g.toLinearMap g.ker) ?_⟩
  simpa only [U, W, map_span_range] using hdis

theorem exists_equiv_sum_spanning {k : ℕ} {ι κ : Type*}
    (x : ι → Vec k) (y : κ → Vec k)
    (hrank : k ≤ Module.finrank ℂ (span ℂ (Set.range x)) +
      Module.finrank ℂ (span ℂ (Set.range y))) :
    ∃ g : Vec k ≃ₗ[ℂ] Vec k,
      span ℂ (Set.range (Sum.elim x (g ∘ y))) = ⊤ := by
  obtain ⟨g, hg⟩ := Submissions.SubspaceMaximalTransversality.Maximal.proof
    k (span ℂ (Set.range x)) (span ℂ (Set.range y))
  refine ⟨g, Submodule.eq_top_of_finrank_eq ?_⟩
  rw [span_sum_elim, ← map_span_range, hg, Nat.min_eq_left hrank]
  simp [Vec]

lemma matrix_isUnit_det {k : ℕ} (g : Vec k ≃ₗ[ℂ] Vec k) :
    IsUnit (LinearMap.toMatrix' g.toLinearMap).det := by
  apply Matrix.isUnit_det_of_left_inverse
    (B := LinearMap.toMatrix' g.symm.toLinearMap)
  rw [← LinearMap.toMatrix'_comp]
  have h : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact g.symm_apply_apply v
  rw [h, LinearMap.toMatrix'_id]

theorem exists_matrix_sum_independent {k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Vec k) (y : κ → Vec k)
    (hx : LinearIndependent ℂ x) (hy : LinearIndependent ℂ y)
    (hsize : Fintype.card ι + Fintype.card κ ≤ k) :
    ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      LinearIndependent ℂ (Sum.elim x (fun j => G.mulVec (y j))) := by
  obtain ⟨g, hg⟩ := exists_equiv_sum_independent x y hx hy hsize
  refine ⟨LinearMap.toMatrix' g.toLinearMap, matrix_isUnit_det g, ?_⟩
  simpa [Function.comp_def] using hg

theorem exists_matrix_sum_spanning {k : ℕ} {ι κ : Type*}
    (x : ι → Vec k) (y : κ → Vec k)
    (hrank : k ≤ Module.finrank ℂ (span ℂ (Set.range x)) +
      Module.finrank ℂ (span ℂ (Set.range y))) :
    ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      span ℂ (Set.range (Sum.elim x (fun j => G.mulVec (y j)))) = ⊤ := by
  obtain ⟨g, hg⟩ := exists_equiv_sum_spanning x y hrank
  refine ⟨LinearMap.toMatrix' g.toLinearMap, matrix_isUnit_det g, ?_⟩
  simpa [Function.comp_def] using hg

theorem independent_subfamily_of_spanning {k : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → Vec k) (hv : span ℂ (Set.range v) = ⊤) :
    ∃ e : Fin k → ι, Function.Injective e ∧ LinearIndependent ℂ (v ∘ e) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hspan, hv]
    simp [Vec]
  let eκ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨a ∘ eκ, ha.comp eκ.injective, hli.comp eκ eκ.injective⟩

def SmallSelections {k n : ℕ} (x : Fin n → Vec k) : Prop :=
  ∀ d : ℕ, d < k → ∀ f : Fin d → Fin n, Injective f →
    LinearIndependent ℂ (x ∘ f)

def LargeSelections {k n : ℕ} (x : Fin n → Vec k) : Prop :=
  ∀ f : Fin (k + 1) → Fin n, Injective f →
    span ℂ (Set.range (x ∘ f)) = ⊤

theorem smallSelections_of_exact {k n : ℕ} (x : Fin n → Vec k) (hn : k - 1 ≤ n)
    (hx : ∀ f : Fin (k - 1) → Fin n, Injective f → LinearIndependent ℂ (x ∘ f)) :
    SmallSelections x := by
  intro d hd f hf
  have hdk : d ≤ k - 1 := by omega
  have hdn : d ≤ n := hdk.trans hn
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE hdn) f (Fin.castLE_injective _) hf
  have hli := hx (σ ∘ Fin.castLE hn) (σ.injective.comp (Fin.castLE_injective _))
  have hres := hli.comp (Fin.castLE hdk) (Fin.castLE_injective _)
  have heq : (x ∘ (σ ∘ Fin.castLE hn)) ∘ Fin.castLE hdk = x ∘ f := by
    funext i
    exact congrArg x (hσ i)
  rwa [heq] at hres

lemma independent_small {k n : ℕ} {ι : Type*} [Fintype ι]
    (x : Fin n → Vec k) (hx : SmallSelections x)
    (f : ι → Fin n) (hf : Injective f) (hsize : Fintype.card ι < k) :
    LinearIndependent ℂ (x ∘ f) := by
  let e := Fintype.equivFin ι
  have h := hx _ hsize (f ∘ e.symm) (hf.comp e.symm.injective)
  simpa [Function.comp_def] using h.comp e e.injective

lemma spanning_large {k n : ℕ} {ι : Type*} [Fintype ι]
    (x : Fin n → Vec k) (hx : LargeSelections x)
    (f : ι → Fin n) (hf : Injective f) (hsize : Fintype.card ι = k + 1) :
    span ℂ (Set.range (x ∘ f)) = ⊤ := by
  let e : Fin (k + 1) ≃ ι := (Fintype.equivFinOfCardEq hsize).symm
  have h := hx (f ∘ e) (hf.comp e.injective)
  simpa only [← Function.comp_assoc, e.surjective.range_comp] using h

lemma pure_rank_lower {k n : ℕ} {ι : Type*} [Fintype ι]
    (hk : 0 < k) (x : Fin n → Vec k) (hx : SmallSelections x)
    (f : ι → Fin n) (hf : Injective f) :
    min (Fintype.card ι) (k - 1) ≤ Module.finrank ℂ (span ℂ (Set.range (x ∘ f))) := by
  let d := min (Fintype.card ι) (k - 1)
  have hd : d < k := lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
  let e : Fin d → ι := fun i => (Fintype.equivFin ι).symm
    (Fin.castLE (Nat.min_le_left _ _) i)
  have he : Injective e := (Fintype.equivFin ι).symm.injective.comp (Fin.castLE_injective _)
  have hli := hx d hd (f ∘ e) (hf.comp he)
  have hs : span ℂ (Set.range (x ∘ (f ∘ e))) ≤ span ℂ (Set.range (x ∘ f)) := by
    apply Submodule.span_mono
    rintro z ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  have hdim : Module.finrank ℂ (span ℂ (Set.range (x ∘ (f ∘ e)))) = d := by
    simpa using finrank_span_eq_card hli
  have hmono := Submodule.finrank_mono hs
  rw [hdim] at hmono
  exact hmono

def leftIndex {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n)
    (i : {i // (f i).isLeft}) : Fin n := (f i.val).getLeft i.property

def rightIndex {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n)
    (i : {i // ¬ (f i).isLeft}) : Fin n :=
  (f i.val).getRight (by simpa using i.property)

lemma leftIndex_injective {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n) (hf : Injective f) :
    Injective (leftIndex f) := by
  intro i j hij
  apply Subtype.ext
  apply hf
  simpa only [leftIndex, Sum.inl_getLeft] using congrArg (Sum.inl : Fin n → Fin n ⊕ Fin n) hij

lemma rightIndex_injective {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n) (hf : Injective f) :
    Injective (rightIndex f) := by
  intro i j hij
  apply Subtype.ext
  apply hf
  simpa only [rightIndex, Sum.inr_getRight] using congrArg (Sum.inr : Fin n → Fin n ⊕ Fin n) hij

lemma partition_card {d n : ℕ} (f : Fin d → Fin n ⊕ Fin n) :
    Fintype.card {i // (f i).isLeft} + Fintype.card {i // ¬ (f i).isLeft} = d := by
  classical
  simpa using Fintype.card_congr (Equiv.sumCompl (fun i => (f i).isLeft))

lemma partition_family {k d n : ℕ} (x y : Fin n → Vec k)
    (f : Fin d → Fin n ⊕ Fin n) (G : Matrix (Fin k) (Fin k) ℂ) :
    Sum.elim (x ∘ leftIndex f) (fun j => G.mulVec (y (rightIndex f j))) =
      (Sum.elim x (fun j => G.mulVec (y j))) ∘ f ∘
        (Equiv.sumCompl (fun i => (f i).isLeft)) := by
  classical
  funext i
  cases i with
  | inl i =>
    change x ((f i.val).getLeft i.property) = Sum.elim x _ (f i.val)
    conv_rhs => rw [← Sum.inl_getLeft (f i.val) i.property]
    rfl
  | inr i =>
    change G.mulVec (y ((f i.val).getRight _)) = Sum.elim x _ (f i.val)
    conv_rhs => rw [← Sum.inr_getRight (f i.val) (by simpa using i.property)]
    rfl

theorem small_selection_gl {k n d : ℕ} (x y : Fin n → Vec k)
    (hx : SmallSelections x) (hy : SmallSelections y)
    (hd : d < k) (f : Fin d → Fin n ⊕ Fin n) (hf : Injective f) :
    ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      LinearIndependent ℂ (fun q => Sum.elim x (fun j => G.mulVec (y j)) (f q)) := by
  classical
  have hc := partition_card f
  have hl := independent_small x hx (leftIndex f) (leftIndex_injective f hf) (by omega)
  have hr := independent_small y hy (rightIndex f) (rightIndex_injective f hf) (by omega)
  obtain ⟨G, hG, hli⟩ := exists_matrix_sum_independent
    (x ∘ leftIndex f) (y ∘ rightIndex f) hl hr (by omega)
  refine ⟨G, hG, ?_⟩
  change LinearIndependent ℂ (Sum.elim (x ∘ leftIndex f)
    (fun j => G.mulVec (y (rightIndex f j)))) at hli
  rw [partition_family x y f G] at hli
  simpa [Function.comp_def] using
    hli.comp (Equiv.sumCompl (fun i => (f i).isLeft)).symm
      (Equiv.sumCompl (fun i => (f i).isLeft)).symm.injective

theorem large_selection_gl_spanning {k n : ℕ} (hk : 2 ≤ k)
    (x y : Fin n → Vec k)
    (hx : SmallSelections x) (hy : SmallSelections y)
    (hx' : LargeSelections x) (hy' : LargeSelections y)
    (f : Fin (k + 1) → Fin n ⊕ Fin n) (hf : Injective f) :
    ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      span ℂ (Set.range (fun q => Sum.elim x (fun j => G.mulVec (y j)) (f q))) = ⊤ := by
  classical
  have hc := partition_card f
  have hrank : k ≤
      Module.finrank ℂ (span ℂ (Set.range (x ∘ leftIndex f))) +
      Module.finrank ℂ (span ℂ (Set.range (y ∘ rightIndex f))) := by
    by_cases hl : Fintype.card {i // (f i).isLeft} = 0
    · have hs := spanning_large y hy' (rightIndex f) (rightIndex_injective f hf) (by omega)
      rw [hs]
      simp [Vec]
    by_cases hr : Fintype.card {i // ¬ (f i).isLeft} = 0
    · have hs := spanning_large x hx' (leftIndex f) (leftIndex_injective f hf) (by omega)
      rw [hs]
      simp [Vec]
    have hxl := pure_rank_lower (by omega) x hx (leftIndex f) (leftIndex_injective f hf)
    have hyl := pure_rank_lower (by omega) y hy (rightIndex f) (rightIndex_injective f hf)
    omega
  obtain ⟨G, hG, hs⟩ := exists_matrix_sum_spanning
    (x ∘ leftIndex f) (y ∘ rightIndex f) hrank
  refine ⟨G, hG, ?_⟩
  change span ℂ (Set.range (Sum.elim (x ∘ leftIndex f)
    (fun j => G.mulVec (y (rightIndex f j))))) = ⊤ at hs
  rw [partition_family x y f G] at hs
  change span ℂ (Set.range (((Sum.elim x (fun j => G.mulVec (y j))) ∘ f) ∘
    (Equiv.sumCompl (fun i => (f i).isLeft)))) = ⊤ at hs
  rw [(Equiv.sumCompl (fun i => (f i).isLeft)).surjective.range_comp] at hs
  exact hs

theorem large_selection_gl {k n : ℕ} (hk : 2 ≤ k)
    (x y : Fin n → Vec k)
    (hx : SmallSelections x) (hy : SmallSelections y)
    (hx' : LargeSelections x) (hy' : LargeSelections y)
    (f : Fin (k + 1) → Fin n ⊕ Fin n) (hf : Injective f) :
    ∃ e : Fin k → Fin (k + 1), Injective e ∧
      ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
        LinearIndependent ℂ
          (fun q => Sum.elim x (fun j => G.mulVec (y j)) (f (e q))) := by
  obtain ⟨G, hG, hs⟩ := large_selection_gl_spanning hk x y hx hy hx' hy' f hf
  obtain ⟨e, he, hli⟩ := independent_subfamily_of_spanning
    (fun q => Sum.elim x (fun j => G.mulVec (y j)) (f q)) hs
  exact ⟨e, he, G, hG, hli⟩

end P14MixedRanks
end


/- Source: elliptic_audit/HermitianAssembly.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Reused, attributed kernel-green Jig p14 lemmas s63 and s70.
The s63 Gram construction is retained before its positive-definite wrapper,
so its already-constructed invertible factor need not be recovered by CFC.sqrt.
The unused s63 coordinate-minor/subspace helpers are omitted; s70 is retained. -/


/-!
# Finite positive-Hermitian genericity

This file gives an algebraic replacement for the informal assertion that the
positive-definite Hermitian cone is Zariski dense.  The key construction pulls
a polynomial in a matrix `K` back along `K = star L * L`, writes the entries of
`L` in independent real and imaginary coordinates, and proves that this
pullback is injective by an explicit polynomial retraction.

No measure theory, classical Zariski topology, or unproved density statement is
used.
-/

namespace P14Hermitian.GreenGenericity

open Matrix MvPolynomial
open scoped Matrix ComplexConjugate

noncomputable section

abbrev MatVar (k : ℕ) := Fin k × Fin k

/-- Real and imaginary coordinate variables for a complex matrix. -/
abbrev GramVar (k : ℕ) := Bool × Fin k × Fin k

private def delta {k : ℕ} (i j : Fin k) : ℂ :=
  if i = j then 1 else 0

/-- The polynomial matrix `L = A + iB`. -/
def lPoly {k : ℕ} (i j : Fin k) : MvPolynomial (GramVar k) ℂ :=
  X (false, i, j) + C Complex.I * X (true, i, j)

/-- The entrywise conjugate polynomial matrix `A - iB`. -/
def lBarPoly {k : ℕ} (i j : Fin k) : MvPolynomial (GramVar k) ℂ :=
  X (false, i, j) - C Complex.I * X (true, i, j)

/-- The universal Gram-matrix entry `(LᴴL)ᵢⱼ`. -/
def gramEntry {k : ℕ} (ij : MatVar k) : MvPolynomial (GramVar k) ℂ :=
  ∑ r : Fin k, lBarPoly r ij.1 * lPoly r ij.2

/-- Pullback of matrix polynomials along `K = LᴴL`. -/
def gramPull {k : ℕ} :
    MvPolynomial (MatVar k) ℂ →ₐ[ℂ] MvPolynomial (GramVar k) ℂ :=
  bind₁ gramEntry

/-- Polynomial substitution used as a left inverse of `gramPull`.

It imposes `A + iB = X` and `A - iB = 1`.
-/
def gramRetractCoord {k : ℕ} (v : GramVar k) :
    MvPolynomial (MatVar k) ℂ :=
  if v.1 then
    C ((2 * Complex.I)⁻¹) *
      (X (v.2.1, v.2.2) - C (delta v.2.1 v.2.2))
  else
    C ((2 : ℂ)⁻¹) *
      (X (v.2.1, v.2.2) + C (delta v.2.1 v.2.2))

def gramRetract {k : ℕ} :
    MvPolynomial (GramVar k) ℂ →ₐ[ℂ] MvPolynomial (MatVar k) ℂ :=
  bind₁ gramRetractCoord

lemma gramRetract_lPoly {k : ℕ} (i j : Fin k) :
    gramRetract (lPoly i j) = X (i, j) := by
  simp only [gramRetract, lPoly, map_add, map_mul, bind₁_X_right,
    gramRetractCoord, Bool.false_eq_true, if_false, if_true, map_C]
  rw [show (2 * Complex.I : ℂ)⁻¹ = -Complex.I / 2 by
    field_simp [Complex.I_ne_zero]
    simpa [pow_two] using congrArg Neg.neg Complex.I_mul_I]
  norm_num
  have hI :
      (C Complex.I : MvPolynomial (MatVar k) ℂ) *
          C (-Complex.I / 2) = C (1 / 2) := by
    rw [← map_mul]
    apply congrArg C
    calc
      Complex.I * (-Complex.I / 2) =
          -(Complex.I * Complex.I) / 2 := by ring
      _ = 1 / 2 := by rw [Complex.I_mul_I]; ring
  rw [← mul_assoc (C Complex.I), hI]
  ring_nf
  calc
    C (1 / 2 : ℂ) * X (i, j) * 2 =
        (C (1 / 2 : ℂ) * C (2 : ℂ)) * X (i, j) := by
          rw [show (2 : MvPolynomial (MatVar k) ℂ) = C (2 : ℂ) from
            (map_ofNat C 2).symm]
          ring
    _ = X (i, j) := by rw [← map_mul]; norm_num

lemma gramRetract_lBarPoly {k : ℕ} (i j : Fin k) :
    gramRetract (lBarPoly i j) = C (delta i j) := by
  simp only [gramRetract, lBarPoly, map_sub, map_mul, bind₁_X_right,
    gramRetractCoord, Bool.false_eq_true, if_false, if_true, map_C]
  rw [show (2 * Complex.I : ℂ)⁻¹ = -Complex.I / 2 by
    field_simp [Complex.I_ne_zero]
    simpa [pow_two] using congrArg Neg.neg Complex.I_mul_I]
  norm_num
  have hI :
      (C Complex.I : MvPolynomial (MatVar k) ℂ) *
          C (-Complex.I / 2) = C (1 / 2) := by
    rw [← map_mul]
    apply congrArg C
    calc
      Complex.I * (-Complex.I / 2) =
          -(Complex.I * Complex.I) / 2 := by ring
      _ = 1 / 2 := by rw [Complex.I_mul_I]; ring
  rw [← mul_assoc (C Complex.I), hI]
  ring_nf
  calc
    C (1 / 2 : ℂ) * C (delta i j) * 2 =
        (C (1 / 2 : ℂ) * C (2 : ℂ)) * C (delta i j) := by
          rw [show (2 : MvPolynomial (MatVar k) ℂ) = C (2 : ℂ) from
            (map_ofNat C 2).symm]
          ring
    _ = C (delta i j) := by rw [← map_mul]; norm_num

/-- The explicit polynomial retraction sends a universal Gram entry back to
the corresponding universal matrix variable. -/
lemma gramRetract_gramEntry {k : ℕ} (ij : MatVar k) :
    gramRetract (gramEntry ij) = X ij := by
  rcases ij with ⟨i, j⟩
  simp only [gramEntry, map_sum, map_mul, gramRetract_lBarPoly,
    gramRetract_lPoly]
  simp [delta, X]

/-- Missing local lemma 1: the Hermitian Gram pullback on matrix polynomials is
injective. -/
lemma gramPull_injective {k : ℕ} : Function.Injective (gramPull (k := k)) := by
  intro p q hpq
  have h := congrArg (fun f => gramRetract (k := k) f) hpq
  rw [gramPull, gramRetract, bind₁_bind₁, bind₁_bind₁] at h
  have hc :
      (fun i : MatVar k => (bind₁ gramRetractCoord) (gramEntry i)) =
        (X : MatVar k → MvPolynomial (MatVar k) ℂ) := by
    funext i
    exact gramRetract_gramEntry i
  rw [hc] at h
  simpa only [bind₁_X_left, AlgHom.id_apply] using h

/-- The determinant of the polynomial matrix `L`. -/
def lDetPoly {k : ℕ} : MvPolynomial (GramVar k) ℂ :=
  Matrix.det (Matrix.of fun i j : Fin k => lPoly i j)

private def identityGramEval {k : ℕ} : GramVar k → ℂ
  | (false, i, j) => delta i j
  | (true, _, _) => 0

lemma eval_lPoly_identity {k : ℕ} (i j : Fin k) :
    eval (identityGramEval (k := k)) (lPoly i j) = delta i j := by
  simp [lPoly, identityGramEval]

lemma lDetPoly_ne_zero {k : ℕ} : lDetPoly (k := k) ≠ 0 := by
  intro h
  have hz : eval (identityGramEval (k := k)) (lDetPoly (k := k)) = 0 := by
    simp [h]
  have ho : eval (identityGramEval (k := k)) (lDetPoly (k := k)) = 1 := by
    unfold lDetPoly
    rw [(eval (identityGramEval (k := k))).map_det]
    convert Matrix.det_one (n := Fin k)
    ext i j
    simp [eval_lPoly_identity, delta, Matrix.one_apply]
  exact one_ne_zero (ho.symm.trans hz)

/-- A valuation of all Gram coordinates by embedded real numbers. -/
def IsRealValuation {k : ℕ} (z : GramVar k → ℂ) : Prop :=
  z ∈ Set.pi Set.univ (fun _ => Set.range ((↑) : ℝ → ℂ))

lemma exists_real_eval_ne_zero {k : ℕ}
    (p : MvPolynomial (GramVar k) ℂ) (hp : p ≠ 0) :
    ∃ z : GramVar k → ℂ, IsRealValuation z ∧ eval z p ≠ 0 := by
  by_contra h
  push_neg at h
  apply hp
  apply funext_set (fun _ : GramVar k => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  simpa [h z hz]

private def realPartOfValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (v : GramVar k) : ℝ :=
  Classical.choose (hz v (Set.mem_univ v))

private lemma ofReal_realPartOfValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (v : GramVar k) :
    (realPartOfValuation z hz v : ℂ) = z v :=
  Classical.choose_spec (hz v (Set.mem_univ v))

def matrixEntryOfRealValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) : ℂ :=
    (realPartOfValuation z hz (false, i, j) : ℂ) +
      Complex.I * (realPartOfValuation z hz (true, i, j) : ℂ)

def matrixOfRealValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of (matrixEntryOfRealValuation z hz)

/-- Entrywise formula for `LᴴL`, avoiding any dependence on matrix notation. -/
def gramOf {k : ℕ} (L : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun i j => ∑ r : Fin k, star (L r i) * L r j

lemma gramOf_eq_conjTranspose_mul {k : ℕ}
    (L : Matrix (Fin k) (Fin k) ℂ) :
    gramOf L = L.conjTranspose * L := by
  ext i j
  simp [gramOf, Matrix.mul_apply, conjTranspose_apply]

lemma eval_lPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (lPoly i j) =
      matrixEntryOfRealValuation z hz i j := by
  rw [show eval z (lPoly i j) =
      z (false, i, j) + Complex.I * z (true, i, j) by
    simp [lPoly]]
  rw [← ofReal_realPartOfValuation z hz (false, i, j),
    ← ofReal_realPartOfValuation z hz (true, i, j)]
  rfl

lemma eval_lBarPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (lBarPoly i j) =
      star (matrixEntryOfRealValuation z hz i j) := by
  rw [show eval z (lBarPoly i j) =
      z (false, i, j) - Complex.I * z (true, i, j) by
    simp [lBarPoly]]
  rw [← ofReal_realPartOfValuation z hz (false, i, j),
    ← ofReal_realPartOfValuation z hz (true, i, j)]
  unfold matrixEntryOfRealValuation
  rw [sub_eq_add_neg]
  change _ = conj
    ((realPartOfValuation z hz (false, i, j) : ℂ) +
      Complex.I * (realPartOfValuation z hz (true, i, j) : ℂ))
  simp

lemma eval_gramEntry_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (gramEntry (i, j)) =
      ∑ r : Fin k,
        star (matrixEntryOfRealValuation z hz r i) *
          matrixEntryOfRealValuation z hz r j := by
  rw [gramEntry, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_mul, eval_lPoly_realValuation, eval_lBarPoly_realValuation]

lemma eval_gramPull_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (p : MvPolynomial (MatVar k) ℂ) :
    eval z (gramPull p) =
      eval (fun ij =>
        ∑ r : Fin k,
          star (matrixEntryOfRealValuation z hz r ij.1) *
            matrixEntryOfRealValuation z hz r ij.2) p := by
  rw [gramPull]
  change aeval z (bind₁ gramEntry p) = _
  rw [aeval_bind₁]
  apply congrArg (fun f => eval f p)
  funext ij
  exact eval_gramEntry_realValuation z hz ij.1 ij.2

lemma eval_lDetPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) :
    eval z (lDetPoly (k := k)) =
      (matrixOfRealValuation (k := k) z hz).det := by
  unfold lDetPoly
  rw [(eval z).map_det]
  apply congrArg Matrix.det
  ext i j
  simpa [matrixOfRealValuation] using eval_lPoly_realValuation z hz i j

/-- The published s63 construction already supplies an invertible Gram factor.
Retaining it avoids subsequently recovering the factor by a matrix square root. -/
theorem exists_gram_eval_ne_zero {k : ℕ}
    (p : MvPolynomial (MatVar k) ℂ) (hp : p ≠ 0) :
    ∃ L : Matrix (Fin k) (Fin k) ℂ, IsUnit L ∧
      eval (fun ij => (L.conjTranspose * L) ij.1 ij.2) p ≠ 0 := by
  have hgp : gramPull p ≠ 0 := (gramPull_injective (k := k)).ne hp
  have hprod : gramPull p * lDetPoly (k := k) ≠ 0 :=
    mul_ne_zero hgp lDetPoly_ne_zero
  obtain ⟨z, hz, hzeval⟩ := exists_real_eval_ne_zero
    (gramPull p * lDetPoly (k := k)) hprod
  let L := matrixOfRealValuation z hz
  have hsplit :
      eval z (gramPull p) * eval z (lDetPoly (k := k)) ≠ 0 := by
    simpa [map_mul] using hzeval
  have hgram : eval z (gramPull p) ≠ 0 :=
    fun h => hsplit (by simp [h])
  have hdetEval : eval z (lDetPoly (k := k)) ≠ 0 :=
    fun h => hsplit (by simp [h])
  have hdet : L.det ≠ 0 := by
    rw [eval_lDetPoly_realValuation z hz] at hdetEval
    exact hdetEval
  have hL : IsUnit L :=
    (Matrix.isUnit_iff_isUnit_det L).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨L, hL, ?_⟩
  rw [eval_gramPull_realValuation z hz] at hgram
  simpa only [← gramOf_eq_conjTranspose_mul, L, gramOf, matrixOfRealValuation, Matrix.of_apply] using hgram

theorem finite_gram_genericity {k : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial (MatVar k) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ L : Matrix (Fin k) (Fin k) ℂ, IsUnit L ∧
      ∀ i, eval (fun ij => (L.conjTranspose * L) ij.1 ij.2) (p i) ≠ 0 := by
  classical
  obtain ⟨L, hL, hprod⟩ := exists_gram_eval_ne_zero (∏ i, p i)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  refine ⟨L, hL, ?_⟩
  rw [map_prod] at hprod
  exact fun i => Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)

end

end P14Hermitian.GreenGenericity


namespace P14Hermitian.GreenMixedMinor

open Matrix MvPolynomial

noncomputable section

abbrev MatVar (k : ℕ) := Fin k × Fin k

def universalMat {k : ℕ} :
    Matrix (Fin k) (Fin k) (MvPolynomial (MatVar k) ℂ) :=
  fun i j => X (i, j)

def mixedPolyVec {k d : ℕ} (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ) (q : Fin d) :
    Fin k → MvPolynomial (MatVar k) ℂ :=
  if move q then
    (universalMat (k := k)).adjugate.mulVec (fun i => C (v q i))
  else fun i => C (v q i)

lemma eval_universalMat (k : ℕ) (H : Matrix (Fin k) (Fin k) ℂ) :
    (eval (fun ij => H ij.1 ij.2)).mapMatrix (universalMat (k := k)) = H := by
  ext i j
  simp [universalMat]

lemma eval_mixedPolyVec {k d : ℕ} (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ) (q : Fin d)
    (H : Matrix (Fin k) (Fin k) ℂ) :
    (fun i => eval (fun ij => H ij.1 ij.2) (mixedPolyVec move v q i)) =
      if move q then H.adjugate.mulVec (v q) else v q := by
  funext i
  by_cases hq : move q
  · simp only [mixedPolyVec, hq, if_true]
    let z : MatVar k → ℂ := fun ij => H ij.1 ij.2
    have hmat :
        (eval z).mapMatrix (universalMat (k := k)).adjugate = H.adjugate := by
      rw [RingHom.map_adjugate, eval_universalMat]
    calc
      eval z ((universalMat (k := k)).adjugate.mulVec
          (fun j => C (v q j)) i) =
          (((eval z).mapMatrix (universalMat (k := k)).adjugate).mulVec
            (fun j => eval z (C (v q j)))) i := by
              exact RingHom.map_mulVec (eval z) _ _ i
      _ = (H.adjugate.mulVec (v q)) i := by rw [hmat]; simp
  · simp [mixedPolyVec, hq]

lemma adjugate_realizes_invertible {k : ℕ}
    (G : Matrix (Fin k) (Fin k) ℂ) (hG : IsUnit G.det) :
    ∃ (H : Matrix (Fin k) (Fin k) ℂ) (c : ℂ),
      IsUnit H.det ∧ c ≠ 0 ∧ H.adjugate = c • G := by
  let H : Matrix (Fin k) (Fin k) ℂ := G⁻¹
  have hH : IsUnit H.det := G.isUnit_nonsing_inv_det hG
  refine ⟨H, H.det, hH, isUnit_iff_ne_zero.mp hH, ?_⟩
  calc
    H.adjugate = 1 * H.adjugate := by rw [Matrix.one_mul]
    _ = (G * H) * H.adjugate := by
      rw [show G * H = 1 by exact G.mul_nonsing_inv hG]
    _ = G * (H * H.adjugate) := by rw [Matrix.mul_assoc]
    _ = G * (H.det • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
      rw [H.mul_adjugate]
    _ = H.det • G := by rw [Matrix.mul_smul, Matrix.mul_one]

lemma exists_adjugate_rank_witness {k d : ℕ}
    (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ)
    (G : Matrix (Fin k) (Fin k) ℂ) (hG : IsUnit G.det)
    (hli : LinearIndependent ℂ
      (fun q => if move q then G.mulVec (v q) else v q)) :
    ∃ H : Matrix (Fin k) (Fin k) ℂ, IsUnit H.det ∧
      LinearIndependent ℂ
        (fun q => if move q then H.adjugate.mulVec (v q) else v q) := by
  obtain ⟨H, c, hH, hc, hAdj⟩ := adjugate_realizes_invertible G hG
  let base : Fin d → (Fin k → ℂ) :=
    fun q => if move q then G.mulVec (v q) else v q
  let hcUnit : IsUnit c := isUnit_iff_ne_zero.mpr hc
  let scale : Fin d → ℂˣ := fun q => if move q then hcUnit.unit else 1
  have hs : LinearIndependent ℂ (scale • base) := by
    exact hli.units_smul scale
  refine ⟨H, hH, ?_⟩
  convert hs using 1
  funext q i
  by_cases hq : move q
  · simp only [Pi.smul_apply', scale, base, hq, if_true]
    rw [hAdj, Matrix.smul_mulVec]
    simp
  · simp [scale, base, hq]

lemma exists_nonzero_coord_minor {k d : ℕ} (A : Fin d → Fin k → ℂ)
    (hA : LinearIndependent ℂ A) :
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      (Matrix.of fun p q => A q (e p)).det ≠ 0 := by
  classical
  let rows : Fin k → (Fin d → ℂ) := fun i q => A q i
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ rows
  have : Finite κ := LinearIndependent.finite (R := ℂ) (M := Fin d → ℂ) hli
  let : Fintype κ := Fintype.ofFinite κ
  let M : Matrix (Fin d) (Fin k) ℂ := A
  have hfinrank_rows :
      Module.finrank ℂ (Submodule.span ℂ (Set.range rows)) = d := by
    have hA' : LinearIndependent ℂ M.row := hA
    have hr : M.rank = d := by
      simpa [Fintype.card_fin] using (LinearIndependent.rank_matrix (M := M) hA')
    have hrows : rows = M.col := by
      funext i q
      rfl
    rw [hrows, ← rank_eq_finrank_span_cols, hr]
  have hcard : Fintype.card κ = d := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)).mp hli
    rw [Set.finrank] at h
    rw [h, hspan, hfinrank_rows]
  let e : Fin d → Fin k :=
    fun i => a ((Fintype.equivFin κ).symm (Fin.cast hcard.symm i))
  have he : Function.Injective e :=
    ha.comp <| (Fintype.equivFin κ).symm.injective.comp
      (Fin.cast_injective hcard.symm)
  have hli_e : LinearIndependent ℂ (fun i : Fin d => rows (e i)) :=
    hli.comp _ <| (Fintype.equivFin κ).symm.injective.comp
      (Fin.cast_injective hcard.symm)
  refine ⟨e, he, ?_⟩
  let B : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun p q => A q (e p)
  have hrow : LinearIndependent ℂ B.row := by
    have : B.row = fun p : Fin d => rows (e p) := by
      funext p q
      rfl
    simpa [this] using hli_e
  exact (nonsingular_iff_det_ne_zero (R := ℂ)).mp
    (Nonsingular.of_linearIndependent_row hrow)

lemma polynomial_minor_from_eval {k d : ℕ} {σ : Type}
    (w : Fin d → Fin k → MvPolynomial σ ℂ) (ξ : σ → ℂ)
    (hli : LinearIndependent ℂ (fun q i => eval ξ (w q i))) :
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      Matrix.det (Matrix.of fun p q => w q (e p)) ≠ 0 := by
  obtain ⟨e, he, hdet⟩ := exists_nonzero_coord_minor
    (fun q i => eval ξ (w q i)) hli
  refine ⟨e, he, ?_⟩
  intro hp
  have hev : eval ξ (Matrix.det (Matrix.of fun p q => w q (e p))) = 0 := by
    simp [hp]
  rw [(eval ξ).map_det] at hev
  exact hdet hev

/-- An invertible mixed-rank witness produces a nonzero coordinate-minor
polynomial for the universal adjugate family. -/
theorem proof :
    ∀ (k d : ℕ) (move : Fin d → Prop) [DecidablePred move]
      (v : Fin d → Fin k → ℂ) (G : Matrix (Fin k) (Fin k) ℂ),
      IsUnit G.det →
      LinearIndependent ℂ
        (fun q => if move q then G.mulVec (v q) else v q) →
      ∃ e : Fin d → Fin k, Function.Injective e ∧
        Matrix.det (Matrix.of fun p q => mixedPolyVec move v q (e p)) ≠ 0 := by
  intro k d move _ v G hG hli
  obtain ⟨H, _hH, hliH⟩ := exists_adjugate_rank_witness move v G hG hli
  apply polynomial_minor_from_eval (mixedPolyVec move v) (fun ij => H ij.1 ij.2)
  have heval :
      (fun q i => eval (fun ij => H ij.1 ij.2) (mixedPolyVec move v q i)) =
        (fun q => if move q then H.adjugate.mulVec (v q) else v q) := by
    funext q
    exact eval_mixedPolyVec move v q H
  rw [heval]
  exact hliH

end

end P14Hermitian.GreenMixedMinor




namespace P14Hermitian

open Matrix MvPolynomial
open scoped Matrix ComplexConjugate BigOperators

noncomputable section

abbrev Vec (k : ℕ) := Fin k → ℂ
abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℂ
abbrev MatVar (k : ℕ) := Fin k × Fin k

/-- Pairing polynomials use unconstrained complex matrix entries. -/
def pairPoly {k : ℕ} (x y : Vec k) : MvPolynomial (MatVar k) ℂ :=
  dotProduct (fun i => C (star (x i)))
    ((GreenMixedMinor.universalMat (k := k)).mulVec (fun i => C (y i)))

def adjPairPoly {k : ℕ} (x y : Vec k) : MvPolynomial (MatVar k) ℂ :=
  dotProduct (fun i => C (star (x i)))
    ((GreenMixedMinor.universalMat (k := k)).adjugate.mulVec (fun i => C (y i)))

lemma eval_pairPoly {k : ℕ} (x y : Vec k) (H : Mat k) :
    eval (fun ij => H ij.1 ij.2) (pairPoly x y) =
      dotProduct (star x) (H.mulVec y) := by
  simp [pairPoly, dotProduct, Matrix.mulVec, GreenMixedMinor.universalMat]

lemma eval_adjPairPoly {k : ℕ} (x y : Vec k) (H : Mat k) :
    eval (fun ij => H ij.1 ij.2) (adjPairPoly x y) =
      dotProduct (star x) (H.adjugate.mulVec y) := by
  let z : MatVar k → ℂ := fun ij => H ij.1 ij.2
  have hmat :
      (eval z).mapMatrix (GreenMixedMinor.universalMat (k := k)).adjugate =
        H.adjugate := by
    rw [RingHom.map_adjugate, GreenMixedMinor.eval_universalMat]
  simp only [adjPairPoly, dotProduct, map_sum, map_mul, eval_C]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  calc
    eval z ((GreenMixedMinor.universalMat (k := k)).adjugate.mulVec
        (fun j => C (y j)) i) =
        (((eval z).mapMatrix (GreenMixedMinor.universalMat (k := k)).adjugate).mulVec
          (fun j => eval z (C (y j)))) i := by
            exact RingHom.map_mulVec (eval z) _ _ i
    _ = (H.adjugate.mulVec y) i := by rw [hmat]; simp

lemma pairPoly_ne_zero {k : ℕ} (x y : Vec k) (hx : x ≠ 0) (hy : y ≠ 0) :
    pairPoly x y ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  let E : Mat k := fun a b => if a = i then if b = j then 1 else 0 else 0
  intro hp
  have hev := eval_pairPoly x y E
  have hzero : dotProduct (star x) (E.mulVec y) = 0 := by
    rw [hp, map_zero] at hev
    exact hev.symm
  have hval : dotProduct (star x) (E.mulVec y) = star (x i) * y j := by
    simp [E, dotProduct, Matrix.mulVec]
  rw [hval] at hzero
  exact (mul_ne_zero (star_ne_zero.mpr hi) hj) hzero

/-- Adjugate pairings are nonzero polynomials too.  The already-proved
positive-cone lemma supplies one invertible witness for the linear pairing. -/
lemma adjPairPoly_ne_zero {k : ℕ} (x y : Vec k) (hx : x ≠ 0) (hy : y ≠ 0) :
    adjPairPoly x y ≠ 0 := by
  obtain ⟨L, hL, hpK⟩ := GreenGenericity.exists_gram_eval_ne_zero
    (pairPoly x y) (pairPoly_ne_zero x y hx hy)
  let K : Mat k := L.conjTranspose * L
  have hK : IsUnit K := ((Matrix.isUnit_conjTranspose L).mpr hL).mul hL
  have hKd : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK
  obtain ⟨H, c, _, hc, hAdj⟩ :=
    GreenMixedMinor.adjugate_realizes_invertible K hKd
  rw [eval_pairPoly] at hpK
  intro hp
  have hev := eval_adjPairPoly x y H
  rw [hp, map_zero] at hev
  have hval : dotProduct (star x) (H.adjugate.mulVec y) =
      c * dotProduct (star x) (K.mulVec y) := by
    rw [hAdj, Matrix.smul_mulVec]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hval] at hev
  exact (mul_ne_zero hc hpK) hev.symm

def right {n : ℕ} : Fin n ⊕ Fin n → Prop
  | .inl _ => False
  | .inr _ => True

instance {n : ℕ} (q : Fin n ⊕ Fin n) : Decidable (right q) := by
  cases q <;> unfold right <;> infer_instance

/-- The common algebraic action on a selected mixed vector. -/
def mixed {k n : ℕ} (x y : Fin n → Vec k) (G : Mat k) :
    Fin n ⊕ Fin n → Vec k := Sum.elim x (fun j => G.mulVec (y j))

lemma mixed_as_if {k n : ℕ} (x y : Fin n → Vec k) (G : Mat k)
    (q : Fin n ⊕ Fin n) :
    mixed x y G q = if right q then G.mulVec (Sum.elim x y q) else Sum.elim x y q := by
  cases q <;> simp [mixed, right]

/-- Finite Hermitian placement for any finite collection of independent
mixed-subfamily tests with separate invertible witnesses. -/
theorem finite_gram_placement {k n : ℕ} {T : Type*} [Fintype T]
    (x y : Fin n → Vec k) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (d : T → ℕ) (f : (t : T) → Fin (d t) → Fin n ⊕ Fin n)
    (hw : ∀ t, ∃ G : Mat k, IsUnit G.det ∧
      LinearIndependent ℂ (fun q => mixed x y G (f t q))) :
    ∃ L : Mat k, IsUnit L ∧
      let K := L.conjTranspose * L
      (∀ t, LinearIndependent ℂ (fun q => mixed x y K.adjugate (f t q))) ∧
      (∀ i j, dotProduct (star (x i)) (K.mulVec (x j)) ≠ 0) ∧
      (∀ i j, dotProduct (star (y i)) (K.adjugate.mulVec (y j)) ≠ 0) := by
  classical
  let base (t : T) : Fin (d t) → Vec k := fun q => Sum.elim x y (f t q)
  let move (t : T) : Fin (d t) → Prop := fun q => right (f t q)
  have hminor : ∀ t, ∃ e : Fin (d t) → Fin k, Function.Injective e ∧
      Matrix.det (Matrix.of fun p q =>
        GreenMixedMinor.mixedPolyVec (move t) (base t) q (e p)) ≠ 0 := by
    intro t
    obtain ⟨G, hG, hli⟩ := hw t
    apply GreenMixedMinor.proof k (d t) (move t) (base t) G hG
    simpa only [base, move, mixed_as_if] using hli
  choose e he hpoly using hminor
  let poly : T ⊕ ((Fin n × Fin n) ⊕ (Fin n × Fin n)) →
      MvPolynomial (MatVar k) ℂ := fun t => match t with
    | .inl t => Matrix.det (Matrix.of fun p q =>
        GreenMixedMinor.mixedPolyVec (move t) (base t) q (e t p))
    | .inr (.inl ij) => pairPoly (x ij.1) (x ij.2)
    | .inr (.inr ij) => adjPairPoly (y ij.1) (y ij.2)
  have hp : ∀ t, poly t ≠ 0 := by
    rintro (t | (ij | ij))
    · exact hpoly t
    · exact pairPoly_ne_zero _ _ (hx ij.1) (hx ij.2)
    · exact adjPairPoly_ne_zero _ _ (hy ij.1) (hy ij.2)
  obtain ⟨L, hL, havoid⟩ := GreenGenericity.finite_gram_genericity poly hp
  let K : Mat k := L.conjTranspose * L
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro t
    have hdet : (Matrix.of fun p q => mixed x y K.adjugate (f t q) (e t p)).det ≠ 0 := by
      have h := havoid (.inl t)
      change eval (fun ij => K ij.1 ij.2)
        (Matrix.det (Matrix.of fun p q =>
          GreenMixedMinor.mixedPolyVec (move t) (base t) q (e t p))) ≠ 0 at h
      rw [(eval (fun ij : MatVar k => K ij.1 ij.2)).map_det] at h
      convert h using 1
      congr 1
      ext p q
      change mixed x y K.adjugate (f t q) (e t p) =
        eval (fun ij => K ij.1 ij.2)
          (GreenMixedMinor.mixedPolyVec (move t) (base t) q (e t p))
      have heval := congrFun
        (GreenMixedMinor.eval_mixedPolyVec (move t) (base t) q K) (e t p)
      simpa only [base, move, mixed_as_if] using heval.symm
    let D : Vec k →ₗ[ℂ] (Fin (d t) → ℂ) :=
      LinearMap.pi (fun p => LinearMap.proj (R := ℂ) (e t p))
    apply LinearIndependent.of_comp D
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  · intro i j
    have h := havoid (.inr (.inl (i, j)))
    simpa only [poly, eval_pairPoly] using h
  · intro i j
    have h := havoid (.inr (.inr (i, j)))
    simpa only [poly, eval_adjPairPoly] using h

/-- Hermitian realization of a finite family of mixed-rank constraints.
The cross pairing is preserved up to one nonzero scalar, hence its zero
pattern is preserved exactly. -/
theorem finite_hermitian_placement {k n : ℕ} {T : Type*} [Fintype T]
    (x y : Fin n → Vec k) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (d : T → ℕ) (f : (t : T) → Fin (d t) → Fin n ⊕ Fin n)
    (hw : ∀ t, ∃ G : Mat k, IsUnit G.det ∧
      LinearIndependent ℂ (fun q => mixed x y G (f t q))) :
    ∃ a b : Fin n → EuclideanSpace ℂ (Fin k),
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (∀ i j, inner ℂ (a i) (b j) = 0 ↔ dotProduct (star (x i)) (y j) = 0) ∧
      (∀ i j, inner ℂ (a i) (a j) ≠ 0 ∧ inner ℂ (b i) (b j) ≠ 0) ∧
      (∀ t, LinearIndependent ℂ (fun q => Sum.elim a b (f t q))) := by
  classical
  obtain ⟨L, hL, hLI, hXX, hYY⟩ := finite_gram_placement x y hx hy d f hw
  let K : Mat k := L.conjTranspose * L
  have hK : IsUnit K := ((Matrix.isUnit_conjTranspose L).mpr hL).mul hL
  have hGram : K = L.conjTranspose * L := rfl
  have hHerm : K.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self L
  let E : Vec k ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) :=
    (WithLp.linearEquiv 2 ℂ (Vec k)).symm
  let F : Vec k →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := E.toLinearMap.comp L.mulVecLin
  have hF : Function.Injective F :=
    E.injective.comp (Matrix.mulVec_injective_iff_isUnit.mpr hL)
  have hinner (u v : Vec k) :
      inner ℂ (F u) (F v) = dotProduct (star u) (K.mulVec v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change dotProduct (star (L.mulVec u)) (L.mulVec v) = _
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hGram]
  let a : Fin n → EuclideanSpace ℂ (Fin k) := fun i => F (x i)
  let b : Fin n → EuclideanSpace ℂ (Fin k) := fun j => F (K.adjugate.mulVec (y j))
  have hdet : K.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det K).mp hK)
  have haa (i j : Fin n) : inner ℂ (a i) (a j) ≠ 0 := by
    change inner ℂ (F (x i)) (F (x j)) ≠ 0
    rw [hinner]
    exact hXX i j
  have hbb (i j : Fin n) : inner ℂ (b i) (b j) ≠ 0 := by
    change inner ℂ (F (K.adjugate.mulVec (y i)))
      (F (K.adjugate.mulVec (y j))) ≠ 0
    rw [hinner, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hHerm.adjugate.eq]
    exact mul_ne_zero hdet (hYY i j)
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · intro hz
      exact haa i i (by simp [hz])
    · intro hz
      exact hbb i i (by simp [hz])
  · intro i j
    change inner ℂ (F (x i)) (F (K.adjugate.mulVec (y j))) = 0 ↔ _
    rw [hinner, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_eq_zero.trans (or_iff_right hdet)
  · intro i j
    exact ⟨haa i j, hbb i j⟩
  · intro t
    have h := (hLI t).map' F (LinearMap.ker_eq_bot.mpr hF)
    have heq : (fun q => Sum.elim a b (f t q)) =
        F ∘ (fun q => mixed x y (L.conjTranspose * L).adjugate (f t q)) := by
      funext q
      cases hf : f t q <;> simp [Function.comp_apply, hf, mixed, a, b, K]
    rw [heq]
    exact h

end
end P14Hermitian


/- Source: literature/SeedAssembly.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Assemble all finite mixed rank tests into one Hermitian seed family. -/

noncomputable section

open Function Submodule

namespace P14SeedAssembly

abbrev Vec (k : ℕ) := Fin k → ℂ

/-- Pure rank conditions suffice for the mixed Hermitian seed conditions. -/
theorem seed_of_pure_ranks {k n : ℕ} (hk : 2 ≤ k) (hn : k - 1 ≤ n)
    (x y : Fin n → Vec k)
    (hx0 : ∀ i, x i ≠ 0) (hy0 : ∀ i, y i ≠ 0)
    (hx : ∀ f : Fin (k - 1) → Fin n, Injective f →
      LinearIndependent ℂ (x ∘ f))
    (hy : ∀ f : Fin (k - 1) → Fin n, Injective f →
      LinearIndependent ℂ (y ∘ f))
    (hx' : ∀ f : Fin (k + 1) → Fin n, Injective f →
      span ℂ (Set.range (x ∘ f)) = ⊤)
    (hy' : ∀ f : Fin (k + 1) → Fin n, Injective f →
      span ℂ (Set.range (y ∘ f)) = ⊤) :
    ∃ a b : Fin n → EuclideanSpace ℂ (Fin k),
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (∀ i j, inner ℂ (a i) (b j) = 0 ↔ dotProduct (star (x i)) (y j) = 0) ∧
      (∀ i j, inner ℂ (a i) (a j) ≠ 0 ∧ inner ℂ (b i) (b j) ≠ 0) ∧
      (∀ S : Finset (Fin n ⊕ Fin n), S.card + 1 ≤ k →
        LinearIndependent ℂ (fun i : (S : Set (Fin n ⊕ Fin n)) =>
          Sum.elim a b i.1)) ∧
      (∀ S : Finset (Fin n ⊕ Fin n), S.card = k + 1 →
        span ℂ (Set.range (fun i : (S : Set (Fin n ⊕ Fin n)) =>
          Sum.elim a b i.1)) = ⊤) := by
  classical
  have hxs := P14MixedRanks.smallSelections_of_exact x hn hx
  have hys := P14MixedRanks.smallSelections_of_exact y hn hy
  let Small := Σ d : Fin k,
    {f : Fin d.val → Fin n ⊕ Fin n // Injective f}
  let Big := {f : Fin (k + 1) → Fin n ⊕ Fin n // Injective f}
  have hb (f : Big) : ∃ e : Fin k → Fin (k + 1), Injective e ∧
      ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
        LinearIndependent ℂ (fun q =>
          P14Hermitian.mixed x y G (f.val (e q))) := by
    exact P14MixedRanks.large_selection_gl hk x y hxs hys hx' hy' f.val f.property
  choose pick hpick hwbig using hb
  let T := Small ⊕ Big
  let d : T → ℕ := Sum.elim (fun t => t.1.val) (fun _ => k)
  let f : (t : T) → Fin (d t) → Fin n ⊕ Fin n := fun t =>
    match t with
    | .inl t => t.2.val
    | .inr t => t.val ∘ pick t
  have hw (t : T) : ∃ G : Matrix (Fin k) (Fin k) ℂ, IsUnit G.det ∧
      LinearIndependent ℂ (fun q => P14Hermitian.mixed x y G (f t q)) := by
    cases t with
    | inl t =>
      exact P14MixedRanks.small_selection_gl x y hxs hys t.1.isLt t.2.val t.2.property
    | inr t => exact hwbig t
  obtain ⟨a, b, hnz, hcross, hsame, htest⟩ :=
    P14Hermitian.finite_hermitian_placement x y hx0 hy0 d f hw
  refine ⟨a, b, hnz, hcross, hsame, ?_, ?_⟩
  · intro S hS
    let e : (S : Set (Fin n ⊕ Fin n)) ≃ Fin S.card :=
      Fintype.equivFinOfCardEq (by simp)
    let s : Fin S.card → Fin n ⊕ Fin n := fun q => (e.symm q).val
    have hs : Injective s := Subtype.val_injective.comp e.symm.injective
    let t : T := .inl ⟨⟨S.card, by omega⟩, ⟨s, hs⟩⟩
    have ht := (htest t).comp e e.injective
    change LinearIndependent ℂ
      (fun i : (S : Set (Fin n ⊕ Fin n)) =>
        Sum.elim a b (e.symm (e i)).val) at ht
    simpa using ht
  · intro S hS
    let e : (S : Set (Fin n ⊕ Fin n)) ≃ Fin (k + 1) :=
      Fintype.equivFinOfCardEq (by simpa using hS)
    let s : Fin (k + 1) → Fin n ⊕ Fin n := fun q => (e.symm q).val
    have hs : Injective s := Subtype.val_injective.comp e.symm.injective
    let t : Big := ⟨s, hs⟩
    have ht := htest (.inr t)
    let w : Fin k → EuclideanSpace ℂ (Fin k) :=
      fun q => Sum.elim a b (s (pick t q))
    have hli : LinearIndependent ℂ w := ht
    have htop : span ℂ (Set.range w) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hli]
      simp
    have hsub : span ℂ (Set.range w) ≤
        span ℂ (Set.range (fun i : (S : Set (Fin n ⊕ Fin n)) =>
          Sum.elim a b i.1)) := by
      apply span_mono
      rintro v ⟨q, rfl⟩
      exact ⟨e.symm (pick t q), rfl⟩
    rw [htop] at hsub
    exact top_unique hsub

end P14SeedAssembly
end


/- Source: cusp_assembly/SeedFinalLocal.lean. Reused authorship is retained in the source comments and artifact citations. -/
namespace Submissions.EllipticBipartiteSeedFamily.CuspAssembly


/-- The even translate offsets. -/
def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

/-- The odd anti-translate offsets
`1,3,...,2r-3,2r+1`. -/
def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

/-- Balanced translate/anti-translate incidence. -/
def CrossAdj {r N : ℕ} (i j : ZMod (2 * N)) : Prop :=
  (∃ c : Fin r, j = i + cOffset c) ∨
  (∃ d : Fin r, j = -i + dOffset d)

/-- Finite-index version of the cyclic incidence relation. -/
def CrossAdjFin {r N : ℕ} (i j : Fin (2 * N)) : Prop :=
  CrossAdj (r := r) (N := N) (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N))

def Tight {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ S : Finset ι, S.card + 1 ≤ k →
    LinearIndependent ℂ fun i : (S : Set ι) => v i.1

def KPlusOneSpanning {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ S : Finset ι, S.card = k + 1 →
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i.1) = ⊤

/-- The elliptic normal curve seed family. -/
abbrev statement : Prop :=
  ∀ r N : ℕ, 2 ≤ r → r + 2 ≤ N →
    let k := 2 * r
    let n := 2 * N
    ∃ a b : Fin n → EuclideanSpace ℂ (Fin k),
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (∀ i j, inner ℂ (a i) (b j) = 0 ↔
        CrossAdjFin (r := r) (N := N) i j) ∧
      (∀ i j, i ≠ j →
        inner ℂ (a i) (a j) ≠ 0 ∧ inner ℂ (b i) (b j) ≠ 0) ∧
      Tight (Sum.elim a b) ∧
      KPlusOneSpanning (Sum.elim a b)


theorem proof : statement := by
  intro r N hr hN
  obtain ⟨x, y, h0, hcross, hsmall, hlarge⟩ :=
    Submissions.CuspBilinearSeedFamilies.Assembly.proof r N hr hN
  obtain ⟨a, b, hab0, hab, hsame, htight, hspan⟩ :=
    P14SeedAssembly.seed_of_pure_ranks (by omega) (by omega) x y
      (fun i => (h0 i).1) (fun i => (h0 i).2)
      (fun f hf => (hsmall f hf).1) (fun f hf => (hsmall f hf).2)
      (fun f hf => (hlarge f hf).1) (fun f hf => (hlarge f hf).2)
  refine ⟨a, b, hab0, ?_, ?_, htight, hspan⟩
  · intro i j
    rw [hab]
    simpa only [dotProduct, Pi.star_apply, CrossAdjFin, CrossAdj, cOffset, dOffset,
      Submissions.CuspBilinearSeedFamilies.Assembly.CuspAllRankMinor.CrossAdj,
      Submissions.CuspBilinearSeedFamilies.Assembly.CuspAllRankMinor.cOffset,
      Submissions.CuspBilinearSeedFamilies.Assembly.CuspAllRankMinor.dOffset]
      using hcross i j
  · intro i j _
    exact hsame i j

end Submissions.EllipticBipartiteSeedFamily.CuspAssembly


/- Source: cusp_assembly/CuspQuarticSeed.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The proved r=2 s55 family supplies every quartic seed order 4*N, N≥4.
The graph proof adds the explicit connectivity and degree obligations. -/

noncomputable section
namespace P14CuspQuarticSeed
open Submodule P14SeedInterface

-- Reused from the existing EvenHalfUPB adapter, retaining the exact cast map.
def finZEquiv (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun := fun i => (i.val : ZMod n)
  invFun := fun i => ⟨i.val,ZMod.val_lt i⟩
  left_inv := by intro i; apply Fin.ext; exact ZMod.val_natCast_of_lt i.isLt
  right_inv := ZMod.natCast_zmod_val

theorem proof (N : ℕ) (hN : 4 ≤ N) : Seed (4*N) := by
  classical
  let : NeZero (2*N) := ⟨by omega⟩
  let V := Fin (2*N) ⊕ Fin (2*N)
  let eZ : V ≃ P14CrossComplement.Vertex N := Equiv.sumCongr (finZEquiv (2*N)) (finZEquiv (2*N))
  let G := (P14CuspSeedGraph.graph hN).comap eZ
  let iso : G ≃g P14CuspSeedGraph.graph hN := SimpleGraph.Iso.comap eZ _
  let e : Fin (4*N) ≃ V := (Fintype.equivFinOfCardEq (by simp [V];omega)).symm
  obtain ⟨a,b,hab0,hab,hsame,htight,hspan⟩ :=
    Submissions.EllipticBipartiteSeedFamily.CuspAssembly.proof 2 N (by decide) hN
  let C : EuclideanSpace ℂ (Fin 4) ≃ₗ[ℂ] (Fin 4 → ℂ) := WithLp.linearEquiv 2 ℂ (Fin 4 → ℂ)
  let u : V → EuclideanSpace ℂ (Fin 4) := Sum.elim a b
  let v : V → Fin 4 → ℂ := fun i => C (u i)
  have hu0 : ∀ i, u i ≠ 0 := by
    rintro (i | i)
    · exact (hab0 i).1
    · exact (hab0 i).2
  have hp (i j : V) : pair (v i) (v j) = inner ℂ (u i) (u j) := by
    simp [pair,v,C,PiLp.inner_apply,RCLike.inner_apply,mul_comm]
  have hc (i j : Fin (2*N)) : inner ℂ (a i) (b j) = 0 ↔ G.Adj (.inl i) (.inr j) := by
    rw [hab]
    change _ ↔ (P14CuspSeedGraph.graph hN).Adj (.inl (i.val : ZMod (2*N)))
      (.inr (j.val : ZMod (2*N)))
    rw [P14CuspSeedGraph.cross_iff]
    rfl
  apply P14ComplexSeedInterface.of_family e G
    (iso.connected_iff.mpr (P14CuspSeedGraph.connected hN))
    (fun i => (iso.degree_eq i).symm.trans (P14CuspSeedGraph.degree hN (eZ i))) v
  · intro i hi
    exact hu0 i (C.map_eq_zero_iff.mp hi)
  · intro i j
    rw [hp]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hn : inner ℂ (a i) (a j) ≠ 0 := by
          by_cases h : i=j
          · subst j
            exact fun h => (hab0 i).1 (inner_self_eq_zero.mp h)
          · exact (hsame i j h).1
        exact iff_of_false hn (P14CuspSeedGraph.same_left hN _ _)
      | inr j => exact hc i j
    | inr i =>
      cases j with
      | inl j =>
        rw [inner_eq_zero_symm]
        exact (hc j i).trans (G.adj_comm (.inl j) (.inr i))
      | inr j =>
        have hn : inner ℂ (b i) (b j) ≠ 0 := by
          by_cases h : i=j
          · subst j
            exact fun h => (hab0 i).2 (inner_self_eq_zero.mp h)
          · exact (hsame i j h).2
        exact iff_of_false hn (P14CuspSeedGraph.same_right hN _ _)
  · intro d hd f hf
    let S : Finset V := Finset.univ.image f
    have hS : S.card=d := by simp [S,Finset.card_image_of_injective _ hf]
    have ht := htight S (by change S.card+1≤4;omega)
    let g : Fin d → (S : Set V) := fun q => ⟨f q,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩⟩
    have hg : Function.Injective g := by
      intro i j he
      exact hf (congrArg Subtype.val he)
    have hh := ((ht.comp g hg).map' C.toLinearMap C.ker)
    simpa [v,u,g,Function.comp_def] using hh
  · intro f hf
    let S : Finset V := Finset.univ.image f
    have hS : S.card=5 := by simp [S,Finset.card_image_of_injective _ hf]
    have ht := congrArg (Submodule.map C.toLinearMap) (hspan S hS)
    have hc : span ℂ (Set.range fun i : (S : Set V) => v i.val) = ⊤ := by
      simpa [v,u,Submodule.map_span,← Set.range_comp,Function.comp_def,
        Submodule.map_top,LinearMap.range_eq_top.mpr C.surjective] using ht
    have he : Set.range (fun i : (S : Set V) => v i.val) = Set.range (fun q => v (f q)) := by
      ext y
      constructor
      · rintro ⟨i,rfl⟩
        obtain ⟨q,_,hq⟩ := Finset.mem_image.mp i.property
        exact ⟨q,congrArg v hq⟩
      · rintro ⟨q,rfl⟩
        exact ⟨⟨f q,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩⟩,rfl⟩
    rwa [he] at hc

end P14CuspQuarticSeed
end


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


/- Source: literature/TenSeedReused.lean. Reused authorship is retained in the source comments and artifact citations. -/
/- Reused unchanged proof body by woshuajolk, Jig p14 TightSpanningOrthRep4C10.
Artifact 268246ab-9321-43c2-9ca2-6dacae09d11c; original SHA256
283db1b3a3de14aadbbfae8ed99815f7dc5d7f6a5ddbe063f70d095a3fb6ac6f.
Only imports and enclosing namespace were changed for a standalone local closure. -/

namespace P14TenSeedReused

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def vZ : Fin 10 → Fin 4 → ℤ
  | ⟨0, _⟩ => ![1, 0, 0, 0]
  | ⟨1, _⟩ => ![0, 2, -1, 0]
  | ⟨2, _⟩ => ![0, 0, 0, 2]
  | ⟨3, _⟩ => ![1, 1, 2, 0]
  | ⟨4, _⟩ => ![2, -2, 0, 0]
  | ⟨5, _⟩ => ![-2, -2, 2, 2]
  | ⟨6, _⟩ => ![-2, -2, -2, -2]
  | ⟨7, _⟩ => ![2, -2, 2, -2]
  | ⟨8, _⟩ => ![0, -2, 0, 2]
  | ⟨9, _⟩ => ![0, -1, -2, -1]

def v (i : Fin 10) : Fin 4 → ℂ := fun r => (vZ i r : ℂ)

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def det4Z (x y z t : Fin 4 → ℤ) : ℤ :=
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

def minor3 (x y z : Fin 4 → ℤ) (c0 c1 c2 : Fin 4) : ℤ :=
  x c0 * y c1 * z c2 - x c0 * y c2 * z c1
    - x c1 * y c0 * z c2 + x c1 * y c2 * z c0
    + x c2 * y c0 * z c1 - x c2 * y c1 * z c0

theorem nzV : ∀ i : Fin 10, ∃ r, vZ i r ≠ 0 := by decide

theorem orthExact :
    ∀ i j : Fin 10, i ≠ j →
      ((let d := (i.val + 10 - j.val) % 10; min d (10 - d) = 1 ∨
        let d := (i.val + 10 - j.val) % 10; min d (10 - d) = 2) ↔
        dot4Z (vZ i) (vZ j) = 0) := by decide

theorem span5 :
    ∀ i j k l t : Fin 10, i < j → j < k → k < l → l < t →
      det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ i) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ i) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ i) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem tight3 :
    ∀ i j k : Fin 10, i < j → j < k →
      minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0 := by decide

lemma dot4_cast (x y : Fin 4 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot4Z x y : ℂ) := by
  simp [dot4Z, Fin.sum_univ_four, star_intCast]

lemma linInd_of_det4 {x y z t : Fin 4 → ℤ} (hd : det4Z x y z t ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ)),
      (fun r : Fin 4 => (t r : ℂ))] := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ), (z 3 : ℂ);
       (t 0 : ℂ), (t 1 : ℂ), (t 2 : ℂ), (t 3 : ℂ)]
  have hdet : M.det = (det4Z x y z t : ℂ) := by
    simp [M, Matrix.det_succ_row_zero, det4Z, Fin.sum_univ_succ,
      Fin.val_succ, Fin.val_eq_zero, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 4 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam :
      (fun i : Fin 4 => M i) =
        ![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ), fun r => (t r : ℂ)] := by
    ext i r; fin_cases i <;> fin_cases r <;> simp [M]
  rwa [hfam] at hrows

lemma linInd_v4 (i j k l : Fin 10) (hd : det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k, v l] := by
  have h := linInd_of_det4 hd
  convert h using 1
  ext s r; fin_cases s <;> simp [v]

lemma linInd3_of_minor012 {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 0 1 2 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have : M.det = (minor3 x y z 0 1 2 : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [this]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) (0 : Fin 4), LinearMap.proj (R := ℂ) (1 : Fin 4),
      LinearMap.proj (R := ℂ) (2 : Fin 4)]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) =
        fun i => M i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, M]
  have : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ this

lemma linInd3_of_minor013 {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 0 1 3 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 3 : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have : M.det = (minor3 x y z 0 1 3 : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [this]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) (0 : Fin 4), LinearMap.proj (R := ℂ) (1 : Fin 4),
      LinearMap.proj (R := ℂ) (3 : Fin 4)]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) =
        fun i => M i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, M]
  have : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ this

lemma linInd3_of_minor023 {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 0 2 3 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 0 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 2 : ℂ), (z 3 : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have : M.det = (minor3 x y z 0 2 3 : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [this]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) (0 : Fin 4), LinearMap.proj (R := ℂ) (2 : Fin 4),
      LinearMap.proj (R := ℂ) (3 : Fin 4)]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) =
        fun i => M i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, M]
  have : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ this

lemma linInd3_of_minor123 {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 1 2 3 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 1 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 1 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 1 : ℂ), (z 2 : ℂ), (z 3 : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have : M.det = (minor3 x y z 1 2 3 : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [this]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) (1 : Fin 4), LinearMap.proj (R := ℂ) (2 : Fin 4),
      LinearMap.proj (R := ℂ) (3 : Fin 4)]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) =
        fun i => M i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, M]
  have : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ this

lemma linInd3_cols {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 0 1 2 ≠ 0 ∨ minor3 x y z 0 1 3 ≠ 0 ∨
          minor3 x y z 0 2 3 ≠ 0 ∨ minor3 x y z 1 2 3 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  rcases hd with h | h | h | h
  · exact linInd3_of_minor012 h
  · exact linInd3_of_minor013 h
  · exact linInd3_of_minor023 h
  · exact linInd3_of_minor123 h

lemma linInd_v3 (i j k : Fin 10)
    (hd : minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
          minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
          minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
          minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k] := by
  have h := linInd3_cols hd
  convert h using 1
  ext s r; fin_cases s <;> simp [v]

theorem proof :
    ∃ v : Fin 10 → Fin 4 → ℂ,
      (∀ i, v i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (((let d := (i.val + 10 - j.val) % 10; min d (10 - d)) = 1 ∨
          (let d := (i.val + 10 - j.val) % 10; min d (10 - d)) = 2) ↔
          (∑ r, star (v i r) * v j r) = 0)) ∧
      (∀ i j k l t : Fin 10, i < j → j < k → k < l → l < t →
        LinearIndependent ℂ ![v i, v j, v k, v l] ∨
        LinearIndependent ℂ ![v i, v j, v k, v t] ∨
        LinearIndependent ℂ ![v i, v j, v l, v t] ∨
        LinearIndependent ℂ ![v i, v k, v l, v t] ∨
        LinearIndependent ℂ ![v j, v k, v l, v t]) ∧
      (∀ i j k : Fin 10, i < j → j < k → LinearIndependent ℂ ![v i, v j, v k]) := by
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨r, hr⟩ := nzV i
    apply hr
    have h := congr_fun hi r
    simpa [v] using h
  · intro i j hij
    constructor
    · intro he
      have hz : dot4Z (vZ i) (vZ j) = 0 := (orthExact i j hij).mp (by simpa using he)
      have hdot : (∑ r, star (v i r) * v j r) = (dot4Z (vZ i) (vZ j) : ℂ) := by
        simpa [v] using dot4_cast (vZ i) (vZ j)
      rw [hdot]; exact_mod_cast hz
    · intro hip
      have hdot : (∑ r, star (v i r) * v j r) = (dot4Z (vZ i) (vZ j) : ℂ) := by
        simpa [v] using dot4_cast (vZ i) (vZ j)
      have hz : dot4Z (vZ i) (vZ j) = 0 := by
        have := hdot.symm.trans hip; exact_mod_cast this
      exact (orthExact i j hij).mpr hz
  · intro i j k l t hij hjk hkl hlt
    rcases span5 i j k l t hij hjk hkl hlt with h | h | h | h | h
    · exact Or.inl (linInd_v4 i j k l h)
    · exact Or.inr <| Or.inl (linInd_v4 i j k t h)
    · exact Or.inr <| Or.inr <| Or.inl (linInd_v4 i j l t h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (linInd_v4 i k l t h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (linInd_v4 j k l t h)
  · intro i j k hij hjk
    exact linInd_v3 i j k (tight3 i j k hij hjk)

end P14TenSeedReused


/- Source: literature/SortedSeedAdapter.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Promote the sorted finite-rank interfaces of the existing ten- and
twelve-state certificates to the exact reusable seed predicate. -/

namespace P14SortedSeedAdapter
open P14SeedInterface Submodule

def Rank4of5 {m : ℕ} (v : Fin m → Fin 4 → ℂ) (i j k l t : Fin m) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

theorem small {m : ℕ} (hm : 3 ≤ m) (v : Fin m → Fin 4 → ℂ)
    (h3 : ∀ i j k : Fin m, i < j → j < k →
      LinearIndependent ℂ ![v i,v j,v k])
    (S : Finset (Fin m)) (hS : S.card ≤ 3) :
    LinearIndependent ℂ (fun i : (S : Set (Fin m)) => v i) := by
  classical
  obtain ⟨T,hST,hT⟩ := Finset.exists_superset_card_eq hS (by simpa using hm)
  let e : Fin 3 ≃o (T : Set (Fin m)) := T.orderIsoOfFin hT
  have h01 : (e 0).val < (e 1).val := e.strictMono (by decide)
  have h12 : (e 1).val < (e 2).val := e.strictMono (by decide)
  have h := h3 (e 0) (e 1) (e 2) h01 h12
  have he : ![v (e 0),v (e 1),v (e 2)] = fun q => v (e q) := by
    ext q
    fin_cases q <;> rfl
  rw [he] at h
  have ht : LinearIndependent ℂ (fun i : (T : Set (Fin m)) => v i) := by
    simpa only [Function.comp_def, e.apply_symm_apply] using h.comp e.symm e.symm.injective
  exact ht.comp (fun i : (S : Set (Fin m)) => (⟨i.val,hST i.property⟩ : (T : Set (Fin m))))
    (fun i j h => Subtype.ext (congrArg (fun x : (T : Set (Fin m)) => x.val) h))

lemma survivor_four {m : ℕ} (v : Fin m → Fin 4 → ℂ) (S : Finset (Fin m))
    (i j k l : Fin m) (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S) (hl : l ∈ S)
    (hli : LinearIndependent ℂ ![v i,v j,v k,v l])
    (a : Fin 4 → ℂ) (ha : a ≠ 0) : ∃ q ∈ S, pair a (v q) ≠ 0 := by
  have hs : span ℂ (Set.range ![v i,v j,v k,v l]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  obtain ⟨q,hq⟩ := spanning_survivor _ hs a ha
  fin_cases q
  · exact ⟨i,hi,hq⟩
  · exact ⟨j,hj,hq⟩
  · exact ⟨k,hk,hq⟩
  · exact ⟨l,hl,hq⟩

theorem five {m : ℕ} (v : Fin m → Fin 4 → ℂ)
    (h5 : ∀ i j k l t : Fin m, i < j → j < k → k < l → l < t →
      Rank4of5 v i j k l t)
    (S : Finset (Fin m)) (hS : S.card = 5) (a : Fin 4 → ℂ) (ha : a ≠ 0) :
    ∃ i ∈ S, pair a (v i) ≠ 0 := by
  classical
  let e : Fin 5 ≃o (S : Set (Fin m)) := S.orderIsoOfFin hS
  have h01 : (e 0).val < (e 1).val := e.strictMono (by decide)
  have h12 : (e 1).val < (e 2).val := e.strictMono (by decide)
  have h23 : (e 2).val < (e 3).val := e.strictMono (by decide)
  have h34 : (e 3).val < (e 4).val := e.strictMono (by decide)
  rcases h5 (e 0) (e 1) (e 2) (e 3) (e 4) h01 h12 h23 h34 with h | h | h | h | h
  · exact survivor_four v S _ _ _ _ (e 0).property (e 1).property
      (e 2).property (e 3).property h a ha
  · exact survivor_four v S _ _ _ _ (e 0).property (e 1).property
      (e 2).property (e 4).property h a ha
  · exact survivor_four v S _ _ _ _ (e 0).property (e 1).property
      (e 3).property (e 4).property h a ha
  · exact survivor_four v S _ _ _ _ (e 0).property (e 2).property
      (e 3).property (e 4).property h a ha
  · exact survivor_four v S _ _ _ _ (e 1).property (e 2).property
      (e 3).property (e 4).property h a ha

theorem of_sorted {m : ℕ} (hm : 3 ≤ m) (v : Fin m → Fin 4 → ℂ)
    (E : Fin m → Fin m → Prop) [DecidableRel E]
    (hnz : ∀ i, v i ≠ 0)
    (hedge : ∀ i j, pair (v i) (v j) = 0 ↔ E i j)
    (hdegree : ∀ i, ((Finset.univ : Finset (Fin m)).filter (E i)).card = 4)
    (hconn : (SimpleGraph.fromRel E).Connected)
    (h3 : ∀ i j k : Fin m, i < j → j < k →
      LinearIndependent ℂ ![v i,v j,v k])
    (h5 : ∀ i j k l t : Fin m, i < j → j < k → k < l → l < t →
      Rank4of5 v i j k l t) : Seed m := by
  classical
  refine ⟨v,fun i => Finset.univ.filter (E i),hnz,?_,hdegree,?_,small hm v h3,five v h5⟩
  · intro i j
    simpa using hedge i j
  · have he : orthGraph v = SimpleGraph.fromRel E := by
      ext i j
      simp only [orthGraph, SimpleGraph.fromRel_adj, hedge]
    rw [he]
    exact hconn

end P14SortedSeedAdapter


/- Source: literature/TenSeed.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! The existing woshuajolk C10(1,2) certificate, adapted to Seed 10.
No new vectors or rank certificates are introduced. -/

namespace P14TenSeed
open P14SeedInterface P14SortedSeedAdapter
open scoped ComplexOrder

def edge (i j : Fin 10) : Prop := i ≠ j ∧
  ((let d := (i.val + 10 - j.val) % 10; min d (10-d)) = 1 ∨
   (let d := (i.val + 10 - j.val) % 10; min d (10-d)) = 2)

instance : DecidableRel edge := fun _ _ => by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 10) := SimpleGraph.fromRel edge

lemma degrees : ∀ i, ((Finset.univ : Finset (Fin 10)).filter (edge i)).card = 4 := by
  decide +kernel

lemma connected : graph.Connected := by
  have step : ∀ i j : Fin 10, i ≠ j → edge i j → graph.Reachable i j :=
    fun i j hne he => ((SimpleGraph.fromRel_adj edge i j).mpr ⟨hne,Or.inl he⟩).reachable
  have r0 : graph.Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have r1 : graph.Reachable 0 1 := step 0 1 (by decide) (by decide)
  have r2 := r1.trans (step 1 2 (by decide) (by decide))
  have r3 := r2.trans (step 2 3 (by decide) (by decide))
  have r4 := r3.trans (step 3 4 (by decide) (by decide))
  have r5 := r4.trans (step 4 5 (by decide) (by decide))
  have r6 := r5.trans (step 5 6 (by decide) (by decide))
  have r7 := r6.trans (step 6 7 (by decide) (by decide))
  have r8 := r7.trans (step 7 8 (by decide) (by decide))
  have r9 := r8.trans (step 8 9 (by decide) (by decide))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0,?_⟩
  intro i
  fin_cases i <;> assumption

theorem proof : Seed 10 := by
  obtain ⟨v,hnz,hedge,h5,h3⟩ := P14TenSeedReused.proof
  apply of_sorted (by decide) v edge hnz ?_ degrees connected h3 h5
  intro i j
  by_cases hij : i = j
  · subst j
    have hn : pair (v i) (v i) ≠ 0 := by
      exact fun h => hnz i (dotProduct_star_self_eq_zero.mp h)
    simp [edge,hn]
  · exact ((hedge i j hij).symm).trans (by simp [edge,hij])

end P14TenSeed


/- Source: literature/TwelveSeedReused.lean. Reused authorship is retained in the source comments and artifact citations. -/
/- Reused unchanged proof body by woshuajolk, Jig p14 ThreeBasisSeedK4M12.
Artifact 25b8a6a9-ad78-4c79-a8ba-bffa4987012c; original SHA256
49fde486ddb0fe597ef81741d72d58c7736cbee6e5f12017fb12e53facfc9a5a.
Only imports and enclosing namespace were changed for a standalone local closure. -/

namespace P14TwelveSeedReused

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def pair (x y : Fin 4 → ℂ) : ℂ := ∑ r, star (x r) * y r

def crossMatch (i j : Fin 12) : Prop :=
  (i.val = 0 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0) ∨
  (i.val = 1 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 1) ∨
  (i.val = 2 ∧ j.val = 10) ∨ (i.val = 10 ∧ j.val = 2) ∨
  (i.val = 3 ∧ j.val = 11) ∨ (i.val = 11 ∧ j.val = 3) ∨
  (i.val = 6 ∧ j.val = 8) ∨ (i.val = 8 ∧ j.val = 6) ∨
  (i.val = 7 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 7)

def edge (i j : Fin 12) : Prop :=
  i ≠ j ∧ (i.val / 4 = j.val / 4 ∨ crossMatch i j)

instance crossMatchDecidable (i j : Fin 12) : Decidable (crossMatch i j) := by
  unfold crossMatch
  infer_instance

instance edgeDecidable (i j : Fin 12) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel edge

def Rank4of5 (v : Fin 12 → Fin 4 → ℂ) (i j k l t : Fin 12) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

def vZ : Fin 12 → Fin 4 → ℤ := ![
  ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
  ![0, 1, 1, 1], ![1, 0, 1, -1], ![1, -3, 1, 2], ![3, 1, -2, 1],
  ![12, 4, -14, 7], ![-4, 12, -7, -14], ![7, -7, 0, -8], ![7, 7, 8, 0]
]

def v (i : Fin 12) : Fin 4 → ℂ := fun r => (vZ i r : ℂ)

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def minor3 (x y z : Fin 4 → ℤ) (c0 c1 c2 : Fin 4) : ℤ :=
  x c0 * y c1 * z c2 - x c0 * y c2 * z c1
    - x c1 * y c0 * z c2 + x c1 * y c2 * z c0
    + x c2 * y c0 * z c1 - x c2 * y c1 * z c0

def det4Z (x y z t : Fin 4 → ℤ) : ℤ :=
  x 0 * y 1 * z 2 * t 3 - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3 + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2 - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3 + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3 - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2 + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3 - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3 + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1 - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2 + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2 - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1 + x 3 * y 2 * z 1 * t 0

lemma nz : ∀ i : Fin 12, ∃ r, vZ i r ≠ 0 := by decide +kernel
lemma orthZ : ∀ i j : Fin 12, dot4Z (vZ i) (vZ j) = 0 ↔ edge i j := by
  decide +kernel
lemma degrees : ∀ i, ((Finset.univ : Finset (Fin 12)).filter (edge i)).card = 4 := by
  decide +kernel
lemma triples : ∀ i j k : Fin 12, i < j → j < k →
    minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0 := by
  decide +kernel
lemma quintuples : ∀ i j k l t : Fin 12, i < j → j < k → k < l → l < t →
    det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
    det4Z (vZ i) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
    det4Z (vZ i) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
    det4Z (vZ i) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
    det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by
  decide +kernel

lemma adjOf {i j : Fin 12} (hne : i ≠ j) (he : edge i j) : graph.Adj i j :=
  (SimpleGraph.fromRel_adj edge i j).mpr ⟨hne, Or.inl he⟩

lemma connected : graph.Connected := by
  have step : ∀ i j : Fin 12, i ≠ j → edge i j → graph.Reachable i j :=
    fun i j hne he => (adjOf hne he).reachable
  have r0 : graph.Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have r1 : graph.Reachable 0 1 := step 0 1 (by decide) (by decide)
  have r2 := r1.trans (step 1 2 (by decide) (by decide))
  have r3 := r2.trans (step 2 3 (by decide) (by decide))
  have r4 : graph.Reachable 0 4 := step 0 4 (by decide) (by decide)
  have r5 := r4.trans (step 4 5 (by decide) (by decide))
  have r6 := r5.trans (step 5 6 (by decide) (by decide))
  have r7 := r6.trans (step 6 7 (by decide) (by decide))
  have r8 := r6.trans (step 6 8 (by decide) (by decide))
  have r9 := r8.trans (step 8 9 (by decide) (by decide))
  have r10 := r9.trans (step 9 10 (by decide) (by decide))
  have r11 := r10.trans (step 10 11 (by decide) (by decide))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro w
  fin_cases w <;> assumption

lemma dot4_cast (x y : Fin 4 → ℤ) : pair (fun r => (x r : ℂ)) (fun r => (y r : ℂ)) =
    (dot4Z x y : ℂ) := by
  simp [pair, dot4Z, Fin.sum_univ_four, star_intCast]

lemma linInd_of_det4 {x y z t : Fin 4 → ℤ} (hd : det4Z x y z t ≠ 0) :
    LinearIndependent ℂ ![fun r => (x r : ℂ), fun r => (y r : ℂ),
      fun r => (z r : ℂ), fun r => (t r : ℂ)] := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ), (z 3 : ℂ);
       (t 0 : ℂ), (t 1 : ℂ), (t 2 : ℂ), (t 3 : ℂ)]
  have hdet : M.det = (det4Z x y z t : ℂ) := by
    simp [M, Matrix.det_succ_row_zero, det4Z, Fin.sum_univ_succ,
      Fin.val_succ, Fin.val_eq_zero, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by rw [hdet]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 4 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam : (fun i : Fin 4 => M i) =
      ![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ),
        fun r => (t r : ℂ)] := by
    ext i r
    fin_cases i <;> fin_cases r <;> simp [M]
  rwa [hfam] at hrows

lemma linInd3_of_cols {x y z : Fin 4 → ℤ} (a b c : Fin 4)
    (hd : minor3 x y z a b c ≠ 0) :
    LinearIndependent ℂ ![fun r => (x r : ℂ), fun r => (y r : ℂ),
      fun r => (z r : ℂ)] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x a : ℂ), (x b : ℂ), (x c : ℂ);
       (y a : ℂ), (y b : ℂ), (y c : ℂ);
       (z a : ℂ), (z b : ℂ), (z c : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have heq : M.det = (minor3 x y z a b c : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [heq]
    exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) a, LinearMap.proj (R := ℂ) b,
      LinearMap.proj (R := ℂ) c]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ),
        fun r => (z r : ℂ)] i)) = fun i => M i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [φ, M]
  have hli : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ),
        fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ hli

lemma linInd_v3 (i j k : Fin 12)
    (hd : minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k] := by
  rcases hd with h | h | h | h
  · have q := linInd3_of_cols 0 1 2 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]
  · have q := linInd3_of_cols 0 1 3 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]
  · have q := linInd3_of_cols 0 2 3 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]
  · have q := linInd3_of_cols 1 2 3 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]

lemma linInd_v4 (i j k l : Fin 12)
    (hd : det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k, v l] := by
  have q := linInd_of_det4 hd
  convert q using 1
  ext s r
  fin_cases s <;> simp [v]

theorem proof :
  ∃ w : Fin 12 → Fin 4 → ℂ,
    (∀ i, w i ≠ 0) ∧
    (∀ i j, pair (w i) (w j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 12)).filter (edge i)).card = 4) ∧
    graph.Connected ∧
    (∀ i j k : Fin 12, i < j → j < k → LinearIndependent ℂ ![w i, w j, w k]) ∧
    (∀ i j k l t : Fin 12, i < j → j < k → k < l → l < t →
      Rank4of5 w i j k l t) := by
  refine ⟨v, ?_, ?_, degrees, connected, ?_, ?_⟩
  · intro i h
    obtain ⟨r, hr⟩ := nz i
    apply hr
    have := congrFun h r
    simpa [v] using this
  · intro i j
    change pair (fun r => (vZ i r : ℂ)) (fun r => (vZ j r : ℂ)) = 0 ↔ edge i j
    rw [dot4_cast, Int.cast_eq_zero]
    exact orthZ i j
  · intro i j k hij hjk
    exact linInd_v3 i j k (triples i j k hij hjk)
  · intro i j k l t hij hjk hkl hlt
    rcases quintuples i j k l t hij hjk hkl hlt with h | h | h | h | h
    · exact Or.inl (linInd_v4 i j k l h)
    · exact Or.inr (Or.inl (linInd_v4 i j k t h))
    · exact Or.inr (Or.inr (Or.inl (linInd_v4 i j l t h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (linInd_v4 i k l t h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (linInd_v4 j k l t h))))

end P14TwelveSeedReused


/- Source: literature/TwelveSeed.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Existing green s73 by woshuajolk, reindexed to the exact Seed 12 interface. -/

namespace P14TwelveSeed

theorem proof : P14SeedInterface.Seed 12 := by
  obtain ⟨v,hnz,hedge,hdegree,hconn,h3,h5⟩ := P14TwelveSeedReused.proof
  exact P14SortedSeedAdapter.of_sorted (by decide) v P14TwelveSeedReused.edge
    hnz hedge hdegree hconn h3 h5

end P14TwelveSeed


/- Source: cusp_assembly/EvenQuarticSeed.lean. Reused authorship is retained in the source comments and artifact citations. -/
/-! Every even seed order in dimension four. The finite endpoints reuse proofs by woshuajolk. The divisible-four family uses
our s55 assembly of woshuajolk components; the odd-half family fills the
remaining even orders. This is not the mixed-UPB root. -/

namespace P14EvenQuarticSeed

theorem proof (m : ℕ) (hm : 10 ≤ m) (heven : m % 2 = 0) :
    P14SeedInterface.Seed m := by
  by_cases h10 : m=10
  · simpa only [h10] using P14TenSeed.proof
  by_cases h12 : m=12
  · simpa only [h12] using P14TwelveSeed.proof
  have hmod : m % 4 = 0 ∨ m % 4 = 2 := by omega
  rcases hmod with hmod | hmod
  · have hN : 4 ≤ m/4 := by omega
    have he : 4*(m/4)=m := by omega
    simpa only [he] using P14CuspQuarticSeed.proof (m/4) hN
  · have hN : 3 ≤ m/4 := by omega
    have he : 4*(m/4)+2=m := by omega
    simpa only [he] using P14OddSeedFinal.proof (m/4) hN

end P14EvenQuarticSeed

theorem proof : ∀ m : ℕ, 10 ≤ m → m % 2 = 0 → P14SeedInterface.Seed m :=
  P14EvenQuarticSeed.proof

end Submissions.QuarticSeedEvenOrders.Assembly
