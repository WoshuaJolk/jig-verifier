import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Saved local p14 construction, flattened for standalone publication review.
Odd-dimensional construction follows Chenhao Wang, arXiv:2609.05657v1, Section 4.
Even-dimensional cycle derivation and Lean source are preserved local campaign work.
This is a known-result formalization, with no novelty or full-root claim. -/

namespace Submissions.J5P14TwoQubitsUPB.Proof

-- BEGIN preserved module QubitRayLabels
section PreservedQubitRayLabels

/-! Explicit qubit rays indexed by a nonnegative integer and a type bit.
The two types are (1,t) and (t,-1). Distinct labels give distinct rays,
so a nonzero complex test can annihilate at most one label, even when
many product rows deliberately reuse that label. -/

noncomputable section
namespace P14QubitRayLabels
open scoped BigOperators

abbrev Label := ℕ × Bool

def ray : Label → Fin 2 → ℂ
  | (t, false) => ![1, (t : ℂ)]
  | (t, true) => ![(t : ℂ), -1]

def pair (x y : Fin 2 → ℂ) : ℂ := ∑ i, star (x i) * y i

theorem ray_ne_zero (l : Label) : ray l ≠ 0 := by
  rcases l with ⟨t, b⟩
  cases b
  · intro h
    have h' := congrFun h 0
    simpa [ray] using h'
  · intro h
    have h' := congrFun h 1
    simpa [ray] using h'

theorem pair_false (t : ℕ) (y : Fin 2 → ℂ) :
    pair (ray (t, false)) y = y 0 + (t : ℂ) * y 1 := by
  simp [pair, ray, Fin.sum_univ_two]

theorem pair_true (t : ℕ) (y : Fin 2 → ℂ) :
    pair (ray (t, true)) y = (t : ℂ) * y 0 - y 1 := by
  simp [pair, ray, Fin.sum_univ_two, sub_eq_add_neg]

theorem opposite_pair (t : ℕ) (b : Bool) :
    pair (ray (t, b)) (ray (t, !b)) = 0 := by
  cases b <;> simp [pair, ray, Fin.sum_univ_two]

private theorem zero_of_coordinates (y : Fin 2 → ℂ)
    (h0 : y 0 = 0) (h1 : y 1 = 0) : y = 0 := by
  funext i
  fin_cases i <;> assumption

private theorem false_false_unique (s t : ℕ) (y : Fin 2 → ℂ) (hy : y ≠ 0)
    (hs : y 0 + (s : ℂ) * y 1 = 0)
    (ht : y 0 + (t : ℂ) * y 1 = 0) : s = t := by
  by_contra hst
  have hstC : (s : ℂ) - (t : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hst)
  have hmul : ((s : ℂ) - (t : ℂ)) * y 1 = 0 := by linear_combination hs - ht
  have h1 : y 1 = 0 := (mul_eq_zero.mp hmul).resolve_left hstC
  have h0 : y 0 = 0 := by simpa [h1] using hs
  exact hy (zero_of_coordinates y h0 h1)

private theorem true_true_unique (s t : ℕ) (y : Fin 2 → ℂ) (hy : y ≠ 0)
    (hs : (s : ℂ) * y 0 - y 1 = 0)
    (ht : (t : ℂ) * y 0 - y 1 = 0) : s = t := by
  by_contra hst
  have hstC : (s : ℂ) - (t : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hst)
  have hmul : ((s : ℂ) - (t : ℂ)) * y 0 = 0 := by linear_combination hs - ht
  have h0 : y 0 = 0 := (mul_eq_zero.mp hmul).resolve_left hstC
  have h1 : y 1 = 0 := by simpa [h0] using ht
  exact hy (zero_of_coordinates y h0 h1)

private theorem false_true_impossible (s t : ℕ) (y : Fin 2 → ℂ) (hy : y ≠ 0)
    (hs : y 0 + (s : ℂ) * y 1 = 0)
    (ht : (t : ℂ) * y 0 - y 1 = 0) : False := by
  have hpos : 0 < t * s + 1 := by omega
  have hc : (t : ℂ) * (s : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
  have hmul : ((t : ℂ) * (s : ℂ) + 1) * y 1 = 0 := by
    linear_combination (t : ℂ) * hs - ht
  have h1 : y 1 = 0 := (mul_eq_zero.mp hmul).resolve_left hc
  have h0 : y 0 = 0 := by simpa [h1] using hs
  exact hy (zero_of_coordinates y h0 h1)

theorem killed_labels_equal (l l' : Label) (y : Fin 2 → ℂ) (hy : y ≠ 0)
    (hl : pair (ray l) y = 0) (hl' : pair (ray l') y = 0) : l = l' := by
  rcases l with ⟨s, b⟩
  rcases l' with ⟨t, b'⟩
  cases b <;> cases b'
  · have h := false_false_unique s t y hy (by simpa [pair_false] using hl)
      (by simpa [pair_false] using hl')
    exact congrArg (fun n => (n, false)) h
  · exact (false_true_impossible s t y hy (by simpa [pair_false] using hl)
      (by simpa [pair_true] using hl')).elim
  · exact (false_true_impossible t s y hy (by simpa [pair_false] using hl')
      (by simpa [pair_true] using hl)).elim
  · have h := true_true_unique s t y hy (by simpa [pair_true] using hl)
      (by simpa [pair_true] using hl')
    exact congrArg (fun n => (n, true)) h

/-- A class may be chosen even when the test kills no label. The implication
is intentionally one-way, allowing unused labels and repeated product rows. -/
theorem exists_killing_label (y : Fin 2 → ℂ) (hy : y ≠ 0) :
    ∃ l : Label, ∀ l', pair (ray l') y = 0 → l' = l := by
  classical
  by_cases h : ∃ l, pair (ray l) y = 0
  · obtain ⟨l, hl⟩ := h
    exact ⟨l, fun l' hl' => killed_labels_equal l' l y hy hl' hl⟩
  · exact ⟨(0, false), fun l hl => (h ⟨l, hl⟩).elim⟩

end P14QubitRayLabels

end -- original noncomputable section
end PreservedQubitRayLabels
-- END preserved module QubitRayLabels

-- BEGIN preserved module CenteredSimplexEdges
section PreservedCenteredSimplexEdges

/-! Actual complex edge coordinates from the centered simplex. The one
orthonormal coordinate map is shared by all edges and all potential tests.
No graph, selected-span, or product-family existence is assumed here. -/

noncomputable section
namespace P14CenteredSimplexEdges
open Submodule
open scoped BigOperators

private abbrev Ambient (k : ℕ) := EuclideanSpace ℂ (Fin (k + 1))

private def ones (k : ℕ) : Ambient k := WithLp.toLp 2 (fun _ => 1)

private theorem ones_ne_zero (k : ℕ) : ones k ≠ 0 := by
  intro h
  have hi := congrArg (fun x : Ambient k => x 0) h
  simpa [ones] using hi

private abbrev centered (k : ℕ) : Submodule ℂ (Ambient k) := (ℂ ∙ ones k)ᗮ

private def coordinateIso (k : ℕ) :
    centered k ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin k) := by
  letI : Fact (Module.finrank ℂ (Ambient k) = k + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton
    (𝕜 := ℂ) (E := Ambient k) k (ones_ne_zero k)).repr

private theorem inner_ones (k : ℕ) (w : Ambient k) :
    inner ℂ (ones k) w = ∑ i, w i := by
  simp [ones, PiLp.inner_apply, RCLike.inner_apply]

private theorem centered_sum {k : ℕ} (w : centered k) :
    (∑ i, (w : Ambient k) i) = 0 := by
  have h : inner ℂ (ones k) (w : Ambient k) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  exact (inner_ones k w).symm.trans h

private def mean (k : ℕ) : ℂ := ((k + 1 : ℕ) : ℂ)⁻¹

private theorem cast_size_ne_zero (k : ℕ) : ((k + 1 : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)

private def simplex (k : ℕ) (i : Fin (k + 1)) : centered k :=
  ⟨EuclideanSpace.single i 1 - mean k • ones k, by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have hnorm : inner ℂ (ones k) (ones k) = ((k + 1 : ℕ) : ℂ) := by
      rw [inner_ones]
      simp [ones]
    rw [inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right, hnorm]
    simp only [ones, PiLp.toLp_apply, map_one, one_mul]
    change 1 - mean k * ((k + 1 : ℕ) : ℂ) = 0
    rw [mean, inv_mul_cancel₀ (cast_size_ne_zero k), sub_self]⟩

private def vertex (k : ℕ) : Option (Fin (k + 1)) → centered k
  | none => 0
  | some i => simplex k i

private theorem simplex_apply (k : ℕ) (i j : Fin (k + 1)) :
    (simplex k i : Ambient k) j = (if j = i then 1 else 0) - mean k := by
  simp [simplex, ones, PiLp.single_apply]

private def potentialOf {k : ℕ} (w : centered k) : Option (Fin (k + 1)) → ℂ
  | none => 0
  | some i => (w : Ambient k) i

private theorem vertex_inner {k : ℕ} (a : Option (Fin (k + 1)))
    (w : centered k) : inner ℂ (vertex k a) w = potentialOf w a := by
  cases a with
  | none => simp [vertex, potentialOf]
  | some i =>
    change inner ℂ (EuclideanSpace.single i 1 - mean k • ones k)
      (w : Ambient k) = (w : Ambient k) i
    have h : inner ℂ (ones k) (w : Ambient k) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
    rw [inner_sub_left, inner_smul_left, EuclideanSpace.inner_single_left, h]
    simp

private theorem diagonal_ne_zero {k : ℕ} (hk : 1 ≤ k) : (1 : ℂ) - mean k ≠ 0 := by
  intro h
  have hm : mean k = 1 := (sub_eq_zero.mp h).symm
  have hs : ((k + 1 : ℕ) : ℂ) * mean k = 1 := by
    exact mul_inv_cancel₀ (cast_size_ne_zero k)
  rw [hm, mul_one] at hs
  have hn : k + 1 = 1 := Nat.cast_injective (by simpa only [Nat.cast_one] using hs)
  have hk0 : k = 0 := Nat.succ.inj hn
  subst k
  exact (Nat.not_succ_le_zero 0) hk

private theorem vertex_ne {k : ℕ} (hk : 1 ≤ k)
    (a b : Option (Fin (k + 1))) (hab : a ≠ b) : vertex k a ≠ vertex k b := by
  intro h
  cases a with
  | none =>
    cases b with
    | none => exact hab rfl
    | some j =>
      apply diagonal_ne_zero hk
      have hi := congrArg (fun w : centered k => (w : Ambient k) j) h
      simpa [vertex, simplex, ones] using hi.symm
  | some i =>
    cases b with
    | none =>
      apply diagonal_ne_zero hk
      have hi := congrArg (fun w : centered k => (w : Ambient k) i) h
      simpa [vertex, simplex, ones] using hi
    | some j =>
      have hij : i ≠ j := fun h => hab (congrArg Option.some h)
      have hi : (1 : ℂ) - mean k = 0 - mean k := by
        simpa [vertex, simplex, ones, PiLp.single_apply, hij] using
          congrArg (fun w : centered k => (w : Ambient k) i) h
      have hz : (1 : ℂ) = 0 := by
        simpa using congrArg (fun z : ℂ => z + mean k) hi
      exact one_ne_zero hz

/-- Coordinates of the oriented edge, using one fixed orthonormal isometry. -/
def edge (k : ℕ) (a b : Option (Fin (k + 1))) : Fin k → ℂ :=
  WithLp.ofLp (coordinateIso k (vertex k a - vertex k b))

private theorem pair_eq_inner {n : ℕ} (x : EuclideanSpace ℂ (Fin n))
    (y : Fin n → ℂ) :
    (∑ r, star (x r) * y r) = inner ℂ x (WithLp.toLp 2 y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

set_option backward.isDefEq.respectTransparency false in
private theorem edge_pair {k : ℕ} (a b : Option (Fin (k + 1)))
    (y : Fin k → ℂ) :
    (∑ r, star (edge k a b r) * y r) =
      inner ℂ (vertex k a - vertex k b)
        ((coordinateIso k).symm (WithLp.toLp 2 y)) := by
  change (∑ r, star ((coordinateIso k (vertex k a - vertex k b)) r) * y r) = _
  rw [pair_eq_inner]
  letI : InnerProductSpace ℂ (Ambient k) := PiLp.innerProductSpace (fun _ : Fin (k + 1) => ℂ)
  letI : InnerProductSpace ℂ (centered k) := Submodule.innerProductSpace (centered k)
  letI : InnerProductSpace ℂ (EuclideanSpace ℂ (Fin k)) :=
    PiLp.innerProductSpace (fun _ : Fin k => ℂ)
  exact LinearIsometryEquiv.inner_map_eq_flip (𝕜 := ℂ)
    (E := centered k) (E' := EuclideanSpace ℂ (Fin k)) (coordinateIso k) _ _

theorem edge_ne_zero {k : ℕ} (hk : 1 ≤ k)
    (a b : Option (Fin (k + 1))) (hab : a ≠ b) : edge k a b ≠ 0 := by
  intro h
  change WithLp.ofLp (coordinateIso k (vertex k a - vertex k b)) = 0 at h
  have hz := (coordinateIso k).map_eq_zero_iff.mp (by
    apply WithLp.ofLp_injective 2
    exact h)
  exact vertex_ne hk a b hab (sub_eq_zero.mp hz)

/-- Cross-disjoint endpoint sets give orthogonal actual coordinate rows. -/
theorem edge_pair_eq_zero {k : ℕ} (a b c d : Option (Fin (k + 1)))
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (∑ r, star (edge k a b r) * edge k c d r) = 0 := by
  rw [edge_pair]
  change inner ℂ (vertex k a - vertex k b)
    ((coordinateIso k).symm (coordinateIso k (vertex k c - vertex k d))) = 0
  rw [(coordinateIso k).symm_apply_apply, inner_sub_left,
    inner_sub_right, inner_sub_right]
  simp only [vertex_inner]
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [potentialOf, vertex, simplex, ones, PiLp.single_apply] <;> ring

/-- Every complex test has an actual zero-sum potential on the vertices.
The edge pairing is the oriented potential difference, with no regularity
or spanning assumption on the test. -/
theorem exists_potential {k : ℕ} (y : Fin k → ℂ) :
    ∃ f : Option (Fin (k + 1)) → ℂ,
      f none = 0 ∧ (∑ i, f (some i)) = 0 ∧ (y ≠ 0 → f ≠ 0) ∧
      ∀ a b, (∑ r, star (edge k a b r) * y r) = f a - f b := by
  let w : centered k := (coordinateIso k).symm (WithLp.toLp 2 y)
  refine ⟨potentialOf w, rfl, centered_sum w, ?_, ?_⟩
  · intro hy hf
    apply hy
    have hw : w = 0 := by
      apply Subtype.ext
      ext i
      change (w : Ambient k) i = 0
      exact congrFun hf (some i)
    have hmap := congrArg (coordinateIso k) hw
    have hz : WithLp.toLp 2 y = 0 := by
      simpa only [w, LinearIsometryEquiv.apply_symm_apply, map_zero] using hmap
    exact congrArg WithLp.ofLp hz
  · intro a b
    rw [edge_pair, inner_sub_left, vertex_inner, vertex_inner]

end P14CenteredSimplexEdges

end -- original noncomputable section
end PreservedCenteredSimplexEdges
-- END preserved module CenteredSimplexEdges

-- BEGIN preserved module ThetaDeletionPotential
section PreservedThetaDeletionPotential

/-! Potentials on a theta graph after deletion of one class from each of the
specified short-edge classings. Only finite equality propagation is used.
The two short paths are indexed by Bool; false is the root-side endpoint.
The long path has L edges and L+1 vertices. No geometry or sum constraint is
assumed, and the statement also makes sense for L=0. -/

namespace P14ThetaDeletionPotential

abbrev Edge (L : ℕ) := (Bool × Bool) ⊕ Fin L
abbrev Class (L : ℕ) := Bool ⊕ Fin L

def classA {L : ℕ} : Edge L → Class L
  | .inl (p, e) => .inl (Bool.xor p e)
  | .inr i => .inr i

def classB {L : ℕ} : Edge L → Class L
  | .inl (_, e) => .inl e
  | .inr i => .inr i

def leftValue {C : Type*} {L : ℕ} (s : Bool → C) (g : Fin (L+1) → C) :
    Edge L → C
  | .inl (p, e) => if e then s p else g 0
  | .inr i => g i.castSucc

def rightValue {C : Type*} {L : ℕ} (s : Bool → C) (g : Fin (L+1) → C) :
    Edge L → C
  | .inl (p, e) => if e then g (Fin.last L) else s p
  | .inr i => g i.succ

/-- Propagation through a specified unbroken interval of a finite path. -/
private theorem path_eq {C : Type*} {L : ℕ} (g : Fin (L+1) → C)
    (a b : Fin (L+1)) (hab : a.val ≤ b.val)
    (hstep : ∀ i : Fin L, a.val ≤ i.val → i.val < b.val →
      g i.castSucc = g i.succ) : g a = g b := by
  revert a
  induction b using Fin.induction with
  | zero =>
      intro a hab _
      have ha : a = 0 := Fin.ext (Nat.eq_zero_of_le_zero hab)
      exact congrArg g ha
  | succ b ih =>
      intro a hab hstep
      by_cases h : a = b.succ
      · exact congrArg g h
      have hne : a.val ≠ b.val + 1 := fun he => h (Fin.ext he)
      have hab' : a.val ≤ b.val := by
        change a.val ≤ b.val + 1 at hab
        omega
      have hleft : g a = g b.castSucc :=
        ih a hab' (fun i hi hj => hstep i hi (Nat.lt_succ_of_lt hj))
      exact hleft.trans (hstep b hab' (Nat.lt_succ_self _))

/-- With one cut, every path value equals one of the two endpoint values. -/
private theorem path_one_cut {C : Type*} {L : ℕ} (g : Fin (L+1) → C)
    (cut : Fin L)
    (hstep : ∀ i : Fin L, i ≠ cut → g i.castSucc = g i.succ)
    (i : Fin (L+1)) : g i = g 0 ∨ g i = g (Fin.last L) := by
  by_cases hi : i.val ≤ cut.val
  · left
    exact (path_eq g 0 i (Nat.zero_le _) (fun k _ hki =>
      hstep k (by intro h; subst k; omega))).symm
  · right
    apply path_eq g i (Fin.last L) (by have := i.isLt; change i.val ≤ L; omega)
    intro k hik _
    apply hstep k
    intro h
    subst k
    omega

/-- When the endpoints are zero, two cuts leave only one possible other value. -/
private theorem path_two_cuts {C : Type*} [Zero C] {L : ℕ}
    (g : Fin (L+1) → C) (lo hi : Fin L) (hle : lo.val ≤ hi.val)
    (hzero : g 0 = 0) (hlast : g (Fin.last L) = 0)
    (hstep : ∀ k : Fin L, k ≠ lo → k ≠ hi → g k.castSucc = g k.succ)
    (i : Fin (L+1)) : g i = 0 ∨ g i = g lo.succ := by
  by_cases hlo : i.val ≤ lo.val
  · left
    apply Eq.trans (b := g 0) _ hzero
    symm
    apply path_eq g 0 i (Nat.zero_le _)
    intro k _ hki
    apply hstep k
    · intro h; subst k; omega
    · intro h; subst k; omega
  · by_cases hhi : i.val ≤ hi.val
    · right
      symm
      apply path_eq g lo.succ i (by change lo.val + 1 ≤ i.val; omega)
      intro k hlk hki
      apply hstep k
      · intro h; subst k; change lo.val + 1 ≤ lo.val at hlk; omega
      · intro h; subst k; omega
    · left
      apply Eq.trans (b := g (Fin.last L)) _ hlast
      apply path_eq g i (Fin.last L) (by have := i.isLt; change i.val ≤ L; omega)
      intro k hik _
      apply hstep k
      · intro h; subst k; omega
      · intro h; subst k; omega

/-- The two deletion classes leave at most the root value and one other value.
The class labels, edge orientations and the same s,g are retained literally. -/
theorem two_values {C : Type*} [Zero C] {L : ℕ}
    (s : Bool → C) (g : Fin (L+1) → C)
    (deletedA deletedB : Class L) (hroot : g 0 = 0)
    (hretained : ∀ e : Edge L,
      classA e ≠ deletedA → classB e ≠ deletedB →
      leftValue s g e = rightValue s g e) :
    ∃ c : C, (∀ p, s p = 0 ∨ s p = c) ∧ ∀ i, g i = 0 ∨ g i = c := by
  cases deletedA with
  | inl a =>
      cases deletedB with
      | inl b =>
          have hg (i : Fin (L+1)) : g i = 0 := by
            apply Eq.trans (b := g 0) _ hroot
            symm
            apply path_eq g 0 i (Nat.zero_le _)
            intro k _ _
            exact hretained (.inr k) (by simp [classA]) (by simp [classB])
          let p : Bool := Bool.xor a b
          have ha : Bool.xor p (!b) ≠ a := by
            dsimp [p]
            cases a <;> cases b <;> decide
          have hb : (!b) ≠ b := by cases b <;> decide
          have hp : s p = 0 := by
            have h := hretained (.inl (p, !b))
              (by simpa only [classA, ne_eq, Sum.inl.injEq] using ha)
              (by simpa only [classB, ne_eq, Sum.inl.injEq] using hb)
            cases b with
            | false => simpa [leftValue, rightValue, hg] using h
            | true => simpa [leftValue, rightValue, hg] using h.symm
          refine ⟨s (!p), ?_, fun i => Or.inl (hg i)⟩
          intro q
          by_cases hq : q = p
          · exact Or.inl ((congrArg s hq).trans hp)
          · right
            have hqp : q = !p := Bool.eq_not_iff.mpr hq
            exact congrArg s hqp
      | inr cut =>
          have hlong (k : Fin L) (hk : k ≠ cut) : g k.castSucc = g k.succ :=
            hretained (.inr k) (by simp [classA])
              (by simpa only [classB, ne_eq, Sum.inr.injEq] using hk)
          refine ⟨g (Fin.last L), ?_, ?_⟩
          · intro p
            by_cases hp : Bool.xor p false = a
            · have ha : Bool.xor p true ≠ a := by
                cases p <;> cases a <;> cases hp <;> decide
              right
              exact hretained (.inl (p, true))
                (by simpa only [classA, ne_eq, Sum.inl.injEq] using ha)
                (by simp [classB])
            · left
              have h := hretained (.inl (p, false))
                (by simpa only [classA, ne_eq, Sum.inl.injEq] using hp)
                (by simp [classB])
              exact h.symm.trans hroot
          · intro i
            rcases path_one_cut g cut hlong i with h | h
            · exact Or.inl (h.trans hroot)
            · exact Or.inr h
  | inr cutA =>
      cases deletedB with
      | inl b =>
          have hlong (k : Fin L) (hk : k ≠ cutA) : g k.castSucc = g k.succ :=
            hretained (.inr k)
              (by simpa only [classA, ne_eq, Sum.inr.injEq] using hk)
              (by simp [classB])
          refine ⟨g (Fin.last L), ?_, ?_⟩
          · intro p
            cases b with
            | false =>
                right
                exact hretained (.inl (p, true)) (by simp [classA]) (by simp [classB])
            | true =>
                left
                have h := hretained (.inl (p, false))
                  (by simp [classA]) (by simp [classB])
                exact h.symm.trans hroot
          · intro i
            rcases path_one_cut g cutA hlong i with h | h
            · exact Or.inl (h.trans hroot)
            · exact Or.inr h
      | inr cutB =>
          have hs (p : Bool) : s p = 0 := by
            have h := hretained (.inl (p, false))
              (by simp [classA]) (by simp [classB])
            exact h.symm.trans hroot
          have hlast : g (Fin.last L) = 0 := by
            have h := hretained (.inl (false, true))
              (by simp [classA]) (by simp [classB])
            exact h.symm.trans (hs false)
          have hlong (k : Fin L) (ha : k ≠ cutA) (hb : k ≠ cutB) :
              g k.castSucc = g k.succ :=
            hretained (.inr k)
              (by simpa only [classA, ne_eq, Sum.inr.injEq] using ha)
              (by simpa only [classB, ne_eq, Sum.inr.injEq] using hb)
          rcases Nat.le_total cutA.val cutB.val with h | h
          · exact ⟨g cutA.succ, fun p => Or.inl (hs p),
              path_two_cuts g cutA cutB h hroot hlast hlong⟩
          · exact ⟨g cutB.succ, fun p => Or.inl (hs p),
              path_two_cuts g cutB cutA h hroot hlast (fun k hb ha => hlong k ha hb)⟩

end P14ThetaDeletionPotential

end PreservedThetaDeletionPotential
-- END preserved module ThetaDeletionPotential

-- BEGIN preserved module ThetaZeroSumPotential
section PreservedThetaZeroSumPotential

/-! The zero-sum condition removes the one remaining potential value after
the actual theta class deletions. This is over the complex field, including
tests with non-real coordinates; no positivity of the potential is used. -/

namespace P14ThetaZeroSumPotential
open P14ThetaDeletionPotential
open scoped BigOperators

theorem zero_of_two_values {ι : Type*} [Fintype ι] (f : ι → ℂ) (c : ℂ)
    (hvalues : ∀ i, f i = 0 ∨ f i = c) (hsum : (∑ i, f i) = 0) : f = 0 := by
  classical
  let S : Finset ι := Finset.univ.filter (fun i => f i ≠ 0)
  have hcount : (∑ i, f i) = (S.card : ℂ) * c := by
    calc
      _ = ∑ i ∈ S, c := by
        dsimp only [S]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : f i = 0
        · simp [hi]
        · rw [if_pos hi]
          exact (hvalues i).resolve_left hi
      _ = _ := by simp
  funext i
  by_contra hi
  have hi' : f i ≠ 0 := hi
  have hmem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hmem⟩
  have hcast : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)
  have hc : c = 0 := (mul_eq_zero.mp (hcount.symm.trans hsum)).resolve_left hcast
  exact hi' (((hvalues i).resolve_left hi').trans hc)

/-- The same s and g that are constant on every retained oriented edge must
vanish if their total coordinate sum is zero. -/
theorem vanish {L : ℕ} (s : Bool → ℂ) (g : Fin (L + 1) → ℂ)
    (deletedA deletedB : Class L) (hroot : g 0 = 0)
    (hsum : (∑ p, s p) + (∑ i, g i) = 0)
    (hretained : ∀ e : Edge L,
      classA e ≠ deletedA → classB e ≠ deletedB →
      leftValue s g e = rightValue s g e) : s = 0 ∧ g = 0 := by
  obtain ⟨c, hs, hg⟩ := two_values s g deletedA deletedB hroot hretained
  let f : Bool ⊕ Fin (L + 1) → ℂ := Sum.elim s g
  have hv : ∀ i, f i = 0 ∨ f i = c := by
    rintro (p | i)
    · exact hs p
    · exact hg i
  have hfSum : (∑ i, f i) = 0 := by
    simpa only [f, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using hsum
  have hf := zero_of_two_values f c hv hfSum
  constructor
  · funext p
    exact congrFun hf (Sum.inl p)
  · funext i
    exact congrFun hf (Sum.inr i)

end P14ThetaZeroSumPotential

end PreservedThetaZeroSumPotential
-- END preserved module ThetaZeroSumPotential

-- BEGIN preserved module ThetaEdgeFamily
section PreservedThetaEdgeFamily

/-! The actual centered-simplex edge family on the theta labels. Deleting
one prescribed class from each qubit leaves no nonzero complex annihilator.
The same coordinates and finite path labels are used throughout. -/

noncomputable section
namespace P14ThetaEdgeFamily
open P14ThetaDeletionPotential
open scoped BigOperators

def shortVertex (L : ℕ) : Bool → Option (Fin (L + 2))
  | false => some 0
  | true => some (0 : Fin (L + 1)).succ

def pathVertex (L : ℕ) : Fin (L + 1) → Option (Fin (L + 2)) :=
  Fin.cases none (fun i => some i.succ.succ)

def leftEnd {L : ℕ} : Edge L → Option (Fin (L + 2)) :=
  leftValue (shortVertex L) (pathVertex L)

def rightEnd {L : ℕ} : Edge L → Option (Fin (L + 2)) :=
  rightValue (shortVertex L) (pathVertex L)

def family (L : ℕ) (e : Edge L) : Fin (L + 1) → ℂ :=
  P14CenteredSimplexEdges.edge (L + 1) (leftEnd e) (rightEnd e)

private theorem potential_sum {L : ℕ} (f : Option (Fin (L + 2)) → ℂ)
    (hroot : f none = 0) (hsum : (∑ i, f (some i)) = 0) :
    (∑ p, f (shortVertex L p)) + (∑ i, f (pathVertex L i)) = 0 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hsum
  convert hsum using 1 <;>
    simp [shortVertex, pathVertex, Fintype.sum_bool, Fin.sum_univ_succ, hroot] <;> abel

/-- This is the rank statement for the literal remaining edge set, not a
rank assumption passed to a product-family constructor. -/
theorem annihilator_eq_zero {L : ℕ} (deletedA deletedB : Class L)
    (y : Fin (L + 1) → ℂ)
    (hkilled : ∀ e : Edge L,
      classA e ≠ deletedA → classB e ≠ deletedB →
      (∑ r, star (family L e r) * y r) = 0) : y = 0 := by
  obtain ⟨f, hroot, hsum, hnonzero, hpair⟩ :=
    P14CenteredSimplexEdges.exists_potential y
  let s : Bool → ℂ := fun p => f (shortVertex L p)
  let g : Fin (L + 1) → ℂ := fun i => f (pathVertex L i)
  have hg0 : g 0 = 0 := hroot
  have htotal : (∑ p, s p) + (∑ i, g i) = 0 := potential_sum f hroot hsum
  have hretained : ∀ e : Edge L,
      classA e ≠ deletedA → classB e ≠ deletedB →
      leftValue s g e = rightValue s g e := by
    intro e ha hb
    have h := sub_eq_zero.mp ((hpair (leftEnd e) (rightEnd e)).symm.trans
      (hkilled e ha hb))
    rcases e with ⟨p, b⟩ | i
    · cases b <;> exact h
    · exact h
  obtain ⟨hs, hg⟩ := P14ThetaZeroSumPotential.vanish s g deletedA deletedB
    hg0 htotal hretained
  by_contra hy
  apply hnonzero hy
  have hsome : ∀ i : Fin (L + 2), f (some i) = 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrFun hs false
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact congrFun hs true
      · exact congrFun hg k.succ
  funext v
  cases v with
  | none => exact hroot
  | some i => exact hsome i

/-- Every nonzero complex third-factor test survives on an edge outside both
deleted classes. This is the form used by the separate-qubit assembly. -/
theorem exists_survivor {L : ℕ} (deletedA deletedB : Class L)
    (y : Fin (L + 1) → ℂ) (hy : y ≠ 0) :
    ∃ e : Edge L, classA e ≠ deletedA ∧ classB e ≠ deletedB ∧
      (∑ r, star (family L e r) * y r) ≠ 0 := by
  classical
  by_contra h
  apply hy
  apply annihilator_eq_zero deletedA deletedB y
  intro e ha hb
  by_contra hp
  exact h ⟨e, ha, hb, hp⟩

end P14ThetaEdgeFamily

end -- original noncomputable section
end PreservedThetaEdgeFamily
-- END preserved module ThetaEdgeFamily

-- BEGIN preserved module ThetaQubitLabels
section PreservedThetaQubitLabels

/-! The two literal qubit-ray assignments for the odd-dimensional theta
construction. Repeated short-edge rays are tracked by their deletion class;
each class has its own ray, including both endpoint classes of family B. -/

noncomputable section
namespace P14ThetaQubitLabels
open P14ThetaDeletionPotential P14QubitRayLabels
open scoped BigOperators

def labelA {L : ℕ} : Class L → Label
  | .inl b => (0, b)
  | .inr i => (i.val / 2 + 1, decide (i.val % 2 = 1))

def labelB (h : ℕ) : Class (2 * h) → Label
  | .inl b => (if b then h else 0, false)
  | .inr i => ((i.val + 1) / 2, decide (i.val % 2 = 0 ∨ i.val + 1 = 2 * h))

theorem labelA_injective {L : ℕ} : Function.Injective (@labelA L) := by
  rintro (a | i) (b | j) he
  · exact congrArg Sum.inl (congrArg Prod.snd he)
  · have hn := congrArg Prod.fst he
    simp [labelA] at hn
  · have hn := congrArg Prod.fst he
    simp [labelA] at hn
  · have hn : i.val / 2 + 1 = j.val / 2 + 1 := congrArg Prod.fst he
    have hb : decide (i.val % 2 = 1) = decide (j.val % 2 = 1) :=
      congrArg Prod.snd he
    have hp := decide_eq_decide.mp hb
    have hij : i.val = j.val := by omega
    exact congrArg Sum.inr (Fin.ext hij)

private theorem labelB_short_ne_long {h : ℕ} (hh : 0 < h)
    (b : Bool) (i : Fin (2 * h)) : labelB h (.inl b) ≠ labelB h (.inr i) := by
  intro he
  have hn : (if b then h else 0) = (i.val + 1) / 2 := congrArg Prod.fst he
  have hb : false = decide (i.val % 2 = 0 ∨ i.val + 1 = 2 * h) :=
    congrArg Prod.snd he
  have hp := Bool.of_decide_false hb.symm
  have hi := i.isLt
  cases b <;> dsimp at hn <;> omega

theorem labelB_injective {h : ℕ} (hh : 0 < h) :
    Function.Injective (labelB h) := by
  rintro (a | i) (b | j) he
  · cases a <;> cases b <;> simp_all [labelB]
  · exact (labelB_short_ne_long hh a j he).elim
  · exact (labelB_short_ne_long hh b i he.symm).elim
  · have hn : (i.val + 1) / 2 = (j.val + 1) / 2 := congrArg Prod.fst he
    have hb : decide (i.val % 2 = 0 ∨ i.val + 1 = 2 * h) =
        decide (j.val % 2 = 0 ∨ j.val + 1 = 2 * h) := congrArg Prod.snd he
    have hp := decide_eq_decide.mp hb
    have hi := i.isLt
    have hj := j.isLt
    have hij : i.val = j.val := by omega
    exact congrArg Sum.inr (Fin.ext hij)

/-- Choose an actual class if one is killed, and a harmless default otherwise.
Injectivity refers to classes, not product rows with deliberately reused rays. -/
theorem exists_deleted_class {L : ℕ} (label : Class L → Label)
    (hinj : Function.Injective label) (y : Fin 2 → ℂ) (hy : y ≠ 0) :
    ∃ c : Class L, ∀ c', pair (ray (label c')) y = 0 → c' = c := by
  classical
  by_cases hk : ∃ c, pair (ray (label c)) y = 0
  · obtain ⟨c, hc⟩ := hk
    exact ⟨c, fun c' hc' => hinj (killed_labels_equal _ _ y hy hc' hc)⟩
  · exact ⟨.inl false, fun c hc => (hk ⟨c, hc⟩).elim⟩

def qubitA {L : ℕ} (e : Edge L) : Fin 2 → ℂ := ray (labelA (classA e))

def qubitB (h : ℕ) (e : Edge (2 * h)) : Fin 2 → ℂ := ray (labelB h (classB e))

theorem qubitA_ne_zero {L : ℕ} (e : Edge L) : qubitA e ≠ 0 := ray_ne_zero _

theorem qubitB_ne_zero (h : ℕ) (e : Edge (2 * h)) : qubitB h e ≠ 0 := ray_ne_zero _

/-- The same edge survives all three arbitrary nonzero complex local tests.
The geometric factor is the actual centered-simplex family already checked. -/
theorem exists_product_survivor {h : ℕ} (hh : 0 < h)
    (x y : Fin 2 → ℂ) (z : Fin (2 * h + 1) → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ e : Edge (2 * h), pair (qubitA e) x ≠ 0 ∧ pair (qubitB h e) y ≠ 0 ∧
      (∑ r, star (P14ThetaEdgeFamily.family (2 * h) e r) * z r) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_deleted_class labelA labelA_injective x hx
  obtain ⟨b, hb⟩ := exists_deleted_class (labelB h) (labelB_injective hh) y hy
  obtain ⟨e, hea, heb, hez⟩ := P14ThetaEdgeFamily.exists_survivor a b z hz
  exact ⟨e, fun he => hea (ha (classA e) he),
    fun he => heb (hb (classB e) he), hez⟩

end P14ThetaQubitLabels

end -- original noncomputable section
end PreservedThetaQubitLabels
-- END preserved module ThetaQubitLabels

-- BEGIN preserved module ThetaIncidenceGeometry
section PreservedThetaIncidenceGeometry

/-! Endpoint checks for the same theta edge vectors. These checks distinguish
the two short interior vertices from every long-path vertex. -/

noncomputable section
namespace P14ThetaIncidenceGeometry
open P14ThetaDeletionPotential P14ThetaEdgeFamily
open scoped BigOperators

theorem short_injective (L : ℕ) : Function.Injective (shortVertex L) := by
  intro p q he
  cases p <;> cases q <;> simp_all [shortVertex, Fin.ext_iff]

theorem path_injective (L : ℕ) : Function.Injective (pathVertex L) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · simp [pathVertex]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [pathVertex]
    · intro he
      have hij : i = j := by simpa [pathVertex] using he
      exact congrArg Fin.succ hij

theorem short_ne_path {L : ℕ} (p : Bool) (i : Fin (L + 1)) :
    shortVertex L p ≠ pathVertex L i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · cases p <;> simp [shortVertex, pathVertex]
  · cases p <;> simp [shortVertex, pathVertex, Fin.ext_iff]

def DisjointEnds {L : ℕ} (e f : Edge L) : Prop :=
  leftEnd e ≠ leftEnd f ∧ leftEnd e ≠ rightEnd f ∧
    rightEnd e ≠ leftEnd f ∧ rightEnd e ≠ rightEnd f

theorem family_ne_zero {L : ℕ} (e : Edge L) : family L e ≠ 0 := by
  apply P14CenteredSimplexEdges.edge_ne_zero (by omega)
  rcases e with ⟨p, b⟩ | i
  · cases b
    · exact (short_ne_path (L := L) p 0).symm
    · exact short_ne_path p (Fin.last L)
  · intro he
    change pathVertex L i.castSucc = pathVertex L i.succ at he
    have hi := congrArg Fin.val (path_injective L he)
    change i.val = i.val + 1 at hi
    omega

theorem disjoint_pair {L : ℕ} {e f : Edge L} (hd : DisjointEnds e f) :
    (∑ r, star (family L e r) * family L f r) = 0 :=
  P14CenteredSimplexEdges.edge_pair_eq_zero _ _ _ _ hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

theorem short_short_disjoint {L : ℕ} (hL : 0 < L) (p q b c : Bool)
    (hpq : p ≠ q) (hbc : b ≠ c) :
    DisjointEnds (.inl (p, b) : Edge L) (.inl (q, c)) := by
  have hp : shortVertex L p ≠ shortVertex L q := fun he => hpq (short_injective L he)
  have hends : pathVertex L 0 ≠ pathVertex L (Fin.last L) := by
    intro he
    have hv := congrArg Fin.val (path_injective L he)
    change 0 = L at hv
    omega
  cases b <;> cases c <;>
    simp_all [DisjointEnds, leftEnd, rightEnd, leftValue, rightValue,
      short_ne_path, Ne.symm (short_ne_path p 0), Ne.symm (short_ne_path q 0),
      Ne.symm (short_ne_path p (Fin.last L)), Ne.symm (short_ne_path q (Fin.last L)),
      Ne.symm hends]

theorem short_long_disjoint {L : ℕ} (p b : Bool) (i : Fin L)
    (hroot : b = false → i.val ≠ 0) (hlast : b = true → i.val + 1 ≠ L) :
    DisjointEnds (.inl (p, b) : Edge L) (.inr i) := by
  have hpath (a c : Fin (L + 1)) (h : a.val ≠ c.val) :
      pathVertex L a ≠ pathVertex L c := fun he => h (congrArg Fin.val (path_injective L he))
  have hi := i.isLt
  cases b with
  | false =>
      exact ⟨hpath 0 i.castSucc (by simp only [Fin.val_zero, Fin.val_castSucc]; exact (hroot rfl).symm),
        hpath 0 i.succ (by simp), short_ne_path p i.castSucc, short_ne_path p i.succ⟩
  | true =>
      exact ⟨short_ne_path p i.castSucc, short_ne_path p i.succ,
        hpath (Fin.last L) i.castSucc (by simp only [Fin.val_last, Fin.val_castSucc]; omega),
        hpath (Fin.last L) i.succ (by simp only [Fin.val_last, Fin.val_succ]; exact (hlast rfl).symm)⟩

theorem long_long_disjoint {L : ℕ} (i j : Fin L)
    (hij : i ≠ j) (hforward : i.val + 1 ≠ j.val) (hback : j.val + 1 ≠ i.val) :
    DisjointEnds (.inr i : Edge L) (.inr j) := by
  have hneq : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hpath (a c : Fin (L + 1)) (h : a.val ≠ c.val) :
      pathVertex L a ≠ pathVertex L c := fun he => h (congrArg Fin.val (path_injective L he))
  refine ⟨hpath i.castSucc j.castSucc hneq, hpath i.castSucc j.succ ?_,
    hpath i.succ j.castSucc hforward, hpath i.succ j.succ ?_⟩
  · change i.val ≠ j.val + 1
    exact hback.symm
  · change i.val + 1 ≠ j.val + 1
    omega

end P14ThetaIncidenceGeometry

end -- original noncomputable section
end PreservedThetaIncidenceGeometry
-- END preserved module ThetaIncidenceGeometry

-- BEGIN preserved module ThetaProductOrthogonality
section PreservedThetaProductOrthogonality

/-! Orthogonality of the very same product rows used by the survivor theorem.
Adjacent long edges alternate between the two qubit factors; endpoint edges
use qubit B. Cross-disjoint edges use the centered geometric factor. -/

noncomputable section
namespace P14ThetaProductOrthogonality
open P14ThetaDeletionPotential P14ThetaEdgeFamily P14ThetaQubitLabels
open P14ThetaIncidenceGeometry P14QubitRayLabels
open scoped BigOperators

private theorem pair_opposite {l m : Label} (hn : l.1 = m.1) (hb : l.2 ≠ m.2) :
    pair (ray l) (ray m) = 0 := by
  rcases l with ⟨s, a⟩
  rcases m with ⟨t, b⟩
  dsimp at hn hb
  subst t
  cases a <;> cases b <;> simp_all [pair, ray, Fin.sum_univ_two]

private theorem zero_pair_symm {n : ℕ} (u v : Fin n → ℂ)
    (he : (∑ r, star (u r) * v r) = 0) : (∑ r, star (v r) * u r) = 0 := by
  have h := congrArg star he
  simpa [star_sum, star_mul, mul_comm] using h

def Orth {h : ℕ} (e f : Edge (2 * h)) : Prop :=
  pair (qubitA e) (qubitA f) = 0 ∨ pair (qubitB h e) (qubitB h f) = 0 ∨
    (∑ r, star (family (2 * h) e r) * family (2 * h) f r) = 0

theorem Orth.symm {h : ℕ} {e f : Edge (2 * h)} (he : Orth e f) : Orth f e := by
  rcases he with he | he | he
  · exact Or.inl (zero_pair_symm _ _ he)
  · exact Or.inr (Or.inl (zero_pair_symm _ _ he))
  · exact Or.inr (Or.inr (zero_pair_symm _ _ he))

private theorem short_short {h : ℕ} (hh : 0 < h) (p q b c : Bool)
    (hne : (Sum.inl (p, b) : Edge (2 * h)) ≠ .inl (q, c)) :
    Orth (.inl (p, b) : Edge (2 * h)) (.inl (q, c)) := by
  by_cases hx : Bool.xor p b ≠ Bool.xor q c
  · left
    exact pair_opposite rfl hx
  · have hp : p ≠ q := by
      cases p <;> cases q <;> cases b <;> cases c <;> simp_all
    have hb : b ≠ c := by
      cases p <;> cases q <;> cases b <;> cases c <;> simp_all
    exact Or.inr (Or.inr (disjoint_pair (short_short_disjoint (by omega) p q b c hp hb)))

private theorem short_long {h : ℕ} (hh : 0 < h) (p b : Bool) (i : Fin (2 * h)) :
    Orth (.inl (p, b) : Edge (2 * h)) (.inr i) := by
  cases b with
  | false =>
      by_cases hi : i.val = 0
      · right; left
        apply pair_opposite
        · simp [qubitB, classB, labelB, hi]
        · simp [qubitB, classB, labelB, hi]
      · exact Or.inr (Or.inr (disjoint_pair (short_long_disjoint p false i
          (fun _ => hi) (by simp))))
  | true =>
      by_cases hi : i.val + 1 = 2 * h
      · right; left
        apply pair_opposite
        · change h = (i.val + 1) / 2
          omega
        · simp [qubitB, classB, labelB, hi]
      · exact Or.inr (Or.inr (disjoint_pair (short_long_disjoint p true i
          (by simp) (fun _ => hi))))

private theorem long_adjacent {h : ℕ} (i j : Fin (2 * h))
    (hij : i.val + 1 = j.val) : Orth (.inr i : Edge (2 * h)) (.inr j) := by
  by_cases hi : i.val % 2 = 0
  · have hj : j.val % 2 = 1 := by omega
    left
    apply pair_opposite
    · change i.val / 2 + 1 = j.val / 2 + 1
      omega
    · simp [qubitA, classA, labelA, hi, hj]
  · have hi' : i.val % 2 = 1 := by omega
    have hj : j.val % 2 = 0 := by omega
    have hend : i.val + 1 ≠ 2 * h := by have := j.isLt; omega
    right; left
    apply pair_opposite
    · change (i.val + 1) / 2 = (j.val + 1) / 2
      omega
    · simp [qubitB, classB, labelB, hi', hj, hend]

/-- Every pair of distinct rows is orthogonal in an actual local factor. -/
theorem all_pairs {h : ℕ} (hh : 0 < h) (e f : Edge (2 * h)) (hne : e ≠ f) :
    Orth e f := by
  rcases e with ⟨p, b⟩ | i <;> rcases f with ⟨q, c⟩ | j
  · exact short_short hh p q b c hne
  · exact short_long hh p b j
  · exact (short_long hh q c i).symm
  · by_cases hf : i.val + 1 = j.val
    · exact long_adjacent i j hf
    · by_cases hb : j.val + 1 = i.val
      · exact (long_adjacent j i hb).symm
      · exact Or.inr (Or.inr (disjoint_pair (long_long_disjoint i j
          (fun he => hne (congrArg Sum.inr he)) hf hb)))

end P14ThetaProductOrthogonality

end -- original noncomputable section
end PreservedThetaProductOrthogonality
-- END preserved module ThetaProductOrthogonality

-- BEGIN preserved module ThetaOddUPB
section PreservedThetaOddUPB

/-! Literal finite complex-coordinate UPBs for dimensions (2,2,2h+1), h>0.
The row count 2h+4 equals the canonical trivial-plus-one ceiling. This is a
scoped construction, not a resolution of the unrestricted mixed problem. -/

noncomputable section
namespace P14ThetaOddUPB
open P14ThetaDeletionPotential P14ThetaEdgeFamily P14ThetaQubitLabels
open P14ThetaIncidenceGeometry P14ThetaProductOrthogonality P14QubitRayLabels
open scoped BigOperators

def dimensions (h : ℕ) : Fin 3 → ℕ :=
  Fin.cases 2 (Fin.cases 2 (fun _ => 2 * h + 1))

def row (h : ℕ) (e : Edge (2 * h)) : (j : Fin 3) → Fin (dimensions h j) → ℂ :=
  Fin.cases (qubitA e) (Fin.cases (qubitB h e) (fun _ => family (2 * h) e))

theorem edge_card (h : ℕ) : Fintype.card (Edge (2 * h)) = 2 * h + 4 := by
  simp [Edge, add_comm]

theorem ceiling (h : ℕ) : 2 + (∑ j, (dimensions h j - 1)) = 2 * h + 4 := by
  simp [dimensions, Fin.sum_univ_succ]
  omega

/-- The conclusion has exactly the saved canonical quantifiers: nonzero
local vectors, actual pairwise local orthogonality, and one row surviving
all arbitrary nonzero complex local tests. No real-only replacement is used. -/
theorem canonical {h : ℕ} (hh : 0 < h) :
    ∃ m : ℕ, m ≤ 2 + ∑ j, (dimensions h j - 1) ∧
      ∃ v : Fin m → (j : Fin 3) → Fin (dimensions h j) → ℂ,
        (∀ i j, v i j ≠ 0) ∧
        (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
        (∀ a : (j : Fin 3) → Fin (dimensions h j) → ℂ, (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0) := by
  let E : Fin (2 * h + 4) ≃ Edge (2 * h) := (Fintype.equivFinOfCardEq (edge_card h)).symm
  refine ⟨2 * h + 4, by rw [ceiling], (fun i => row h (E i)), ?_, ?_, ?_⟩
  · intro i j
    fin_cases j
    · exact qubitA_ne_zero (E i)
    · exact qubitB_ne_zero h (E i)
    · exact family_ne_zero (E i)
  · intro i i' hne
    have he : E i ≠ E i' := fun he => hne (E.injective he)
    rcases all_pairs hh (E i) (E i') he with ha | hb | hc
    · exact ⟨0, ha⟩
    · exact ⟨1, hb⟩
    · exact ⟨2, hc⟩
  · intro a ha
    obtain ⟨e, hx, hy, hz⟩ := exists_product_survivor hh (a 0) (a 1) (a 2)
      (ha 0) (ha 1) (ha 2)
    refine ⟨E.symm e, ?_⟩
    intro j
    fin_cases j
    · change pair (qubitA (E (E.symm e))) (a 0) ≠ 0
      rw [E.apply_symm_apply]
      exact hx
    · change pair (qubitB h (E (E.symm e))) (a 1) ≠ 0
      rw [E.apply_symm_apply]
      exact hy
    · change (∑ r, star (family (2 * h) (E (E.symm e)) r) * a 2 r) ≠ 0
      rw [E.apply_symm_apply]
      exact hz

theorem dimensions_literal (h : ℕ) : dimensions h = ![2, 2, 2 * h + 1] := by
  funext j
  fin_cases j <;> rfl

end P14ThetaOddUPB

end -- original noncomputable section
end PreservedThetaOddUPB
-- END preserved module ThetaOddUPB

-- BEGIN preserved module CycleDeletionPotential
section PreservedCycleDeletionPotential

/-! Potentials on a finite path plus its closing edge after deletion of at
most two edges. The proof extends the same path values to the already checked
theta lemma; auxiliary short vertices impose no new premise on the cycle. -/

namespace P14CycleDeletionPotential
open scoped BigOperators

abbrev Edge (L : ℕ) := Option (Fin L)

def leftValue {C : Type*} {L : ℕ} (g : Fin (L + 1) → C) : Edge L → C
  | none => g (Fin.last L)
  | some i => g i.castSucc

def rightValue {C : Type*} {L : ℕ} (g : Fin (L + 1) → C) : Edge L → C
  | none => g 0
  | some i => g i.succ

theorem two_values {C : Type*} [Zero C] {L : ℕ}
    (g : Fin (L + 1) → C) (a b : Edge L) (hroot : g 0 = 0)
    (hretained : ∀ e, e ≠ a → e ≠ b → leftValue g e = rightValue g e) :
    ∃ c : C, ∀ i, g i = 0 ∨ g i = c := by
  cases a with
  | none =>
      cases b with
      | none =>
          obtain ⟨c, _, hg⟩ := P14ThetaDeletionPotential.two_values
            (fun _ => g (Fin.last L)) g (.inl false) (.inl false) hroot (by
              rintro (⟨p, e⟩ | i) ha hb
              · cases p <;> cases e <;>
                  simp_all [P14ThetaDeletionPotential.classA, P14ThetaDeletionPotential.classB,
                    P14ThetaDeletionPotential.leftValue, P14ThetaDeletionPotential.rightValue]
              · exact hretained (some i) (by simp) (by simp))
          exact ⟨c, hg⟩
      | some cut =>
          obtain ⟨c, _, hg⟩ := P14ThetaDeletionPotential.two_values
            (fun p => if p then 0 else g (Fin.last L)) g (.inl false) (.inr cut) hroot (by
              rintro (⟨p, e⟩ | i) ha hb
              · cases p <;> cases e <;>
                  simp_all [P14ThetaDeletionPotential.classA, P14ThetaDeletionPotential.classB,
                    P14ThetaDeletionPotential.leftValue, P14ThetaDeletionPotential.rightValue]
              · exact hretained (some i) (by simp)
                  (by simpa [P14ThetaDeletionPotential.classB] using hb))
          exact ⟨c, hg⟩
  | some cutA =>
      cases b with
      | none =>
          obtain ⟨c, _, hg⟩ := P14ThetaDeletionPotential.two_values
            (fun _ => g (Fin.last L)) g (.inr cutA) (.inl false) hroot (by
              rintro (⟨p, e⟩ | i) ha hb
              · cases p <;> cases e <;>
                  simp_all [P14ThetaDeletionPotential.classA, P14ThetaDeletionPotential.classB,
                    P14ThetaDeletionPotential.leftValue, P14ThetaDeletionPotential.rightValue]
              · exact hretained (some i)
                  (by simpa [P14ThetaDeletionPotential.classA] using ha) (by simp))
          exact ⟨c, hg⟩
      | some cutB =>
          have hend : g (Fin.last L) = 0 :=
            (hretained none (by simp) (by simp)).trans hroot
          obtain ⟨c, _, hg⟩ := P14ThetaDeletionPotential.two_values
            (fun _ => 0) g (.inr cutA) (.inr cutB) hroot (by
              rintro (⟨p, e⟩ | i) ha hb
              · cases e <;>
                  simp_all [P14ThetaDeletionPotential.leftValue, P14ThetaDeletionPotential.rightValue]
              · exact hretained (some i)
                  (by simpa [P14ThetaDeletionPotential.classA] using ha)
                  (by simpa [P14ThetaDeletionPotential.classB] using hb))
          exact ⟨c, hg⟩

/-- The actual complex potential vanishes when its total sum is zero. -/
theorem vanish {L : ℕ} (g : Fin (L + 1) → ℂ) (a b : Edge L)
    (hroot : g 0 = 0) (hsum : (∑ i, g i) = 0)
    (hretained : ∀ e, e ≠ a → e ≠ b → leftValue g e = rightValue g e) : g = 0 := by
  obtain ⟨c, hc⟩ := two_values g a b hroot hretained
  exact P14ThetaZeroSumPotential.zero_of_two_values g c hc hsum

end P14CycleDeletionPotential

end PreservedCycleDeletionPotential
-- END preserved module CycleDeletionPotential

-- BEGIN preserved module CycleEdgeFamily
section PreservedCycleEdgeFamily

/-! Actual centered-simplex edge coordinates on a cycle. Every nonzero
complex test survives outside two deleted edges. Endpoint classification
also supplies the third-factor orthogonality used by the product assembly. -/

noncomputable section
namespace P14CycleEdgeFamily
open P14CycleDeletionPotential
open scoped BigOperators

def vertex (k : ℕ) : Fin (k + 2) → Option (Fin (k + 1)) := Fin.cases none some

def leftEnd {k : ℕ} : Edge (k + 1) → Option (Fin (k + 1)) := leftValue (vertex k)

def rightEnd {k : ℕ} : Edge (k + 1) → Option (Fin (k + 1)) := rightValue (vertex k)

def family (k : ℕ) (e : Edge (k + 1)) : Fin k → ℂ :=
  P14CenteredSimplexEdges.edge k (leftEnd e) (rightEnd e)

theorem vertex_injective (k : ℕ) : Function.Injective (vertex k) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · simp [vertex]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [vertex]
    · intro he
      have hij : i = j := by simpa [vertex] using he
      exact congrArg Fin.succ hij

theorem family_ne_zero {k : ℕ} (hk : 1 ≤ k) (e : Edge (k + 1)) : family k e ≠ 0 := by
  apply P14CenteredSimplexEdges.edge_ne_zero hk
  intro he
  cases e with
  | none =>
      change vertex k (Fin.last (k + 1)) = vertex k 0 at he
      have hv := congrArg Fin.val (vertex_injective k he)
      change k + 1 = 0 at hv
      omega
  | some i =>
      change vertex k i.castSucc = vertex k i.succ at he
      have hv := congrArg Fin.val (vertex_injective k he)
      change i.val = i.val + 1 at hv
      omega

theorem annihilator_eq_zero {k : ℕ} (a b : Edge (k + 1)) (y : Fin k → ℂ)
    (hkilled : ∀ e, e ≠ a → e ≠ b → (∑ r, star (family k e r) * y r) = 0) : y = 0 := by
  obtain ⟨f, hroot, hsum, hnonzero, hpair⟩ := P14CenteredSimplexEdges.exists_potential y
  let g : Fin (k + 2) → ℂ := fun i => f (vertex k i)
  have hgroot : g 0 = 0 := hroot
  have hgsum : (∑ i, g i) = 0 := by
    simpa [g, vertex, Fin.sum_univ_succ, hroot] using hsum
  have hretained : ∀ e, e ≠ a → e ≠ b → leftValue g e = rightValue g e := by
    intro e ha hb
    have he := sub_eq_zero.mp ((hpair (leftEnd e) (rightEnd e)).symm.trans (hkilled e ha hb))
    cases e <;> exact he
  have hg := P14CycleDeletionPotential.vanish g a b hgroot hgsum hretained
  by_contra hy
  apply hnonzero hy
  funext v
  cases v with
  | none => exact congrFun hg 0
  | some i => exact congrFun hg i.succ

theorem exists_survivor {k : ℕ} (a b : Edge (k + 1)) (y : Fin k → ℂ) (hy : y ≠ 0) :
    ∃ e : Edge (k + 1), e ≠ a ∧ e ≠ b ∧ (∑ r, star (family k e r) * y r) ≠ 0 := by
  classical
  by_contra he
  apply hy
  apply annihilator_eq_zero a b y
  intro e ha hb
  by_contra hp
  exact he ⟨e, ha, hb, hp⟩

def DisjointEnds {k : ℕ} (e f : Edge (k + 1)) : Prop :=
  leftEnd e ≠ leftEnd f ∧ leftEnd e ≠ rightEnd f ∧
    rightEnd e ≠ leftEnd f ∧ rightEnd e ≠ rightEnd f

theorem disjoint_pair {k : ℕ} {e f : Edge (k + 1)} (hd : DisjointEnds e f) :
    (∑ r, star (family k e r) * family k f r) = 0 :=
  P14CenteredSimplexEdges.edge_pair_eq_zero _ _ _ _ hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

theorem closing_path_disjoint {k : ℕ} (i : Fin (k + 1))
    (hroot : i.val ≠ 0) (hlast : i.val + 1 ≠ k + 1) :
    DisjointEnds (none : Edge (k + 1)) (some i) := by
  have hpath (a c : Fin (k + 2)) (h : a.val ≠ c.val) :
      vertex k a ≠ vertex k c := fun he => h (congrArg Fin.val (vertex_injective k he))
  have hi := i.isLt
  refine ⟨hpath (Fin.last (k + 1)) i.castSucc ?_, hpath (Fin.last (k + 1)) i.succ ?_,
    hpath 0 i.castSucc ?_, hpath 0 i.succ ?_⟩
  · change k + 1 ≠ i.val
    omega
  · change k + 1 ≠ i.val + 1
    exact hlast.symm
  · exact hroot.symm
  · simp

theorem path_path_disjoint {k : ℕ} (i j : Fin (k + 1))
    (hij : i ≠ j) (hforward : i.val + 1 ≠ j.val) (hback : j.val + 1 ≠ i.val) :
    DisjointEnds (some i : Edge (k + 1)) (some j) := by
  have hneq : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hpath (a c : Fin (k + 2)) (h : a.val ≠ c.val) :
      vertex k a ≠ vertex k c := fun he => h (congrArg Fin.val (vertex_injective k he))
  refine ⟨hpath i.castSucc j.castSucc hneq, hpath i.castSucc j.succ ?_,
    hpath i.succ j.castSucc hforward, hpath i.succ j.succ ?_⟩
  · change i.val ≠ j.val + 1
    exact hback.symm
  · change i.val + 1 ≠ j.val + 1
    omega

end P14CycleEdgeFamily

end -- original noncomputable section
end PreservedCycleEdgeFamily
-- END preserved module CycleEdgeFamily

-- BEGIN preserved module CycleQubitLabels
section PreservedCycleQubitLabels

/-! Two injective qubit-ray labelings of the even cycle edges. Each nonzero
complex qubit test kills at most one edge, and the same remaining edge then
survives all three local tests. -/

noncomputable section
namespace P14CycleQubitLabels
open P14CycleDeletionPotential P14QubitRayLabels
open scoped BigOperators

def labelA (h : ℕ) : Edge (2 * h + 1) → Label
  | none => (h, true)
  | some i => (i.val / 2, decide (i.val % 2 = 1))

def labelB {L : ℕ} : Edge L → Label
  | none => (0, false)
  | some i => ((i.val + 1) / 2, decide (i.val % 2 = 0))

private theorem labelA_none_ne_some (h : ℕ) (i : Fin (2 * h + 1)) :
    labelA h none ≠ labelA h (some i) := by
  intro he
  have hn : h = i.val / 2 := congrArg Prod.fst he
  have hb : true = decide (i.val % 2 = 1) := congrArg Prod.snd he
  have hp : i.val % 2 = 1 := of_decide_eq_true hb.symm
  have hi := i.isLt
  omega

theorem labelA_injective (h : ℕ) : Function.Injective (labelA h) := by
  intro e f he
  cases e with
  | none =>
      cases f with
      | none => rfl
      | some i => exact (labelA_none_ne_some h i he).elim
  | some i =>
      cases f with
      | none => exact (labelA_none_ne_some h i he.symm).elim
      | some j =>
          have hn : i.val / 2 = j.val / 2 := congrArg Prod.fst he
          have hb : decide (i.val % 2 = 1) = decide (j.val % 2 = 1) := congrArg Prod.snd he
          have hp := decide_eq_decide.mp hb
          exact congrArg some (Fin.ext (by omega))

private theorem labelB_none_ne_some {L : ℕ} (i : Fin L) :
    labelB (L := L) none ≠ labelB (some i) := by
  intro he
  have hn : 0 = (i.val + 1) / 2 := congrArg Prod.fst he
  have hb : false = decide (i.val % 2 = 0) := congrArg Prod.snd he
  have hp := Bool.of_decide_false hb.symm
  omega

theorem labelB_injective {L : ℕ} : Function.Injective (@labelB L) := by
  intro e f he
  cases e with
  | none =>
      cases f with
      | none => rfl
      | some i => exact (labelB_none_ne_some i he).elim
  | some i =>
      cases f with
      | none => exact (labelB_none_ne_some i he.symm).elim
      | some j =>
          have hn : (i.val + 1) / 2 = (j.val + 1) / 2 := congrArg Prod.fst he
          have hb : decide (i.val % 2 = 0) = decide (j.val % 2 = 0) := congrArg Prod.snd he
          have hp := decide_eq_decide.mp hb
          exact congrArg some (Fin.ext (by omega))

theorem exists_deleted_edge {L : ℕ} (label : Edge L → Label)
    (hinj : Function.Injective label) (y : Fin 2 → ℂ) (hy : y ≠ 0) :
    ∃ e : Edge L, ∀ e', pair (ray (label e')) y = 0 → e' = e := by
  classical
  by_cases hk : ∃ e, pair (ray (label e)) y = 0
  · obtain ⟨e, he⟩ := hk
    exact ⟨e, fun e' he' => hinj (killed_labels_equal _ _ y hy he' he)⟩
  · exact ⟨none, fun e he => (hk ⟨e, he⟩).elim⟩

def qubitA (h : ℕ) (e : Edge (2 * h + 1)) : Fin 2 → ℂ := ray (labelA h e)

def qubitB {L : ℕ} (e : Edge L) : Fin 2 → ℂ := ray (labelB e)

theorem qubitA_ne_zero (h : ℕ) (e : Edge (2 * h + 1)) : qubitA h e ≠ 0 := ray_ne_zero _

theorem qubitB_ne_zero {L : ℕ} (e : Edge L) : qubitB e ≠ 0 := ray_ne_zero _

theorem exists_product_survivor (h : ℕ) (x y : Fin 2 → ℂ) (z : Fin (2 * h) → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ e : Edge (2 * h + 1), pair (qubitA h e) x ≠ 0 ∧ pair (qubitB e) y ≠ 0 ∧
      (∑ r, star (P14CycleEdgeFamily.family (2 * h) e r) * z r) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_deleted_edge (labelA h) (labelA_injective h) x hx
  obtain ⟨b, hb⟩ := exists_deleted_edge labelB labelB_injective y hy
  obtain ⟨e, hea, heb, hez⟩ := P14CycleEdgeFamily.exists_survivor a b z hz
  exact ⟨e, fun he => hea (ha e he), fun he => heb (hb e he), hez⟩

end P14CycleQubitLabels

end -- original noncomputable section
end PreservedCycleQubitLabels
-- END preserved module CycleQubitLabels

-- BEGIN preserved module CycleProductOrthogonality
section PreservedCycleProductOrthogonality

/-! The two qubit assignments cover every adjacent pair of cycle edges.
All other distinct pairs are orthogonal in the same actual geometric factor. -/

noncomputable section
namespace P14CycleProductOrthogonality
open P14CycleDeletionPotential P14CycleEdgeFamily P14CycleQubitLabels P14QubitRayLabels
open scoped BigOperators

private theorem pair_opposite {l m : Label} (hn : l.1 = m.1) (hb : l.2 ≠ m.2) :
    pair (ray l) (ray m) = 0 := by
  rcases l with ⟨s, a⟩
  rcases m with ⟨t, b⟩
  dsimp at hn hb
  subst t
  cases a <;> cases b <;> simp_all [pair, ray, Fin.sum_univ_two]

private theorem zero_pair_symm {n : ℕ} (u v : Fin n → ℂ)
    (he : (∑ r, star (u r) * v r) = 0) : (∑ r, star (v r) * u r) = 0 := by
  have h := congrArg star he
  simpa [star_sum, star_mul, mul_comm] using h

def Orth {h : ℕ} (e f : Edge (2 * h + 1)) : Prop :=
  pair (qubitA h e) (qubitA h f) = 0 ∨ pair (qubitB e) (qubitB f) = 0 ∨
    (∑ r, star (family (2 * h) e r) * family (2 * h) f r) = 0

theorem Orth.symm {h : ℕ} {e f : Edge (2 * h + 1)} (he : Orth e f) : Orth f e := by
  rcases he with he | he | he
  · exact Or.inl (zero_pair_symm _ _ he)
  · exact Or.inr (Or.inl (zero_pair_symm _ _ he))
  · exact Or.inr (Or.inr (zero_pair_symm _ _ he))

private theorem closing_path (h : ℕ) (i : Fin (2 * h + 1)) :
    Orth (none : Edge (2 * h + 1)) (some i) := by
  by_cases hroot : i.val = 0
  · right; left
    apply pair_opposite
    · simp [labelB, hroot]
    · simp [labelB, hroot]
  · by_cases hlast : i.val = 2 * h
    · left
      apply pair_opposite
      · change h = i.val / 2
        omega
      · simp [labelA, hlast]
    · exact Or.inr (Or.inr (disjoint_pair (closing_path_disjoint i hroot (by omega))))

private theorem path_adjacent {h : ℕ} (i j : Fin (2 * h + 1))
    (hij : i.val + 1 = j.val) : Orth (some i : Edge (2 * h + 1)) (some j) := by
  by_cases hi : i.val % 2 = 0
  · have hj : j.val % 2 = 1 := by omega
    left
    apply pair_opposite
    · change i.val / 2 = j.val / 2
      omega
    · simp [labelA, hi, hj]
  · have hi' : i.val % 2 = 1 := by omega
    have hj : j.val % 2 = 0 := by omega
    right; left
    apply pair_opposite
    · change (i.val + 1) / 2 = (j.val + 1) / 2
      omega
    · simp [labelB, hi', hj]

theorem all_pairs (h : ℕ) (e f : Edge (2 * h + 1)) (hne : e ≠ f) : Orth e f := by
  cases e with
  | none =>
      cases f with
      | none => exact (hne rfl).elim
      | some i => exact closing_path h i
  | some i =>
      cases f with
      | none => exact (closing_path h i).symm
      | some j =>
          by_cases hf : i.val + 1 = j.val
          · exact path_adjacent i j hf
          · by_cases hb : j.val + 1 = i.val
            · exact (path_adjacent j i hb).symm
            · exact Or.inr (Or.inr (disjoint_pair (path_path_disjoint i j
                (fun he => hne (congrArg some he)) hf hb)))

end P14CycleProductOrthogonality

end -- original noncomputable section
end PreservedCycleProductOrthogonality
-- END preserved module CycleProductOrthogonality

-- BEGIN preserved module CycleEvenUPB
section PreservedCycleEvenUPB

/-! Literal complex-coordinate UPBs in dimensions (2,2,2h), h>=2. The
2h+2 cycle rows lie one below the original trivial-plus-one ceiling. -/

noncomputable section
namespace P14CycleEvenUPB
open P14CycleDeletionPotential P14CycleEdgeFamily P14CycleQubitLabels
open P14CycleProductOrthogonality P14QubitRayLabels
open scoped BigOperators

def dimensions (h : ℕ) : Fin 3 → ℕ :=
  Fin.cases 2 (Fin.cases 2 (fun _ => 2 * h))

def row (h : ℕ) (e : Edge (2 * h + 1)) : (j : Fin 3) → Fin (dimensions h j) → ℂ :=
  Fin.cases (qubitA h e) (Fin.cases (qubitB e) (fun _ => family (2 * h) e))

theorem edge_card (h : ℕ) : Fintype.card (Edge (2 * h + 1)) = 2 * h + 2 := by
  simp [Edge, add_assoc]

theorem ceiling (h : ℕ) (hh : 0 < h) :
    2 + (∑ j, (dimensions h j - 1)) = 2 * h + 3 := by
  simp [dimensions, Fin.sum_univ_succ]
  omega

theorem canonical {h : ℕ} (hh : 2 ≤ h) :
    ∃ m : ℕ, m ≤ 2 + ∑ j, (dimensions h j - 1) ∧
      ∃ v : Fin m → (j : Fin 3) → Fin (dimensions h j) → ℂ,
        (∀ i j, v i j ≠ 0) ∧
        (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
        (∀ a : (j : Fin 3) → Fin (dimensions h j) → ℂ, (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0) := by
  let E : Fin (2 * h + 2) ≃ Edge (2 * h + 1) := (Fintype.equivFinOfCardEq (edge_card h)).symm
  refine ⟨2 * h + 2, by rw [ceiling h (by omega)]; omega,
    (fun i => row h (E i)), ?_, ?_, ?_⟩
  · intro i j
    fin_cases j
    · exact qubitA_ne_zero h (E i)
    · exact qubitB_ne_zero (E i)
    · exact family_ne_zero (by omega) (E i)
  · intro i i' hne
    have he : E i ≠ E i' := fun he => hne (E.injective he)
    rcases all_pairs h (E i) (E i') he with ha | hb | hc
    · exact ⟨0, ha⟩
    · exact ⟨1, hb⟩
    · exact ⟨2, hc⟩
  · intro a ha
    obtain ⟨e, hx, hy, hz⟩ := exists_product_survivor h (a 0) (a 1) (a 2)
      (ha 0) (ha 1) (ha 2)
    refine ⟨E.symm e, ?_⟩
    intro j
    fin_cases j
    · change pair (qubitA h (E (E.symm e))) (a 0) ≠ 0
      rw [E.apply_symm_apply]
      exact hx
    · change pair (qubitB (E (E.symm e))) (a 1) ≠ 0
      rw [E.apply_symm_apply]
      exact hy
    · change (∑ r, star (family (2 * h) (E (E.symm e)) r) * a 2 r) ≠ 0
      rw [E.apply_symm_apply]
      exact hz

theorem dimensions_literal (h : ℕ) : dimensions h = ![2, 2, 2 * h] := by
  funext j
  fin_cases j <;> rfl

end P14CycleEvenUPB

end -- original noncomputable section
end PreservedCycleEvenUPB
-- END preserved module CycleEvenUPB

-- BEGIN preserved module TwoQubitsUPB
section PreservedTwoQubitsUPB

/-! Complete (2,2,K), K>=3, specialization of the corrected mixed UPB
conclusion, including arbitrary reordering of its three original factors.
This does not cover the other mixed dimension patterns. -/

namespace P14TwoQubitsUPB
open scoped BigOperators

def Conclusion (d : Fin 3 → ℕ) : Prop :=
  ∃ m : ℕ, m ≤ 2 + ∑ j, (d j - 1) ∧
    ∃ v : Fin m → (j : Fin 3) → Fin (d j) → ℂ,
      (∀ i j, v i j ≠ 0) ∧
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
      (∀ a : (j : Fin 3) → Fin (d j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem reindex (d : Fin 3 → ℕ) (e : Fin 3 ≃ Fin 3) (hc : Conclusion d) :
    Conclusion (fun j => d (e j)) := by
  obtain ⟨m, hm, v, hv, ho, hs⟩ := hc
  refine ⟨m, ?_, (fun i j => v i (e j)), (fun i j => hv i (e j)), ?_, ?_⟩
  · have hsum : (∑ j, (d (e j) - 1)) = ∑ j, (d j - 1) :=
      e.sum_comp (fun j => d j - 1)
    simpa only [hsum] using hm
  · intro i i' hi
    obtain ⟨j, hj⟩ := ho i i' hi
    obtain ⟨l, rfl⟩ := e.surjective j
    exact ⟨l, hj⟩
  · intro a ha
    let b : (j : Fin 3) → Fin (d j) → ℂ :=
      Equiv.piCongrLeft (fun j => Fin (d j) → ℂ) e a
    have hb : ∀ j, b j ≠ 0 := by
      intro j
      obtain ⟨l, rfl⟩ := e.surjective j
      simpa only [b, Equiv.piCongrLeft_apply_apply] using ha l
    obtain ⟨i, hi⟩ := hs b hb
    refine ⟨i, ?_⟩
    intro j
    simpa only [b, Equiv.piCongrLeft_apply_apply] using hi (e j)

theorem canonical_even {h : ℕ} (hh : 2 ≤ h) : Conclusion ![2, 2, 2 * h] := by
  have hc := P14CycleEvenUPB.canonical hh
  rw [P14CycleEvenUPB.dimensions_literal] at hc
  exact hc

theorem canonical_odd {h : ℕ} (hh : 0 < h) : Conclusion ![2, 2, 2 * h + 1] := by
  have hc := P14ThetaOddUPB.canonical hh
  rw [P14ThetaOddUPB.dimensions_literal] at hc
  exact hc

/-- Every mixed three-factor tuple (2,2,K), with no parity restriction. -/
theorem canonical (K : ℕ) (hK : 3 ≤ K) : Conclusion ![2, 2, K] := by
  obtain ⟨h, he | ho⟩ := Nat.even_or_odd' K
  · subst K
    exact canonical_even (by omega)
  · subst K
    exact canonical_odd (by omega)

/-- Preserve an original ordered tuple through one exact factor equivalence. -/
theorem of_dimensions (K : ℕ) (hK : 3 ≤ K) (D : Fin 3 → ℕ) (e : Fin 3 ≃ Fin 3)
    (hD : ∀ j, D j = (![2, 2, K] : Fin 3 → ℕ) (e j)) : Conclusion D := by
  have hd : D = fun j => (![2, 2, K] : Fin 3 → ℕ) (e j) := funext hD
  rw [hd]
  exact reindex _ e (canonical K hK)

end P14TwoQubitsUPB

end PreservedTwoQubitsUPB
-- END preserved module TwoQubitsUPB

open scoped BigOperators

theorem proof : ∀ (K : ℕ), 3 ≤ K →
    ∀ (D : Fin 3 → ℕ) (e : Fin 3 ≃ Fin 3),
      (∀ j, D j = (![2, 2, K] : Fin 3 → ℕ) (e j)) →
      ∃ m : ℕ, m ≤ 2 + ∑ j, (D j - 1) ∧
        ∃ v : Fin m → (j : Fin 3) → Fin (D j) → ℂ,
          (∀ i j, v i j ≠ 0) ∧
          (∀ i i', i ≠ i' →
            ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
          (∀ a : (j : Fin 3) → Fin (D j) → ℂ,
            (∀ j, a j ≠ 0) →
            ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0) := by
  intro K hK D e hD
  exact P14TwoQubitsUPB.of_dimensions K hK D e hD

end Submissions.J5P14TwoQubitsUPB.Proof
