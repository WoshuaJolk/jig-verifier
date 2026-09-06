import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/- Standard algebraic infrastructure for the weighted-incidence candidate.
   No novelty is claimed for these lemmas. -/
namespace Submissions.OVWeightedInclusionRank.Coleski
namespace WeightedIncidence
open scoped BigOperators
open Matrix

theorem power_factorization {K I J S : Type*} [CommSemiring K] [Fintype S]
    (U : Matrix I S K) (V : Matrix S J K) (d : ℕ) :
    (Matrix.of fun i j => (U * V) i j ^ d) =
      (Matrix.of fun i (a : Fin d → S) => ∏ t, U i (a t)) *
      (Matrix.of fun (a : Fin d → S) j => ∏ t, V (a t) j) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_pow, Finset.prod_mul_distrib]

theorem power_rank_bound {K I J S : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype S]
    (U : Matrix I S K) (V : Matrix S J K) (d : ℕ) :
    Matrix.rank (Matrix.of fun i j => (U * V) i j ^ d) ≤ Fintype.card S ^ d := by
  rw [power_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width
      (Matrix.of fun i (a : Fin d → S) => ∏ t, U i (a t)))

theorem tensor_mul {K T S : Type*} [CommSemiring K]
    [Fintype T] [DecidableEq T] [Fintype S]
    (A B : Matrix S S K) :
    (Matrix.of fun (x y : T → S) => ∏ t, A (x t) (y t)) *
      (Matrix.of fun (x y : T → S) => ∏ t, B (x t) (y t)) =
      (fun (x y : T → S) => ∏ t, (A * B) (x t) (y t)) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.of_apply, ← Finset.prod_mul_distrib, Fintype.prod_sum]

theorem off_diagonal_inverse {K S : Type*} [CommRing K]
    [Fintype S] [DecidableEq S] (h : (Fintype.card S : K) = 0) :
    ((Matrix.of fun (_ _ : S) => (1 : K)) - 1 : Matrix S S K) *
      (-1 - (Matrix.of fun (_ _ : S) => (1 : K))) = 1 := by
  have hJ : (Matrix.of fun (_ _ : S) => (1 : K)) *
      (Matrix.of fun (_ _ : S) => (1 : K)) =
      (0 : Matrix S S K) := by
    ext i j
    simp [Matrix.mul_apply, h]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_one,
    Matrix.one_mul, hJ]
  abel

theorem tensor_one {K T S : Type*} [CommSemiring K]
    [Fintype T] [DecidableEq T] [Fintype S] [DecidableEq S] :
    (Matrix.of fun (x y : T → S) => ∏ t, (1 : Matrix S S K) (x t) (y t)) = 1 := by
  classical
  ext x y
  by_cases h : x = y
  · subst y
    simp
  · have hn : ¬ ∀ t, x t = y t := fun he => h (funext he)
    obtain ⟨t, ht⟩ := not_forall.mp hn
    simp only [Matrix.of_apply, Matrix.one_apply, if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])

theorem tensor_inverse {K T S : Type*} [CommSemiring K]
    [Fintype T] [DecidableEq T] [Fintype S] [DecidableEq S]
    (A B : Matrix S S K) (h : A * B = 1) :
    (Matrix.of fun (x y : T → S) => ∏ t, A (x t) (y t)) *
      (Matrix.of fun (x y : T → S) => ∏ t, B (x t) (y t)) = 1 := by
  rw [tensor_mul, h]
  exact tensor_one

theorem transversal_bound (p k q r : ℕ) [Fact p.Prime]
    (hq : (q : ZMod p) = 0)
    (U : Matrix (Fin k → Fin q) (Fin r) (ZMod p))
    (V : Matrix (Fin r) (Fin k → Fin q) (ZMod p))
    (hs : ∀ x y, (U * V) x y ≠ 0 ↔ ∀ t, x t ≠ y t) :
    q ^ k ≤ r ^ (p - 1) := by
  classical
  let D : Matrix (Fin q) (Fin q) (ZMod p) :=
    (Matrix.of fun _ _ => 1) - 1
  let E : Matrix (Fin q) (Fin q) (ZMod p) :=
    -1 - (Matrix.of fun _ _ => 1)
  have hDE : D * E = 1 := off_diagonal_inverse (by simpa using hq)
  have hpow : (Matrix.of fun x y => (U * V) x y ^ (p - 1)) =
      (Matrix.of fun (x y : Fin k → Fin q) => ∏ t, D (x t) (y t)) := by
    ext x y
    simp only [Matrix.of_apply]
    by_cases hxy : ∀ t, x t ≠ y t
    · rw [ZMod.pow_card_sub_one_eq_one ((hs x y).mpr hxy)]
      symm
      apply Finset.prod_eq_one
      intro t _
      simp [D, hxy t]
    · have hz : (U * V) x y = 0 := by simpa using mt (hs x y).mp hxy
      have hp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
      rw [hz, zero_pow hp]
      symm
      obtain ⟨t, ht⟩ := not_forall.mp hxy
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp [D, not_not.mp ht]
  have hinv := tensor_inverse (T := Fin k) D E hDE
  rw [← hpow] at hinv
  have hl := Matrix.rank_mul_le_left
    (Matrix.of fun x y => (U * V) x y ^ (p - 1))
    (Matrix.of fun (x y : Fin k → Fin q) => ∏ t, E (x t) (y t))
  rw [hinv, Matrix.rank_one] at hl
  have hu := power_rank_bound U V (p - 1)
  exact (by simpa using hl : q ^ k ≤ _).trans (by simpa using hu)

set_option backward.isDefEq.respectTransparency false in
theorem exists_rank_factorization {K I J : Type*} [Field K]
    [Fintype I] [Fintype J] (M : Matrix I J K) :
    ∃ (U : Matrix I (Fin M.rank) K) (V : Matrix (Fin M.rank) J K), M = U * V := by
  classical
  let b : Module.Basis (Fin M.rank) K (LinearMap.range M.mulVecLin) :=
    Module.finBasis K (LinearMap.range M.mulVecLin)
  let c (j : J) : LinearMap.range M.mulVecLin :=
    ⟨M.col j, by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span (Set.mem_range_self j)⟩
  refine ⟨Matrix.of (fun i s => (b s).val i), Matrix.of (fun s j => b.repr (c j) s), ?_⟩
  ext i j
  have hh := congrArg (fun z : LinearMap.range M.mulVecLin => z.val i) (b.sum_repr (c j))
  simpa only [Matrix.mul_apply, Matrix.of_apply, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm, c, Matrix.col_apply] using hh.symm

theorem transversal_rank_bound (p k q : ℕ) [Fact p.Prime]
    (hq : (q : ZMod p) = 0)
    (W : Matrix (Fin k → Fin q) (Fin k → Fin q) (ZMod p))
    (hs : ∀ x y, W x y ≠ 0 ↔ ∀ t, x t ≠ y t) :
    q ^ k ≤ W.rank ^ (p - 1) := by
  obtain ⟨U, V, hUV⟩ := exists_rank_factorization W
  apply transversal_bound p k q W.rank hq U V
  simpa only [← hUV] using hs

def transversalSet {X : Type*} {k q : ℕ}
    (e : (Fin k × Fin q) ↪ X) (x : Fin k → Fin q) : Finset X :=
  Finset.univ.map ⟨fun t => e (t, x t), fun _ _ h => congrArg Prod.fst (e.injective h)⟩

theorem transversalSet_card {X : Type*} {k q : ℕ}
    (e : (Fin k × Fin q) ↪ X) (x : Fin k → Fin q) :
    (transversalSet e x).card = k := by simp [transversalSet]

theorem transversalSet_disjoint {X : Type*} {k q : ℕ}
    (e : (Fin k × Fin q) ↪ X) (x y : Fin k → Fin q) :
    Disjoint (transversalSet e x) (transversalSet e y) ↔ ∀ t, x t ≠ y t := by
  classical
  simp only [Finset.disjoint_left]
  constructor
  · intro h t ht
    apply h (a := e (t, x t))
    · exact Finset.mem_map.mpr ⟨t, Finset.mem_univ t, rfl⟩
    · exact Finset.mem_map.mpr ⟨t, Finset.mem_univ t, by
        change e (t, y t) = e (t, x t)
        rw [ht]⟩
  · intro h z hz hy
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hz
    obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hy
    have hab : (a, x a) = (b, y b) := e.injective (ha.trans hb.symm)
    have hab' : a = b := congrArg Prod.fst hab
    subst b
    exact h a (congrArg Prod.snd hab)

theorem weighted_inclusion_bound_embedded (p k q : ℕ) [Fact p.Prime]
    {X : Type*} [Fintype X] [DecidableEq X]
    (hq : (q : ZMod p) = 0) (e : (Fin k × Fin q) ↪ X)
    (M : Matrix {A : Finset X // A.card = k}
      {B : Finset X // B.card = Fintype.card X - k} (ZMod p))
    (hs : ∀ A B, M A B ≠ 0 ↔ A.val ⊆ B.val) :
    q ^ k ≤ M.rank ^ (p - 1) := by
  classical
  let row (x : Fin k → Fin q) : {A : Finset X // A.card = k} :=
    ⟨transversalSet e x, transversalSet_card e x⟩
  let col (y : Fin k → Fin q) :
      {B : Finset X // B.card = Fintype.card X - k} :=
    ⟨(transversalSet e y)ᶜ, by rw [Finset.card_compl, transversalSet_card]⟩
  have hsupport : ∀ x y, (M.submatrix row col) x y ≠ 0 ↔ ∀ t, x t ≠ y t := by
    intro x y
    rw [Matrix.submatrix_apply, hs]
    change transversalSet e x ⊆ (transversalSet e y)ᶜ ↔ _
    rw [Finset.subset_compl_iff_disjoint_right]
    exact transversalSet_disjoint e x y
  exact (transversal_rank_bound p k q hq (M.submatrix row col) hsupport).trans
    (Nat.pow_le_pow_left (Matrix.rank_submatrix_le M row col) (p - 1))

set_option backward.isDefEq.respectTransparency false in
theorem weighted_inclusion_bound (p k n : ℕ) [Fact p.Prime]
    (M : Matrix {A : Finset (Fin n) // A.card = k}
      {B : Finset (Fin n) // B.card = n - k} (ZMod p))
    (hs : ∀ A B, M A B ≠ 0 ↔ A.val ⊆ B.val) :
    (p * (n / (k * p))) ^ k ≤ M.rank ^ (p - 1) := by
  classical
  let q := p * (n / (k * p))
  have hsize : k * q ≤ n := by
    dsimp [q]
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_le n (k * p)
  obtain ⟨e⟩ : Nonempty ((Fin k × Fin q) ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hsize)
  have hq : (q : ZMod p) = 0 := by simp [q]
  have h := weighted_inclusion_bound_embedded p k q hq e
  rw [Fintype.card_fin] at h
  exact h M hs

theorem weighted_inclusion_polynomial_bound (p k n : ℕ) [Fact p.Prime]
    (hk : 1 ≤ k) (hn : k * p ≤ n)
    (M : Matrix {A : Finset (Fin n) // A.card = k}
      {B : Finset (Fin n) // B.card = n - k} (ZMod p))
    (hs : ∀ A B, M A B ≠ 0 ↔ A.val ⊆ B.val) :
    n ^ k ≤ (2 * k) ^ k * M.rank ^ (p - 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hkp : 0 < k * p := Nat.mul_pos (by omega) hp
  have hd : 1 ≤ n / (k * p) := (Nat.le_div_iff_mul_le hkp).mpr (by simpa using hn)
  have hm := Nat.mod_lt n hkp
  have he := Nat.div_add_mod n (k * p)
  have hl := Nat.mul_le_mul_left (k * p) hd
  have hb : n ≤ (2 * k) * (p * (n / (k * p))) := by nlinarith
  calc
    n ^ k ≤ ((2 * k) * (p * (n / (k * p)))) ^ k := Nat.pow_le_pow_left hb k
    _ = (2 * k) ^ k * (p * (n / (k * p))) ^ k := Nat.mul_pow _ _ _
    _ ≤ (2 * k) ^ k * M.rank ^ (p - 1) :=
      Nat.mul_le_mul_left _ (weighted_inclusion_bound p k n M hs)

/- The source's asymptotic question, with a natural constant and threshold.
   Raising the usual real-valued Omega inequality to p-1 gives this equivalent form. -/
def PublishedProblem1 : Prop :=
  ∀ (p k : ℕ), p.Prime → 2 ≤ k →
    ∃ C : ℕ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ M : Matrix {A : Finset (Fin n) // A.card = k}
        {B : Finset (Fin n) // B.card = n - k} (ZMod p),
        (∀ A B, M A B ≠ 0 ↔ A.val ⊆ B.val) →
        n ^ k ≤ C * M.rank ^ (p - 1)

theorem published_problem_one : PublishedProblem1 := by
  intro p k hp hk
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨(2 * k) ^ k, Nat.pow_pos (by omega), k * p, ?_⟩
  intro n hn M hs
  exact weighted_inclusion_polynomial_bound p k n (by omega) hn M hs

/- Nonvacuity: the quantified matrix class is inhabited at every n and k.
   The proof does not exploit impossible weights or an empty hypothesis class. -/
theorem support_witness (p k n : ℕ) [Fact p.Prime] :
    ∃ M : Matrix {A : Finset (Fin n) // A.card = k}
      {B : Finset (Fin n) // B.card = n - k} (ZMod p),
      ∀ A B, M A B ≠ 0 ↔ A.val ⊆ B.val := by
  classical
  refine ⟨Matrix.of (fun A B => if A.val ⊆ B.val then 1 else 0), ?_⟩
  intro A B
  simp

#print axioms published_problem_one
#print axioms support_witness
#print axioms weighted_inclusion_polynomial_bound
#print axioms weighted_inclusion_bound
#print axioms weighted_inclusion_bound_embedded
#print axioms transversal_rank_bound
#print axioms exists_rank_factorization
#print axioms transversal_bound
#print axioms power_factorization
#print axioms power_rank_bound
#print axioms tensor_mul
#print axioms off_diagonal_inverse
end WeightedIncidence

theorem proof : WeightedIncidence.PublishedProblem1 := WeightedIncidence.published_problem_one

end Submissions.OVWeightedInclusionRank.Coleski
