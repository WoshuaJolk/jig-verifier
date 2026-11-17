import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Lattice

/-
O'Neill–Verstraëte Conjecture 2 (A note on k-wise oddtown problems, Graphs and
Combinatorics 38:101, 2022), derived from the tensor-power rank argument.

The lemmas `power_factorization` through `transversal_bound` below are copied
unchanged from coleski's proof of the same paper's Problem 1 (Jig problem 406,
artifact a59f3e01-829e-41d6-b1cb-5c778dbb96bb). They carry the mathematical
weight. What is added here is the reduction of Conjecture 2 to
`transversal_bound`: `core` and `proof`.
-/
namespace Submissions.Erdos1041DegreeTwo.DryRunOV2
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

/-- The reduction. Split the first `2 * (k / 2)` families into two halves and
`[m]` into `k / 2` blocks of size `q` plus one spare index; choosing one index
per block for each half gives a matrix of intersection sizes, of rank at most
`n`, whose support is exactly the transversal pattern of `transversal_bound`. -/
theorem core (p k n m q : ℕ) [Fact p.Prime] (hk : 2 ≤ k)
    (A : Fin k → Fin m → Finset (Fin n))
    (h : ∀ idx : Fin k → Fin m,
      (((Finset.univ.filter (fun z : Fin n => ∀ j, z ∈ A j (idx j))).card : ℕ) : ZMod p) ≠ 0 ↔
        Function.Injective idx)
    (hq : (q : ZMod p) = 0) (hsize : (k / 2) * q + 1 ≤ m) :
    q ^ (k / 2) ≤ n ^ (p - 1) := by
  have hk' : 0 < k / 2 := by omega
  obtain ⟨e⟩ : Nonempty ((Fin (k / 2) × Fin q) ⊕ Unit ↪ Fin m) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hsize)
  obtain ⟨tm, htm⟩ : ∃ tm : Fin k → Fin (k / 2), ∀ j, (tm j).val = j.val % (k / 2) :=
    ⟨fun j => ⟨j.val % (k / 2), Nat.mod_lt _ hk'⟩, fun _ => rfl⟩
  obtain ⟨f1, hf1⟩ : ∃ f1 : (Fin (k / 2) → Fin q) → Fin k → Fin m,
      ∀ x j, f1 x j = e (Sum.inl (tm j, x (tm j))) :=
    ⟨fun x j => e (Sum.inl (tm j, x (tm j))), fun _ _ => rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ f2 : (Fin (k / 2) → Fin q) → Fin k → Fin m,
      ∀ y j, f2 y j =
        if j.val < 2 * (k / 2) then e (Sum.inl (tm j, y (tm j))) else e (Sum.inr ()) :=
    ⟨fun y j => if j.val < 2 * (k / 2) then e (Sum.inl (tm j, y (tm j))) else e (Sum.inr ()),
      fun _ _ => rfl⟩
  obtain ⟨idx, hidx⟩ : ∃ idx : (Fin (k / 2) → Fin q) → (Fin (k / 2) → Fin q) → Fin k → Fin m,
      ∀ x y j, idx x y j = if j.val < k / 2 then f1 x j else f2 y j :=
    ⟨fun x y j => if j.val < k / 2 then f1 x j else f2 y j, fun _ _ _ => rfl⟩
  have hmod : ∀ j : ℕ, k / 2 ≤ j → j < 2 * (k / 2) → j % (k / 2) = j - k / 2 := by
    intro j h1 h2
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  -- injectivity of the index choice is the transversal pattern
  have hinj : ∀ x y : Fin (k / 2) → Fin q,
      Function.Injective (idx x y) ↔ ∀ t, x t ≠ y t := by
    intro x y
    constructor
    · intro hI t hxy
      have htlt : t.val < k / 2 := t.isLt
      obtain ⟨j1, hj1⟩ : ∃ j1 : Fin k, j1.val = t.val := ⟨⟨t.val, by omega⟩, rfl⟩
      obtain ⟨j2, hj2⟩ : ∃ j2 : Fin k, j2.val = k / 2 + t.val :=
        ⟨⟨k / 2 + t.val, by omega⟩, rfl⟩
      have ht1 : tm j1 = t := by
        apply Fin.ext
        rw [htm, hj1]
        exact Nat.mod_eq_of_lt htlt
      have ht2 : tm j2 = t := by
        apply Fin.ext
        rw [htm, hj2, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt htlt
      have c1 : j1.val < k / 2 := by rw [hj1]; exact htlt
      have c2 : ¬ j2.val < k / 2 := by rw [hj2]; omega
      have c3 : j2.val < 2 * (k / 2) := by rw [hj2]; omega
      have e1 : idx x y j1 = e (Sum.inl (t, x t)) := by
        rw [hidx, if_pos c1, hf1, ht1]
      have e2 : idx x y j2 = e (Sum.inl (t, y t)) := by
        rw [hidx, if_neg c2, hf2, if_pos c3, ht2]
      have hj : j1 = j2 := hI (by rw [e1, e2, hxy])
      have hv : j1.val = j2.val := congrArg Fin.val hj
      rw [hj1, hj2] at hv
      omega
    · intro hne j1 j2 heq
      rw [hidx, hidx] at heq
      have hl1 := j1.isLt
      have hl2 := j2.isLt
      by_cases c1 : j1.val < k / 2 <;> by_cases c2 : j2.val < k / 2
      · rw [if_pos c1, if_pos c2, hf1, hf1] at heq
        have h2 := Sum.inl.inj (e.injective heq)
        have h4 : (tm j1).val = (tm j2).val := congrArg Fin.val (congrArg Prod.fst h2)
        rw [htm, htm, Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at h4
        exact Fin.ext h4
      · rw [if_pos c1, if_neg c2, hf1, hf2] at heq
        by_cases d2 : j2.val < 2 * (k / 2)
        · rw [if_pos d2] at heq
          have h2 := Sum.inl.inj (e.injective heq)
          have h3 : tm j1 = tm j2 := congrArg Prod.fst h2
          have h5 : x (tm j1) = y (tm j2) := congrArg Prod.snd h2
          rw [h3] at h5
          exact absurd h5 (hne (tm j2))
        · rw [if_neg d2] at heq
          exact absurd (e.injective heq) (by simp)
      · rw [if_neg c1, if_pos c2, hf2, hf1] at heq
        by_cases d1 : j1.val < 2 * (k / 2)
        · rw [if_pos d1] at heq
          have h2 := Sum.inl.inj (e.injective heq)
          have h3 : tm j1 = tm j2 := congrArg Prod.fst h2
          have h5 : y (tm j1) = x (tm j2) := congrArg Prod.snd h2
          rw [h3] at h5
          exact absurd h5.symm (hne (tm j2))
        · rw [if_neg d1] at heq
          exact absurd (e.injective heq) (by simp)
      · rw [if_neg c1, if_neg c2, hf2, hf2] at heq
        by_cases d1 : j1.val < 2 * (k / 2) <;> by_cases d2 : j2.val < 2 * (k / 2)
        · rw [if_pos d1, if_pos d2] at heq
          have h2 := Sum.inl.inj (e.injective heq)
          have h4 : (tm j1).val = (tm j2).val := congrArg Fin.val (congrArg Prod.fst h2)
          rw [htm, htm, hmod j1.val (by omega) d1, hmod j2.val (by omega) d2] at h4
          exact Fin.ext (by omega)
        · rw [if_pos d1, if_neg d2] at heq
          exact absurd (e.injective heq) (by simp)
        · rw [if_neg d1, if_pos d2] at heq
          exact absurd (e.injective heq) (by simp)
        · exact Fin.ext (by omega)
  -- the two indicator matrices
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin (k / 2) → Fin q) (Fin n) (ZMod p),
      ∀ x z, U x z =
        if (∀ j : Fin k, j.val < k / 2 → z ∈ A j (f1 x j)) then 1 else 0 :=
    ⟨fun x z => if (∀ j : Fin k, j.val < k / 2 → z ∈ A j (f1 x j)) then 1 else 0,
      fun _ _ => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin n) (Fin (k / 2) → Fin q) (ZMod p),
      ∀ z y, V z y =
        if (∀ j : Fin k, ¬ j.val < k / 2 → z ∈ A j (f2 y j)) then 1 else 0 :=
    ⟨fun z y => if (∀ j : Fin k, ¬ j.val < k / 2 → z ∈ A j (f2 y j)) then 1 else 0,
      fun _ _ => rfl⟩
  have hsplit : ∀ (x y : Fin (k / 2) → Fin q) (z : Fin n),
      (∀ j, z ∈ A j (idx x y j)) ↔
        ((∀ j : Fin k, j.val < k / 2 → z ∈ A j (f1 x j)) ∧
          (∀ j : Fin k, ¬ j.val < k / 2 → z ∈ A j (f2 y j))) := by
    intro x y z
    constructor
    · intro hall
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · have hz := hall j
        rw [hidx, if_pos hj] at hz
        exact hz
      · have hz := hall j
        rw [hidx, if_neg hj] at hz
        exact hz
    · rintro ⟨h1, h2⟩ j
      rw [hidx]
      by_cases hj : j.val < k / 2
      · rw [if_pos hj]
        exact h1 j hj
      · rw [if_neg hj]
        exact h2 j hj
  have hUV : ∀ (x y : Fin (k / 2) → Fin q) (z : Fin n),
      U x z * V z y = if (∀ j, z ∈ A j (idx x y j)) then (1 : ZMod p) else 0 := by
    intro x y z
    rw [hU, hV]
    by_cases h1 : (∀ j : Fin k, j.val < k / 2 → z ∈ A j (f1 x j)) <;>
      by_cases h2 : (∀ j : Fin k, ¬ j.val < k / 2 → z ∈ A j (f2 y j))
    · rw [if_pos h1, if_pos h2, if_pos ((hsplit x y z).mpr ⟨h1, h2⟩), mul_one]
    · rw [if_pos h1, if_neg h2, if_neg (fun hc => h2 ((hsplit x y z).mp hc).2), mul_zero]
    · rw [if_neg h1, if_neg (fun hc => h1 ((hsplit x y z).mp hc).1), zero_mul]
    · rw [if_neg h1, if_neg (fun hc => h1 ((hsplit x y z).mp hc).1), zero_mul]
  have hW : ∀ x y : Fin (k / 2) → Fin q,
      (U * V) x y =
        (((Finset.univ.filter (fun z : Fin n => ∀ j, z ∈ A j (idx x y j))).card : ℕ) : ZMod p) := by
    intro x y
    rw [Matrix.mul_apply]
    calc ∑ z, U x z * V z y
        = ∑ z, (if (∀ j, z ∈ A j (idx x y j)) then (1 : ZMod p) else 0) :=
          Finset.sum_congr rfl (fun z _ => hUV x y z)
      _ = (((Finset.univ.filter (fun z : Fin n => ∀ j, z ∈ A j (idx x y j))).card : ℕ) : ZMod p) :=
          Finset.sum_boole _ _
  have hs : ∀ x y : Fin (k / 2) → Fin q, (U * V) x y ≠ 0 ↔ ∀ t, x t ≠ y t := by
    intro x y
    rw [hW]
    exact (h (idx x y)).trans (hinj x y)
  exact transversal_bound p (k / 2) q n hq U V hs

/-- O'Neill–Verstraëte Conjecture 2: `m = O(n ^ ((p - 1) / ⌊k / 2⌋))`, in the
equivalent integer form `m ^ ⌊k / 2⌋ ≤ C * n ^ (p - 1)` with `C` depending only
on `p` and `k`. -/
theorem proof :
    ∀ (p k : ℕ), p.Prime → 2 ≤ k →
      ∃ C : ℕ, ∀ n m : ℕ, 1 ≤ n →
        ∀ A : Fin k → Fin m → Finset (Fin n),
          (∀ idx : Fin k → Fin m,
            (((Finset.univ.inf (fun j : Fin k => A j (idx j))).card : ℕ) : ZMod p) ≠ 0 ↔
              Function.Injective idx) →
          m ^ (k / 2) ≤ C * n ^ (p - 1) := by
  intro p k hp hk
  haveI : Fact p.Prime := ⟨hp⟩
  have hppos : 0 < p := hp.pos
  have hk' : 0 < k / 2 := by omega
  refine ⟨(2 * (k / 2) * p) ^ (k / 2), ?_⟩
  intro n m hn A h0
  have hcard : ∀ idx : Fin k → Fin m,
      (Finset.univ.inf (fun j : Fin k => A j (idx j))).card
        = (Finset.univ.filter (fun z : Fin n => ∀ j, z ∈ A j (idx j))).card := by
    intro idx
    congr 1
    ext z
    simp [Finset.mem_inf]
  have h : ∀ idx : Fin k → Fin m,
      (((Finset.univ.filter (fun z : Fin n => ∀ j, z ∈ A j (idx j))).card : ℕ) : ZMod p) ≠ 0 ↔
        Function.Injective idx := by
    intro idx
    rw [← hcard idx]
    exact h0 idx
  have hnpow : 0 < n ^ (p - 1) := Nat.pow_pos hn
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = (k / 2) * p := ⟨_, rfl⟩
  have hKpos : 0 < K := by
    rw [hK]
    exact Nat.mul_pos hk' hppos
  have hK2 : K ≤ 2 * (k / 2) * p := by
    rw [hK]
    exact Nat.mul_le_mul_right p (by omega)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (m - 1) / K := ⟨_, rfl⟩
  have hdm := Nat.div_add_mod (m - 1) K
  have hmodlt := Nat.mod_lt (m - 1) hKpos
  rw [← hd] at hdm
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hmK : m ≤ K := by
      rw [hd0, Nat.mul_zero] at hdm
      omega
    calc m ^ (k / 2) ≤ K ^ (k / 2) := Nat.pow_le_pow_left hmK _
      _ ≤ (2 * (k / 2) * p) ^ (k / 2) := Nat.pow_le_pow_left hK2 _
      _ ≤ (2 * (k / 2) * p) ^ (k / 2) * n ^ (p - 1) := Nat.le_mul_of_pos_right _ hnpow
  · obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = p * d := ⟨_, rfl⟩
    have hqz : (q : ZMod p) = 0 := by
      rw [hqdef]
      simp
    obtain ⟨P, hP⟩ : ∃ P : ℕ, P = K * d := ⟨_, rfl⟩
    rw [← hP] at hdm
    have hkq : (k / 2) * q = P := by
      rw [hqdef, hP, hK]
      ring
    have hPpos : 1 ≤ P := by
      rw [hP]
      exact Nat.mul_pos hKpos hdpos
    have hKle : K ≤ P := by
      rw [hP]
      exact Nat.le_mul_of_pos_right K hdpos
    have hsize : (k / 2) * q + 1 ≤ m := by
      rw [hkq]
      omega
    have hcore := core p k n m q hk A h hqz hsize
    have hm2 : m ≤ 2 * (k / 2) * q := by
      have e2 : 2 * (k / 2) * q = 2 * P := by
        rw [← hkq]
        ring
      rw [e2]
      omega
    calc m ^ (k / 2) ≤ (2 * (k / 2) * q) ^ (k / 2) := Nat.pow_le_pow_left hm2 _
      _ = (2 * (k / 2)) ^ (k / 2) * q ^ (k / 2) := Nat.mul_pow _ _ _
      _ ≤ (2 * (k / 2)) ^ (k / 2) * n ^ (p - 1) := Nat.mul_le_mul_left _ hcore
      _ ≤ (2 * (k / 2) * p) ^ (k / 2) * n ^ (p - 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hppos) _)

end Submissions.Erdos1041DegreeTwo.DryRunOV2
