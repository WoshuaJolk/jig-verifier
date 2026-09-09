import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos241BoseChowlaConstruction.BoseChowla

open Polynomial

/-- The polynomial cancellation step in the classical Bose–Chowla construction. -/
theorem triple_product_injective {K E : Type*} [Field K] [Field E] [Algebra K E]
    (θ : E) (hθ : (minpoly K θ).natDegree = 3)
    {m n : Multiset K} (hm : m.card = 3) (hn : n.card = 3)
    (hprod : (m.map (fun a => θ - algebraMap K E a)).prod =
      (n.map (fun a => θ - algebraMap K E a)).prod) : m = n := by
  classical
  let p : K[X] := (m.map fun a => X - C a).prod
  let q : K[X] := (n.map fun a => X - C a).prod
  have hp : p.Monic := monic_multisetProd_X_sub_C m
  have hq : q.Monic := monic_multisetProd_X_sub_C n
  have hdp : p.degree = 3 := by
    rw [degree_eq_natDegree hp.ne_zero]
    simp [p, natDegree_multiset_prod_X_sub_C_eq_card, hm]
  have hdq : q.degree = 3 := by
    rw [degree_eq_natDegree hq.ne_zero]
    simp [q, natDegree_multiset_prod_X_sub_C_eq_card, hn]
  have hdθ : (minpoly K θ).degree = 3 := by
    have hne : minpoly K θ ≠ 0 := by
      intro he
      simp [he] at hθ
    rw [degree_eq_natDegree hne, hθ]
    simp
  have heval : aeval θ p = aeval θ q := by
    simpa [p, q, map_multiset_prod, Multiset.map_map, Function.comp_def] using hprod
  have heq : p = q := by
    apply eq_of_sub_eq_zero
    by_contra hne
    have hle := minpoly.degree_le_of_ne_zero K θ hne
      (by rw [map_sub, heval, sub_self])
    have hlt := degree_sub_lt_left (hdp.trans hdq.symm) hp.ne_zero
      (hp.leadingCoeff.trans hq.leadingCoeff.symm)
    rw [hdθ] at hle
    rw [hdp] at hlt
    exact (not_lt_of_ge hle) hlt
  simpa [p, q] using congrArg Polynomial.roots heq

end Submissions.Erdos241BoseChowlaConstruction.BoseChowla

namespace Submissions.Erdos241BoseChowlaConstruction.BoseLog

/-- The finite-field logarithm step of the classical Bose–Chowla construction. -/
theorem exists_log_embedding {K E : Type*} [Field K] [Field E] [Algebra K E]
    [Finite E] (θ : E) (hθ : (minpoly K θ).natDegree = 3) :
    ∃ f : K → ℕ, Function.Injective f ∧
      (∀ a, 1 ≤ f a ∧ f a ≤ Nat.card E - 2) ∧
      (∀ m n : Multiset K, m.card = 3 → n.card = 3 →
        (m.map f).sum = (n.map f).sum → m = n) := by
  classical
  have hnot : θ ∉ (algebraMap K E).range := by
    rw [← minpoly.natDegree_eq_one_iff, hθ]
    decide
  have hne (a : K) : θ - algebraMap K E a ≠ 0 := by
    intro h
    exact hnot ⟨a, (sub_eq_zero.mp h).symm⟩
  let u : K → Eˣ := fun a => Units.mk0 (θ - algebraMap K E a) (hne a)
  have hu_inj : Function.Injective u := by
    intro a b h
    have hv : θ - algebraMap K E a = θ - algebraMap K E b := by
      simpa [u] using congrArg (fun z : Eˣ => (z : E)) h
    exact (algebraMap K E).injective (sub_right_inj.mp hv)
  have hu_ne_one (a : K) : u a ≠ 1 := by
    intro h
    have hv : θ - algebraMap K E a = 1 := by
      simpa [u] using congrArg (fun z : Eˣ => (z : E)) h
    apply hnot
    refine ⟨a + 1, ?_⟩
    simpa [map_add, map_one, add_comm] using (sub_eq_iff_eq_add.mp hv).symm
  let M := Nat.card Eˣ
  letI : NeZero M := by
    dsimp [M]
    infer_instance
  let e : Multiplicative (ZMod M) ≃* Eˣ :=
    zmodCyclicMulEquiv (G := Eˣ) inferInstance
  let L : K → ZMod M := fun a => (e.symm (u a)).toAdd
  have hL (a : K) : e (Multiplicative.ofAdd (L a)) = u a := by
    simp [L]
  have hL_ne_zero (a : K) : L a ≠ 0 := by
    intro h
    apply hu_ne_one a
    rw [← hL a, h]
    simp
  let f : K → ℕ := fun a => (L a).val
  have hf (a : K) : e (Multiplicative.ofAdd (f a : ZMod M)) = u a := by
    simpa only [f, ZMod.natCast_zmod_val] using hL a
  have hprod (s : Multiset K) :
      e (Multiplicative.ofAdd ((s.map f).sum : ZMod M)) = (s.map u).prod := by
    refine Multiset.induction_on s ?_ ?_
    · simp
    · intro a s ih
      simp only [Multiset.map_cons, Multiset.sum_cons, Nat.cast_add,
        ofAdd_add, map_mul, hf, ih, Multiset.prod_cons]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a b h
    have hab : L a = L b := ZMod.val_injective M h
    apply hu_inj
    rw [← hL a, ← hL b, hab]
  · intro a
    constructor
    · exact Nat.succ_le_of_lt (ZMod.val_pos.mpr (hL_ne_zero a))
    · have hlt : f a < M := ZMod.val_lt (L a)
      simpa [M, Nat.card_units, Nat.sub_sub] using Nat.le_sub_one_of_lt hlt
  · intro m n hm hn hsum
    apply BoseChowla.triple_product_injective θ hθ hm hn
    have hp : (m.map u).prod = (n.map u).prod := by
      rw [← hprod m, ← hprod n, hsum]
    simpa [map_multiset_prod, Multiset.map_map, Function.comp_def, u] using
      congrArg (Units.coeHom E) hp

end Submissions.Erdos241BoseChowlaConstruction.BoseLog

namespace Submissions.Erdos241BoseChowlaConstruction.BoseFinite

open Finset

def UniqueTripleSums (A : Finset ℕ) : Prop :=
  ∀ m n : Multiset ℕ, m.card = 3 → n.card = 3 →
    (∀ x ∈ m, x ∈ A) → (∀ x ∈ n, x ∈ A) → m.sum = n.sum → m = n

theorem exists_set_of_embedding {K : Type*} [Fintype K] [Nonempty K]
    (N : ℕ) (f : K → ℕ) (hf : Function.Injective f)
    (hb : ∀ a, 1 ≤ f a ∧ f a ≤ N)
    (hu : ∀ m n : Multiset K, m.card = 3 → n.card = 3 →
      (m.map f).sum = (n.map f).sum → m = n) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ A.card = Fintype.card K ∧ UniqueTripleSums A := by
  classical
  let A := univ.image f
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := mem_image.mp hx
    exact mem_Icc.mpr (hb a)
  · simp [A, card_image_of_injective _ hf]
  · let g := Function.invFun f
    have recover (m : Multiset ℕ) (hm : ∀ x ∈ m, x ∈ A) :
        (m.map g).map f = m := by
      rw [Multiset.map_map]
      calc
        _ = m.map id := Multiset.map_congr rfl (by
          intro x hx
          obtain ⟨a, _, rfl⟩ := mem_image.mp (hm x hx)
          exact congrArg f (Function.leftInverse_invFun hf a))
        _ = m := Multiset.map_id m
    intro m n hm hn hmA hnA hs
    have heq : m.map g = n.map g := hu _ _ (by simpa using hm)
      (by simpa using hn) (by rw [recover m hmA, recover n hnA, hs])
    simpa only [recover m hmA, recover n hnA] using congrArg (Multiset.map f) heq

/-- The classical finite Bose–Chowla construction for prime parameters. -/
theorem exists_b3_prime (p : ℕ) [Fact p.Prime] :
    ∃ A : Finset ℕ, A ⊆ Icc 1 (p ^ 3 - 2) ∧ A.card = p ∧ UniqueTripleSums A := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) (GaloisField p 3)
  have hd : (minpoly (ZMod p) θ).natDegree = 3 :=
    ((Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) θ).mp hθ).trans
      (GaloisField.finrank p (by decide))
  obtain ⟨f, hf, hb, hu⟩ := BoseLog.exists_log_embedding θ hd
  obtain ⟨A, hA, hc, hU⟩ := exists_set_of_embedding (p ^ 3 - 2) f hf
    (by simpa only [GaloisField.card p 3 (by decide)] using hb) hu
  exact ⟨A, hA, (hc.trans (ZMod.card p)), hU⟩

/-- The exact finite extremum from the #89 root statement. -/
noncomputable def maxUniqueSums (N r : ℕ) : ℕ :=
  open scoped Classical in
  let candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

theorem lower_bound_prime (p : ℕ) (hp : p.Prime) :
    p ≤ maxUniqueSums (p ^ 3 - 2) 3 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA, hc, hU⟩ := exists_b3_prime p
  calc
    p = A.card := hc.symm
    _ ≤ maxUniqueSums (p ^ 3 - 2) 3 :=
      le_sup (mem_filter.mpr ⟨mem_powerset.mpr hA, hU⟩)

end Submissions.Erdos241BoseChowlaConstruction.BoseFinite
