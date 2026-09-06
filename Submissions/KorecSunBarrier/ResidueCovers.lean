import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Sigma

/-!
The two finite constructions supplied by woshuajolk in Jig problem 1, statement 9.
This proves exactly the existence, cover, and arithmetic conditions below.
It makes no additional claim about the scope of Korec–Sun theorems or about
the impossibility of an entire proof method.
-/

namespace Submissions.KorecSunBarrier.ResidueCovers

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def part {G : Type} [Group G] {r : ℕ} (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G) (p : (i : Fin r) × Fin (c i)) : Set G :=
  {x : G | (rep p)⁻¹ * x ∈ H p.1}

def IsHoleCover {G : Type} [Group G] {r : ℕ} (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G) : Prop :=
  Function.Injective H ∧
  (∀ p, (1 : G) ∉ part H c rep p) ∧
  (∀ p q, p ≠ q → Disjoint (part H c rep p) (part H c rep q)) ∧
  (⋃ p, part H c rep p) ∪ {1} = Set.univ

theorem cover_of_pointwise {G : Type} [Group G] {r : ℕ}
    (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G)
    (hH : Function.Injective H)
    (hone : ∀ p, (1 : G) ∉ part H c rep p)
    (hunique : ∀ p q x, x ∈ part H c rep p → x ∈ part H c rep q → p = q)
    (hcover : ∀ x : G, x = 1 ∨ ∃ p, x ∈ part H c rep p) :
    IsHoleCover H c rep := by
  refine ⟨hH, hone, ?_, ?_⟩
  · intro p q hpq
    exact Set.disjoint_left.mpr (fun x hx hy => hpq (hunique p q x hx hy))
  · ext x
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ,
      iff_true]
    exact (hcover x).symm

abbrev G5 := Multiplicative (ZMod 5)
abbrev G16 := Multiplicative (ZMod 16)

def H5 : Fin 1 → Subgroup G5 := fun _ => ⊥
def c5 : Fin 1 → ℕ := fun _ => 4
def rep5 (p : (i : Fin 1) × Fin (c5 i)) : G5 :=
  Multiplicative.ofAdd ((p.2.val + 1 : ℕ) : ZMod 5)

def H16 (i : Fin 4) : Subgroup G16 where
  carrier := {x | x.toAdd.val % (2 ^ (i.val + 1)) = 0}
  one_mem' := by
    exact (show ∀ j : Fin 4, (1 : G16).toAdd.val % (2 ^ (j.val + 1)) = 0 by decide) i
  mul_mem' := by
    intro a b ha hb
    exact (show ∀ (j : Fin 4) (x y : G16),
      x.toAdd.val % (2 ^ (j.val + 1)) = 0 →
      y.toAdd.val % (2 ^ (j.val + 1)) = 0 →
      (x * y).toAdd.val % (2 ^ (j.val + 1)) = 0 by decide) i a b ha hb
  inv_mem' := by
    intro a ha
    exact (show ∀ (j : Fin 4) (x : G16),
      x.toAdd.val % (2 ^ (j.val + 1)) = 0 →
      x⁻¹.toAdd.val % (2 ^ (j.val + 1)) = 0 by decide) i a ha

def c16 : Fin 4 → ℕ := fun _ => 1
def rep16 (p : (i : Fin 4) × Fin (c16 i)) : G16 :=
  Multiplicative.ofAdd (2 ^ p.1.val : ZMod 16)

theorem H16_injective : Function.Injective H16 := by
  intro i j hij
  have distinguish : ∀ i j : Fin 4,
      (∀ x : G16, x.toAdd.val % (2 ^ (i.val + 1)) = 0 ↔
        x.toAdd.val % (2 ^ (j.val + 1)) = 0) → i = j := by decide
  apply distinguish i j
  intro x
  change x ∈ H16 i ↔ x ∈ H16 j
  rw [hij]

theorem cover5 : IsHoleCover H5 c5 rep5 := by
  apply cover_of_pointwise
  · intro i j _
    exact Subsingleton.elim i j
  · simp only [part, H5, Subgroup.mem_bot, Set.mem_ofPred_eq]
    decide
  · simp only [part, H5, Subgroup.mem_bot, Set.mem_ofPred_eq]
    decide
  · simp only [part, H5, Subgroup.mem_bot, Set.mem_ofPred_eq]
    decide

theorem cover16 : IsHoleCover H16 c16 rep16 := by
  apply cover_of_pointwise
  · exact H16_injective
  · change ∀ p, ¬ ((rep16 p)⁻¹ * 1).toAdd.val % (2 ^ (p.1.val + 1)) = 0
    decide
  · change ∀ p q x,
      ((rep16 p)⁻¹ * x).toAdd.val % (2 ^ (p.1.val + 1)) = 0 →
      ((rep16 q)⁻¹ * x).toAdd.val % (2 ^ (q.1.val + 1)) = 0 → p = q
    decide
  · change ∀ x : G16, x = 1 ∨
      ∃ p, ((rep16 p)⁻¹ * x).toAdd.val % (2 ^ (p.1.val + 1)) = 0
    decide

theorem proof :
  (∃ (r : ℕ) (H : Fin r → Subgroup (Multiplicative (ZMod 5))) (c : Fin r → ℕ)
      (rep : ((i : Fin r) × Fin (c i)) → Multiplicative (ZMod 5)),
        IsHoleCover H c rep ∧ (∑ i, c i) = 4 ∧ (∏ i, (c i + 1)) = 5) ∧
  (∃ (r : ℕ) (H : Fin r → Subgroup (Multiplicative (ZMod 16))) (c : Fin r → ℕ)
      (rep : ((i : Fin r) × Fin (c i)) → Multiplicative (ZMod 16)),
        IsHoleCover H c rep ∧ (∑ i, c i) = 4 ∧ (∏ i, (c i + 1)) = 16) := by
  constructor
  · exact ⟨1, H5, c5, rep5, cover5, by decide, by decide⟩
  · exact ⟨4, H16, c16, rep16, cover16, by decide, by decide⟩

end Submissions.KorecSunBarrier.ResidueCovers
