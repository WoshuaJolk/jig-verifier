import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

namespace Submissions.UPBIffNoDeficientCover.DeficientCover

open scoped BigOperators ComplexConjugate

noncomputable section

def Deficient {p m : ℕ} {d : Fin p → ℕ}
    (v : Fin m → (j : Fin p) → EuclideanSpace ℂ (Fin (d j)))
    (j : Fin p) (S : Finset (Fin m)) : Prop :=
  Submodule.span ℂ
    (Set.range fun i : (S : Set (Fin m)) => v i.1 j) ≠ ⊤

def Covers {p m : ℕ} (S : (j : Fin p) → Finset (Fin m)) : Prop :=
  ∀ i, ∃ j, i ∈ S j

def Unextendible {p m : ℕ} {d : Fin p → ℕ}
    (v : Fin m → (j : Fin p) → EuclideanSpace ℂ (Fin (d j))) : Prop :=
  ∀ a : (j : Fin p) → EuclideanSpace ℂ (Fin (d j)), (∀ j, a j ≠ 0) →
    ∃ i, ∀ j, inner ℂ (v i j) (a j) ≠ 0

lemma exists_nonzero_orthogonal_of_ne_top
    {d : ℕ} (K : Submodule ℂ (EuclideanSpace ℂ (Fin d))) (hK : K ≠ ⊤) :
    ∃ a : EuclideanSpace ℂ (Fin d), a ≠ 0 ∧ ∀ x ∈ K, inner ℂ x a = 0 := by
  have hex : ∃ x : EuclideanSpace ℂ (Fin d), x ∉ K := by
    by_contra h
    push Not at h
    apply hK
    rw [eq_top_iff]
    intro x _
    exact h x
  obtain ⟨x, hx⟩ := hex
  obtain ⟨y, hy, z, hz, hxyz⟩ := K.exists_add_mem_mem_orthogonal x
  have hz0 : z ≠ 0 := by
    intro hzero
    apply hx
    rw [hxyz, hzero, add_zero]
    exact hy
  refine ⟨z, hz0, ?_⟩
  intro u hu
  exact (K.mem_orthogonal z).mp hz u hu

lemma span_inner_right_eq_zero
    {d : ℕ} {s : Set (EuclideanSpace ℂ (Fin d))}
    {a x : EuclideanSpace ℂ (Fin d)}
    (hgen : ∀ y ∈ s, inner ℂ y a = 0)
    (hx : x ∈ Submodule.span ℂ s) :
    inner ℂ x a = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | smul c x _ hx => simp [inner_smul_left, hx]

theorem proof :
    ∀ (p m : ℕ) (d : Fin p → ℕ)
      (v : Fin m → (j : Fin p) → EuclideanSpace ℂ (Fin (d j))),
      Unextendible v ↔
        ¬ ∃ S : (j : Fin p) → Finset (Fin m),
            Covers S ∧ ∀ j, Deficient v j (S j) := by
  intro p m d v
  constructor
  · intro hu
    rintro ⟨S, hcover, hdef⟩
    have hex :
        ∀ j : Fin p,
          ∃ a : EuclideanSpace ℂ (Fin (d j)),
            a ≠ 0 ∧
              ∀ x ∈ Submodule.span ℂ
                (Set.range fun i : (S j : Set (Fin m)) => v i.1 j),
                inner ℂ x a = 0 := by
      intro j
      exact exists_nonzero_orthogonal_of_ne_top _ (hdef j)
    choose a ha0 haorth using hex
    obtain ⟨i, hi⟩ := hu a ha0
    obtain ⟨j, hij⟩ := hcover i
    have hvspan :
        v i j ∈ Submodule.span ℂ
          (Set.range fun t : (S j : Set (Fin m)) => v t.1 j) := by
      apply Submodule.subset_span
      exact ⟨⟨i, hij⟩, rfl⟩
    exact hi j (haorth j (v i j) hvspan)
  · intro hnocover a ha0
    by_contra hsurvivor
    push Not at hsurvivor
    let S : (j : Fin p) → Finset (Fin m) :=
      fun j => Finset.univ.filter fun i => inner ℂ (v i j) (a j) = 0
    apply hnocover
    refine ⟨S, ?_, ?_⟩
    · intro i
      obtain ⟨j, hj⟩ := hsurvivor i
      exact ⟨j, by simp [S, hj]⟩
    · intro j
      intro htop
      have haj :
          a j ∈ Submodule.span ℂ
            (Set.range fun i : (S j : Set (Fin m)) => v i.1 j) := by
        rw [htop]
        exact Submodule.mem_top
      have hgen :
          ∀ y ∈ (Set.range fun i : (S j : Set (Fin m)) => v i.1 j),
            inner ℂ y (a j) = 0 := by
        rintro y ⟨i, rfl⟩
        simpa [S] using i.2
      have hself : inner ℂ (a j) (a j) = 0 :=
        span_inner_right_eq_zero hgen haj
      exact ha0 j (inner_self_eq_zero.mp hself)

end

end Submissions.UPBIffNoDeficientCover.DeficientCover
