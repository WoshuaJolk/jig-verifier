import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
namespace Submissions.Erdos193AxisWalkWitness.Worker01
open Set
def IsSWalk {V : Type*} [AddCommGroup V] (S : Set V) (a : ℕ → V) : Prop := ∀ n, a (n+1)-a n ∈ S
def HasCollinearTriple (R) {V : Type*} [DivisionRing R] [AddCommGroup V] [Module R V] (A : Set V) : Prop := ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x≠y ∧ y≠z ∧ x≠z ∧ Collinear R ({x,y,z}:Set V)
def axisStep : Fin 3 → ℤ := fun i ↦ if i=0 then 1 else 0
def axisWalk : ℕ → Fin 3 → ℤ := fun n ↦ (n:ℤ) • axisStep
theorem proof : IsSWalk {axisStep} axisWalk ∧ (range axisWalk).Infinite ∧ HasCollinearTriple ℚ (range (fun n ↦ (↑) ∘ axisWalk n : ℕ → Fin 3 → ℚ)) := by
 refine ⟨?_,?_,?_⟩
 · intro n; simp [axisWalk,sub_eq_add_neg,add_smul]
 · apply Set.infinite_range_of_injective
   intro m n h
   have h0 := congrFun h (0:Fin 3)
   simp [axisWalk,axisStep] at h0
   exact_mod_cast h0
 · let p : ℕ → Fin 3 → ℚ := fun n ↦ (↑) ∘ axisWalk n
   refine ⟨p 0,⟨0,rfl⟩,p 1,⟨1,rfl⟩,p 2,⟨2,rfl⟩,?_,?_,?_,?_⟩
   · intro h; have h0 := congrFun h (0:Fin 3); norm_num [p,axisWalk,axisStep] at h0
   · intro h; have h0 := congrFun h (0:Fin 3); norm_num [p,axisWalk,axisStep] at h0
   · intro h; have h0 := congrFun h (0:Fin 3); norm_num [p,axisWalk,axisStep] at h0
   · rw [collinear_iff_exists_forall_eq_smul_vadd]
     refine ⟨p 0,fun i ↦ (axisStep i:ℚ),?_⟩
     intro q hq
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hq
     rcases hq with rfl|rfl|rfl
     · refine ⟨0,?_⟩; ext i; simp [p,axisWalk]
     · refine ⟨1,?_⟩; ext i; simp [p,axisWalk]
     · refine ⟨2,?_⟩; ext i; simp [p,axisWalk]
end Submissions.Erdos193AxisWalkWitness.Worker01
