import Mathlib.Algebra.Module.Submodule.Defs

namespace Submissions.J5P26RectangularGluing.Proof

universe uR uU uO uK

variable {R U O K : Type*} [Ring R] [AddCommGroup U] [Module R U]
variable [AddCommGroup O] [Module R O]

def Cover (D A B C : Submodule R U) : Prop :=
  ∀ h, h ∈ D → ∃ x y, x ∈ D ∧ x ∈ A ∧ y ∈ D ∧ y ∈ B ∧ y ∈ C ∧ h = x + y

theorem refine_cover [AddCommGroup K]
    (D A1 A2 A3 : Submodule R U) (f1 f2 f3 : U → K)
    (f1a : ∀ x y, f1 (x + y) = f1 x + f1 y)
    (f2a : ∀ x y, f2 (x + y) = f2 x + f2 y)
    (f3a : ∀ x y, f3 (x + y) = f3 x + f3 y)
    (dmem : ∀ u, u ∈ D ↔ f1 u = 0 ∧ f2 u = 0 ∧ f3 u = 0)
    (v1 : ∀ u, u ∈ A1 → f1 u = 0)
    (v2 : ∀ u, u ∈ A2 → f2 u = 0)
    (v3 : ∀ u, u ∈ A3 → f3 u = 0)
    (raw : ∀ h, h ∈ D → ∃ x y, x ∈ A1 ∧ y ∈ A2 ∧ y ∈ A3 ∧ h = x + y) :
    Cover D A1 A2 A3 := by
  intro h hd
  obtain ⟨x, y, hx, hy2, hy3, heq⟩ := raw h hd
  have hz := (dmem h).1 hd
  have h1 : f1 x + f1 y = 0 := by rw [← f1a, ← heq]; exact hz.1
  have h2 : f2 x + f2 y = 0 := by rw [← f2a, ← heq]; exact hz.2.1
  have h3 : f3 x + f3 y = 0 := by rw [← f3a, ← heq]; exact hz.2.2
  have fy1 : f1 y = 0 := by rw [v1 x hx, zero_add] at h1; exact h1
  have fx2 : f2 x = 0 := by rw [v2 y hy2, add_zero] at h2; exact h2
  have fx3 : f3 x = 0 := by rw [v3 y hy3, add_zero] at h3; exact h3
  exact ⟨x, y, (dmem x).2 ⟨v1 x hx, fx2, fx3⟩, hx,
    (dmem y).2 ⟨fy1, v2 y hy2, v3 y hy3⟩, hy2, hy3, heq⟩

theorem domain_pair_decomposition (D A1 A2 A3 : Submodule R U)
    (c1 : Cover D A1 A2 A3) (c2 : Cover D A2 A1 A3)
    (h : U) (hd : h ∈ D) :
    ∃ x12 x13 x23,
      (x12 ∈ D ∧ x12 ∈ A1 ∧ x12 ∈ A2) ∧
      (x13 ∈ D ∧ x13 ∈ A1 ∧ x13 ∈ A3) ∧
      (x23 ∈ D ∧ x23 ∈ A2 ∧ x23 ∈ A3) ∧ h = (x12 + x13) + x23 := by
  obtain ⟨x, x23, xd, xa1, x23d, x23a2, x23a3, heq⟩ := c1 h hd
  obtain ⟨x12, x13, x12d, x12a2, x13d, x13a1, x13a3, xeq⟩ := c2 x xd
  have x12eq : x12 = x - x13 := (eq_sub_iff_add_eq).2 xeq.symm
  have x12a1 : x12 ∈ A1 := by
    rw [x12eq]
    exact A1.sub_mem xa1 x13a1
  exact ⟨x12, x13, x23, ⟨x12d, x12a1, x12a2⟩,
    ⟨x13d, x13a1, x13a3⟩, ⟨x23d, x23a2, x23a3⟩, by rw [heq, xeq]⟩

theorem vanish_on_two_outputs [AddCommGroup K] (W1 W2 : Submodule R O)
    (f : O → K) (fa : ∀ x y, f (x + y) = f x + f y)
    (cover : ∀ z, ∃ x y, x ∈ W1 ∧ y ∈ W2 ∧ z = x + y)
    (v1 : ∀ x, x ∈ W1 → f x = 0) (v2 : ∀ y, y ∈ W2 → f y = 0)
    (z : O) : f z = 0 := by
  obtain ⟨x, y, hx, hy, heq⟩ := cover z
  rw [heq, fa, v1 x hx, v2 y hy, add_zero]

theorem vanish_on_three_frames [AddCommGroup K]
    (D A1 A2 A3 : Submodule R U) (W1 W2 W3 : Submodule R O)
    (c1 : Cover D A1 A2 A3) (c2 : Cover D A2 A1 A3)
    (Q : U → O → K)
    (qa : ∀ x y z, Q (x + y) z = Q x z + Q y z)
    (qz : ∀ h x y, Q h (x + y) = Q h x + Q h y)
    (w12 : ∀ z, ∃ x y, x ∈ W1 ∧ y ∈ W2 ∧ z = x + y)
    (w13 : ∀ z, ∃ x y, x ∈ W1 ∧ y ∈ W3 ∧ z = x + y)
    (w23 : ∀ z, ∃ x y, x ∈ W2 ∧ y ∈ W3 ∧ z = x + y)
    (v1 : ∀ h, h ∈ D → h ∈ A1 → ∀ z, z ∈ W1 → Q h z = 0)
    (v2 : ∀ h, h ∈ D → h ∈ A2 → ∀ z, z ∈ W2 → Q h z = 0)
    (v3 : ∀ h, h ∈ D → h ∈ A3 → ∀ z, z ∈ W3 → Q h z = 0)
    (h : U) (hd : h ∈ D) (z : O) : Q h z = 0 := by
  obtain ⟨x12, x13, x23, h12, h13, h23, heq⟩ :=
    domain_pair_decomposition D A1 A2 A3 c1 c2 h hd
  have z12 : Q x12 z = 0 := vanish_on_two_outputs W1 W2 (Q x12) (qz x12) w12
    (v1 x12 h12.1 h12.2.1) (v2 x12 h12.1 h12.2.2) z
  have z13 : Q x13 z = 0 := vanish_on_two_outputs W1 W3 (Q x13) (qz x13) w13
    (v1 x13 h13.1 h13.2.1) (v3 x13 h13.1 h13.2.2) z
  have z23 : Q x23 z = 0 := vanish_on_two_outputs W2 W3 (Q x23) (qz x23) w23
    (v2 x23 h23.1 h23.2.1) (v3 x23 h23.1 h23.2.2) z
  rw [heq, qa, qa, z12, z13, z23, add_zero, add_zero]

theorem solves :
  (∀ {R : Type uR} {U : Type uU} {K : Type uK} [Ring R] [AddCommGroup U] [Module R U] [AddCommGroup K]
    (D A1 A2 A3 : Submodule R U) (f1 f2 f3 : U → K)
    (f1a : ∀ x y, f1 (x + y) = f1 x + f1 y)
    (f2a : ∀ x y, f2 (x + y) = f2 x + f2 y)
    (f3a : ∀ x y, f3 (x + y) = f3 x + f3 y)
    (dmem : ∀ u, u ∈ D ↔ f1 u = 0 ∧ f2 u = 0 ∧ f3 u = 0)
    (v1 : ∀ u, u ∈ A1 → f1 u = 0)
    (v2 : ∀ u, u ∈ A2 → f2 u = 0)
    (v3 : ∀ u, u ∈ A3 → f3 u = 0)
    (raw : ∀ h, h ∈ D → ∃ x y, x ∈ A1 ∧ y ∈ A2 ∧ y ∈ A3 ∧ h = x + y), Cover D A1 A2 A3) ∧
  (∀ {R : Type uR} {U : Type uU} {O : Type uO} {K : Type uK} [Ring R] [AddCommGroup U] [Module R U] [AddCommGroup O] [Module R O] [AddCommGroup K]
    (D A1 A2 A3 : Submodule R U) (W1 W2 W3 : Submodule R O)
    (c1 : Cover D A1 A2 A3) (c2 : Cover D A2 A1 A3)
    (Q : U → O → K)
    (qa : ∀ x y z, Q (x + y) z = Q x z + Q y z)
    (qz : ∀ h x y, Q h (x + y) = Q h x + Q h y)
    (w12 : ∀ z, ∃ x y, x ∈ W1 ∧ y ∈ W2 ∧ z = x + y)
    (w13 : ∀ z, ∃ x y, x ∈ W1 ∧ y ∈ W3 ∧ z = x + y)
    (w23 : ∀ z, ∃ x y, x ∈ W2 ∧ y ∈ W3 ∧ z = x + y)
    (v1 : ∀ h, h ∈ D → h ∈ A1 → ∀ z, z ∈ W1 → Q h z = 0)
    (v2 : ∀ h, h ∈ D → h ∈ A2 → ∀ z, z ∈ W2 → Q h z = 0)
    (v3 : ∀ h, h ∈ D → h ∈ A3 → ∀ z, z ∈ W3 → Q h z = 0)
    (h : U) (hd : h ∈ D) (z : O), Q h z = 0) := by
  exact ⟨@refine_cover, @vanish_on_three_frames⟩

end Submissions.J5P26RectangularGluing.Proof
