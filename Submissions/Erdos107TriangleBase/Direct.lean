import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Euclidean.Triangle

namespace Submissions.Erdos107TriangleBase.Direct

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def NonTrilinear (A : Set Plane) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → ∀ ⦃z⦄, z ∈ A →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ {x, y, z}

def ConvexIndep (S : Set Plane) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

def HasConvexNGon (n : ℕ) (P : Set Plane) : Prop :=
  ∃ S : Finset Plane, S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

def cardSet (n : ℕ) : Set ℕ :=
  {N | ∀ pts : Finset Plane, pts.card = N → NonTrilinear pts →
    HasConvexNGon n pts}

noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

private lemma convexIndep_triple_of_not_collinear {a b c : Plane}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcoll : ¬ Collinear ℝ ({a, b, c} : Set Plane)) :
    ConvexIndep ({a, b, c} : Set Plane) := by
  intro x hx hmem
  apply hcoll
  have hx_aff : x ∈ affineSpan ℝ (({a, b, c} : Set Plane) \ {x}) :=
    convexHull_subset_affineSpan _ hmem
  rw [show ({a, b, c} : Set Plane) =
      insert x (({a, b, c} : Set Plane) \ {x}) from
    (Set.insert_sdiff_self_of_mem hx).symm,
    collinear_insert_iff_of_mem_affineSpan hx_aff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show ({x, b, c} : Set Plane) \ {x} = ({b, c} : Set Plane) by
      ext
      aesop]
    exact collinear_pair ℝ b c
  · rw [show ({a, x, c} : Set Plane) \ {x} = ({a, c} : Set Plane) by
      ext
      aesop]
    exact collinear_pair ℝ a c
  · rw [show ({a, b, x} : Set Plane) \ {x} = ({a, b} : Set Plane) by
      ext
      aesop]
    exact collinear_pair ℝ a b

theorem proof : f 3 = 3 := by
  have hmem3 : (3 : ℕ) ∈ cardSet 3 := by
    intro pts hpts hnontri
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hpts
    refine ⟨{a, b, c}, by simp [hab, hac, hbc], subset_refl _, ?_⟩
    have hcoerce :
        (({a, b, c} : Finset Plane) : Set Plane) = ({a, b, c} : Set Plane) := by
      simp
    have hnc : ¬ Collinear ℝ ({a, b, c} : Set Plane) :=
      hnontri (by simp) (by simp) (by simp) hab hbc hac
    rw [hcoerce]
    exact convexIndep_triple_of_not_collinear hab hac hbc hnc
  refine le_antisymm (Nat.sInf_le hmem3) (le_csInf ⟨3, hmem3⟩ fun N hN => ?_)
  by_contra! hlt
  let g : ℕ → Plane := fun i => EuclideanSpace.single 0 (i : ℝ)
  let pts : Finset Plane := (Finset.range N).image g
  have hinj : Function.Injective g := fun i j hij => by
    have h := congrArg (fun v : Plane => v 0) hij
    simpa [g] using h
  have hpts_card : pts.card = N := by
    simp [pts, Finset.card_image_of_injOn hinj.injOn]
  have hnontri : NonTrilinear (pts : Set Plane) := by
    intro x hx y hy z hz hxy hyz hxz
    exfalso
    have hsub : ({x, y, z} : Finset Plane) ⊆ pts := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hx, hy, hz⟩
    have hthree : ({x, y, z} : Finset Plane).card = 3 := by
      simp [hxy, hyz, hxz]
    have hle := Finset.card_le_card hsub
    rw [hthree, hpts_card] at hle
    omega
  obtain ⟨S, hScard, hSsub, _⟩ := hN pts hpts_card hnontri
  have hle : S.card ≤ pts.card := Finset.card_le_card (by exact_mod_cast hSsub)
  omega

end Submissions.Erdos107TriangleBase.Direct
