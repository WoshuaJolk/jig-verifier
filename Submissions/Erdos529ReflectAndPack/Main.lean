import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Prod

namespace Submissions.Erdos529ReflectAndPack.Main

abbrev Point := ℤ × ℤ

def verticalReflection (H : ℤ) (x : Point) : Point :=
  (2 * H - x.1, x.2)

theorem verticalReflection_involutive (H : ℤ) :
    Function.Involutive (verticalReflection H) := by
  intro x
  apply Prod.ext
  · change 2 * H - (2 * H - x.1) = x.1
    omega
  · rfl

theorem verticalReflection_injective (H : ℤ) :
    Function.Injective (verticalReflection H) := by
  intro x y h
  have h' := congrArg (verticalReflection H) h
  simpa only [verticalReflection_involutive H x,
    verticalReflection_involutive H y] using h'

theorem verticalReflection_fixed (H : ℤ) (x : Point) (hx : x.1 = H) :
    verticalReflection H x = x := by
  apply Prod.ext
  · change 2 * H - x.1 = x.1
    omega
  · rfl

def reflectSuffix {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) (t : Fin (n + 1)) : Point :=
  if t ≤ L then p t else verticalReflection H (p t)

theorem reflectSuffix_of_le {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) (t : Fin (n + 1)) (ht : t ≤ L) :
    reflectSuffix p L H t = p t := by
  simp only [reflectSuffix, if_pos ht]

theorem reflectSuffix_of_gt {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) (t : Fin (n + 1)) (ht : L < t) :
    reflectSuffix p L H t = verticalReflection H (p t) := by
  have hnot : ¬ t ≤ L := by omega
  simp only [reflectSuffix, if_neg hnot]

theorem reflectSuffix_involutive {n : ℕ} (L : Fin (n + 1)) (H : ℤ) :
    Function.Involutive (fun p : Fin (n + 1) → Point => reflectSuffix p L H) := by
  intro p
  funext t
  by_cases ht : t ≤ L
  · simp only [reflectSuffix, if_pos ht]
  · simp only [reflectSuffix, if_neg ht, verticalReflection_involutive H (p t)]

theorem reflectSuffix_zero {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) :
    reflectSuffix p L H 0 = p 0 :=
  reflectSuffix_of_le p L H 0 (Fin.zero_le L)

theorem reflectSuffix_endpoint {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) (hcut : (p L).1 = H) :
    reflectSuffix p L H (Fin.last n) = verticalReflection H (p (Fin.last n)) := by
  by_cases h : Fin.last n ≤ L
  · have heq : Fin.last n = L := Fin.ext (Nat.le_antisymm h (Fin.le_last L))
    rw [reflectSuffix_of_le p L H (Fin.last n) h, heq]
    exact (verticalReflection_fixed H (p L) hcut).symm
  · simp only [reflectSuffix, if_neg h]

/-- The cut vertex is handled by the original injectivity, rather than by a
strict separation assumption that would incorrectly exclude it. -/
theorem prefix_ne_reflected_suffix {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) (hp : Function.Injective p)
    (hcut : (p L).1 = H)
    (hbefore : ∀ t, t < L → (p t).1 < H)
    (hafter : ∀ t, L < t → (p t).1 ≤ H)
    (a b : Fin (n + 1)) (ha : a ≤ L) (hb : L < b) :
    p a ≠ verticalReflection H (p b) := by
  intro h
  by_cases haL : a = L
  · subst a
    have h' := congrArg (verticalReflection H) h
    have hpLb : p L = p b := by
      simpa only [verticalReflection_fixed H (p L) hcut,
        verticalReflection_involutive H (p b)] using h'
    have hLb := hp hpLb
    omega
  · have ha' : a < L := by omega
    have hleft := hbefore a ha'
    have hright := hafter b hb
    have hfirst := congrArg Prod.fst h
    change (p a).1 = 2 * H - (p b).1 at hfirst
    omega

theorem reflectSuffix_injective {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) (hp : Function.Injective p)
    (hcut : (p L).1 = H)
    (hbefore : ∀ t, t < L → (p t).1 < H)
    (hafter : ∀ t, L < t → (p t).1 ≤ H) :
    Function.Injective (reflectSuffix p L H) := by
  intro a b h
  by_cases ha : a ≤ L
  · by_cases hb : b ≤ L
    · apply hp
      simpa only [reflectSuffix, if_pos ha, if_pos hb] using h
    · exact False.elim (prefix_ne_reflected_suffix p L H hp hcut hbefore hafter
        a b ha (by omega) (by
          simpa only [reflectSuffix, if_pos ha, if_neg hb] using h))
  · by_cases hb : b ≤ L
    · exact False.elim (prefix_ne_reflected_suffix p L H hp hcut hbefore hafter
        b a hb (by omega) (by
          simpa only [reflectSuffix, if_pos hb, if_neg ha] using h.symm))
    · apply hp
      apply verticalReflection_injective H
      simpa only [reflectSuffix, if_neg ha, if_neg hb] using h

/-- Consecutive vertices differ by one of the four square-lattice unit steps. -/
def GridAdjacent (x y : Point) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
  (y.1 = x.1 ∧ y.2 = x.2 - 1)

theorem verticalReflection_gridAdjacent (H : ℤ) {x y : Point}
    (h : GridAdjacent x y) :
    GridAdjacent (verticalReflection H x) (verticalReflection H y) := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · right; left
    constructor <;> dsimp [verticalReflection] <;> omega
  · left
    constructor <;> dsimp [verticalReflection] <;> omega
  · right; right; left
    constructor <;> dsimp [verticalReflection] <;> omega
  · right; right; right
    constructor <;> dsimp [verticalReflection] <;> omega

def HasUnitSteps {n : ℕ} (p : Fin (n + 1) → Point) : Prop :=
  ∀ i : Fin n, GridAdjacent (p i.castSucc) (p i.succ)

theorem reflectSuffix_hasUnitSteps {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) (hcut : (p L).1 = H)
    (hsteps : HasUnitSteps p) : HasUnitSteps (reflectSuffix p L H) := by
  intro i
  have hi := hsteps i
  have hiSucc : i.succ.val = i.castSucc.val + 1 := rfl
  by_cases ha : i.castSucc ≤ L
  · by_cases hb : i.succ ≤ L
    · simpa only [reflectSuffix, if_pos ha, if_pos hb] using hi
    · have hiL : i.castSucc = L := by omega
      have hfix : verticalReflection H (p i.castSucc) = p i.castSucc := by
        apply verticalReflection_fixed
        simpa only [hiL] using hcut
      have href := verticalReflection_gridAdjacent H hi
      simpa only [reflectSuffix, if_pos ha, if_neg hb, hfix] using href
  · have hb : ¬ i.succ ≤ L := by omega
    simpa only [reflectSuffix, if_neg ha, if_neg hb] using
      verticalReflection_gridAdjacent H hi

/-- A nontrivial instance: the suffix turns left on the original path and right
on its reflection. This checks that the separation hypotheses are satisfiable. -/
def examplePath (t : Fin 4) : Point :=
  if t = 0 then (0, 0) else if t = 1 then (1, 0)
  else if t = 2 then (1, 1) else (0, 1)

example : Function.Injective examplePath ∧
    (examplePath 1).1 = 1 ∧
    (∀ t : Fin 4, t < 1 → (examplePath t).1 < 1) ∧
    (∀ t : Fin 4, 1 < t → (examplePath t).1 ≤ 1) ∧
    HasUnitSteps examplePath ∧
    reflectSuffix examplePath 1 1 3 = (2, 1) := by
  unfold Function.Injective HasUnitSteps GridAdjacent
  decide



/-- An injective lattice path in a square uses at most the square's vertices. -/
theorem length_le_box_card {n r : ℕ} (p : Fin (n + 1) → ℤ × ℤ)
    (hp : Function.Injective p)
    (hbox : ∀ t, -(r : ℤ) ≤ (p t).1 ∧ (p t).1 ≤ r ∧
      -(r : ℤ) ≤ (p t).2 ∧ (p t).2 ≤ r) :
    n + 1 ≤ (2 * r + 1) ^ 2 := by
  let I := Finset.Icc (-(r : ℤ)) (r : ℤ)
  have hI : I.card = 2 * r + 1 := by
    rw [Int.card_Icc]
    omega
  have hsub : Finset.univ.image p ⊆ I ×ˢ I := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    rcases hbox t with ⟨h₁, h₂, h₃, h₄⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h₁, h₂⟩,
      Finset.mem_Icc.mpr ⟨h₃, h₄⟩⟩
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hp, Finset.card_univ,
    Fintype.card_fin, Finset.card_product, hI, pow_two] using hcard

/-- A path longer than the number of square vertices must leave the square. -/
theorem exists_outside_box {n r : ℕ} (p : Fin (n + 1) → ℤ × ℤ)
    (hp : Function.Injective p) (hn : (2 * r + 1) ^ 2 < n + 1) :
    ∃ t, (p t).1 < -(r : ℤ) ∨ (r : ℤ) < (p t).1 ∨
      (p t).2 < -(r : ℤ) ∨ (r : ℤ) < (p t).2 := by
  by_contra h
  push Not at h
  have hbound := length_le_box_card p hp (fun t => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h t
    exact ⟨h₁, h₂, h₃, h₄⟩)
  omega


abbrev statement : Prop :=
  ∀ (n : ℕ) (p : Fin (n + 1) → Point) (L : Fin (n + 1)) (H : ℤ),
    Function.Injective p → p 0 = (0, 0) → HasUnitSteps p →
    (p L).1 = H →
    (∀ t, t < L → (p t).1 < H) →
    (∀ t, L < t → (p t).1 ≤ H) →
    let q := reflectSuffix p L H
    Function.Injective q ∧ q 0 = (0, 0) ∧ HasUnitSteps q ∧
    q (Fin.last n) = verticalReflection H (p (Fin.last n)) ∧
    ∀ r : ℕ, (2 * r + 1) ^ 2 < n + 1 →
      ∃ t, (q t).1 < -(r : ℤ) ∨ (r : ℤ) < (q t).1 ∨
        (q t).2 < -(r : ℤ) ∨ (r : ℤ) < (q t).2

theorem proof : statement := by
  intro n p L H hp hzero hsteps hcut hbefore hafter
  have hq := reflectSuffix_injective p L H hp hcut hbefore hafter
  refine ⟨hq, ?_, reflectSuffix_hasUnitSteps p L H hcut hsteps,
    reflectSuffix_endpoint p L H hcut, ?_⟩
  · rw [reflectSuffix_zero, hzero]
  · intro r hr
    exact exists_outside_box (reflectSuffix p L H) hq hr

example : examplePath 0 = (0, 0) := by decide

/-- Omitting the strictly-left prefix permits a reflected collision. -/
def badCutPath (t : Fin 5) : Point :=
  if t = 0 then (0, 0) else if t = 1 then (1, 0)
  else if t = 2 then (1, 1) else if t = 3 then (0, 1) else (-1, 1)

example : Function.Injective badCutPath ∧ HasUnitSteps badCutPath ∧
    badCutPath 0 = (0, 0) ∧ (badCutPath 3).1 = 0 ∧
    (∀ t : Fin 5, 3 < t → (badCutPath t).1 ≤ 0) ∧
    ¬ Function.Injective (reflectSuffix (n := 4) badCutPath 3 0) := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_⟩
  · unfold HasUnitSteps GridAdjacent
    decide
  · intro h
    have heq : (2 : Fin 5) = 4 := h (by decide)
    exact (by decide : (2 : Fin 5) ≠ 4) heq

/-- Without injectivity, arbitrarily repeated vertices invalidate box packing. -/
example : (∀ t : Fin 2, (fun _ : Fin 2 => ((0 : ℤ), (0 : ℤ))) t = (0, 0)) ∧
    ¬ Function.Injective (fun _ : Fin 2 => ((0 : ℤ), (0 : ℤ))) := by decide

end Submissions.Erdos529ReflectAndPack.Main
