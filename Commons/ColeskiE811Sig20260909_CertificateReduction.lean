import Mathlib

/- BEGIN bundled local module CertificateReduction -/

open scoped BigOperators
namespace ColeskiFiniteBalance

/-- Sum a function by separating a chosen coordinate from all other coordinates. -/
theorem sum_split {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    (z : I) (F : (I → V) → ℝ) :
    (∑ x, F x) = ∑ rest : ({i : I // i ≠ z} → V),
      ∑ a : V, F ((Equiv.funSplitAt z V).symm (a, rest)) := by
  rw [← (Equiv.funSplitAt z V).symm.sum_comp F]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- A marked coefficient independent of the sampled coordinate has zero total
against a balanced color row. This is the finite conditional-expectation step. -/
theorem marked_balance {I V C : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [Fintype C] [DecidableEq C]
    (z v : I) (hv : v ≠ z) (color : V → V → C)
    (weight : ({i : I // i ≠ z} → V) → C → ℝ)
    (hbalanced : ∀ u c, (∑ a : V, ((if color u a = c then (Fintype.card C : ℝ) else 0) - 1)) = 0) :
    (∑ x : I → V, ∑ c : C,
      weight (fun i => x i) c *
        ((if color (x v) (x z) = c then (Fintype.card C : ℝ) else 0) - 1)) = 0 := by
  rw [sum_split z]
  apply Finset.sum_eq_zero
  intro rest _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  have hrest (a : V) :
      (fun i : {i : I // i ≠ z} => (Equiv.funSplitAt z V).symm (a,rest) i) = rest := by
    funext i
    simp [Equiv.funSplitAt, Equiv.piSplitAt, i.property]
  simp only [hrest]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, hv, ↓reduceDIte]
  rw [← Finset.mul_sum, hbalanced]
  simp

/-- Exact color-class counts imply the centered row identity used above. -/
theorem balance_of_card {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (color : V → V → C) (t : ℕ)
    (hsize : Fintype.card V = Fintype.card C * t)
    (hcard : ∀ u c, (Finset.univ.filter (fun a => color u a = c)).card = t) :
    ∀ u c, (∑ a : V,
      ((if color u a = c then (Fintype.card C : ℝ) else 0) - 1)) = 0 := by
  classical
  intro u c
  rw [Finset.sum_sub_distrib]
  simp [← Finset.sum_filter, hcard, hsize, Nat.cast_mul]
  ring

/-- The exact finite counting contradiction used by the D-palette certificate.
The positivity premise must separately be proved for every sampled coloring. -/
theorem separator_obstruction {I V C : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [Nonempty V] [Fintype C] [DecidableEq C]
    (color : V → V → C)
    (weight : (z : I) → {v : I // v ≠ z} →
      ({i : I // i ≠ z} → V) → C → ℝ)
    (hbalanced : ∀ u c, (∑ a : V,
      ((if color u a = c then (Fintype.card C : ℝ) else 0) - 1)) = 0)
    (hpositive : ∀ x : I → V, 0 <
      ∑ z : I, ∑ v : {v : I // v ≠ z}, ∑ c : C,
        weight z v (fun i => x i) c *
          ((if color (x v) (x z) = c then (Fintype.card C : ℝ) else 0) - 1)) : False := by
  classical
  let Q (x : I → V) : ℝ :=
    ∑ z : I, ∑ v : {v : I // v ≠ z}, ∑ c : C,
      weight z v (fun i => x i) c *
        ((if color (x v) (x z) = c then (Fintype.card C : ℝ) else 0) - 1)
  have hzero : (∑ x, Q x) = 0 := by
    dsimp only [Q]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro z _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro v _
    exact marked_balance z v v.property color (weight z v) hbalanced
  have hpos : 0 < ∑ x, Q x := by
    apply Finset.sum_pos
    · intro x _
      exact hpositive x
    · exact Finset.univ_nonempty
  linarith

end ColeskiFiniteBalance

open scoped BigOperators
namespace ColeskiDeletedVertex

def loopColor {V C : Type*} [DecidableEq V] (c : V → V → C) (r : V)
    (u v : {x : V // x ≠ r}) : C :=
  if u = v then c u r else c u v

def rowEquiv {V : Type*} [DecidableEq V] (r : V) (u : {x : V // x ≠ r}) :
    {x : V // x ≠ r} ≃ {x : V // x ≠ (u : V)} :=
  (Equiv.swap (u : V) r).subtypeEquiv (by
    intro x
    constructor
    · intro hx he
      have := congrArg (Equiv.swap (u : V) r) he
      exact hx (by simpa using this)
    · intro hx he
      subst x
      simp at hx)

theorem loopColor_rowEquiv {V C : Type*} [DecidableEq V] (c : V → V → C)
    (r : V) (u v : {x : V // x ≠ r}) :
    loopColor c r u v = c u (rowEquiv r u v) := by
  by_cases h : u = v
  · subst v
    simp [loopColor, rowEquiv]
  · have huv : (v : V) ≠ (u : V) := by
      intro e
      exact h (Subtype.ext e.symm)
    simp [loopColor, h, rowEquiv, Equiv.swap_apply_of_ne_of_ne huv v.property]

theorem row_sum {V C : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → C) (r : V) (u : {x : V // x ≠ r}) (f : C → ℝ) :
    (∑ v : {x : V // x ≠ r}, f (loopColor c r u v)) =
      ∑ v : {x : V // x ≠ (u : V)}, f (c u v) := by
  simp_rw [loopColor_rowEquiv]
  exact (rowEquiv r u).sum_comp (fun v => f (c u v))

theorem symmetric {V C : Type*} [DecidableEq V] (c : V → V → C)
    (h : ∀ u v, c u v = c v u) (r : V) :
    ∀ u v : {x : V // x ≠ r}, loopColor c r u v = loopColor c r v u := by
  intro u v
  by_cases huv : u = v
  · subst v; rfl
  · simp [loopColor, huv, Ne.symm huv, h]

/-- Deleting a vertex and using its incident color on each diagonal preserves
all restrictions on palettes of rainbow triangles, even with repeated indices. -/
theorem triangle_preserved {V C : Type*} [DecidableEq V] (c : V → V → C)
    (h : ∀ u v, c u v = c v u) (P : C → C → C → Prop)
    (hc : ∀ u v w, u ≠ v → v ≠ w → u ≠ w →
      c u v = c v w ∨ c v w = c u w ∨ c u v = c u w ∨ P (c u v) (c v w) (c u w))
    (r : V) (u v w : {x : V // x ≠ r}) :
    loopColor c r u v = loopColor c r v w ∨
    loopColor c r v w = loopColor c r u w ∨
    loopColor c r u v = loopColor c r u w ∨
    P (loopColor c r u v) (loopColor c r v w) (loopColor c r u w) := by
  by_cases huv : u = v
  · subst v; exact Or.inr (Or.inl rfl)
  by_cases hvw : v = w
  · subst w; exact Or.inr (Or.inr (Or.inl rfl))
  by_cases huw : u = w
  · subst w; exact Or.inl (symmetric c h r u v)
  simpa [loopColor, huv, hvw, huw] using
    hc u v w (fun e => huv (Subtype.ext e))
      (fun e => hvw (Subtype.ext e)) (fun e => huw (Subtype.ext e))

theorem balanced_rows {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (c : V → V → C) (t : ℕ)
    (hsize : Fintype.card V = Fintype.card C * t + 1)
    (hcard : ∀ u a,
      (Finset.univ.filter (fun v => v ≠ u ∧ c u v = a)).card = t)
    (r : V) (u : {x : V // x ≠ r}) (a : C) :
    (∑ v : {x : V // x ≠ r},
      ((if loopColor c r u v = a then (Fintype.card C : ℝ) else 0) - 1)) = 0 := by
  classical
  rw [row_sum c r u (fun b => (if b = a then (Fintype.card C : ℝ) else 0) - 1)]
  rw [← Finset.sum_subtype (p := fun v : V => v ≠ (u : V))
    (Finset.univ.filter (fun v : V => v ≠ (u : V))) (by simp)
    (fun v : V => (if c u v = a then (Fintype.card C : ℝ) else 0) - 1)]
  rw [Finset.sum_sub_distrib]
  have hcount : (Finset.univ.filter (fun v : V => v ≠ (u : V))).card =
      Fintype.card C * t := by
    have h := Fintype.card_subtype_compl (fun v : V => v = (u : V))
    rw [Fintype.card_subtype_eq] at h
    simpa [Fintype.card_subtype, hsize] using h
  simp [← Finset.sum_filter, Finset.filter_filter, hcard, hcount]
  ring

end ColeskiDeletedVertex
#print axioms ColeskiDeletedVertex.row_sum
#print axioms ColeskiDeletedVertex.triangle_preserved

#print axioms ColeskiDeletedVertex.balanced_rows

namespace ColeskiCertificateReduction
open ColeskiDeletedVertex ColeskiFiniteBalance
abbrev Positions (z : Fin 6) := {i : Fin 6 // i ≠ z}

theorem excludes_balanced_graph {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (P : Fin 6 → Fin 6 → Fin 6 → Prop)
    (weight : (z : Fin 6) → Positions z →
      (Positions z → Positions z → Fin 6) → Fin 6 → ℝ)
    (certificate : ∀ d : Fin 6 → Fin 6 → Fin 6,
      (∀ u v, d u v = d v u) →
      (∀ u v w, d u v = d v w ∨ d v w = d u w ∨ d u v = d u w ∨
        P (d u v) (d v w) (d u w)) →
      0 < ∑ z : Fin 6, ∑ v : Positions z, ∑ a : Fin 6,
        weight z v (fun i j => d i j) a * ((if d v z = a then (6 : ℝ) else 0) - 1))
    (t : ℕ) (hsize : Fintype.card V = 6*t+1)
    (c : V → V → Fin 6) (hsymm : ∀ u v, c u v = c v u)
    (hdegree : ∀ u a, (Finset.univ.filter (fun v => v ≠ u ∧ c u v = a)).card = t)
    (hpalettes : ∀ u v w, u ≠ v → v ≠ w → u ≠ w →
      c u v = c v w ∨ c v w = c u w ∨ c u v = c u w ∨
        P (c u v) (c v w) (c u w)) (r : V) : False := by
  classical
  let W := {v : V // v ≠ r}
  letI : Nonempty W := by
    obtain ⟨v,hv⟩ := exists_ne r
    exact ⟨⟨v,hv⟩⟩
  let d : W → W → Fin 6 := loopColor c r
  apply separator_obstruction d
    (fun z v rest a => weight z v (fun i j => d (rest i) (rest j)) a)
  · intro u a
    exact balanced_rows c t (by simpa using hsize) hdegree r u a
  · intro x
    have hsym : ∀ i j : Fin 6, d (x i) (x j) = d (x j) (x i) := by
      intro i j
      exact symmetric c hsymm r _ _
    have hgood : ∀ i j k : Fin 6,
        d (x i) (x j) = d (x j) (x k) ∨ d (x j) (x k) = d (x i) (x k) ∨
        d (x i) (x j) = d (x i) (x k) ∨
        P (d (x i) (x j)) (d (x j) (x k)) (d (x i) (x k)) := by
      intro i j k
      exact triangle_preserved c hsymm P hpalettes r _ _ _
    simpa using certificate (fun i j => d (x i) (x j)) hsym hgood
end ColeskiCertificateReduction
#print axioms ColeskiCertificateReduction.excludes_balanced_graph

/- END bundled local module CertificateReduction -/
