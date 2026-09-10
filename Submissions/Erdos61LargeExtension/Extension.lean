import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators

namespace Jig50.CopyCounting

/-- Count a labeled family of `k`-sets meeting every `r`-set by containment.
Different labels may have the same image. -/
theorem covering_choose_bound
    {β E : Type*} [Fintype β] [Fintype E] [DecidableEq β]
    (A : E → Finset β) (k r : ℕ)
    (hsize : ∀ e, (A e).card = k) (hkr : k ≤ r)
    (hcover : ∀ S : Finset β, S.card = r → ∃ e, A e ⊆ S) :
    (Fintype.card β).choose r ≤
      Fintype.card E * (Fintype.card β - k).choose (r - k) := by
  classical
  have hc : ((Finset.univ : Finset β).powersetCard r).card * 1 ≤
      (Finset.univ : Finset E).card *
        (Fintype.card β - k).choose (r - k) := by
    apply Finset.card_mul_le_card_mul (fun S e => A e ⊆ S)
    · intro S hS
      obtain ⟨e, he⟩ := hcover S (Finset.mem_powersetCard.mp hS).2
      apply Finset.one_le_card.mpr
      exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩⟩
    · intro e _
      change (((Finset.univ : Finset β).powersetCard r).filter
        (fun S => A e ⊆ S)).card ≤
          (Fintype.card β - k).choose (r - k)
      have he := Finset.card_filter_powersetCard_subset
        (A e) (Finset.univ : Finset β) r (Finset.subset_univ _)
        (by simpa only [hsize e] using hkr)
      simpa only [Finset.card_univ, hsize e] using he.le
  simpa only [Nat.mul_one, Finset.card_powersetCard, Finset.card_univ] using hc

/-- A division-free comparison of normalized falling factorials.
This also holds for `r < k`, when the left side vanishes. -/
theorem descFactorial_mul_pow_le {r n : ℕ} (hrn : r ≤ n) (k : ℕ) :
    r.descFactorial k * n ^ k ≤ n.descFactorial k * r ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hfactor : (r - k) * n ≤ (n - k) * r := by
      have hmul : k * r ≤ k * n := Nat.mul_le_mul_left k hrn
      rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm r n]
      exact Nat.sub_le_sub_left hmul (n * r)
    calc
      r.descFactorial (k + 1) * n ^ (k + 1)
          = ((r - k) * n) * (r.descFactorial k * n ^ k) := by
            rw [Nat.descFactorial_succ, pow_succ]
            ac_rfl
      _ ≤ ((n - k) * r) * (n.descFactorial k * r ^ k) :=
        Nat.mul_le_mul hfactor ih
      _ = n.descFactorial (k + 1) * r ^ (k + 1) := by
        rw [Nat.descFactorial_succ, pow_succ]
        ac_rfl

/-- The exact incidence bound forces a polynomial lower bound on the number
of labels. All cancellations have positive natural factors. -/
theorem power_bound_of_choose_bound {n r k e : ℕ}
    (hkr : k ≤ r) (hrn : r ≤ n)
    (hc : n.choose r ≤ e * (n - k).choose (r - k)) :
    n ^ k ≤ e * r ^ k := by
  have hB : 0 < (n - k).choose (r - k) :=
    Nat.choose_pos (Nat.sub_le_sub_right hrn k)
  have hchoose : n.choose k ≤ e * r.choose k := by
    refine Nat.le_of_mul_le_mul_right ?_ hB
    calc
      n.choose k * (n - k).choose (r - k)
          = n.choose r * r.choose k := (Nat.choose_mul (n := n) hkr).symm
      _ ≤ (e * (n - k).choose (r - k)) * r.choose k :=
        Nat.mul_le_mul_right (r.choose k) hc
      _ = (e * r.choose k) * (n - k).choose (r - k) := by ac_rfl
  have hdesc : n.descFactorial k ≤ e * r.descFactorial k := by
    calc
      n.descFactorial k = k.factorial * n.choose k :=
        Nat.descFactorial_eq_factorial_mul_choose n k
      _ ≤ k.factorial * (e * r.choose k) :=
        Nat.mul_le_mul_left k.factorial hchoose
      _ = e * r.descFactorial k := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        ac_rfl
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.descFactorial_pos.mpr hkr)
  calc
    r.descFactorial k * n ^ k ≤ n.descFactorial k * r ^ k :=
      descFactorial_mul_pow_le hrn k
    _ ≤ (e * r.descFactorial k) * r ^ k := Nat.mul_le_mul_right (r ^ k) hdesc
    _ = r.descFactorial k * (e * r ^ k) := by ac_rfl

-- A strict numerical case checks the direction of the two cross-multiplied terms.
example : (3 : ℕ).descFactorial 2 * 5 ^ 2 = 150 ∧
    (5 : ℕ).descFactorial 2 * 3 ^ 2 = 180 := by decide

end Jig50.CopyCounting

namespace Jig50.ExtensionVertices

open SimpleGraph

abbrev Away {α : Type*} (v : α) := {a : α // a ≠ v}

variable {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) (v : α)

def restrict (e : H ↪g G) : H.induce {a | a ≠ v} ↪g G :=
  e.comp (SimpleGraph.Embedding.induce {a | a ≠ v})

@[simp]
theorem restrict_apply (e : H ↪g G) (u : Away v) :
    restrict H G v e u = e u.val := rfl

/-- The new vertex avoids every anchor and has exactly the prescribed adjacency. -/
abbrev CanExtend (φ : H.induce {a | a ≠ v} ↪g G) (x : β) : Prop :=
  (∀ u : Away v, x ≠ φ u) ∧
  (∀ u : Away v, G.Adj x (φ u) ↔ H.Adj v u.val)

noncomputable def extend (φ : H.induce {a | a ≠ v} ↪g G)
    (x : β) (hx : CanExtend H G v φ x) : H ↪g G := by
  classical
  let f : α → β := fun a => if h : a = v then x else φ ⟨a, h⟩
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro a b hab
    by_cases ha : a = v
    · subst a
      by_cases hb : b = v
      · exact hb.symm
      · have hbad : x = φ ⟨b, hb⟩ := by simpa [f, hb] using hab
        exact False.elim (hx.1 ⟨b, hb⟩ hbad)
    · by_cases hb : b = v
      · subst b
        have hbad : φ ⟨a, ha⟩ = x := by simpa [f, ha] using hab
        exact False.elim (hx.1 ⟨a, ha⟩ hbad.symm)
      · have hφ : φ ⟨a, ha⟩ = φ ⟨b, hb⟩ := by simpa [f, ha, hb] using hab
        exact congrArg Subtype.val (φ.injective hφ)
  · intro a b
    change G.Adj (f a) (f b) ↔ H.Adj a b
    by_cases ha : a = v
    · subst a
      by_cases hb : b = v
      · subst b
        simp [f]
      · simpa [f, hb] using hx.2 ⟨b, hb⟩
    · by_cases hb : b = v
      · subst b
        have hp : G.Adj (φ ⟨a, ha⟩) x ↔ H.Adj a v :=
          (G.adj_comm _ _).trans ((hx.2 ⟨a, ha⟩).trans (H.adj_comm _ _))
        simpa [f, ha] using hp
      · have hp : G.Adj (φ ⟨a, ha⟩) (φ ⟨b, hb⟩) ↔ H.Adj a b :=
          φ.map_adj_iff
        simpa [f, ha, hb] using hp

@[simp]
theorem extend_apply_self (φ : H.induce {a | a ≠ v} ↪g G)
    (x : β) (hx : CanExtend H G v φ x) : extend H G v φ x hx v = x := by
  classical
  simp [extend]

@[simp]
theorem extend_apply_of_ne (φ : H.induce {a | a ≠ v} ↪g G)
    (x : β) (hx : CanExtend H G v φ x) {a : α} (ha : a ≠ v) :
    extend H G v φ x hx a = φ ⟨a, ha⟩ := by
  classical
  simp [extend, ha]

theorem restrict_extend (φ : H.induce {a | a ≠ v} ↪g G)
    (x : β) (hx : CanExtend H G v φ x) :
    restrict H G v (extend H G v φ x hx) = φ := by
  apply DFunLike.ext
  intro u
  change extend H G v φ x hx u.val = φ u
  exact extend_apply_of_ne H G v φ x hx u.property

theorem canExtend_of_restrict_eq (φ : H.induce {a | a ≠ v} ↪g G)
    (e : H ↪g G) (he : restrict H G v e = φ) :
    CanExtend H G v φ (e v) := by
  have hu : ∀ u : Away v, e u.val = φ u := by
    intro u
    exact congrArg (fun ψ : H.induce {a | a ≠ v} ↪g G => ψ u) he
  constructor
  · intro u h
    have hv : e v = e u.val := h.trans (hu u).symm
    exact u.property (e.injective hv).symm
  · intro u
    rw [← hu u]
    exact e.map_adj_iff

noncomputable def extensions [Fintype β]
    (φ : H.induce {a | a ≠ v} ↪g G) : Finset β := by
  classical
  exact Finset.univ.filter (CanExtend H G v φ)

@[simp]
theorem mem_extensions [Fintype β] (φ : H.induce {a | a ≠ v} ↪g G) (x : β) :
    x ∈ extensions H G v φ ↔ CanExtend H G v φ x := by
  classical
  simp [extensions]

/-- A full induced embedding with fixed restriction is determined exactly by its new vertex. -/
noncomputable def fiberEquiv [Fintype β]
    (φ : H.induce {a | a ≠ v} ↪g G) :
    {e : H ↪g G // restrict H G v e = φ} ≃ ↥(extensions H G v φ) where
  toFun e := ⟨e.val v, (mem_extensions H G v φ _).mpr
    (canExtend_of_restrict_eq H G v φ e.val e.property)⟩
  invFun x := ⟨extend H G v φ x.val ((mem_extensions H G v φ _).mp x.property),
    restrict_extend H G v φ x.val ((mem_extensions H G v φ _).mp x.property)⟩
  left_inv e := by
    classical
    apply Subtype.ext
    apply DFunLike.ext
    intro a
    let hx := canExtend_of_restrict_eq H G v φ e.val e.property
    change extend H G v φ (e.val v) hx a = e.val a
    by_cases ha : a = v
    · subst a
      exact extend_apply_self H G v φ (e.val v) hx
    · rw [extend_apply_of_ne H G v φ (e.val v) hx ha]
      exact (congrArg (fun ψ : H.induce {a | a ≠ v} ↪g G => ψ ⟨a, ha⟩)
        e.property).symm
  right_inv x := by
    apply Subtype.ext
    let hx := (mem_extensions H G v φ x.val).mp x.property
    change extend H G v φ x.val hx v = x.val
    exact extend_apply_self H G v φ x.val hx

theorem card_restriction_fiber [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (φ : H.induce {a | a ≠ v} ↪g G) :
    Fintype.card {e : H ↪g G // restrict H G v e = φ} =
      (extensions H G v φ).card := by
  classical
  exact (Fintype.card_congr (fiberEquiv H G v φ)).trans (Fintype.card_coe _)

/-- An anchor is never a valid new vertex, including when it is isolated. -/
theorem anchor_not_mem_extensions [Fintype β]
    (φ : H.induce {a | a ≠ v} ↪g G) (u : Away v) :
    φ u ∉ extensions H G v φ := by
  intro h
  exact ((mem_extensions H G v φ _).mp h).1 u rfl

/-- For a one-vertex forbidden graph, there are no anchors and every host vertex extends. -/
theorem extensions_eq_univ_of_subsingleton [Subsingleton α] [Fintype β]
    (φ : H.induce {a | a ≠ v} ↪g G) : extensions H G v φ = Finset.univ := by
  classical
  apply Finset.ext
  intro x
  simp only [mem_extensions, Finset.mem_univ, iff_true]
  constructor <;> intro u <;>
    exact False.elim (u.property (Subsingleton.elim u.val v))

end Jig50.ExtensionVertices

namespace Jig50.LargeExtension

open SimpleGraph
open Jig50.ExtensionVertices

/-- If every `r`-vertex set contains an induced copy, there are polynomially
many labeled induced embeddings. Labels may have the same vertex image. -/
theorem labeled_copy_power_bound
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (H : SimpleGraph α) (G : SimpleGraph β) (r : ℕ)
    (hkr : Fintype.card α ≤ r) (hrn : r ≤ Fintype.card β)
    (hcover : ∀ S : Finset β, S.card = r →
      ∃ e : H ↪g G, ∀ a : α, e a ∈ S) :
    (Fintype.card β) ^ Fintype.card α ≤
      Fintype.card (H ↪g G) * r ^ Fintype.card α := by
  classical
  have hc := Jig50.CopyCounting.covering_choose_bound
    (fun e : H ↪g G => (Finset.univ : Finset α).map e.toEmbedding)
    (Fintype.card α) r (fun _ => by simp) hkr (by
      intro S hS
      obtain ⟨e, he⟩ := hcover S hS
      refine ⟨e, ?_⟩
      intro b hb
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hb
      exact he a)
  exact Jig50.CopyCounting.power_bound_of_choose_bound hkr hrn hc

/-- Some fixed embedding away from `v` has at least `|β| / r^|α|`
extension vertices, expressed without division or rounding. -/
theorem exists_large_extension
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (H : SimpleGraph α) (G : SimpleGraph β) (v : α) (r : ℕ)
    (hkr : Fintype.card α ≤ r) (hrn : r ≤ Fintype.card β)
    (hcover : ∀ S : Finset β, S.card = r →
      ∃ e : H ↪g G, ∀ a : α, e a ∈ S) :
    ∃ φ : H.induce {a | a ≠ v} ↪g G,
      Fintype.card β ≤ (extensions H G v φ).card * r ^ Fintype.card α := by
  classical
  let E := H ↪g G
  let F := H.induce {a | a ≠ v} ↪g G
  have hcopy : (Fintype.card β) ^ Fintype.card α ≤
      Fintype.card E * r ^ Fintype.card α :=
    labeled_copy_power_bound H G r hkr hrn hcover
  have hsets : ((Finset.univ : Finset β).powersetCard r).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa only [Finset.card_univ] using hrn)
  obtain ⟨S, hS⟩ := hsets
  obtain ⟨e₀, _⟩ := hcover S (Finset.mem_powersetCard.mp hS).2
  have hF : (Finset.univ : Finset F).Nonempty :=
    ⟨restrict H G v e₀, Finset.mem_univ _⟩
  obtain ⟨φ, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset F)
    (fun ψ => (extensions H G v ψ).card) hF
  have hfiber (ψ : F) :
      ((Finset.univ : Finset E).filter (fun e => restrict H G v e = ψ)).card =
        (extensions H G v ψ).card :=
    (Fintype.card_subtype (fun e : E => restrict H G v e = ψ)).symm.trans
      (card_restriction_fiber H G v ψ)
  have hcount : (Finset.univ : Finset E).card * 1 ≤
      (Finset.univ : Finset F).card * (extensions H G v φ).card := by
    apply Finset.card_mul_le_card_mul (fun e ψ => restrict H G v e = ψ)
    · intro e _
      apply Finset.one_le_card.mpr
      exact ⟨restrict H G v e,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · intro ψ hψ
      change ((Finset.univ : Finset E).filter
        (fun e => restrict H G v e = ψ)).card ≤ (extensions H G v φ).card
      rw [hfiber ψ]
      exact hmax ψ hψ
  have hEbound : Fintype.card E ≤ Fintype.card F * (extensions H G v φ).card := by
    simpa only [Finset.card_univ, Nat.mul_one] using hcount
  have hAway : Fintype.card (Away v) = Fintype.card α - 1 := by
    simpa only [Away, Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun a : α => a = v)
  have hFbound : Fintype.card F ≤ (Fintype.card β) ^ (Fintype.card α - 1) := by
    calc
      Fintype.card F ≤ Fintype.card (Away v → β) :=
        Fintype.card_le_of_injective (fun ψ : F => (ψ : Away v → β))
          DFunLike.coe_injective
      _ = (Fintype.card β) ^ (Fintype.card α - 1) := by
        rw [Fintype.card_fun, hAway]
  have hkpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨v⟩
  have hnpos : 0 < Fintype.card β := lt_of_lt_of_le hkpos (hkr.trans hrn)
  have hk : Fintype.card α - 1 + 1 = Fintype.card α :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
  refine ⟨φ, Nat.le_of_mul_le_mul_left
    (c := (Fintype.card β) ^ (Fintype.card α - 1)) ?_ (Nat.pow_pos hnpos)⟩
  calc
    (Fintype.card β) ^ (Fintype.card α - 1) * Fintype.card β
        = (Fintype.card β) ^ Fintype.card α := by
          rw [← pow_succ, hk]
    _ ≤ Fintype.card E * r ^ Fintype.card α := hcopy
    _ ≤ (Fintype.card F * (extensions H G v φ).card) * r ^ Fintype.card α :=
      Nat.mul_le_mul_right (r ^ Fintype.card α) hEbound
    _ ≤ ((Fintype.card β) ^ (Fintype.card α - 1) * (extensions H G v φ).card) *
        r ^ Fintype.card α :=
      Nat.mul_le_mul_right (r ^ Fintype.card α)
        (Nat.mul_le_mul_right (extensions H G v φ).card hFbound)
    _ = (Fintype.card β) ^ (Fintype.card α - 1) *
        ((extensions H G v φ).card * r ^ Fintype.card α) := by ac_rfl

end Jig50.LargeExtension

namespace Submissions.Erdos61LargeExtension.Extension

open SimpleGraph

theorem proof
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H : SimpleGraph α) (G : SimpleGraph β) (v : α) (r : ℕ)
    (hkr : Fintype.card α ≤ r) (hrn : r ≤ Fintype.card β)
    (hcover : ∀ S : Finset β, S.card = r →
      ∃ e : H ↪g G, ∀ a : α, e a ∈ S) :
    ∃ φ : H.induce {a | a ≠ v} ↪g G,
      Fintype.card β ≤ (Jig50.ExtensionVertices.extensions H G v φ).card *
        r ^ Fintype.card α :=
  Jig50.LargeExtension.exists_large_extension H G v r hkr hrn hcover

end Submissions.Erdos61LargeExtension.Extension
