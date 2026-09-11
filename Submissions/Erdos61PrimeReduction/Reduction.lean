import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum

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

namespace Jig50.HomogeneousTransport

open SimpleGraph

universe u v w

noncomputable abbrev hom {α : Type*} (G : SimpleGraph α) : ℕ :=
  max G.indepNum G.cliqueNum

/-- Induced embeddings preserve clique cardinalities. Only the target must be finite. -/
theorem cliqueNum_mono {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}
    [Finite β] (e : G ↪g G') : G.cliqueNum ≤ G'.cliqueNum := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hmap : G.map e.toEmbedding ≤ G' :=
    (SimpleGraph.map_le_iff_le_comap e.toEmbedding G G').2 e.toHom.le_comap
  have ht : G'.IsNClique G.cliqueNum (s.map e.toEmbedding) :=
    SimpleGraph.IsNClique.mono hmap (hs.map (f := e.toEmbedding))
  exact ht.card_eq ▸ ht.isClique.card_le_cliqueNum

theorem indepNum_mono {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}
    [Finite β] (e : G ↪g G') : G.indepNum ≤ G'.indepNum := by
  simpa only [SimpleGraph.cliqueNum_compl] using
    cliqueNum_mono (SimpleGraph.Embedding.complEquiv e)

theorem hom_mono {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}
    [Finite β] (e : G ↪g G') : hom G ≤ hom G' :=
  max_le_max (indepNum_mono e) (cliqueNum_mono e)

theorem hom_iso {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}
    [Finite α] [Finite β] (e : G ≃g G') : hom G = hom G' :=
  le_antisymm (hom_mono e.toEmbedding) (hom_mono e.symm.toEmbedding)

theorem hom_induce_le {β : Type*} [Finite β] (G : SimpleGraph β) (s : Set β) :
    hom (G.induce s) ≤ hom G :=
  hom_mono (SimpleGraph.Embedding.induce s)

theorem hom_induce_finset_le {β : Type*} [Finite β]
    (G : SimpleGraph β) (s : Finset β) :
    hom (G.induce (s : Set β)) ≤ hom G :=
  hom_induce_le G (s : Set β)

/-- Any two distinct host vertices form a clique or an independent set. -/
theorem two_le_hom {β : Type*} [Fintype β] (G : SimpleGraph β)
    (hβ : 2 ≤ Fintype.card β) : 2 ≤ hom G := by
  classical
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (Nat.lt_of_succ_le hβ)
  by_cases h : G.Adj a b
  · have hc : G.IsClique (↑({a, b} : Finset β) : Set β) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, isClique_pair] using
        (fun _ : a ≠ b => h)
    have hb := hc.card_le_cliqueNum
    simp only [Finset.card_pair hab] at hb
    exact hb.trans (le_max_right _ _)
  · have hc : Gᶜ.IsClique (↑({a, b} : Finset β) : Set β) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, isClique_pair] using
        (fun _ : a ≠ b => show Gᶜ.Adj a b from ⟨hab, h⟩)
    have hb := hc.card_le_cliqueNum
    simp only [Finset.card_pair hab, cliqueNum_compl] at hb
    exact hb.trans (le_max_left _ _)

/-- The canonical injective-comap exclusion is exactly absence of an induced embedding. -/
theorem nonempty_embedding_iff {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) :
    Nonempty (H ↪g G) ↔ ∃ f : α ↪ β, H = G.comap f := by
  change SimpleGraph.IsIndContained H G ↔ _
  exact (SimpleGraph.isIndContained_iff_exists_comap_eq (H := H) (G := G)).trans
    (exists_congr fun _ => eq_comm)

/-- A strict integer-power bound on every finite induced-H-free host of order at least two.
The positive-exponent requirement is separate: use `∃ k, 0 < k ∧ EHBound H k`. -/
def EHBound {α : Type u} (H : SimpleGraph α) (k : ℕ) : Prop :=
  ∀ {β : Type v} [Fintype β] [DecidableEq β] (G : SimpleGraph β),
    2 ≤ Fintype.card β → (¬Nonempty (H ↪g G)) →
      Fintype.card β < (max G.indepNum G.cliqueNum) ^ k

/-- Finite relabeling preserves the canonical bound, at every host universe.
The forward direction uses ULift so it does not accidentally specialize the host universe. -/
theorem ehBound_iff_fin {α : Type u} (H : SimpleGraph α) (k : ℕ) :
    EHBound.{u, v} H k ↔
      ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n),
        (¬∃ f : α ↪ Fin n, H = G.comap f) →
          n < (max G.indepNum G.cliqueNum) ^ k := by
  classical
  constructor
  · intro h n hn G hfree
    let G' : SimpleGraph (ULift.{v} (Fin n)) := G.comap ULift.down
    let e : G' ≃g G := SimpleGraph.Iso.comap Equiv.ulift G
    have hfree' : ¬Nonempty (H ↪g G') := by
      rintro ⟨f⟩
      exact hfree ((nonempty_embedding_iff H G).1 ⟨e.toEmbedding.comp f⟩)
    have h' : Fintype.card (ULift.{v} (Fin n)) < hom G' ^ k :=
      h G' (by simpa only [Fintype.card_ulift, Fintype.card_fin] using hn) hfree'
    have hb : n < hom G' ^ k := by
      simpa only [Fintype.card_ulift, Fintype.card_fin] using h'
    exact hb.trans_le (Nat.pow_le_pow_left (hom_mono e.toEmbedding) k)
  · intro h β _ _ G hβ hfree
    let G' : SimpleGraph (Fin (Fintype.card β)) := G.overFin rfl
    let e : G ≃g G' := G.overFinIso rfl
    have hfree' : ¬∃ f : α ↪ Fin (Fintype.card β), H = G'.comap f := by
      intro hf
      obtain ⟨f⟩ := (nonempty_embedding_iff H G').2 hf
      exact hfree ⟨e.symm.toEmbedding.comp f⟩
    have hb : Fintype.card β < hom G' ^ k := h (Fintype.card β) hβ G' hfree'
    exact hb.trans_le (Nat.pow_le_pow_left (hom_mono e.symm.toEmbedding) k)

/-- A bound on an induced finite vertex set may be weakened to the ambient homogeneous number. -/
theorem EHBound.card_finset_lt {α : Type u} {β : Type v}
    [Fintype β] [DecidableEq β] {H : SimpleGraph α} {k : ℕ}
    (h : EHBound.{u, v} H k) (G : SimpleGraph β) (s : Finset β)
    (hs : 2 ≤ s.card) (hfree : ¬Nonempty (H ↪g G.induce (s : Set β))) :
    s.card < hom G ^ k := by
  have hb : Fintype.card s < hom (G.induce (s : Set β)) ^ k :=
    h (G.induce (s : Set β))
      (by rw [show Fintype.card (s : Set β) = s.card from Fintype.card_coe s]; exact hs) hfree
  have hb' : s.card < hom (G.induce (s : Set β)) ^ k := by
    simpa only [Fintype.card_coe] using hb
  exact hb'.trans_le (Nat.pow_le_pow_left (hom_induce_finset_le G s) k)

-- The two-vertex case is valid for both adjacency choices; no exclusion hypothesis is needed.
example (G : SimpleGraph (Fin 2)) : 2 ≤ hom G :=
  two_le_hom G (by decide)

end Jig50.HomogeneousTransport

namespace Jig50.SubstitutionGraph

open SimpleGraph
open Jig50.ExtensionVertices

variable {α β δ : Type*}

/-- Replace `v` in `H₁` by `H₂`. Every inserted vertex has the former
neighbourhood of `v` among the surviving vertices of `H₁`. -/
def replacement (H₁ : SimpleGraph α) (H₂ : SimpleGraph δ) (v : α) :
    SimpleGraph (Away v ⊕ δ) where
  Adj
    | .inl u, .inl w => H₁.Adj u.val w.val
    | .inl u, .inr _ => H₁.Adj v u.val
    | .inr _, .inl u => H₁.Adj v u.val
    | .inr x, .inr y => H₂.Adj x y
  symm.symm
    | .inl _, .inl _ => H₁.adj_symm
    | .inl _, .inr _ => id
    | .inr _, .inl _ => id
    | .inr _, .inr _ => H₂.adj_symm
  loopless.irrefl
    | .inl _ => H₁.irrefl
    | .inr _ => H₂.irrefl

variable (H₁ : SimpleGraph α) (H₂ : SimpleGraph δ) (v : α)

@[simp]
theorem replacement_adj_inl (u w : Away v) :
    (replacement H₁ H₂ v).Adj (.inl u) (.inl w) ↔ H₁.Adj u.val w.val := Iff.rfl

@[simp]
theorem replacement_adj_inr (x y : δ) :
    (replacement H₁ H₂ v).Adj (.inr x) (.inr y) ↔ H₂.Adj x y := Iff.rfl

@[simp]
theorem replacement_adj_inl_inr (u : Away v) (x : δ) :
    (replacement H₁ H₂ v).Adj (.inl u) (.inr x) ↔ H₁.Adj v u.val := Iff.rfl

@[simp]
theorem replacement_adj_inr_inl (x : δ) (u : Away v) :
    (replacement H₁ H₂ v).Adj (.inr x) (.inl u) ↔ H₁.Adj v u.val := Iff.rfl

variable (G : SimpleGraph β) [Fintype β]

/-- Glue the fixed anchors to an induced `H₂` inside their extension set.
Range avoidance prevents collisions, and the extension equivalence preserves
both edges and nonedges across the two parts. -/
def glue
    (φ : H₁.induce {u | u ≠ v} ↪g G)
    (ψ : H₂ ↪g G.induce (extensions H₁ G v φ : Set β)) :
    replacement H₁ H₂ v ↪g G where
  toFun := Sum.elim (fun u => φ u) (fun x => (ψ x).val)
  inj' := by
    rintro (u | x) (w | y) h
    · exact congrArg Sum.inl (φ.injective h)
    · have hy := (mem_extensions H₁ G v φ (ψ y).val).mp (ψ y).property
      exact False.elim (hy.1 u h.symm)
    · have hx := (mem_extensions H₁ G v φ (ψ x).val).mp (ψ x).property
      exact False.elim (hx.1 w h)
    · exact congrArg Sum.inr (ψ.injective (Subtype.ext h))
  map_rel_iff' := by
    rintro (u | x) (w | y)
    · exact φ.map_adj_iff
    · have hy := (mem_extensions H₁ G v φ (ψ y).val).mp (ψ y).property
      exact (G.adj_comm _ _).trans (hy.2 u)
    · have hx := (mem_extensions H₁ G v φ (ψ x).val).mp (ψ x).property
      exact hx.2 w
    · exact ψ.map_adj_iff

@[simp]
theorem glue_inl
    (φ : H₁.induce {u | u ≠ v} ↪g G)
    (ψ : H₂ ↪g G.induce (extensions H₁ G v φ : Set β)) (u : Away v) :
    glue H₁ H₂ v G φ ψ (.inl u) = φ u := rfl

@[simp]
theorem glue_inr
    (φ : H₁.induce {u | u ≠ v} ↪g G)
    (ψ : H₂ ↪g G.induce (extensions H₁ G v φ : Set β)) (x : δ) :
    glue H₁ H₂ v G φ ψ (.inr x) = (ψ x).val := rfl

end Jig50.SubstitutionGraph

namespace Jig50.SubstitutionBound

open SimpleGraph
open Jig50.ExtensionVertices Jig50.SubstitutionGraph Jig50.HomogeneousTransport

universe u v w

/-- Quantitative substitution closure, using the actual induced-copy extension lemma. -/
theorem ehBound_replacement
    {α : Type u} {δ : Type w} [Fintype α] [Fintype δ]
    (H₁ : SimpleGraph α) (H₂ : SimpleGraph δ) (v₀ : α)
    {k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (h₁ : EHBound.{u, v} H₁ k₁) (h₂ : EHBound.{w, v} H₂ k₂) :
    EHBound.{max u w, v} (replacement H₁ H₂ v₀) (Fintype.card α * k₁ + k₂) := by
  classical
  intro β _ _ G hn hfree
  let m := max G.indepNum G.cliqueNum
  let r := m ^ k₁
  have hm₂ : 2 ≤ m := two_le_hom G hn
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm₂
  have hpow (k : ℕ) (hk : 0 < k) : m ≤ m ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right hmpos (Nat.succ_le_of_lt hk)
  have hr₂ : 2 ≤ r := hm₂.trans (hpow k₁ hk₁)
  have hα : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨v₀⟩
  have hK : k₁ ≤ Fintype.card α * k₁ + k₂ := by
    have := Nat.mul_le_mul_right k₁ (Nat.succ_le_of_lt hα)
    omega
  by_contra hsmall
  have hlarge : m ^ (Fintype.card α * k₁ + k₂) ≤ Fintype.card β :=
    Nat.le_of_not_gt hsmall
  have hrn : r ≤ Fintype.card β :=
    (Nat.pow_le_pow_right hmpos hK).trans hlarge
  have hcontains (S : Finset β) (hS : S.card = r) :
      Nonempty (H₁ ↪g G.induce (S : Set β)) := by
    by_contra hf
    have hb := h₁.card_finset_lt G S (by simpa only [hS] using hr₂) hf
    exact (Nat.lt_irrefl r) (by simpa only [hS] using hb)
  obtain ⟨S₀, hS₀⟩ := Finset.powersetCard_nonempty.mpr
    (show r ≤ (Finset.univ : Finset β).card by simpa only [Finset.card_univ] using hrn)
  have hS₀card : S₀.card = r := (Finset.mem_powersetCard.mp hS₀).2
  obtain ⟨e₀⟩ := hcontains S₀ hS₀card
  have hkr : Fintype.card α ≤ r := by
    have hc : Fintype.card (S₀ : Set β) = S₀.card := Fintype.card_coe S₀
    have he := Fintype.card_le_of_injective e₀ e₀.injective
    rwa [hc, hS₀card] at he
  have hcover : ∀ S : Finset β, S.card = r →
      ∃ e : H₁ ↪g G, ∀ a : α, e a ∈ S := by
    intro S hS
    obtain ⟨e⟩ := hcontains S hS
    refine ⟨(SimpleGraph.Embedding.induce (S : Set β)).comp e, ?_⟩
    intro a
    exact (e a).property
  obtain ⟨φ, hφ⟩ := Jig50.LargeExtension.exists_large_extension H₁ G v₀ r hkr hrn hcover
  let T := extensions H₁ G v₀ φ
  have ht : m ^ k₂ ≤ T.card := by
    refine Nat.le_of_mul_le_mul_right
      (c := r ^ Fintype.card α) ?_ (Nat.pow_pos (Nat.pow_pos hmpos))
    calc
      m ^ k₂ * r ^ Fintype.card α = m ^ (Fintype.card α * k₁ + k₂) := by
        dsimp [r]
        rw [Nat.mul_comm (Fintype.card α) k₁, pow_add, pow_mul]
        ac_rfl
      _ ≤ Fintype.card β := hlarge
      _ ≤ T.card * r ^ Fintype.card α := hφ
  have hT₂ : 2 ≤ T.card := (hm₂.trans (hpow k₂ hk₂)).trans ht
  obtain ⟨ψ⟩ : Nonempty (H₂ ↪g G.induce (T : Set β)) := by
    by_contra hf
    exact (Nat.not_lt_of_ge ht) (h₂.card_finset_lt G T hT₂ hf)
  exact hfree ⟨glue H₁ H₂ v₀ G φ ψ⟩

end Jig50.SubstitutionBound

namespace Submissions.Erdos61UniformExponent.Uniform

open Filter SimpleGraph Real

def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) →
      G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

def HasErdosHajnalProperty {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

lemma homogeneous_pair {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) :
    2 ≤ max G.indepNum G.cliqueNum := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  by_cases h : G.Adj a b
  · have hc : G.IsClique (↑({a, b} : Finset (Fin n)) : Set (Fin n)) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, isClique_pair] using
        (fun _ : a ≠ b => h)
    have hb := hc.card_le_cliqueNum
    simp only [Finset.card_pair hab] at hb
    exact hb.trans (le_max_right _ _)
  · have hc : Gᶜ.IsClique (↑({a, b} : Finset (Fin n)) : Set (Fin n)) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, isClique_pair] using
        (fun _ : a ≠ b => show Gᶜ.Adj a b from ⟨hab, h⟩)
    have hb := hc.card_le_cliqueNum
    simp only [Finset.card_pair hab, cliqueNum_compl] at hb
    exact hb.trans (le_max_left _ _)

/-- An eventual positive real power bound can be normalized to a strict integer
power bound at every host size at least two. -/
theorem proof {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α) :
    HasErdosHajnalProperty H ↔
      ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n),
        (¬∃ g : α ↪ Fin n, H = G.comap g) →
          n < (max G.indepNum G.cliqueNum) ^ k := by
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 he
    obtain ⟨k, hk⟩ := exists_nat_gt (max (N : ℝ) c⁻¹)
    have hNk : N < k := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hk)
    have hck : c⁻¹ < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
    have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le N) hNk
    refine ⟨k, hk0, fun n hn G hfree => ?_⟩
    by_cases hnN : N ≤ n
    · have hp : (n : ℝ) ^ c ≤ (max G.indepNum G.cliqueNum : ℕ) := by
        rcases hN n hnN G hfree with hi | hw
        · exact hi.trans (by exact_mod_cast le_max_left G.indepNum G.cliqueNum)
        · exact hw.trans (by exact_mod_cast le_max_right G.indepNum G.cliqueNum)
      have hprod : 1 < c * (k : ℝ) := by
        have hmul := mul_lt_mul_of_pos_left hck hc
        simpa [mul_inv_cancel₀ hc.ne'] using hmul
      have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      have hstrict : (n : ℝ) < ((max G.indepNum G.cliqueNum : ℕ) : ℝ) ^ k := by
        calc
          (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
          _ < (n : ℝ) ^ (c * (k : ℝ)) := rpow_lt_rpow_of_exponent_lt hn1 hprod
          _ = ((n : ℝ) ^ c) ^ k := rpow_mul_natCast (Nat.cast_nonneg n) c k
          _ ≤ ((max G.indepNum G.cliqueNum : ℕ) : ℝ) ^ k :=
            pow_le_pow_left₀ (rpow_nonneg (Nat.cast_nonneg n) c) hp k
      exact_mod_cast hstrict
    · calc
        n < k := (Nat.lt_of_not_ge hnN).trans hNk
        _ < 2 ^ k := Nat.lt_two_pow_self
        _ ≤ (max G.indepNum G.cliqueNum) ^ k :=
          Nat.pow_le_pow_left (homogeneous_pair hn G) k
  · rintro ⟨k, hk, hall⟩
    refine ⟨(k : ℝ)⁻¹, inv_pos.2 (by exact_mod_cast hk), ?_⟩
    apply eventually_atTop.2
    refine ⟨2, fun n hn G hfree => ?_⟩
    have hb : (n : ℝ) ≤ ((max G.indepNum G.cliqueNum : ℕ) : ℝ) ^ (k : ℝ) := by
      rw [rpow_natCast]
      exact_mod_cast (hall n hn G hfree).le
    have hp := (rpow_inv_le_iff_of_pos (Nat.cast_nonneg n)
      (Nat.cast_nonneg (max G.indepNum G.cliqueNum))
      (show 0 < (k : ℝ) by exact_mod_cast hk)).2 hb
    simpa only [Nat.cast_max, le_max_iff] using hp


end Submissions.Erdos61UniformExponent.Uniform

namespace Submissions.Erdos61Substitution.Closure

open SimpleGraph Jig50.SubstitutionGraph Jig50.HomogeneousTransport
open Submissions.Erdos61UniformExponent.Uniform

universe u w

/-- The original eventual positive-real-exponent EH property is closed under substitution. -/
theorem proof {α : Type u} {δ : Type w}
    [Fintype α] [Fintype δ] [DecidableEq α] [DecidableEq δ]
    (H₁ : SimpleGraph α) (H₂ : SimpleGraph δ) (v₀ : α) :
    HasErdosHajnalProperty H₁ → HasErdosHajnalProperty H₂ →
      HasErdosHajnalProperty (replacement H₁ H₂ v₀) := by
  classical
  intro h₁ h₂
  obtain ⟨k₁, hk₁, hb₁⟩ := (Submissions.Erdos61UniformExponent.Uniform.proof H₁).mp h₁
  obtain ⟨k₂, hk₂, hb₂⟩ := (Submissions.Erdos61UniformExponent.Uniform.proof H₂).mp h₂
  have b₁ : EHBound.{u, 0} H₁ k₁ := (ehBound_iff_fin H₁ k₁).mpr hb₁
  have b₂ : EHBound.{w, 0} H₂ k₂ := (ehBound_iff_fin H₂ k₂).mpr hb₂
  have b : EHBound.{max u w, 0} (replacement H₁ H₂ v₀)
      (Fintype.card α * k₁ + k₂) :=
    Jig50.SubstitutionBound.ehBound_replacement H₁ H₂ v₀ hk₁ hk₂ b₁ b₂
  apply (Submissions.Erdos61UniformExponent.Uniform.proof (replacement H₁ H₂ v₀)).mpr
  exact ⟨Fintype.card α * k₁ + k₂, by omega,
    (ehBound_iff_fin (replacement H₁ H₂ v₀) _).mp b⟩

end Submissions.Erdos61Substitution.Closure

namespace Jig50.ModuleDecomposition

open SimpleGraph
open Jig50.ExtensionVertices Jig50.SubstitutionGraph

variable {α : Type*}

/-- Every outside vertex has the same adjacency to all vertices of a module. -/
def IsModule (H : SimpleGraph α) (S : Set α) : Prop :=
  ∀ x, x ∉ S → ∀ a, a ∈ S → ∀ b, b ∈ S → (H.Adj x a ↔ H.Adj x b)

/-- The vertices outside `S`, together with the chosen representative. -/
abbrev collapsedVertices (S : Set α) (v : α) : Set α :=
  {x | x ∉ S ∨ x = v}

abbrev representative (S : Set α) (v : α) : collapsedVertices S v :=
  ⟨v, Or.inr rfl⟩

theorem outside_of_away (S : Set α) (v : α)
    (u : Away (representative S v)) : u.val.val ∉ S := by
  rcases u.val.property with hu | hu
  · exact hu
  · exact False.elim (u.property (Subtype.ext hu))

/-- Expanding the representative of a module recovers the original graph.
The left part maps to the outside vertices, and the inserted part maps to `S`. -/
noncomputable def moduleIso (H : SimpleGraph α) (S : Set α) (v : α)
    (hv : v ∈ S) (hS : IsModule H S) :
    replacement (H.induce (collapsedVertices S v)) (H.induce S)
      (representative S v) ≃g H := by
  classical
  let f : Away (representative S v) ⊕ S → α :=
    Sum.elim (fun u => u.val.val) (fun x => x.val)
  have hinj : Function.Injective f := by
    rintro (u | x) (w | y) h
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
    · change u.val.val = y.val at h
      exact False.elim (outside_of_away S v u (h.symm ▸ y.property))
    · change x.val = w.val.val at h
      exact False.elim (outside_of_away S v w (h ▸ x.property))
    · exact congrArg Sum.inr (Subtype.ext h)
  have hsurj : Function.Surjective f := by
    intro a
    by_cases ha : a ∈ S
    · exact ⟨.inr ⟨a, ha⟩, rfl⟩
    · let b : collapsedVertices S v := ⟨a, Or.inl ha⟩
      have hb : b ≠ representative S v := by
        intro h
        have hav : a = v := congrArg Subtype.val h
        exact ha (hav.symm ▸ hv)
      exact ⟨.inl ⟨b, hb⟩, rfl⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  rintro (u | x) (w | y)
  · exact Iff.rfl
  · change H.Adj u.val.val y.val ↔ H.Adj v u.val.val
    exact (hS u.val.val (outside_of_away S v u) y.val y.property v hv).trans
      (H.adj_comm u.val.val v)
  · change H.Adj x.val w.val.val ↔ H.Adj v w.val.val
    exact (H.adj_comm x.val w.val.val).trans
      ((hS w.val.val (outside_of_away S v w) x.val x.property v hv).trans
        (H.adj_comm w.val.val v))
  · exact Iff.rfl

/-- A nontrivial module removes at least one vertex when collapsed. -/
theorem card_collapsed_lt [Fintype α] [DecidableEq α]
    (S : Finset α) (v : α) (hS : 1 < S.card) :
    Fintype.card (collapsedVertices (S : Set α) v) < Fintype.card α := by
  classical
  obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne hS v
  apply Fintype.card_subtype_lt (x := w)
  change ¬(w ∉ (S : Set α) ∨ w = v)
  rintro (hout | heq)
  · exact hout hw
  · exact hwv heq

/-- A proper module's induced graph has fewer vertices than the ambient graph. -/
theorem card_module_lt [Fintype α] (S : Finset α)
    (hS : S.card < Fintype.card α) :
    Fintype.card (S : Set α) < Fintype.card α := by
  have hc : Fintype.card (S : Set α) = S.card := Fintype.card_coe S
  rw [hc]
  exact hS

end Jig50.ModuleDecomposition

namespace Jig50.EHInvariance

open SimpleGraph Jig50.HomogeneousTransport
open Submissions.Erdos61UniformExponent.Uniform

/-- Relabeling the forbidden graph preserves its induced copies in every host. -/
theorem induced_copy_iff {α β γ : Type*}
    {H : SimpleGraph α} {H' : SimpleGraph β} (e : H ≃g H') (G : SimpleGraph γ) :
    (∃ f : α ↪ γ, H = G.comap f) ↔ (∃ f : β ↪ γ, H' = G.comap f) := by
  rw [← nonempty_embedding_iff H G, ← nonempty_embedding_iff H' G]
  constructor
  · rintro ⟨f⟩
    exact ⟨f.comp e.symm.toEmbedding⟩
  · rintro ⟨f⟩
    exact ⟨f.comp e.toEmbedding⟩

/-- The entire lower-bound function transfers unchanged, with the same host orders. -/
theorem lower_bound_iso {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {H : SimpleGraph α} {H' : SimpleGraph β} (e : H ≃g H') (f : ℕ → ℝ) :
    IsErdosHajnalLowerBound H f ↔ IsErdosHajnalLowerBound H' f := by
  unfold IsErdosHajnalLowerBound
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall fun _ => by simp only [induced_copy_iff e]

/-- Isomorphic forbidden graphs have the same original EH property and may use the same exponent. -/
theorem property_iso {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {H : SimpleGraph α} {H' : SimpleGraph β} (e : H ≃g H') :
    HasErdosHajnalProperty H ↔ HasErdosHajnalProperty H' := by
  unfold HasErdosHajnalProperty
  exact exists_congr fun _ => and_congr Iff.rfl (lower_bound_iso e _)

end Jig50.EHInvariance

namespace Jig50.PrimeReduction

open SimpleGraph Jig50.ModuleDecomposition
open Submissions.Erdos61UniformExponent.Uniform

universe u

/-- No module has order strictly between one and the whole graph.
This convention explicitly includes the degenerate graphs of orders zero, one and two. -/
def IsPrime {α : Type*} [Fintype α] (H : SimpleGraph α) : Prop :=
  ∀ S : Finset α, 1 < S.card → S.card < Fintype.card α → ¬IsModule H (S : Set α)

/-- Substitution and finite cardinal induction reduce every forbidden graph to prime graphs. -/
theorem property_of_prime
    (hprime : ∀ {β : Type u} [Fintype β] [DecidableEq β] (G : SimpleGraph β),
      IsPrime G → HasErdosHajnalProperty G)
    {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α) :
    HasErdosHajnalProperty H := by
  classical
  refine (Fintype.induction_subsingleton_or_nontrivial
    (P := fun (β : Type u) _ => ∀ [DecidableEq β] (G : SimpleGraph β),
      HasErdosHajnalProperty G) α ?_ ?_) H
  · intro β _ _ _ G
    apply hprime G
    intro S hS hproper
    have hβ : Fintype.card β ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  · intro β _ _ ih _ G
    by_cases hp : IsPrime G
    · exact hprime G hp
    · simp only [IsPrime, not_forall, Classical.not_imp, not_not] at hp
      obtain ⟨S, hS, hproper, hm⟩ := hp
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_trans (by decide : 0 < 1) hS)
      have hleft : HasErdosHajnalProperty (G.induce (collapsedVertices (S : Set β) v)) :=
        ih (collapsedVertices (S : Set β) v) (card_collapsed_lt S v hS) _
      have hright : HasErdosHajnalProperty (G.induce (S : Set β)) :=
        ih (S : Set β) (card_module_lt S hproper) _
      have hrep := Submissions.Erdos61Substitution.Closure.proof
        (G.induce (collapsedVertices (S : Set β) v)) (G.induce (S : Set β))
        (representative (S : Set β) v) hleft hright
      exact (Jig50.EHInvariance.property_iso
        (moduleIso G (S : Set β) v hv hm)).mp hrep

theorem reduction :
    (∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      HasErdosHajnalProperty H) ↔
    (∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      IsPrime H → HasErdosHajnalProperty H) := by
  constructor
  · intro h α _ _ H _
    exact h H
  · intro h α _ _ H
    exact property_of_prime h H

end Jig50.PrimeReduction

namespace Submissions.Erdos61PrimeReduction.Reduction

open SimpleGraph Jig50.PrimeReduction
open Submissions.Erdos61UniformExponent.Uniform

universe u

theorem proof :
    (∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      HasErdosHajnalProperty H) ↔
    (∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      IsPrime H → HasErdosHajnalProperty H) :=
  Jig50.PrimeReduction.reduction

end Submissions.Erdos61PrimeReduction.Reduction
