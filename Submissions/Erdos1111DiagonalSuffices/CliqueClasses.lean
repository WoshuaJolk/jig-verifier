import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

namespace Submissions.Erdos1111DiagonalSuffices.CliqueClasses

def ProperColoring {V C : Type} (G : SimpleGraph V) (color : V → C) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → color v ≠ color w

def Colorable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ color : V → Fin k, ProperColoring G color

def ChromaticAtLeast {V : Type} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ k : ℕ, k < d → ¬Colorable G k

def ChromaticAtLeastOn {V : Type} (G : SimpleGraph V)
    (A : Finset V) (c : ℕ) : Prop :=
  ChromaticAtLeast (G.induce (A : Set V)) c

def Anticomplete {V : Type} (G : SimpleGraph V)
    (A B : Finset V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b

/-- A clique on `c` vertices is not colourable with fewer than `c` colours. -/
theorem clique_chrom {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset V) (c : ℕ)
    (hT : G.IsClique (T : Set V)) (hc : T.card = c) : ChromaticAtLeastOn G T c := by
  intro k hk
  rintro ⟨color, hcol⟩
  have hinj : Function.Injective color := by
    intro a b hab
    by_contra hne
    have hadj : (G.induce (T : Set V)).Adj a b := by
      have : G.Adj a.1 b.1 := hT a.2 b.2 (fun h => hne (Subtype.ext h))
      simpa using this
    exact hcol hadj hab
  have hcard := Fintype.card_le_of_injective color hinj
  have h3 : Fintype.card (↥(T : Set V)) = c := by
    rw [← hc]; simp
  rw [h3] at hcard
  simp at hcard
  omega

/-- If a set is not of chromatic number at least `m + 1`, it carries an `m`-colouring,
extended arbitrarily to all vertices. -/
theorem colouring_of_not {V : Type} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) (m : ℕ)
    (hm : 0 < m) (h : ¬ChromaticAtLeastOn G X (m + 1)) :
    ∃ f : V → Fin m, ∀ v w, v ∈ X → w ∈ X → G.Adj v w → f v ≠ f w := by
  unfold ChromaticAtLeastOn ChromaticAtLeast at h
  push_neg at h
  obtain ⟨k, hk, color, hcol⟩ := h
  have hkm : k ≤ m := by omega
  refine ⟨fun v => if hv : v ∈ X then Fin.castLE hkm (color ⟨v, by exact_mod_cast hv⟩)
    else ⟨0, hm⟩, ?_⟩
  intro v w hv hw hvw heq
  simp only [dif_pos hv, dif_pos hw] at heq
  have hadj : (G.induce (X : Set V)).Adj ⟨v, by exact_mod_cast hv⟩ ⟨w, by exact_mod_cast hw⟩ := by
    simpa using hvw
  exact hcol hadj (Fin.castLE_injective hkm heq)

/-- Chromatic lower bounds pass from the graph cut down to a vertex class `Y` back to `G`. -/
theorem transfer {V : Type} [DecidableEq V] (G G' : SimpleGraph V) (Y : V → Prop)
    [DecidablePred Y] (hG' : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ Y a ∧ Y b) (c : ℕ) (hc : 2 ≤ c)
    (A : Finset V) (h : ChromaticAtLeastOn G' A c) : ChromaticAtLeastOn G (A.filter Y) c := by
  intro k hk
  rintro ⟨color, hcol⟩
  have hmem : ∀ a : V, a ∈ (A : Set V) → Y a → a ∈ ((A.filter Y : Finset V) : Set V) := by
    intro a ha hy
    have ha' : a ∈ A := by exact_mod_cast ha
    exact_mod_cast Finset.mem_filter.mpr ⟨ha', hy⟩
  by_cases hk0 : k = 0
  · subst hk0
    apply h 1 (by omega)
    refine ⟨fun _ => 0, ?_⟩
    intro a b hab
    have hab' : G'.Adj a.1 b.1 := by simpa using hab
    have hy := ((hG' _ _).mp hab').2.1
    exact (color ⟨a.1, hmem a.1 a.2 hy⟩).elim0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    apply h k hk
    refine ⟨fun a => if hy : Y a.1 then color ⟨a.1, hmem a.1 a.2 hy⟩ else ⟨0, hkpos⟩, ?_⟩
    intro a b hab heq
    have hab' : G'.Adj a.1 b.1 := by simpa using hab
    obtain ⟨hadj, hya, hyb⟩ := (hG' _ _).mp hab'
    simp only [dif_pos hya, dif_pos hyb] at heq
    have hadj' : (G.induce ((A.filter Y : Finset V) : Set V)).Adj
        ⟨a.1, hmem a.1 a.2 hya⟩ ⟨b.1, hmem b.1 b.2 hyb⟩ := by
      simpa using hadj
    exact hcol hadj' heq

/-- The El-Zahar–Erdős reduction: for `c ≥ 2`, a threshold on the diagonal `t = c` yields a
threshold for every `t`. Fix a maximum clique `K` and sort each vertex by its non-neighbours
in `K`: a class with `c` chosen non-neighbours is anticomplete to that `K_c`, and a class with
fewer than `c` non-neighbours in total is `K_c`-free. -/
theorem proof :
    ∀ c : ℕ, 2 ≤ c →
      (∃ d : ℕ, 1 ≤ d ∧
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
          ChromaticAtLeast G d →
          G.CliqueFree c →
          ∃ A B : Finset (Fin n),
            Anticomplete G A B ∧
            ChromaticAtLeastOn G A c ∧
            ChromaticAtLeastOn G B c) →
      ∀ t : ℕ, 1 ≤ t →
        ∃ d : ℕ, 1 ≤ d ∧
          ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
            ChromaticAtLeast G d →
            G.CliqueFree t →
            ∃ A B : Finset (Fin n),
              Anticomplete G A B ∧
              ChromaticAtLeastOn G A c ∧
              ChromaticAtLeastOn G B c := by
  classical
  intro c hc2 hdiag t ht
  obtain ⟨D, hD1, hD⟩ := hdiag
  refine ⟨2 ^ (t - 1) * (c + D) + 1, by omega, ?_⟩
  intro n G hchi hfree
  by_contra hno
  have hno' : ∀ A B : Finset (Fin n), Anticomplete G A B → ChromaticAtLeastOn G A c →
      ChromaticAtLeastOn G B c → False := fun A B h1 h2 h3 => hno ⟨A, B, h1, h2, h3⟩
  apply hchi (2 ^ (t - 1) * (c + D)) (by omega)
  -- a maximum clique
  obtain ⟨K, hKmem, hKmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun s : Finset (Fin n) => G.IsClique (s : Set (Fin n))) Finset.card
    ⟨∅, by simp⟩
  have hK : G.IsClique (K : Set (Fin n)) := by simpa using hKmem
  have hmax : ∀ s : Finset (Fin n), G.IsClique (s : Set (Fin n)) → s.card ≤ K.card :=
    fun s hs => hKmax s (by simpa using hs)
  have hKt : K.card ≤ t - 1 := by
    by_contra hlt
    have hle : t ≤ K.card := by omega
    obtain ⟨s, hsK, hscard⟩ := Finset.exists_subset_card_eq hle
    exact hfree s ⟨hK.subset (by exact_mod_cast hsK), hscard⟩
  let S : Fin n → Finset (Fin n) := fun v => K.filter fun k => ¬G.Adj v k
  have memS : ∀ x k, k ∈ S x ↔ k ∈ K ∧ ¬G.Adj x k := by
    intro x k; simp [S]
  have hSK : ∀ v, S v ⊆ K := fun v => Finset.filter_subset _ _
  have hSself : ∀ v, v ∈ K → S v = {v} := by
    intro v hv
    ext k
    rw [memS, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hna⟩
      by_contra hne
      exact hna (hK hv hk (fun h => hne h.symm))
    · rintro rfl
      exact ⟨hv, fun h => (G.ne_of_adj h) rfl⟩
  have hT : ∀ v, ∃ T : Finset (Fin n), T ⊆ S v ∧ (T.card = c ∨ (T.card < c ∧ T = S v)) := by
    intro v
    by_cases h3 : c ≤ (S v).card
    · obtain ⟨T, hTs, hTc⟩ := Finset.exists_subset_card_eq h3
      exact ⟨T, hTs, Or.inl hTc⟩
    · exact ⟨S v, subset_rfl, Or.inr ⟨by omega, rfl⟩⟩
  choose T hTS hTc using hT
  have hTK : ∀ v, T v ⊆ K := fun v => (hTS v).trans (hSK v)
  let X : Finset (Fin n) → Finset (Fin n) := fun T0 => Finset.univ.filter fun v => T v = T0
  have memX : ∀ T0 v, v ∈ X T0 ↔ T v = T0 := by
    intro T0 v; simp [X]
  have hM : 0 < c + D := by omega
  -- every class is (c + D)-colourable
  have hcol : ∀ T0 : Finset (Fin n), ∃ f : Fin n → Fin (c + D), T0 ⊆ K → T0.card ≤ c →
      ∀ v w, v ∈ X T0 → w ∈ X T0 → G.Adj v w → f v ≠ f w := by
    intro T0
    by_cases hT0 : T0 ⊆ K ∧ T0.card ≤ c
    · obtain ⟨hsub, hcard⟩ := hT0
      by_cases hceq : T0.card = c
      · -- the class is anticomplete to the clique T0
        have hnot : ¬ChromaticAtLeastOn G (X T0) ((c - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega)]
          intro hX
          apply hno' T0 (X T0) ⟨?_, ?_⟩
            (clique_chrom G T0 c (hK.subset (by exact_mod_cast hsub)) hceq) hX
          · rw [Finset.disjoint_left]
            intro x hx hx'
            rw [memX] at hx'
            have h1 : T x ⊆ {x} := by rw [← hSself x (hsub hx)]; exact hTS x
            have h2 := Finset.card_le_card h1
            rw [hx', hceq] at h2
            simp at h2
            omega
          · intro a ha b hb hab
            rw [memX] at hb
            have : a ∈ S b := hTS b (by rw [hb]; exact ha)
            exact ((memS b a).mp this).2 hab.symm
        obtain ⟨f, hf⟩ := colouring_of_not G (X T0) (c - 1) (by omega) hnot
        have hle : c - 1 ≤ c + D := by omega
        exact ⟨fun v => Fin.castLE hle (f v), fun _ _ v w hv hw hvw heq =>
          hf v w hv hw hvw (Fin.castLE_injective hle heq)⟩
      · have hlt : T0.card < c := by omega
        let G' : SimpleGraph (Fin n) :=
          G ⊓ SimpleGraph.fromRel fun a b : Fin n => T a = T0 ∧ T b = T0
        have hG' : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ T a = T0 ∧ T b = T0 := by
          intro a b
          show (G ⊓ SimpleGraph.fromRel fun a b : Fin n => T a = T0 ∧ T b = T0).Adj a b ↔ _
          rw [SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
          constructor
          · rintro ⟨h, -, (h' | h')⟩
            · exact ⟨h, h'⟩
            · exact ⟨h, h'.2, h'.1⟩
          · rintro ⟨h, h1, h2⟩
            exact ⟨h, G.ne_of_adj h, Or.inl ⟨h1, h2⟩⟩
        have hsee : ∀ a, T a = T0 → ∀ k ∈ K \ T0, G.Adj a k := by
          intro a ha k hk
          obtain ⟨hkK, hkT⟩ := Finset.mem_sdiff.mp hk
          have hSa : S a = T0 := by
            rcases hTc a with h | ⟨_, h⟩
            · rw [ha] at h; omega
            · rw [← h, ha]
          by_contra hna
          exact hkT (hSa ▸ (memS a k).mpr ⟨hkK, hna⟩)
        have hout : ∀ a, T a = T0 → a ∉ K \ T0 := fun a ha hmem =>
          (G.ne_of_adj (hsee a ha a hmem)) rfl
        have hfree' : G'.CliqueFree c := by
          intro s hs
          obtain ⟨hscl, hscard⟩ := hs
          -- every member of s lies in the class
          have hclass : ∀ x ∈ s, T x = T0 := by
            intro x hx
            have h1 : 1 < s.card := by omega
            obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne h1 x
            have := hscl (by exact_mod_cast hx) (by exact_mod_cast hy) (Ne.symm hyx)
            exact ((hG' x y).mp this).2.1
          have hdisj : Disjoint s (K \ T0) := by
            rw [Finset.disjoint_left]
            intro x hx hx'
            exact hout x (hclass x hx) hx'
          have hcl : G.IsClique ((s ∪ (K \ T0) : Finset (Fin n)) : Set (Fin n)) := by
            intro x hx y hy hxy
            have hx' : x ∈ s ∪ (K \ T0) := by exact_mod_cast hx
            have hy' : y ∈ s ∪ (K \ T0) := by exact_mod_cast hy
            rcases Finset.mem_union.mp hx' with hxs | hxk <;>
              rcases Finset.mem_union.mp hy' with hys | hyk
            · exact ((hG' x y).mp
                (hscl (by exact_mod_cast hxs) (by exact_mod_cast hys) hxy)).1
            · exact hsee x (hclass x hxs) y hyk
            · exact (hsee y (hclass y hys) x hxk).symm
            · exact hK (by exact_mod_cast (Finset.mem_sdiff.mp hxk).1)
                (by exact_mod_cast (Finset.mem_sdiff.mp hyk).1) hxy
          have hcardle := hmax _ hcl
          have hu := Finset.card_union_add_card_inter s (K \ T0)
          rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty] at hu
          have hsd := Finset.card_sdiff_add_card_eq_card hsub
          omega
        by_cases hch : ChromaticAtLeast G' D
        · exfalso
          obtain ⟨A, B, ⟨hdisj, hanti⟩, hA, hB⟩ := hD n G' hch hfree'
          apply hno' (A.filter fun v => T v = T0) (B.filter fun v => T v = T0) ⟨?_, ?_⟩
            (transfer G G' (fun v => T v = T0) hG' c hc2 A hA)
            (transfer G G' (fun v => T v = T0) hG' c hc2 B hB)
          · exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
              (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisj)
          · intro a ha b hb hab
            obtain ⟨haA, hta⟩ := Finset.mem_filter.mp ha
            obtain ⟨hbB, htb⟩ := Finset.mem_filter.mp hb
            exact hanti a haA b hbB ((hG' a b).mpr ⟨hab, hta, htb⟩)
        · unfold ChromaticAtLeast at hch
          push_neg at hch
          obtain ⟨k, hk, f, hf⟩ := hch
          have hle : k ≤ c + D := by omega
          refine ⟨fun v => Fin.castLE hle (f v), fun _ _ v w hv hw hvw heq => ?_⟩
          rw [memX] at hv hw
          exact hf ((hG' v w).mpr ⟨hvw, hv, hw⟩) (Fin.castLE_injective hle heq)
    · exact ⟨fun _ => ⟨0, hM⟩, fun h1 h2 => absurd ⟨h1, h2⟩ hT0⟩
  choose f hf using hcol
  have hTcard : ∀ v, (T v).card ≤ c := by
    intro v
    rcases hTc v with h | ⟨h, _⟩ <;> omega
  let P : Finset (Finset (Fin n) × ℕ) := K.powerset ×ˢ Finset.range (c + D)
  have hmemP : ∀ v, (T v, (f (T v) v : ℕ)) ∈ P :=
    fun v => Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (hTK v), Finset.mem_range.mpr (f (T v) v).isLt⟩
  have hPcard : P.card ≤ 2 ^ (t - 1) * (c + D) := by
    have h1 : P.card = 2 ^ K.card * (c + D) := by
      show (K.powerset ×ˢ Finset.range (c + D)).card = _
      rw [Finset.card_product, Finset.card_powerset, Finset.card_range]
    rw [h1]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hKt)
  have hcardP : Fintype.card P ≤ Fintype.card (Fin (2 ^ (t - 1) * (c + D))) := by
    simpa using hPcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardP
  refine ⟨fun v => e ⟨(T v, (f (T v) v : ℕ)), hmemP v⟩, ?_⟩
  intro v w hvw heq
  have hpair : (T v, (f (T v) v : ℕ)) = (T w, (f (T w) w : ℕ)) :=
    congrArg Subtype.val (e.injective heq)
  have hTeq : T v = T w := congrArg Prod.fst hpair
  have hbeq : (f (T v) v : ℕ) = (f (T w) w : ℕ) := congrArg Prod.snd hpair
  rw [← hTeq] at hbeq
  exact hf (T v) (hTK v) (hTcard v) v w ((memX _ _).mpr rfl) ((memX _ _).mpr hTeq.symm) hvw
    (Fin.ext hbeq)

end Submissions.Erdos1111DiagonalSuffices.CliqueClasses
