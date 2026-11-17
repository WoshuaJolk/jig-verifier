import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

namespace Submissions.Erdos1111WagonC2AllT.WagonAllT

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

/-- The two endpoints of an edge induce a graph that is not `k`-colourable for `k < 2`. -/
theorem edge_chromaticAtLeastOn_two {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {a b : V} (hab : G.Adj a b) : ChromaticAtLeastOn G ({a, b} : Finset V) 2 := by
  intro k hk
  rintro ⟨color, hcol⟩
  have ha : a ∈ (({a, b} : Finset V) : Set V) := by simp
  have hb : b ∈ (({a, b} : Finset V) : Set V) := by simp
  have hadj : (G.induce (({a, b} : Finset V) : Set V)).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
    simpa using hab
  have hne := hcol hadj
  apply hne
  have h1 : (color ⟨a, ha⟩ : ℕ) < k := (color ⟨a, ha⟩).isLt
  have h2 : (color ⟨b, hb⟩ : ℕ) < k := (color ⟨b, hb⟩).isLt
  apply Fin.ext
  omega

/-- Wagon's theorem in the form used here: a `K_t`-free graph with no induced `2K₂` is
`C(t,2)`-colourable. Fix a maximum clique `K`; colour each vertex by one or two of its
non-neighbours in `K` (itself counting as a non-neighbour), using a single one only when it
is the only one. -/
theorem colorable_of_no_2K2 {n t : ℕ} (G : SimpleGraph (Fin n)) (hfree : G.CliqueFree t)
    (h2 : ∀ a b v w : Fin n, G.Adj a b → G.Adj v w → a ≠ v → a ≠ w → b ≠ v → b ≠ w →
        ¬G.Adj a v → ¬G.Adj a w → ¬G.Adj b v → ¬G.Adj b w → False) :
    Colorable G (t.choose 2) := by
  classical
  obtain ⟨K, hKmem, hKmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun s : Finset (Fin n) => G.IsClique (s : Set (Fin n))) Finset.card
    ⟨∅, by simp⟩
  have hK : G.IsClique (K : Set (Fin n)) := by simpa using hKmem
  have hmax : ∀ s : Finset (Fin n), G.IsClique (s : Set (Fin n)) → s.card ≤ K.card :=
    fun s hs => hKmax s (by simpa using hs)
  have hKt : K.card + 1 ≤ t := by
    by_contra hlt
    have hle : t ≤ K.card := by omega
    obtain ⟨s, hsK, hscard⟩ := Finset.exists_subset_card_eq hle
    exact hfree s ⟨hK.subset (by exact_mod_cast hsK), hscard⟩
  let S : Fin n → Finset (Fin n) := fun v => K.filter fun k => ¬G.Adj v k
  have memS : ∀ x k, k ∈ S x ↔ k ∈ K ∧ ¬G.Adj x k := by
    intro x k; simp [S]
  have hS : ∀ v, (S v).Nonempty := by
    intro v
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hadj : ∀ k ∈ K, G.Adj v k := by
      intro k hk
      by_contra hna
      have hmem : k ∈ S v := (memS v k).mpr ⟨hk, hna⟩
      rw [hne] at hmem
      simp at hmem
    have hvK : v ∉ K := fun hv => (G.ne_of_adj (hadj v hv)) rfl
    have hcl : G.IsClique ((insert v K : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert, SimpleGraph.isClique_insert]
      exact ⟨hK, fun b hb _ => hadj b (by exact_mod_cast hb)⟩
    have hc := hmax _ hcl
    rw [Finset.card_insert_of_notMem hvK] at hc
    omega
  have hT : ∀ v, ∃ T : Finset (Fin n), T ⊆ S v ∧ (T.card = 2 ∨ (T.card = 1 ∧ T = S v)) := by
    intro v
    by_cases h : 2 ≤ (S v).card
    · obtain ⟨T, hTs, hTc⟩ := Finset.exists_subset_card_eq h
      exact ⟨T, hTs, Or.inl hTc⟩
    · have hpos := (hS v).card_pos
      have h1 : (S v).card = 1 := by omega
      exact ⟨S v, subset_rfl, Or.inr ⟨h1, rfl⟩⟩
  choose T hTS hTc using hT
  let P : Finset (Finset (Fin n)) := K.powersetCard 1 ∪ K.powersetCard 2
  have hTP : ∀ v, T v ∈ P := by
    intro v
    have hsub : T v ⊆ K := (hTS v).trans (Finset.filter_subset _ _)
    rcases hTc v with h | ⟨h, _⟩
    · exact Finset.mem_union_right _ (Finset.mem_powersetCard.mpr ⟨hsub, h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_powersetCard.mpr ⟨hsub, h⟩)
  have hPcard : P.card ≤ t.choose 2 := by
    calc P.card ≤ (K.powersetCard 1).card + (K.powersetCard 2).card := Finset.card_union_le _ _
      _ = K.card.choose 1 + K.card.choose 2 := by
          rw [Finset.card_powersetCard, Finset.card_powersetCard]
      _ = (K.card + 1).choose 2 := (Nat.choose_succ_succ' _ 1).symm
      _ ≤ t.choose 2 := Nat.choose_le_choose 2 hKt
  have hcardP : Fintype.card P ≤ Fintype.card (Fin (t.choose 2)) := by
    simpa using hPcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardP
  refine ⟨fun v => e ⟨T v, hTP v⟩, ?_⟩
  intro v w hvw heq
  have hTeq : T v = T w := congrArg Subtype.val (e.injective heq)
  rcases hTc v with h2c | ⟨h1, hTv⟩
  · obtain ⟨i, j, hij, hTij⟩ := Finset.card_eq_two.mp h2c
    have hi_v : i ∈ S v := hTS v (by rw [hTij]; simp)
    have hj_v : j ∈ S v := hTS v (by rw [hTij]; simp)
    have hi_w : i ∈ S w := hTS w (by rw [← hTeq, hTij]; simp)
    have hj_w : j ∈ S w := hTS w (by rw [← hTeq, hTij]; simp)
    rw [memS] at hi_v hj_v hi_w hj_w
    have hadjij : G.Adj i j := hK hi_v.1 hj_v.1 hij
    have hiv : i ≠ v := by rintro rfl; exact hi_w.2 hvw.symm
    have hiw : i ≠ w := by rintro rfl; exact hi_v.2 hvw
    have hjv : j ≠ v := by rintro rfl; exact hj_w.2 hvw.symm
    have hjw : j ≠ w := by rintro rfl; exact hj_v.2 hvw
    exact h2 i j v w hadjij hvw hiv hiw hjv hjw (fun h => hi_v.2 h.symm)
      (fun h => hi_w.2 h.symm) (fun h => hj_v.2 h.symm) (fun h => hj_w.2 h.symm)
  · have hTw : T w = S w := by
      rcases hTc w with h | ⟨_, h⟩
      · rw [← hTeq, h1] at h; omega
      · exact h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    have hSv : S v = {i} := by rw [← hTv, hi]
    have hSw : S w = {i} := by rw [← hTw, ← hTeq, hi]
    have key : ∀ x, S x = {i} → ∀ k ∈ K, k ≠ i → G.Adj x k := by
      intro x hx k hk hki
      by_contra hna
      have hmem : k ∈ S x := (memS x k).mpr ⟨hk, hna⟩
      rw [hx] at hmem
      exact hki (Finset.mem_singleton.mp hmem)
    have hiK : i ∈ K := ((memS v i).mp (by rw [hSv]; simp)).1
    have hvK : v ∉ K.erase i := by
      intro hv
      obtain ⟨hvne, hvK⟩ := Finset.mem_erase.mp hv
      exact (G.ne_of_adj (key v hSv v hvK hvne)) rfl
    have hwK : w ∉ K.erase i := by
      intro hw
      obtain ⟨hwne, hwK⟩ := Finset.mem_erase.mp hw
      exact (G.ne_of_adj (key w hSw w hwK hwne)) rfl
    have hcl : G.IsClique ((insert v (insert w (K.erase i)) : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert, SimpleGraph.isClique_insert, Finset.coe_insert,
        SimpleGraph.isClique_insert]
      refine ⟨⟨hK.subset (by exact_mod_cast Finset.erase_subset i K), ?_⟩, ?_⟩
      · intro b hb _
        have hb' := Finset.mem_erase.mp (by exact_mod_cast hb)
        exact key w hSw b hb'.2 hb'.1
      · intro b hb _
        rcases hb with rfl | hb
        · exact hvw
        · have hb' := Finset.mem_erase.mp (by exact_mod_cast hb)
          exact key v hSv b hb'.2 hb'.1
    have hcard := hmax _ hcl
    have hvw' : v ∉ insert w (K.erase i) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨G.ne_of_adj hvw, hvK⟩
    rw [Finset.card_insert_of_notMem hvw', Finset.card_insert_of_notMem hwK,
      Finset.card_erase_of_mem hiK] at hcard
    have hpos := Finset.card_pos.mpr ⟨i, hiK⟩
    omega

/-- The `c = 2` slice of the El-Zahar–Erdős problem for every `t`, with Wagon's threshold
`d(t,2) ≤ C(t,2) + 1`. -/
theorem proof :
    ∀ t : ℕ, 1 ≤ t →
      ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
        ChromaticAtLeast G (t.choose 2 + 1) →
        G.CliqueFree t →
        ∃ A B : Finset (Fin n),
          Anticomplete G A B ∧
          ChromaticAtLeastOn G A 2 ∧
          ChromaticAtLeastOn G B 2 := by
  classical
  intro t _ n G hchi hfree
  by_contra hno
  apply hchi (t.choose 2) (Nat.lt_succ_self _)
  apply colorable_of_no_2K2 G hfree
  intro a b v w hab hvw hav haw hbv hbw nav naw nbv nbw
  apply hno
  refine ⟨{a, b}, {v, w}, ⟨?_, ?_⟩, edge_chromaticAtLeastOn_two G hab,
    edge_chromaticAtLeastOn_two G hvw⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;> contradiction
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> assumption

end Submissions.Erdos1111WagonC2AllT.WagonAllT
