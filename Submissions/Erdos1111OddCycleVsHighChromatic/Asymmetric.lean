import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic

namespace Submissions.Erdos1111OddCycleVsHighChromatic.Asymmetric

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

/-! ### The colour pattern around a shortest odd cycle of length `l`

`hcol l i` colours the cycle vertex of index `i`, `gcol l i` colours the outside neighbours
attached to index `i`. Away from the last three indices the pattern is `i % 2` / `2 + i % 2`;
the last three indices absorb the parity defect with a fifth colour. -/

def gcol (l i : ℕ) : ℕ :=
  if i + 3 < l then i % 2 else if i + 3 = l then 3 else if i + 2 = l then 4 else 2

def hcol (l i : ℕ) : ℕ :=
  if i + 3 < l then 2 + i % 2 else if i + 3 = l then 1 else if i + 2 = l then 2 else 0

theorem gcol_lt (l i : ℕ) : gcol l i < 5 := by
  unfold gcol; split_ifs <;> omega

theorem hcol_lt (l i : ℕ) : hcol l i < 5 := by
  unfold hcol; split_ifs <;> omega

theorem hh {l i p : ℕ} (hl : l % 2 = 1) (h5 : 5 ≤ l) (hip : i + p < l)
    (hp : p = 1 ∨ p + 1 = l) : hcol l i ≠ hcol l (i + p) := by
  unfold hcol; split_ifs <;> omega

theorem hg {l i p : ℕ} (hl : l % 2 = 1) (h5 : 5 ≤ l) (hip : i + p < l)
    (hp : p = 0 ∨ p = 2 ∨ p + 2 = l) :
    hcol l i ≠ gcol l (i + p) ∧ hcol l (i + p) ≠ gcol l i := by
  unfold hcol gcol; split_ifs <;> omega

theorem gg {l i p : ℕ} (hl : l % 2 = 1) (h5 : 5 ≤ l) (hip : i + p < l)
    (hp : p = 1 ∨ p = 3 ∨ p + 3 = l ∨ p + 1 = l) : gcol l i ≠ gcol l (i + p) := by
  unfold gcol; split_ifs <;> omega

/-! ### Segments of a closed walk given as a periodic sequence -/

theorem seg {V : Type} {G : SimpleGraph V} {c : ℕ → V}
    (hadj : ∀ k, G.Adj (c k) (c (k + 1))) (a q : ℕ) :
    ∃ W : G.Walk (c a) (c (a + q)), W.length = q := by
  induction q with
  | zero => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ q ih =>
    obtain ⟨W, hW⟩ := ih
    exact ⟨W.concat (hadj (a + q)), by rw [SimpleGraph.Walk.length_concat, hW]⟩

/-- A detour of length `r` from index `a + p` back to index `a` of a shortest odd closed walk
of length `l`: whichever of the two closed walks it creates is odd cannot be shorter. -/
theorem detour {V : Type} {G : SimpleGraph V} {c : ℕ → V} {l : ℕ}
    (hodd : l % 2 = 1) (hadj : ∀ k, G.Adj (c k) (c (k + 1)))
    (hper : ∀ k, c (k + l) = c k)
    (hmin : ∀ (u : V) (w : G.Walk u u), Odd w.length → l ≤ w.length)
    {a p r : ℕ} (hp : p ≤ l) (D : G.Walk (c (a + p)) (c a)) (hD : D.length = r) :
    ((p + r) % 2 = 1 → l ≤ p + r) ∧ ((p + r) % 2 = 0 → p ≤ r) := by
  constructor
  · intro h
    obtain ⟨W, hW⟩ := seg hadj a p
    have hlen : (W.append D).length = p + r := by
      rw [SimpleGraph.Walk.length_append, hW, hD]
    have := hmin _ (W.append D) (by rw [hlen]; exact Nat.odd_iff.mpr h)
    rw [hlen] at this
    exact this
  · intro h
    obtain ⟨W, hW⟩ := seg hadj (a + p) (l - p)
    have e : c (a + p + (l - p)) = c a := by
      have : a + p + (l - p) = a + l := by omega
      rw [this, hper]
    have hlen : ((W.copy rfl e).append D.reverse).length = (l - p) + r := by
      simp [hW, hD]
    have := hmin _ ((W.copy rfl e).append D.reverse)
      (by rw [hlen]; exact Nat.odd_iff.mpr (by omega))
    rw [hlen] at this
    omega

/-- Triangle-free case: a shortest odd cycle together with its neighbourhood is 5-colourable,
so if `G` is not `(c+4)`-colourable the rest has chromatic number at least `c`. -/
theorem tf :
    ∀ c : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ChromaticAtLeast G (c + 5) →
      G.CliqueFree 3 →
      ∃ A B : Finset (Fin n),
        Anticomplete G A B ∧
        ChromaticAtLeastOn G A 3 ∧
        ChromaticAtLeastOn G B c := by
  classical
  intro c0 n G hchi hfree
  -- a shortest odd closed walk
  have h2 : ¬G.Colorable 2 := by
    rintro ⟨col⟩
    exact hchi 2 (by omega) ⟨col, fun v w hvw => col.valid hvw⟩
  rw [SimpleGraph.two_colorable_iff_forall_loop_even] at h2
  push_neg at h2
  obtain ⟨u0, w0, hw0⟩ := h2
  have hex : ∃ L, ∃ (u : Fin n) (w : G.Walk u u), w.length = L ∧ Odd L :=
    ⟨w0.length, u0, w0, rfl, Nat.not_even_iff_odd.mp hw0⟩
  obtain ⟨l, hmin, u, w, hwl, hoddl⟩ :
      ∃ l, (∀ (x : Fin n) (w' : G.Walk x x), Odd w'.length → l ≤ w'.length) ∧
        ∃ (u : Fin n) (w : G.Walk u u), w.length = l ∧ Odd l :=
    ⟨Nat.find hex, fun x w' ho => Nat.find_min' hex ⟨x, w', rfl, ho⟩, Nat.find_spec hex⟩
  have hl2 : l % 2 = 1 := Nat.odd_iff.mp hoddl
  have hlpos : 0 < l := by omega
  let c : ℕ → Fin n := fun k => w.getVert (k % l)
  have hper : ∀ k, c (k + l) = c k := by
    intro k; simp [c]
  have hgl : w.getVert l = u := by rw [← hwl]; exact w.getVert_length
  have hadj : ∀ k, G.Adj (c k) (c (k + 1)) := by
    intro k
    have hr : k % l < l := Nat.mod_lt _ hlpos
    have hmod : (k + 1) % l = (k % l + 1) % l := (Nat.mod_add_mod k l 1).symm
    show G.Adj (w.getVert (k % l)) (w.getVert ((k + 1) % l))
    rw [hmod]
    have hstep := w.adj_getVert_succ (i := k % l) (by rw [hwl]; exact hr)
    by_cases hlt : k % l + 1 < l
    · rw [Nat.mod_eq_of_lt hlt]; exact hstep
    · have he : k % l + 1 = l := by omega
      rw [he] at hstep ⊢
      rw [Nat.mod_self, w.getVert_zero]
      rwa [hgl] at hstep
  have h5 : 5 ≤ l := by
    by_contra hlt
    have h13 : l = 1 ∨ l = 3 := by omega
    rcases h13 with h1 | h3
    · have ha : G.Adj (c 0) (c 1) := hadj 0
      have hp : c 1 = c 0 := by have := hper 0; simpa [h1] using this
      exact (G.ne_of_adj ha) hp.symm
    · have a1 : G.Adj (c 0) (c 1) := hadj 0
      have a2 : G.Adj (c 1) (c 2) := hadj 1
      have a3 : G.Adj (c 2) (c 3) := hadj 2
      have hp : c 3 = c 0 := by have := hper 0; simpa [h3] using this
      rw [hp] at a3
      exact hfree {c 0, c 1, c 2} (SimpleGraph.is3Clique_triple_iff.mpr ⟨a1, a3.symm, a2⟩)
  -- index facts from minimality
  have F3' : ∀ i p, i + p < l → G.Adj (c i) (c (i + p)) → p = 1 ∨ p + 1 = l := by
    intro i p hip h
    have hd := detour hl2 hadj hper hmin (a := i) (p := p) (r := 1) (by omega)
      (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil) (by simp)
    rcases Nat.mod_two_eq_zero_or_one (p + 1) with h0 | h1
    · have := hd.2 h0; omega
    · have := hd.1 h1; omega
  have F1' : ∀ (m : Fin n) i p, i + p < l → G.Adj m (c i) → G.Adj m (c (i + p)) →
      p = 0 ∨ p = 2 ∨ p + 2 = l := by
    intro m i p hip h1 h2
    have hd := detour hl2 hadj hper hmin (a := i) (p := p) (r := 2) (by omega)
      (SimpleGraph.Walk.cons h2.symm (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil)) (by simp)
    rcases Nat.mod_two_eq_zero_or_one (p + 2) with h0 | h1
    · have := hd.2 h0; omega
    · have := hd.1 h1; omega
  have F2' : ∀ (m m' : Fin n) i p, i + p < l → G.Adj m (c i) → G.Adj m' (c (i + p)) →
      G.Adj m m' → p = 1 ∨ p = 3 ∨ p + 3 = l ∨ p + 1 = l := by
    intro m m' i p hip h1 h2 hmm
    have hd := detour hl2 hadj hper hmin (a := i) (p := p) (r := 3) (by omega)
      (SimpleGraph.Walk.cons h2.symm (SimpleGraph.Walk.cons hmm.symm
        (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil))) (by simp)
    rcases Nat.mod_two_eq_zero_or_one (p + 3) with h0 | h1
    · have := hd.2 h0; omega
    · have := hd.1 h1; omega
  have F3 : ∀ i j, i < l → j < l → G.Adj (c i) (c j) → hcol l i ≠ hcol l j := by
    intro i j hi hj h
    rcases le_total i j with hij | hji
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact hh hl2 h5 hj (F3' i p hj h)
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hji
      exact (hh hl2 h5 hi (F3' j p hi h.symm)).symm
  have F1 : ∀ (m : Fin n) i j, i < l → j < l → G.Adj m (c i) → G.Adj m (c j) →
      hcol l i ≠ gcol l j := by
    intro m i j hi hj h1 h2
    rcases le_total i j with hij | hji
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact (hg hl2 h5 hj (F1' m i p hj h1 h2)).1
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hji
      exact (hg hl2 h5 hi (F1' m j p hi h2 h1)).2
  have F2 : ∀ (m m' : Fin n) i j, i < l → j < l → G.Adj m (c i) → G.Adj m' (c j) →
      G.Adj m m' → gcol l i ≠ gcol l j := by
    intro m m' i j hi hj h1 h2 hmm
    rcases le_total i j with hij | hji
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact gg hl2 h5 hj (F2' m m' i p hj h1 h2 hmm)
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hji
      exact (gg hl2 h5 hi (F2' m' m j p hi h2 h1 hmm.symm)).symm
  -- the cycle, its neighbourhood, and the 5-colouring of both
  let inC : Fin n → Prop := fun v => ∃ i, i < l ∧ c i = v
  let inM : Fin n → Prop := fun v => ∃ i, i < l ∧ G.Adj v (c i)
  have cmem : ∀ k, inC (c k) := fun k => ⟨k % l, Nat.mod_lt _ hlpos, by simp [c]⟩
  let col5 : Fin n → ℕ := fun v =>
    if hC : inC v then hcol l (Classical.choose hC)
    else if hM : inM v then gcol l (Classical.choose hM) else 0
  have col5_lt : ∀ v, col5 v < 5 := by
    intro v
    by_cases hC : inC v
    · simp only [col5, dif_pos hC]; exact hcol_lt _ _
    · by_cases hM : inM v
      · simp only [col5, dif_neg hC, dif_pos hM]; exact gcol_lt _ _
      · simp only [col5, dif_neg hC, dif_neg hM]; norm_num
  have col5_proper : ∀ v w, G.Adj v w → (inC v ∨ inM v) → (inC w ∨ inM w) →
      col5 v ≠ col5 w := by
    intro v w hvw hv hw
    by_cases hCv : inC v
    · obtain ⟨hi, hci⟩ := Classical.choose_spec hCv
      by_cases hCw : inC w
      · obtain ⟨hj, hcj⟩ := Classical.choose_spec hCw
        simp only [col5, dif_pos hCv, dif_pos hCw]
        exact F3 _ _ hi hj (by rw [hci, hcj]; exact hvw)
      · have hMw : inM w := hw.resolve_left hCw
        obtain ⟨hj, hwj⟩ := Classical.choose_spec hMw
        simp only [col5, dif_pos hCv, dif_neg hCw, dif_pos hMw]
        exact F1 w _ _ hi hj (by rw [hci]; exact hvw.symm) hwj
    · have hMv : inM v := hv.resolve_left hCv
      obtain ⟨hi, hvi⟩ := Classical.choose_spec hMv
      by_cases hCw : inC w
      · obtain ⟨hj, hcj⟩ := Classical.choose_spec hCw
        simp only [col5, dif_neg hCv, dif_pos hMv, dif_pos hCw]
        exact (F1 v _ _ hj hi (by rw [hcj]; exact hvw) hvi).symm
      · have hMw : inM w := hw.resolve_left hCw
        obtain ⟨hj, hwj⟩ := Classical.choose_spec hMw
        simp only [col5, dif_neg hCv, dif_pos hMv, dif_neg hCw, dif_pos hMw]
        exact F2 v w _ _ hi hj hvi hwj hvw
  let A : Finset (Fin n) := Finset.univ.filter fun v => inC v
  let B : Finset (Fin n) := Finset.univ.filter fun v => ¬(inC v ∨ inM v)
  have hmemA : ∀ i, c i ∈ (A : Set (Fin n)) := fun i => by
    simp only [A, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact cmem i
  have hmemB : ∀ v, ¬(inC v ∨ inM v) → v ∈ (B : Set (Fin n)) := fun v hv => by
    simp only [B, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hv
  -- the cycle itself is not 2-colourable
  have hA3 : ChromaticAtLeastOn G A 3 := by
    intro k hk
    rintro ⟨color, hcol⟩
    let f : ℕ → ℕ := fun i => (color ⟨c i, hmemA i⟩ : ℕ)
    have hne : ∀ i, f i ≠ f (i + 1) := by
      intro i hEq
      have hadj' : (G.induce (A : Set (Fin n))).Adj ⟨c i, hmemA i⟩ ⟨c (i + 1), hmemA (i + 1)⟩ := by
        simpa using hadj i
      exact hcol hadj' (Fin.ext hEq)
    have hlt : ∀ i, f i < 2 := fun i => by
      have := (color ⟨c i, hmemA i⟩).isLt
      show (color ⟨c i, hmemA i⟩ : ℕ) < 2
      omega
    have hstep : ∀ i, f (i + 2) = f i := by
      intro i
      have h1 := hne i
      have h2 : f (i + 1) ≠ f (i + 2) := hne (i + 1)
      have := hlt i; have := hlt (i + 1); have := hlt (i + 2)
      omega
    have hev : ∀ q, f (2 * q + 1) = f 1 := by
      intro q
      induction q with
      | zero => rfl
      | succ q ih => rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by ring, hstep, ih]
    have hfl : f l = f 0 := by
      have hsub : (⟨c l, hmemA l⟩ : ↥(A : Set (Fin n))) = ⟨c 0, hmemA 0⟩ :=
        Subtype.ext (by have := hper 0; simpa using this)
      show (color ⟨c l, hmemA l⟩ : ℕ) = (color ⟨c 0, hmemA 0⟩ : ℕ)
      rw [hsub]
    obtain ⟨q, hq⟩ : ∃ q, l = 2 * q + 1 := ⟨l / 2, by omega⟩
    have h01 : f 0 ≠ f 1 := hne 0
    rw [hq, hev] at hfl
    exact h01 hfl.symm
  by_cases hB3 : ChromaticAtLeastOn G B c0
  · refine ⟨A, B, ⟨?_, ?_⟩, hA3, hB3⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      exact hx' (Or.inl hx)
    · intro a ha b hb hab
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨i, hi, rfl⟩ := ha
      exact hb (Or.inr ⟨i, hi, hab.symm⟩)
  · exfalso
    unfold ChromaticAtLeastOn ChromaticAtLeast at hB3
    push_neg at hB3
    obtain ⟨k, hk, color, hcol⟩ := hB3
    apply hchi (5 + k) (by omega)
    let col7 : Fin n → ℕ := fun v =>
      if hv : inC v ∨ inM v then col5 v else 5 + (color ⟨v, hmemB v hv⟩ : ℕ)
    have col7_lt : ∀ v, col7 v < 5 + k := by
      intro v
      by_cases hv : inC v ∨ inM v
      · simp only [col7, dif_pos hv]; have := col5_lt v; omega
      · simp only [col7, dif_neg hv]; have := (color ⟨v, hmemB v hv⟩).isLt; omega
    refine ⟨fun v => ⟨col7 v, col7_lt v⟩, ?_⟩
    intro v w hvw heq
    have heq' : col7 v = col7 w := congrArg Fin.val heq
    by_cases hv : inC v ∨ inM v <;> by_cases hw : inC w ∨ inM w
    · simp only [col7, dif_pos hv, dif_pos hw] at heq'
      exact col5_proper v w hvw hv hw heq'
    · simp only [col7, dif_pos hv, dif_neg hw] at heq'
      have := col5_lt v; omega
    · simp only [col7, dif_neg hv, dif_pos hw] at heq'
      have := col5_lt w; omega
    · simp only [col7, dif_neg hv, dif_neg hw] at heq'
      have hadj' : (G.induce (B : Set (Fin n))).Adj ⟨v, hmemB v hv⟩ ⟨w, hmemB w hw⟩ := by
        simpa using hvw
      exact hcol hadj' (Fin.ext (by omega))

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

/-- El-Zahar–Erdős, asymmetric form: for all `t, c` there is `d` such that a `K_t`-free graph
that is not `(d-1)`-colourable has anticomplete `A, B` with `A` not 2-colourable and `B` not
`(c-1)`-colourable. -/
theorem proof :
    ∀ t c : ℕ, 1 ≤ t → 1 ≤ c →
      ∃ d : ℕ, 1 ≤ d ∧
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
          ChromaticAtLeast G d →
          G.CliqueFree t →
          ∃ A B : Finset (Fin n),
            Anticomplete G A B ∧
            ChromaticAtLeastOn G A 3 ∧
            ChromaticAtLeastOn G B c := by
  classical
  intro t c0 ht hc0
  obtain ⟨c, hc2, hcc⟩ : ∃ c, 2 ≤ c ∧ c0 ≤ c := ⟨max c0 2, le_max_right _ _, le_max_left _ _⟩
  refine ⟨2 ^ (t - 1) * (c + 5) + 1, by omega, ?_⟩
  intro n G hchi hfree
  by_contra hno
  have hno' : ∀ A B : Finset (Fin n), Anticomplete G A B → ChromaticAtLeastOn G A 3 →
      ChromaticAtLeastOn G B c → False := fun A B h1 h2 h3 =>
    hno ⟨A, B, h1, h2, fun k hk => h3 k (by omega)⟩
  apply hchi (2 ^ (t - 1) * (c + 5)) (by omega)
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
  have hT : ∀ v, ∃ T : Finset (Fin n), T ⊆ S v ∧ (T.card = 3 ∨ (T.card < 3 ∧ T = S v)) := by
    intro v
    by_cases h3 : 3 ≤ (S v).card
    · obtain ⟨T, hTs, hTc⟩ := Finset.exists_subset_card_eq h3
      exact ⟨T, hTs, Or.inl hTc⟩
    · exact ⟨S v, subset_rfl, Or.inr ⟨by omega, rfl⟩⟩
  choose T hTS hTc using hT
  have hTK : ∀ v, T v ⊆ K := fun v => (hTS v).trans (hSK v)
  let X : Finset (Fin n) → Finset (Fin n) := fun T0 => Finset.univ.filter fun v => T v = T0
  have memX : ∀ T0 v, v ∈ X T0 ↔ T v = T0 := by
    intro T0 v; simp [X]
  have hM : 0 < c + 5 := by omega
  have hcol : ∀ T0 : Finset (Fin n), ∃ f : Fin n → Fin (c + 5), T0 ⊆ K → T0.card ≤ 3 →
      ∀ v w, v ∈ X T0 → w ∈ X T0 → G.Adj v w → f v ≠ f w := by
    intro T0
    by_cases hT0 : T0 ⊆ K ∧ T0.card ≤ 3
    · obtain ⟨hsub, hcard⟩ := hT0
      by_cases hceq : T0.card = 3
      · have hnot : ¬ChromaticAtLeastOn G (X T0) ((c - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega)]
          intro hX
          apply hno' T0 (X T0) ⟨?_, ?_⟩
            (clique_chrom G T0 3 (hK.subset (by exact_mod_cast hsub)) hceq) hX
          · rw [Finset.disjoint_left]
            intro x hx hx'
            rw [memX] at hx'
            have h1 : T x ⊆ {x} := by rw [← hSself x (hsub hx)]; exact hTS x
            have h2 := Finset.card_le_card h1
            rw [hx', hceq] at h2
            simp at h2
          · intro a ha b hb hab
            rw [memX] at hb
            have : a ∈ S b := hTS b (by rw [hb]; exact ha)
            exact ((memS b a).mp this).2 hab.symm
        obtain ⟨f, hf⟩ := colouring_of_not G (X T0) (c - 1) (by omega) hnot
        have hle : c - 1 ≤ c + 5 := by omega
        exact ⟨fun v => Fin.castLE hle (f v), fun _ _ v w hv hw hvw heq =>
          hf v w hv hw hvw (Fin.castLE_injective hle heq)⟩
      · have hlt : T0.card < 3 := by omega
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
        have hfree' : G'.CliqueFree 3 := by
          intro s hs
          obtain ⟨hscl, hscard⟩ := hs
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
        by_cases hch : ChromaticAtLeast G' (c + 5)
        · exfalso
          obtain ⟨A, B, ⟨hdisj, hanti⟩, hA, hB⟩ := tf c n G' hch hfree'
          apply hno' (A.filter fun v => T v = T0) (B.filter fun v => T v = T0) ⟨?_, ?_⟩
            (transfer G G' (fun v => T v = T0) hG' 3 (by norm_num) A hA)
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
          have hle : k ≤ c + 5 := by omega
          refine ⟨fun v => Fin.castLE hle (f v), fun _ _ v w hv hw hvw heq => ?_⟩
          rw [memX] at hv hw
          exact hf ((hG' v w).mpr ⟨hvw, hv, hw⟩) (Fin.castLE_injective hle heq)
    · exact ⟨fun _ => ⟨0, hM⟩, fun h1 h2 => absurd ⟨h1, h2⟩ hT0⟩
  choose f hf using hcol
  have hTcard : ∀ v, (T v).card ≤ 3 := by
    intro v
    rcases hTc v with h | ⟨h, _⟩ <;> omega
  let P : Finset (Finset (Fin n) × ℕ) := K.powerset ×ˢ Finset.range (c + 5)
  have hmemP : ∀ v, (T v, (f (T v) v : ℕ)) ∈ P :=
    fun v => Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (hTK v), Finset.mem_range.mpr (f (T v) v).isLt⟩
  have hPcard : P.card ≤ 2 ^ (t - 1) * (c + 5) := by
    have h1 : P.card = 2 ^ K.card * (c + 5) := by
      show (K.powerset ×ˢ Finset.range (c + 5)).card = _
      rw [Finset.card_product, Finset.card_powerset, Finset.card_range]
    rw [h1]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hKt)
  have hcardP : Fintype.card P ≤ Fintype.card (Fin (2 ^ (t - 1) * (c + 5))) := by
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

end Submissions.Erdos1111OddCycleVsHighChromatic.Asymmetric
