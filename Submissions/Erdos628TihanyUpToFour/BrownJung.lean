import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic

namespace Submissions.Erdos628TihanyUpToFour.BrownJung

/-! ### Colour patterns on a shortest odd cycle of length `l` -/

/-- A proper 3-colouring of the cycle by index. -/
def h3 (l i : ℕ) : ℕ := if i + 1 = l then 2 else i % 2

/-- A colour avoided by the cycle indices `i0`, `i0 + 2`, `i0 + (l - 2)`. -/
def free3 (l i0 : ℕ) : ℕ :=
  if i0 = 1 then 0 else if i0 + 3 = l then 1 else if i0 + 1 = l then 0 else 2

theorem h3_lt (l i : ℕ) : h3 l i < 3 := by
  unfold h3; split_ifs <;> omega

theorem free3_lt (l i : ℕ) : free3 l i < 3 := by
  unfold free3; split_ifs <;> omega

theorem h3_adj {l i p : ℕ} (hl : l % 2 = 1) (h5 : 5 ≤ l) (hip : i + p < l)
    (hp : p = 1 ∨ p + 1 = l) : h3 l i ≠ h3 l (i + p) := by
  unfold h3; split_ifs <;> omega

theorem h3_free {l i p : ℕ} (hl : l % 2 = 1) (h5 : 5 ≤ l) (hip : i + p < l)
    (hp : p = 0 ∨ p = 2 ∨ p + 2 = l) : h3 l (i + p) ≠ free3 l i := by
  unfold h3 free3; split_ifs <;> omega

/-! ### Shortest odd closed walks as periodic sequences -/

theorem seg {V : Type} {G : SimpleGraph V} {c : ℕ → V}
    (hadj : ∀ k, G.Adj (c k) (c (k + 1))) (a q : ℕ) :
    ∃ W : G.Walk (c a) (c (a + q)), W.length = q := by
  induction q with
  | zero => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ q ih =>
    obtain ⟨W, hW⟩ := ih
    exact ⟨W.concat (hadj (a + q)), by rw [SimpleGraph.Walk.length_concat, hW]⟩

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

/-- A graph that is not 2-colourable has a shortest odd closed walk, presented as a periodic
sequence of vertices. -/
theorem exists_shortest_odd {V : Type} (G : SimpleGraph V) (h2 : ¬G.Colorable 2) :
    ∃ (l : ℕ) (c : ℕ → V), l % 2 = 1 ∧ (∀ k, G.Adj (c k) (c (k + 1))) ∧
      (∀ k, c (k + l) = c k) ∧
      (∀ (u : V) (w : G.Walk u u), Odd w.length → l ≤ w.length) := by
  classical
  rw [SimpleGraph.two_colorable_iff_forall_loop_even] at h2
  push_neg at h2
  obtain ⟨u0, w0, hw0⟩ := h2
  have hex : ∃ L, ∃ (u : V) (w : G.Walk u u), w.length = L ∧ Odd L :=
    ⟨w0.length, u0, w0, rfl, Nat.not_even_iff_odd.mp hw0⟩
  obtain ⟨l, hmin, u, w, hwl, hoddl⟩ :
      ∃ l, (∀ (x : V) (w' : G.Walk x x), Odd w'.length → l ≤ w'.length) ∧
        ∃ (u : V) (w : G.Walk u u), w.length = l ∧ Odd l :=
    ⟨Nat.find hex, fun x w' ho => Nat.find_min' hex ⟨x, w', rfl, ho⟩, Nat.find_spec hex⟩
  have hl2 : l % 2 = 1 := Nat.odd_iff.mp hoddl
  have hlpos : 0 < l := by omega
  refine ⟨l, fun k => w.getVert (k % l), hl2, ?_, ?_, hmin⟩
  · intro k
    have hr : k % l < l := Nat.mod_lt _ hlpos
    have hmod : (k + 1) % l = (k % l + 1) % l := (Nat.mod_add_mod k l 1).symm
    have hgl : w.getVert l = u := by rw [← hwl]; exact w.getVert_length
    show G.Adj (w.getVert (k % l)) (w.getVert ((k + 1) % l))
    rw [hmod]
    have hstep := w.adj_getVert_succ (i := k % l) (by rw [hwl]; exact hr)
    by_cases hlt : k % l + 1 < l
    · rw [Nat.mod_eq_of_lt hlt]; exact hstep
    · have he : k % l + 1 = l := by omega
      rw [he] at hstep ⊢
      rw [Nat.mod_self, w.getVert_zero]
      rwa [hgl] at hstep
  · intro k
    simp

/-- A set containing an odd closed sequence does not induce a 2-colourable graph. -/
theorem not_colorable_two_of_odd {V : Type} (G : SimpleGraph V) (S : Set V) {c : ℕ → V} {l : ℕ}
    (hodd : l % 2 = 1) (hadj : ∀ k, G.Adj (c k) (c (k + 1))) (hper : ∀ k, c (k + l) = c k)
    (hS : ∀ k, c k ∈ S) : ¬(G.induce S).Colorable 2 := by
  rintro ⟨col⟩
  let f : ℕ → ℕ := fun i => (col ⟨c i, hS i⟩ : ℕ)
  have hne : ∀ i, f i ≠ f (i + 1) := by
    intro i hEq
    have hadj' : (G.induce S).Adj ⟨c i, hS i⟩ ⟨c (i + 1), hS (i + 1)⟩ := by
      simpa using hadj i
    exact col.valid hadj' (Fin.ext hEq)
  have hlt : ∀ i, f i < 2 := fun i => (col ⟨c i, hS i⟩).isLt
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
    have hsub : (⟨c l, hS l⟩ : ↥S) = ⟨c 0, hS 0⟩ :=
      Subtype.ext (by have := hper 0; simpa using this)
    show (col ⟨c l, hS l⟩ : ℕ) = (col ⟨c 0, hS 0⟩ : ℕ)
    rw [hsub]
  obtain ⟨q, hq⟩ : ∃ q, l = 2 * q + 1 := ⟨l / 2, by omega⟩
  have h01 : f 0 ≠ f 1 := hne 0
  rw [hq, hev] at hfl
  exact h01 hfl.symm

/-- In a triangle-free graph the shortest odd closed walk has length at least 5. -/
theorem five_le {V : Type} {G : SimpleGraph V} {c : ℕ → V} {l : ℕ}
    (hfree : ∀ x y z : V, G.Adj x y → G.Adj x z → G.Adj y z → False)
    (hodd : l % 2 = 1) (hadj : ∀ k, G.Adj (c k) (c (k + 1))) (hper : ∀ k, c (k + l) = c k) :
    5 ≤ l := by
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
    exact hfree (c 0) (c 1) (c 2) a1 a3.symm a2

/-- Triangle-free and not 2-colourable: two vertex-disjoint edges. -/
theorem two_disjoint_edges {V : Type} (G : SimpleGraph V) (h2 : ¬G.Colorable 2)
    (hfree : ∀ x y z : V, G.Adj x y → G.Adj x z → G.Adj y z → False) :
    ∃ u v x y : V, G.Adj u v ∧ G.Adj x y ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v := by
  obtain ⟨l, c, hl2, hadj, hper, hmin⟩ := exists_shortest_odd G h2
  have h5 := five_le hfree hl2 hadj hper
  have hinj : ∀ a p, 0 < p → p < l → c (a + p) ≠ c a := by
    intro a p hp0 hpl heq
    have hd := detour hl2 hadj hper hmin (a := a) (p := p) (r := 0) (by omega)
      ((SimpleGraph.Walk.nil : G.Walk (c a) (c a)).copy heq.symm rfl) (by simp)
    rcases Nat.mod_two_eq_zero_or_one (p + 0) with h0 | h1
    · have := hd.2 h0; omega
    · have := hd.1 h1; omega
  exact ⟨c 0, c 1, c 2, c 3, hadj 0, hadj 2, hinj 0 2 (by omega) (by omega),
    hinj 1 1 (by omega) (by omega), hinj 0 3 (by omega) (by omega),
    hinj 1 2 (by omega) (by omega)⟩

/-- Brown–Jung: a `K₄`-free graph that is not 3-colourable has an edge `uv` whose removal
(of both ends) leaves a graph that is not 2-colourable. -/
theorem edge_and_odd_cycle {V : Type} (G : SimpleGraph V) (h3c : ¬G.Colorable 3)
    (hK4 : G.CliqueFree 4) :
    ∃ u v : V, G.Adj u v ∧ ¬(G.induce ({u, v}ᶜ : Set V)).Colorable 2 := by
  classical
  by_contra hno
  push_neg at hno
  apply h3c
  -- every edge meets every set that is not 2-colourable
  have hmeet : ∀ (S : Set V), ¬(G.induce S).Colorable 2 → ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S := by
    intro S hS u v huv
    by_contra hout
    push_neg at hout
    obtain ⟨col⟩ := hno u v huv
    apply hS
    have hsub : ∀ x : ↥S, (x : V) ∈ ({u, v}ᶜ : Set V) := by
      intro x hx
      rcases hx with h | h
      · exact hout.1 (h ▸ x.2)
      · exact hout.2 (h ▸ x.2)
    refine ⟨SimpleGraph.Coloring.mk (fun x => col ⟨x.1, hsub x⟩) ?_⟩
    intro a b hab
    have hab' : G.Adj a.1 b.1 := by simpa using hab
    exact col.valid (by simpa using hab')
  by_cases htri : ∃ x y z : V, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z
  · -- a triangle: everything else is independent and misses a triangle vertex
    obtain ⟨x, y, z, hxy, hxz, hyz⟩ := htri
    have hT : ¬(G.induce ({x, y, z} : Set V)).Colorable 2 := by
      rintro ⟨col⟩
      have mx : x ∈ ({x, y, z} : Set V) := by simp
      have my : y ∈ ({x, y, z} : Set V) := by simp
      have mz : z ∈ ({x, y, z} : Set V) := by simp
      have e1 := col.valid (show (G.induce ({x, y, z} : Set V)).Adj ⟨x, mx⟩ ⟨y, my⟩ by simpa using hxy)
      have e2 := col.valid (show (G.induce ({x, y, z} : Set V)).Adj ⟨x, mx⟩ ⟨z, mz⟩ by simpa using hxz)
      have e3 := col.valid (show (G.induce ({x, y, z} : Set V)).Adj ⟨y, my⟩ ⟨z, mz⟩ by simpa using hyz)
      have l1 := (col ⟨x, mx⟩).isLt
      have l2 := (col ⟨y, my⟩).isLt
      have l3 := (col ⟨z, mz⟩).isLt
      have n1 : (col ⟨x, mx⟩ : ℕ) ≠ col ⟨y, my⟩ := fun h => e1 (Fin.ext h)
      have n2 : (col ⟨x, mx⟩ : ℕ) ≠ col ⟨z, mz⟩ := fun h => e2 (Fin.ext h)
      have n3 : (col ⟨y, my⟩ : ℕ) ≠ col ⟨z, mz⟩ := fun h => e3 (Fin.ext h)
      omega
    have hin : ∀ u v, G.Adj u v → (u = x ∨ u = y ∨ u = z) ∨ (v = x ∨ v = y ∨ v = z) := by
      intro u v huv
      have := hmeet _ hT u v huv
      simpa using this
    have hnoK : ∀ v, G.Adj v x → G.Adj v y → G.Adj v z → False := by
      intro v hvx hvy hvz
      have hcard : ({v, x, y, z} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [G.ne_of_adj hyz]
        · simp [G.ne_of_adj hxy, G.ne_of_adj hxz]
        · simp [G.ne_of_adj hvx, G.ne_of_adj hvy, G.ne_of_adj hvz]
      refine hK4 {v, x, y, z} ⟨?_, hcard⟩
      intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl hab
        | assumption
        | (apply SimpleGraph.Adj.symm; assumption)
    let col : V → ℕ := fun v =>
      if v = x then 0 else if v = y then 1 else if v = z then 2
      else if ¬G.Adj v x then 0 else if ¬G.Adj v y then 1 else 2
    have col_lt : ∀ v, col v < 3 := by
      intro v; simp only [col]; split_ifs <;> omega
    -- colour of a vertex outside the triangle against a triangle vertex
    have hxy' := G.ne_of_adj hxy
    have hxz' := G.ne_of_adj hxz
    have hyz' := G.ne_of_adj hyz
    have cx : col x = 0 := by simp [col]
    have cy : col y = 1 := by simp [col, hxy'.symm]
    have cz : col z = 2 := by simp [col, hxz'.symm, hyz'.symm]
    have key : ∀ v w, G.Adj v w → (w = x ∨ w = y ∨ w = z) → col v ≠ col w := by
      intro v w hvw hw
      by_cases hvx : v = x
      · subst hvx
        rcases hw with rfl | rfl | rfl
        · exact absurd hvw (G.irrefl)
        · rw [cx, cy]; norm_num
        · rw [cx, cz]; norm_num
      by_cases hvy : v = y
      · subst hvy
        rcases hw with rfl | rfl | rfl
        · rw [cx, cy]; norm_num
        · exact absurd hvw (G.irrefl)
        · rw [cy, cz]; norm_num
      by_cases hvz : v = z
      · subst hvz
        rcases hw with rfl | rfl | rfl
        · rw [cx, cz]; norm_num
        · rw [cy, cz]; norm_num
        · exact absurd hvw (G.irrefl)
      have cv : col v = if ¬G.Adj v x then 0 else if ¬G.Adj v y then 1 else 2 := by
        simp only [col, if_neg hvx, if_neg hvy, if_neg hvz]
      rcases hw with rfl | rfl | rfl
      · rw [cv, cx]
        by_cases h2 : G.Adj v y
        · rw [if_neg (not_not.mpr hvw), if_neg (not_not.mpr h2)]; norm_num
        · rw [if_neg (not_not.mpr hvw), if_pos h2]; norm_num
      · rw [cv, cy]
        by_cases h1 : G.Adj v x
        · rw [if_neg (not_not.mpr h1), if_neg (not_not.mpr hvw)]; norm_num
        · rw [if_pos h1]; norm_num
      · rw [cv, cz]
        by_cases h1 : G.Adj v x
        · by_cases h2 : G.Adj v y
          · exact (hnoK v h1 h2 hvw).elim
          · rw [if_neg (not_not.mpr h1), if_pos h2]; norm_num
        · rw [if_pos h1]; norm_num
    refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨col v, col_lt v⟩) ?_⟩
    intro v w hvw heq
    have heq' : col v = col w := congrArg Fin.val heq
    rcases hin v w hvw with hv | hw
    · exact key w v hvw.symm hv heq'.symm
    · exact key v w hvw hw heq'
  · -- triangle-free
    have hfree : ∀ x y z : V, G.Adj x y → G.Adj x z → G.Adj y z → False :=
      fun x y z h1 h2 h3 => htri ⟨x, y, z, h1, h2, h3⟩
    by_cases h2 : G.Colorable 2
    · exact h2.mono (by norm_num)
    obtain ⟨l, c, hl2, hadj, hper, hmin⟩ := exists_shortest_odd G h2
    have h5 := five_le hfree hl2 hadj hper
    have hlpos : 0 < l := by omega
    let inC : V → Prop := fun v => ∃ i, i < l ∧ c i = v
    have cmem : ∀ k, inC (c k) := by
      intro k
      refine ⟨k % l, Nat.mod_lt _ hlpos, ?_⟩
      have hq : ∀ q r, c (r + q * l) = c r := by
        intro q
        induction q with
        | zero => intro r; simp
        | succ q ih => intro r; rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]
      have := hq (k / l) (k % l)
      rw [Nat.mul_comm, Nat.mod_add_div] at this
      exact this.symm
    have hC : ¬(G.induce {v | inC v}).Colorable 2 :=
      not_colorable_two_of_odd G {v | inC v} hl2 hadj hper cmem
    have hedge : ∀ u v, G.Adj u v → inC u ∨ inC v := fun u v huv => hmeet _ hC u v huv
    have F3' : ∀ i p, i + p < l → G.Adj (c i) (c (i + p)) → p = 1 ∨ p + 1 = l := by
      intro i p hip h
      have hd := detour hl2 hadj hper hmin (a := i) (p := p) (r := 1) (by omega)
        (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil) (by simp)
      rcases Nat.mod_two_eq_zero_or_one (p + 1) with h0 | h1
      · have := hd.2 h0; omega
      · have := hd.1 h1; omega
    have F1' : ∀ (m : V) i p, i + p < l → G.Adj m (c i) → G.Adj m (c (i + p)) →
        p = 0 ∨ p = 2 ∨ p + 2 = l := by
      intro m i p hip h1 h2
      have hd := detour hl2 hadj hper hmin (a := i) (p := p) (r := 2) (by omega)
        (SimpleGraph.Walk.cons h2.symm (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil)) (by simp)
      rcases Nat.mod_two_eq_zero_or_one (p + 2) with h0 | h1
      · have := hd.2 h0; omega
      · have := hd.1 h1; omega
    let inM : V → Prop := fun v => ∃ i, i < l ∧ G.Adj v (c i)
    let col : V → ℕ := fun v =>
      if hCv : inC v then h3 l (Classical.choose hCv)
      else if hM : inM v then free3 l (Nat.find hM) else 0
    have col_lt : ∀ v, col v < 3 := by
      intro v
      by_cases hCv : inC v
      · simp only [col, dif_pos hCv]; exact h3_lt _ _
      · by_cases hM : inM v
        · simp only [col, dif_neg hCv, dif_pos hM]; exact free3_lt _ _
        · simp only [col, dif_neg hCv, dif_neg hM]; norm_num
    -- an outside vertex against a cycle vertex
    have key : ∀ v w, G.Adj v w → ¬inC v → inC w → col w ≠ col v := by
      intro v w hvw hCv hCw
      obtain ⟨hj, hcj⟩ := Classical.choose_spec hCw
      have hM : inM v := ⟨_, hj, by rw [hcj]; exact hvw⟩
      obtain ⟨hi0, hadj0⟩ := Nat.find_spec hM
      have hle : Nat.find hM ≤ Classical.choose hCw :=
        Nat.find_min' hM ⟨hj, by rw [hcj]; exact hvw⟩
      obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le hle
      simp only [col, dif_pos hCw, dif_neg hCv, dif_pos hM]
      rw [hp]
      have hjl : Nat.find hM + p < l := by rw [← hp]; exact hj
      refine h3_free hl2 h5 hjl (F1' v _ p hjl hadj0 ?_)
      rw [← hp, hcj]; exact hvw
    refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨col v, col_lt v⟩) ?_⟩
    intro v w hvw heq
    have heq' : col v = col w := congrArg Fin.val heq
    by_cases hCv : inC v
    · by_cases hCw : inC w
      · obtain ⟨hi, hci⟩ := Classical.choose_spec hCv
        obtain ⟨hj, hcj⟩ := Classical.choose_spec hCw
        simp only [col, dif_pos hCv, dif_pos hCw] at heq'
        have hvw' : G.Adj (c (Classical.choose hCv)) (c (Classical.choose hCw)) := by
          rw [hci, hcj]; exact hvw
        rcases le_total (Classical.choose hCv) (Classical.choose hCw) with hij | hji
        · obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le hij
          rw [hp] at heq' hvw' hj
          exact h3_adj hl2 h5 hj (F3' _ p hj hvw') heq'
        · obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le hji
          rw [hp] at heq' hvw' hi
          exact h3_adj hl2 h5 hi (F3' _ p hi hvw'.symm) heq'.symm
      · exact key w v hvw.symm hCw hCv heq'
    · by_cases hCw : inC w
      · exact key v w hvw hCv hCw heq'.symm
      · rcases hedge v w hvw with h | h
        · exact hCv h
        · exact hCw h

/-- The Erdős–Lovász Tihany conjecture for `k ≤ 4`: the pairs `(2,2)` and `(2,3)`. -/
theorem proof :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k : ℕ),
      k ≤ 4 →
      G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
        ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → a + b = k + 1 →
          ∃ s : Set V,
            (a : ℕ∞) ≤ (G.induce s).chromaticNumber ∧
              (b : ℕ∞) ≤ (G.induce sᶜ).chromaticNumber := by
  classical
  intro V _ G k hk4 hchi hfree a b ha hb hab
  have three_le : ∀ (S : Set V), ¬(G.induce S).Colorable 2 →
      (3 : ℕ∞) ≤ (G.induce S).chromaticNumber := by
    intro S hS
    by_contra h
    have h' : (G.induce S).chromaticNumber ≤ 2 := Order.le_of_lt_add_one <| not_le.mp h
    exact hS (SimpleGraph.chromaticNumber_le_iff_colorable.mp (by exact_mod_cast h'))
  have hk : k = 3 ∨ k = 4 := by omega
  rcases hk with rfl | rfl
  · -- k = 3, a = b = 2
    have ha2 : a = 2 := by omega
    have hb2 : b = 2 := by omega
    subst ha2 hb2
    have h2 : ¬G.Colorable 2 := by
      intro hc
      have := hc.chromaticNumber_le
      rw [hchi] at this
      exact absurd this (by norm_cast)
    have htf : ∀ x y z : V, G.Adj x y → G.Adj x z → G.Adj y z → False :=
      fun x y z h1 h2 h3 => hfree {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
    obtain ⟨u, v, x, y, huv, hxy, hxu, hxv, hyu, hyv⟩ := two_disjoint_edges G h2 htf
    refine ⟨{u, v}, ?_, ?_⟩
    · have mu : u ∈ ({u, v} : Set V) := by simp
      have mv : v ∈ ({u, v} : Set V) := by simp
      exact_mod_cast SimpleGraph.two_le_chromaticNumber_of_adj
        (show (G.induce ({u, v} : Set V)).Adj ⟨u, mu⟩ ⟨v, mv⟩ by simpa using huv)
    · have mx : x ∈ ({u, v}ᶜ : Set V) := by simp [hxu, hxv]
      have my : y ∈ ({u, v}ᶜ : Set V) := by simp [hyu, hyv]
      exact_mod_cast SimpleGraph.two_le_chromaticNumber_of_adj
        (show (G.induce ({u, v}ᶜ : Set V)).Adj ⟨x, mx⟩ ⟨y, my⟩ by simpa using hxy)
  · -- k = 4
    have h3c : ¬G.Colorable 3 := by
      intro hc
      have := hc.chromaticNumber_le
      rw [hchi] at this
      exact absurd this (by norm_cast)
    obtain ⟨u, v, huv, hodd⟩ := edge_and_odd_cycle G h3c hfree
    have mu : u ∈ ({u, v} : Set V) := by simp
    have mv : v ∈ ({u, v} : Set V) := by simp
    have e2 : (2 : ℕ∞) ≤ (G.induce ({u, v} : Set V)).chromaticNumber :=
      SimpleGraph.two_le_chromaticNumber_of_adj
        (show (G.induce ({u, v} : Set V)).Adj ⟨u, mu⟩ ⟨v, mv⟩ by simpa using huv)
    have e3 := three_le _ hodd
    have hcase : (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) := by omega
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨{u, v}, by exact_mod_cast e2, by exact_mod_cast e3⟩
    · refine ⟨{u, v}ᶜ, by exact_mod_cast e3, ?_⟩
      rw [compl_compl]
      exact_mod_cast e2

end Submissions.Erdos628TihanyUpToFour.BrownJung
