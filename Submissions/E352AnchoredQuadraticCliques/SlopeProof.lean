import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Interval
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace Submissions.E352AnchoredQuadraticCliques.SlopeProof

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

lemma floor_gap (s t : ℚ) (h : Int.floor s % 1000 = Int.floor t % 1000) :
    |s-t| < 1 ∨ 999 < |s-t| := by
  have hs := Int.floor_le s
  have ht := Int.floor_le t
  have hs' := Int.lt_floor_add_one s
  have ht' := Int.lt_floor_add_one t
  by_cases he : Int.floor s = Int.floor t
  · left
    rw [abs_lt]
    constructor <;> (rw [he] at hs hs'; linarith)
  · right
    have hd : Int.floor s + 1000 ≤ Int.floor t ∨
        Int.floor t + 1000 ≤ Int.floor s := by omega
    rcases hd with hd | hd
    · have hd' : (Int.floor s : ℚ) + 1000 ≤ Int.floor t := by exact_mod_cast hd
      rw [lt_abs]
      right
      linarith
    · have hd' : (Int.floor t : ℚ) + 1000 ≤ Int.floor s := by exact_mod_cast hd
      rw [lt_abs]
      left
      linarith

lemma scaled_gap (m u v u' v' : ℚ) (hm : 0 < m)
    (hu : 25*m ≤ u) (hu' : 25*m ≤ u')
    (huU : u ≤ 100*m) (huU' : u' ≤ 100*m)
    (h : Int.floor (1000*m*v/u) % 1000 = Int.floor (1000*m*v'/u') % 1000) :
    180*m < abs (abs (u*v'-u'*v) - 200*m) := by
  have up : 0 < u := by linarith
  have up' : 0 < u' := by linarith
  have mp : 0 < 1000*m := by positivity
  let w := u*u'/(1000*m)
  have wp : 0 < w := by dsimp [w]; positivity
  have wl : (5/8:ℚ)*m ≤ w := by
    dsimp [w]
    rw [le_div_iff₀ mp]
    have hh := mul_le_mul hu hu' (by positivity : 0 ≤ 25*m) (le_of_lt up)
    nlinarith
  have wu : w ≤ 10*m := by
    dsimp [w]
    rw [div_le_iff₀ mp]
    have hh := mul_le_mul huU huU' (le_of_lt up') (by positivity : 0 ≤ 100*m)
    nlinarith
  have ident : |u*v'-u'*v| = w * |1000*m*v/u-1000*m*v'/u'| := by
    rw [← abs_of_pos wp, ← abs_mul]
    apply abs_eq_abs.mpr
    right
    dsimp [w]
    field_simp
    ring
  rw [ident]
  rcases floor_gap _ _ h with hl | hh
  · have ht := mul_lt_mul_of_pos_left hl wp
    have hsmall : w * |1000*m*v/u-1000*m*v'/u'| < 10*m := by nlinarith
    rw [lt_abs]
    right
    linarith
  · have ht := mul_lt_mul_of_pos_left hh wp
    have hlarge : 380*m < w * |1000*m*v/u-1000*m*v'/u'| := by nlinarith
    rw [lt_abs]
    left
    linarith

abbrev Point := ℤ × ℤ

def anchors (m : ℕ) : Finset Point :=
  {(0, 0), (60 * (m : ℤ), 60 * (m : ℤ)), (60 * (m : ℤ), 0)}

def inBox (m : ℕ) (p : Point) : Prop :=
  29 * (m : ℤ) ≤ p.1 ∧ p.1 ≤ 31 * (m : ℤ) ∧
  19 * (m : ℤ) ≤ p.2 ∧ p.2 ≤ 21 * (m : ℤ)

def distSq (p q : Point) : ℤ :=
  (p.1 - q.1)^2 + (p.2 - q.2)^2

def twiceArea (a p q : Point) : ℤ :=
  |(p.1 - a.1) * (q.2 - a.2) - (q.1 - a.1) * (p.2 - a.2)|

def good (m : ℕ) (a p q : Point) : Prop :=
  180 * (m : ℤ) < |twiceArea a p q - 200 * (m : ℤ)|

noncomputable def bucket (m : ℕ) (u v : ℤ) : Fin 1000 :=
  ⟨(Int.floor (1000*(m:ℚ)*(v:ℚ)/(u:ℚ)) % 1000).toNat, by
    have := Int.emod_lt_of_pos (Int.floor (1000*(m:ℚ)*(v:ℚ)/(u:ℚ)))
      (by norm_num : (0:ℤ) < 1000)
    omega⟩

lemma bucket_eq (m : ℕ) (u v u' v' : ℤ)
    (h : bucket m u v = bucket m u' v') :
    Int.floor (1000*(m:ℚ)*(v:ℚ)/(u:ℚ)) % 1000 =
    Int.floor (1000*(m:ℚ)*(v':ℚ)/(u':ℚ)) % 1000 := by
  have hh := congrArg Fin.val h
  dsimp [bucket] at hh
  have h1 := Int.emod_nonneg (Int.floor (1000*(m:ℚ)*(v:ℚ)/(u:ℚ)))
    (by norm_num : (1000:ℤ) ≠ 0)
  have h2 := Int.emod_nonneg (Int.floor (1000*(m:ℚ)*(v':ℚ)/(u':ℚ)))
    (by norm_num : (1000:ℤ) ≠ 0)
  omega

abbrev Color := Fin 1000 × Fin 1000 × Fin 1000

noncomputable def color (m : ℕ) (p : Point) : Color :=
  (bucket m p.1 p.2,
   bucket m (60*(m:ℤ)-p.1) (60*(m:ℤ)-p.2),
   bucket m (60*(m:ℤ)-p.1) p.2)

lemma int_scaled_gap (m : ℕ) (hm : 1 ≤ m) (u v u' v' : ℤ)
    (hu : 25*(m:ℤ) ≤ u) (hu' : 25*(m:ℤ) ≤ u')
    (huU : u ≤ 100*(m:ℤ)) (huU' : u' ≤ 100*(m:ℤ))
    (h : bucket m u v = bucket m u' v') :
    180*(m:ℤ) < abs (abs (u*v'-u'*v) - 200*(m:ℤ)) := by
  have hmq : (0:ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have huq : 25*(m:ℚ) ≤ (u:ℚ) := by exact_mod_cast hu
  have huq' : 25*(m:ℚ) ≤ (u':ℚ) := by exact_mod_cast hu'
  have huqU : (u:ℚ) ≤ 100*(m:ℚ) := by exact_mod_cast huU
  have huqU' : (u':ℚ) ≤ 100*(m:ℚ) := by exact_mod_cast huU'
  have hh := scaled_gap (m:ℚ) u v u' v' hmq huq huq' huqU huqU' (bucket_eq _ _ _ _ _ h)
  exact_mod_cast hh

lemma pinned_box (m : ℕ) (hm : 1 ≤ m) (p q : Point)
    (hp : inBox m p) (hq : inBox m q) (hc : color m p = color m q) :
    ∀ a ∈ anchors m, good m a p q := by
  rcases hp with ⟨hp1, hp2, hp3, hp4⟩
  rcases hq with ⟨hq1, hq2, hq3, hq4⟩
  have hmz : (1:ℤ) ≤ m := by exact_mod_cast hm
  intro a ha
  simp only [anchors, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · have hc1 : bucket m p.1 p.2 = bucket m q.1 q.2 := congrArg Prod.fst hc
    have hh := int_scaled_gap m hm p.1 p.2 q.1 q.2
      (by omega) (by omega) (by omega) (by omega) hc1
    simpa [good, twiceArea] using hh
  · have hc2 : bucket m (60*(m:ℤ)-p.1) (60*(m:ℤ)-p.2) =
        bucket m (60*(m:ℤ)-q.1) (60*(m:ℤ)-q.2) := congrArg (fun c => c.2.1) hc
    have hh := int_scaled_gap m hm (60*(m:ℤ)-p.1) (60*(m:ℤ)-p.2)
      (60*(m:ℤ)-q.1) (60*(m:ℤ)-q.2)
      (by omega) (by omega) (by omega) (by omega) hc2
    unfold good twiceArea
    have he : (p.1-60*(m:ℤ))*(q.2-60*(m:ℤ))-(q.1-60*(m:ℤ))*(p.2-60*(m:ℤ)) =
        (60*(m:ℤ)-p.1)*(60*(m:ℤ)-q.2)-(60*(m:ℤ)-q.1)*(60*(m:ℤ)-p.2) := by ring
    simpa only [he] using hh
  · have hc3 : bucket m (60*(m:ℤ)-p.1) p.2 =
        bucket m (60*(m:ℤ)-q.1) q.2 := congrArg (fun c => c.2.2) hc
    have hh := int_scaled_gap m hm (60*(m:ℤ)-p.1) p.2
      (60*(m:ℤ)-q.1) q.2
      (by omega) (by omega) (by omega) (by omega) hc3
    unfold good twiceArea
    have he : (p.1-60*(m:ℤ))*(q.2-0)-(q.1-60*(m:ℤ))*(p.2-0) =
        -((60*(m:ℤ)-p.1)*q.2-(60*(m:ℤ)-q.1)*p.2) := by ring
    simpa only [he, abs_neg] using hh

lemma good_swap_first (m : ℕ) (a p q : Point) : good m a p q ↔ good m p a q := by
  unfold good twiceArea
  have he : (p.1-a.1)*(q.2-a.2)-(q.1-a.1)*(p.2-a.2) =
      -((a.1-p.1)*(q.2-p.2)-(q.1-p.1)*(a.2-p.2)) := by ring
  rw [he, abs_neg]

lemma good_swap_last (m : ℕ) (a p q : Point) : good m a p q ↔ good m a q p := by
  unfold good twiceArea
  have he : (p.1-a.1)*(q.2-a.2)-(q.1-a.1)*(p.2-a.2) =
      -((q.1-a.1)*(p.2-a.2)-(p.1-a.1)*(q.2-a.2)) := by ring
  rw [he, abs_neg]

lemma large_good (m : ℕ) (a p q : Point) (h : 380*(m:ℤ) < twiceArea a p q) :
    good m a p q := by
  unfold good
  exact lt_abs.mpr (Or.inl (by omega))

lemma repeat_good (m : ℕ) (hm : 1 ≤ m) (a q : Point) : good m a a q := by
  have hmz : (1:ℤ) ≤ m := by exact_mod_cast hm
  simp only [good, twiceArea, sub_self, zero_mul, mul_zero, abs_zero,
    zero_sub, abs_neg]
  rw [abs_of_nonneg (by positivity : 0 ≤ 200*(m:ℤ))]
  omega

lemma two_anchor_box (m : ℕ) (hm : 1 ≤ m) (q : Point) (hq : inBox m q) :
    ∀ a ∈ anchors m, ∀ b ∈ anchors m, good m a b q := by
  rcases hq with ⟨h1,h2,h3,h4⟩
  have hmz : (1:ℤ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℤ) ≤ m := by omega
  have mm : (m:ℤ) ≤ (m:ℤ)^2 := by nlinarith
  have hh1 := mul_nonneg hm0 (show 0 ≤ q.1-q.2-8*(m:ℤ) by omega)
  have hh2 := mul_nonneg hm0 (show 0 ≤ q.2-19*(m:ℤ) by omega)
  have hh3 := mul_nonneg hm0 (show 0 ≤ 31*(m:ℤ)-q.1 by omega)
  have ab : good m (0,0) (60*(m:ℤ),60*(m:ℤ)) q := by
    apply large_good
    unfold twiceArea
    simp only [sub_zero]
    apply lt_abs.mpr
    right
    nlinarith
  have ah : good m (0,0) (60*(m:ℤ),0) q := by
    apply large_good
    unfold twiceArea
    simp only [sub_zero, mul_zero]
    apply lt_abs.mpr
    left
    nlinarith
  have bh : good m (60*(m:ℤ),60*(m:ℤ)) (60*(m:ℤ),0) q := by
    apply large_good
    unfold twiceArea
    simp only [sub_self, zero_mul, zero_sub]
    apply lt_abs.mpr
    right
    nlinarith
  intro a ha b hb
  simp only [anchors, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact repeat_good m hm _ _
  · exact ab
  · exact ah
  · exact (good_swap_first _ _ _ _).mp ab
  · exact repeat_good m hm _ _
  · exact bh
  · exact (good_swap_first _ _ _ _).mp ah
  · exact (good_swap_first _ _ _ _).mp bh
  · exact repeat_good m hm _ _

lemma three_anchors (m : ℕ) (hm : 1 ≤ m) :
    ∀ a ∈ anchors m, ∀ b ∈ anchors m, ∀ c ∈ anchors m, good m a b c := by
  have hmz : (1:ℤ) ≤ m := by exact_mod_cast hm
  have mm : (m:ℤ) ≤ (m:ℤ)^2 := by nlinarith
  intro a ha b hb c hc
  simp only [anchors, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    norm_num [good, twiceArea, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ m)] <;>
    first | omega | (apply lt_abs.mpr; left; nlinarith)

def inSquare (m : ℕ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 60*(m:ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ 60*(m:ℤ)

lemma square_of_box (m : ℕ) (p : Point) (h : inBox m p) : inSquare m p := by
  rcases h with ⟨h1,h2,h3,h4⟩
  have : (0:ℤ) ≤ m := by positivity
  unfold inSquare
  omega

lemma square_of_anchor (m : ℕ) (p : Point) (h : p ∈ anchors m) : inSquare m p := by
  simp only [anchors, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl <;> simp [inSquare]

lemma square_dist (m : ℕ) (p q : Point) (hp : inSquare m p) (hq : inSquare m q) :
    distSq p q ≤ 7200*(m:ℤ)^2 := by
  rcases hp with ⟨hp1,hp2,hp3,hp4⟩
  rcases hq with ⟨hq1,hq2,hq3,hq4⟩
  have hx := mul_nonneg (show 0 ≤ 60*(m:ℤ)-(p.1-q.1) by omega)
    (show 0 ≤ 60*(m:ℤ)+(p.1-q.1) by omega)
  have hy := mul_nonneg (show 0 ≤ 60*(m:ℤ)-(p.2-q.2) by omega)
    (show 0 ≤ 60*(m:ℤ)+(p.2-q.2) by omega)
  unfold distSq
  nlinarith

noncomputable def box (m : ℕ) : Finset Point :=
  (Finset.Icc (29*(m:ℤ)) (31*(m:ℤ))).product
    (Finset.Icc (19*(m:ℤ)) (21*(m:ℤ)))

lemma mem_box (m : ℕ) (p : Point) : p ∈ box m ↔ inBox m p := by
  simp [box, inBox, and_assoc]

lemma card_box (m : ℕ) : (box m).card = (2*m+1)^2 := by
  have hx : 31*(m:ℤ)+1-29*(m:ℤ) = ((2*m+1:ℕ):ℤ) := by omega
  have hy : 21*(m:ℤ)+1-19*(m:ℤ) = ((2*m+1:ℕ):ℤ) := by omega
  unfold box
  rw [Finset.product_eq_sprod, Finset.card_product, Int.card_Icc, Int.card_Icc, hx, hy]
  simp only [Int.toNat_natCast]
  ring

lemma pigeon {α β : Type*} [Fintype β] [Nonempty β]
    (T : Finset α) (f : α → β) : ∃ S : Finset α,
    S ⊆ T ∧ T.card ≤ Fintype.card β*S.card ∧
    (∀ p ∈ S, ∀ q ∈ S, f p = f q) := by
  classical
  have hn : (0:ℚ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hb : (Finset.univ : Finset β).card • (T.card / (Fintype.card β:ℚ)) ≤
      (T.card:ℚ) := by
    rw [Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hn)]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (M := ℚ) (b := T.card / (Fintype.card β:ℚ))
    (s := T) (t := (Finset.univ : Finset β)) (f := f)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty hb
  let S := T.filter (fun p => f p = c)
  refine ⟨S, ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _
  · have hc' : (T.card:ℚ) ≤ (Fintype.card β:ℚ)*(S.card:ℚ) := by
      have hh := (div_le_iff₀ hn).mp hc
      simpa only [mul_comm] using hh
    exact_mod_cast hc'
  · intro p hp q hq
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm

lemma large_color_class (m : ℕ) : ∃ S : Finset Point,
    (∀ p ∈ S, inBox m p) ∧ (2*m+1)^2 ≤ 1000000000*S.card ∧
    (∀ p ∈ S, ∀ q ∈ S, color m p = color m q) := by
  obtain ⟨S,hsub,hcard,hcolor⟩ := pigeon (box m) (color m)
  refine ⟨S, ?_, ?_, hcolor⟩
  · intro p hp
    exact (mem_box m p).mp (hsub hp)
  · simpa [card_box, Color] using hcard

theorem proof :
  ∀ m : ℕ, 1 ≤ m → ∃ S : Finset Point,
    (∀ p ∈ S, inBox m p) ∧
    (2 * m + 1)^2 ≤ 1000000000 * S.card ∧
    (∀ p ∈ S ∪ anchors m, ∀ q ∈ S ∪ anchors m,
      distSq p q ≤ 7200 * (m : ℤ)^2) ∧
    (∀ a ∈ anchors m, ∀ p ∈ S ∪ anchors m, ∀ q ∈ S ∪ anchors m,
      180 * (m : ℤ) < |twiceArea a p q - 200 * (m : ℤ)|) := by
  intro m hm
  obtain ⟨S,hbox,hcard,hcolor⟩ := large_color_class m
  refine ⟨S,hbox,hcard,?_,?_⟩
  · have hs : ∀ p ∈ S ∪ anchors m, inSquare m p := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact square_of_box m p (hbox p hp)
      · exact square_of_anchor m p hp
    intro p hp q hq
    exact square_dist m p q (hs p hp) (hs q hq)
  · intro a ha p hp q hq
    change good m a p q
    rcases Finset.mem_union.mp hp with hp | hp <;>
      rcases Finset.mem_union.mp hq with hq | hq
    · exact pinned_box m hm p q (hbox p hp) (hbox q hq) (hcolor p hp q hq) a ha
    · exact (good_swap_last _ _ _ _).mpr (two_anchor_box m hm p (hbox p hp) a ha q hq)
    · exact two_anchor_box m hm q (hbox q hq) a ha p hp
    · exact three_anchors m hm a ha p hp q hq

end Submissions.E352AnchoredQuadraticCliques.SlopeProof
