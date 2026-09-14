import Init


namespace Submissions.J4P41SourceReconstruction.Proof.P41Reconstruction

def OrdinarySidon (S : Int → Prop) : Prop :=
  ∀ a b c d, S a → S b → S c → S d → a+b=c+d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

-- For fixed distinct external marks x,y, the same-sign matching of
-- their distances to a common Sidon core has at most one ordered pair.
theorem signed_match_unique (S : Int → Prop) (hs : OrdinarySidon S)
    (x y a b c d : Int) (hxy : x ≠ y)
    (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hab : x-a=y-b) (hcd : x-c=y-d) : a=c ∧ b=d := by
  have hh := hs a d c b ha hd hc hb (show a+d=c+b by omega)
  omega

-- The opposite-sign matching has at most two ordered pairs, including
-- the possible doubled-summand case.
theorem opposite_match_two (S : Int → Prop) (hs : OrdinarySidon S)
    (x y a b c d : Int)
    (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hab : x-a=b-y) (hcd : x-c=d-y) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  exact hs a b c d ha hb hc hd (by omega)

-- If both matching types occur, these three listed ordered pairs cover
-- all matches. If a type does not occur, its contribution is absent.
theorem three_match_cover (S : Int → Prop) (hs : OrdinarySidon S)
    (x y a0 b0 a1 b1 a b : Int) (hxy : x ≠ y)
    (ha0 : S a0) (hb0 : S b0) (ha1 : S a1) (hb1 : S b1)
    (ha : S a) (hb : S b)
    (h0 : x-a0=y-b0) (h1 : x-a1=b1-y)
    (hm : x-a=y-b ∨ x-a=b-y) :
    (a=a0 ∧ b=b0) ∨ (a=a1 ∧ b=b1) ∨ (a=b1 ∧ b=a1) := by
  rcases hm with hm | hm
  · exact Or.inl (signed_match_unique S hs x y a b a0 b0 hxy ha hb ha0 hb0 hm h0)
  · exact Or.inr (opposite_match_two S hs x y a b a1 b1 ha hb ha1 hb1 hm h1)

-- The combinatorial count of common-core, cross/core and internal edges
-- supplies hcommon. This lemma checks the resulting exact normalization.
theorem edit_discrepancy_bound (k r c delta : Int)
    (hdelta : delta=k*(k-1)-2*c)
    (hcommon : 2*c ≤ (k-r)*(k-r-1)+8*r*r-2*r) :
    2*k*r-9*r*r+r ≤ delta := by
  grind

theorem local_inverse_bound (k r delta : Int) (hr : 0 ≤ r)
    (hbasin : 9*r ≤ k) (hdelta : 2*k*r-9*r*r+r ≤ delta) :
    k*r ≤ delta := by
  have hh := Int.mul_nonneg hr (show 0 ≤ k-9*r by omega)
  grind

def tri (h d : Int) : Int := if d<h then h-d else 0

theorem tri_of_le (h d : Int) (hd : d ≤ h) : tri h d=h-d := by
  unfold tri
  split <;> omega

theorem tri_of_ge (h d : Int) (hd : h ≤ d) : tri h d=0 := by
  simp [tri, show ¬ d<h by omega]

theorem triangle_curvature (h d : Int) :
    tri (h+1) d - 2*tri h d + tri (h-1) d = if d=h then 1 else 0 := by
  by_cases hd : d<h
  · rw [tri_of_le (h+1) d (by omega), tri_of_le h d (by omega),
      tri_of_le (h-1) d (by omega), if_neg (show d≠h by omega)]
    omega
  · by_cases heq : d=h
    · subst d
      rw [tri_of_le (h+1) h (by omega), tri_of_le h h (by omega),
        tri_of_ge (h-1) h (by omega), if_pos rfl]
      omega
    · rw [tri_of_ge (h+1) d (by omega), tri_of_ge h d (by omega),
        tri_of_ge (h-1) d (by omega), if_neg heq]
      omega

theorem triangle_sum_curvature (h : Int) (ds : List Int) :
    (ds.map (tri (h+1))).sum - 2*(ds.map (tri h)).sum +
      (ds.map (tri (h-1))).sum = (ds.map (fun d => if d=h then 1 else 0)).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hh := triangle_curvature h d
    simp only [List.map_cons, List.sum_cons]
    omega

def windowSquare (k : Int) (ds : List Int) (h : Int) : Int :=
  k*h+2*(ds.map (tri h)).sum

theorem window_square_curvature (k h : Int) (ds : List Int) :
    windowSquare k ds (h+1)-2*windowSquare k ds h+windowSquare k ds (h-1) =
      2*(ds.map (fun d => if d=h then 1 else 0)).sum := by
  have hh := triangle_sum_curvature h ds
  unfold windowSquare
  grind


end Submissions.J4P41SourceReconstruction.Proof.P41Reconstruction

namespace Submissions.J4P41SourceReconstruction.Proof

theorem proof :
  (∀ (S : Int → Prop) (hs : P41Reconstruction.OrdinarySidon S)
    (x y a0 b0 a1 b1 a b : Int) (hxy : x ≠ y)
    (ha0 : S a0) (hb0 : S b0) (ha1 : S a1) (hb1 : S b1)
    (ha : S a) (hb : S b)
    (h0 : x-a0=y-b0) (h1 : x-a1=b1-y)
    (hm : x-a=y-b ∨ x-a=b-y),
    (a=a0 ∧ b=b0) ∨ (a=a1 ∧ b=b1) ∨ (a=b1 ∧ b=a1)) ∧
  (∀ (k r delta : Int) (hr : 0 ≤ r)
    (hbasin : 9*r ≤ k) (hdelta : 2*k*r-9*r*r+r ≤ delta),
    k*r ≤ delta) ∧
  (∀ (k h : Int) (ds : List Int),
    P41Reconstruction.windowSquare k ds (h+1)-2*P41Reconstruction.windowSquare k ds h+P41Reconstruction.windowSquare k ds (h-1) =
      2*(ds.map (fun d => if d=h then 1 else 0)).sum) :=
  ⟨@P41Reconstruction.three_match_cover, @P41Reconstruction.local_inverse_bound, @P41Reconstruction.window_square_curvature⟩

end Submissions.J4P41SourceReconstruction.Proof
