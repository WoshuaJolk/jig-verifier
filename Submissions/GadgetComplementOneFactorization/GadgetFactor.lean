/-
  GadgetComplementOneFactorization: the complement of c disjoint copies of the
  gadget graph G_k in K_{2kc} has an explicit 1-factorization into 2kc - k - 1
  factors, for all k ≥ 2, c ≥ 1.

  Construction:
  * Half 1 (k-1 factors): within each copy, K_{k,k} minus a perfect matching is
    1-factorized by shifts d = 1, ..., k-1 in ZMod k.
  * Half 2 ((2c-2)·k factors): a round-robin 1-factorization of K_{2c} on the
    super-vertices (copy, side), labeled by Option (ZMod (2c-1)); each round-robin
    factor is refined by a shift β in ZMod k using an orientation of its edges.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

namespace Submissions.GadgetComplementOneFactorization.GadgetFactor

/-- Vertices: a copy, a side, and a position. -/
abbrev V (c k : ℕ) : Type := Fin c × Fin 2 × Fin k

/-- `K_m` minus the degenerate class. -/
def compl (c k : ℕ) : SimpleGraph (V c k) :=
  SimpleGraph.fromRel fun v w =>
    v.1 ≠ w.1 ∨ (v.1 = w.1 ∧ v.2.1 ≠ w.2.1 ∧ v.2.2 ≠ w.2.2)

/-- The adjacency of `compl` in usable form. -/
lemma adj_iff {c k : ℕ} (v w : V c k) :
    (compl c k).Adj v w ↔ (v.1 ≠ w.1 ∨ (v.2.1 ≠ w.2.1 ∧ v.2.2 ≠ w.2.2)) := by
  rw [compl, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with h1 | ⟨_, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h2, h3⟩
    · rcases h with h1 | ⟨_, h2, h3⟩
      · exact Or.inl (Ne.symm h1)
      · exact Or.inr ⟨Ne.symm h2, Ne.symm h3⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h with h1 | ⟨h2, _⟩
      · exact fun he => h1 (congrArg Prod.fst he)
      · exact fun he => h2 (congrArg (fun x => x.2.1) he)
    · rcases h with h1 | ⟨h2, h3⟩
      · exact Or.inl (Or.inl h1)
      · by_cases hcc : v.1 = w.1
        · exact Or.inl (Or.inr ⟨hcc, h2, h3⟩)
        · exact Or.inl (Or.inl hcc)

/-! ### Core: round-robin partner map on `Option (ZMod (2c-1))` -/

section Core

variable {c : ℕ}

/-- Round-robin partner map for round `a` on labels `Option (ZMod (2c-1))`. -/
def pim (a : ZMod (2 * c - 1)) : Option (ZMod (2 * c - 1)) → Option (ZMod (2 * c - 1))
  | none => some a
  | some x => if x = a then none else some (2 * a - x)

/-- (F0) `2 * c = 1` in `ZMod (2c-1)`. -/
lemma two_mul_c (hc : 1 ≤ c) : (2 : ZMod (2 * c - 1)) * (c : ZMod (2 * c - 1)) = 1 := by
  have he : 2 * c = (2 * c - 1) + 1 := by omega
  calc (2 : ZMod (2 * c - 1)) * (c : ZMod (2 * c - 1))
      = ((2 * c : ℕ) : ZMod (2 * c - 1)) := by push_cast; ring
    _ = (((2 * c - 1) + 1 : ℕ) : ZMod (2 * c - 1)) := by rw [← he]
    _ = 1 := by rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]

/-- Cancellation of 2 in `ZMod (2c-1)`. -/
lemma two_cancel (hc : 1 ≤ c) {x y : ZMod (2 * c - 1)} (h : 2 * x = 2 * y) : x = y := by
  have h1 := two_mul_c hc
  calc x = ((2 : ZMod (2 * c - 1)) * c) * x := by rw [h1, one_mul]
    _ = (c : ZMod (2 * c - 1)) * (2 * x) := by ring
    _ = (c : ZMod (2 * c - 1)) * (2 * y) := by rw [h]
    _ = ((2 : ZMod (2 * c - 1)) * c) * y := by ring
    _ = y := by rw [h1, one_mul]

/-- (F1) `pim a` is an involution. -/
lemma pim_invol (a : ZMod (2 * c - 1)) (P : Option (ZMod (2 * c - 1))) :
    pim a (pim a P) = P := by
  match P with
  | none =>
    simp [pim]
  | some x =>
    by_cases hx : x = a
    · simp [pim, hx]
    · have hne : 2 * a - x ≠ a := by
        intro h
        apply hx
        have h' : a = x := by linear_combination h
        exact h'.symm
      simp only [pim, if_neg hx, if_neg hne]
      congr 1
      ring

/-- (F2) `pim a` has no fixed point. -/
lemma pim_ne (hc : 1 ≤ c) (a : ZMod (2 * c - 1)) (P : Option (ZMod (2 * c - 1))) :
    pim a P ≠ P := by
  match P with
  | none => simp [pim]
  | some x =>
    by_cases hx : x = a
    · simp [pim, hx]
    · simp only [pim, if_neg hx, ne_eq, Option.some.injEq]
      intro h
      apply hx
      apply two_cancel hc
      linear_combination -h

/-- (F3, uniqueness) the round `a` is determined by one matched pair. -/
lemma pim_arg_inj (hc : 1 ≤ c) {a b : ZMod (2 * c - 1)}
    (X : Option (ZMod (2 * c - 1))) (h : pim a X = pim b X) : a = b := by
  match X with
  | none => simpa [pim] using h
  | some x =>
    by_cases hxa : x = a <;> by_cases hxb : x = b
    · rw [← hxa, ← hxb]
    · rw [pim, pim, if_pos hxa, if_neg hxb] at h
      exact absurd h (by simp)
    · rw [pim, pim, if_neg hxa, if_pos hxb] at h
      exact absurd h (by simp)
    · rw [pim, pim, if_neg hxa, if_neg hxb, Option.some.injEq] at h
      apply two_cancel hc
      linear_combination h

/-- (F3, existence) a round matching `X` to `Y`. -/
def solveA : Option (ZMod (2 * c - 1)) → Option (ZMod (2 * c - 1)) → ZMod (2 * c - 1)
  | none, some y => y
  | some x, none => x
  | some x, some y => (c : ZMod (2 * c - 1)) * (x + y)
  | none, none => 0

lemma pim_solveA (hc : 1 ≤ c) {X Y : Option (ZMod (2 * c - 1))} (hXY : X ≠ Y) :
    pim (solveA X Y) X = Y := by
  match X, Y with
  | none, none => exact absurd rfl hXY
  | none, some y => simp [pim, solveA]
  | some x, none => simp [pim, solveA]
  | some x, some y =>
    have hxy : x ≠ y := by
      intro h; exact hXY (by rw [h])
    have h2 : 2 * ((c : ZMod (2 * c - 1)) * (x + y)) = x + y := by
      calc 2 * ((c : ZMod (2 * c - 1)) * (x + y))
          = ((2 : ZMod (2 * c - 1)) * c) * (x + y) := by ring
        _ = x + y := by rw [two_mul_c hc, one_mul]
    have hxa : x ≠ (c : ZMod (2 * c - 1)) * (x + y) := by
      intro h
      apply hxy
      have h3 : 2 * x = x + y := by
        calc 2 * x = 2 * ((c : ZMod (2 * c - 1)) * (x + y)) := by rw [← h]
          _ = x + y := h2
      linear_combination h3
    rw [show solveA (some x) (some y) = (c : ZMod (2 * c - 1)) * (x + y) from rfl]
    simp only [pim]
    rw [if_neg hxa]
    congr 1
    linear_combination h2

/-- (F4) orientation of the round-`a` matching. -/
def orient (a : ZMod (2 * c - 1)) : Option (ZMod (2 * c - 1)) → Bool
  | none => false
  | some x => if x = a then true else decide (c ≤ (x - a).val)

/-- (F4) flip law: the partner has the opposite orientation. -/
lemma orient_pim (hc : 1 ≤ c) (a : ZMod (2 * c - 1)) (P : Option (ZMod (2 * c - 1))) :
    orient a (pim a P) = ! orient a P := by
  have : NeZero (2 * c - 1) := ⟨by omega⟩
  match P with
  | none => simp [pim, orient]
  | some x =>
    by_cases hx : x = a
    · simp [pim, orient, hx]
    · have hne : 2 * a - x ≠ a := by
        intro h
        apply hx
        have h' : a = x := by linear_combination h
        exact h'.symm
      simp only [pim, orient, if_neg hx, if_neg hne]
      have hz : x - a ≠ 0 := sub_ne_zero_of_ne hx
      have hz' : (2 * a - x) - a = -(x - a) := by ring
      rw [hz', ZMod.neg_val, if_neg hz]
      have hv1 : 1 ≤ (x - a).val := by
        rcases Nat.eq_zero_or_pos (x - a).val with h0 | h0
        · exact absurd ((ZMod.val_eq_zero _).mp h0) hz
        · exact h0
      have hv2 : (x - a).val < 2 * c - 1 := ZMod.val_lt _
      rw [← decide_not]
      apply decide_eq_decide.mpr
      omega

end Core

/-! ### Sides: `Fin 2` helpers -/

/-- The side flip. -/
def flip2 (s : Fin 2) : Fin 2 := ⟨1 - s.val, by omega⟩

lemma flip2_flip2 (s : Fin 2) : flip2 (flip2 s) = s := by
  have hs := s.isLt
  apply Fin.ext
  show 1 - (1 - s.val) = s.val
  omega

lemma flip2_ne (s : Fin 2) : flip2 s ≠ s := by
  intro h
  have hv := congrArg Fin.val h
  have hs := s.isLt
  simp only [flip2] at hv
  omega

lemma fin2_eq_or_flip (s s' : Fin 2) : s' = s ∨ s' = flip2 s := by
  have h1 := s.isLt
  have h2 := s'.isLt
  by_cases h : s'.val = s.val
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (show s'.val = 1 - s.val by omega))

/-- The side as a Boolean direction. -/
def sideBool (s : Fin 2) : Bool := decide (s.val = 1)

lemma sideBool_flip2 (s : Fin 2) : sideBool (flip2 s) = ! sideBool s := by
  have hs := s.isLt
  by_cases h : s.val = 1
  · simp [sideBool, flip2, h]
  · have h0 : s.val = 0 := by omega
    simp [sideBool, flip2, h0]

/-! ### The label bijection `Fin c × Fin 2 ≃ Option (ZMod (2c-1))` -/

section Lab

variable {c : ℕ}

/-- The labeling of super-vertices (copy, side) by round-robin labels. -/
def lab (P : Fin c × Fin 2) : Option (ZMod (2 * c - 1)) :=
  if P.2.val = 0 then
    (if P.1.val = 0 then none else some ((P.1.val : ℕ) : ZMod (2 * c - 1)))
  else some (-((P.1.val : ℕ) : ZMod (2 * c - 1)))

/-- The inverse labeling. -/
def labInv (hc : 1 ≤ c) (Q : Option (ZMod (2 * c - 1))) : Fin c × Fin 2 :=
  match Q with
  | none => (⟨0, hc⟩, ⟨0, by omega⟩)
  | some x =>
    if h : x.val < c then
      (⟨x.val, h⟩, if x = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩)
    else
      (⟨2 * c - 1 - x.val, by omega⟩, ⟨1, by omega⟩)

lemma copy_val_lt (hc : 1 ≤ c) (u : Fin c) : u.val < 2 * c - 1 := by
  have := u.isLt
  omega

lemma cast_copy_val (hc : 1 ≤ c) (u : Fin c) :
    ((u.val : ℕ) : ZMod (2 * c - 1)).val = u.val :=
  ZMod.val_cast_of_lt (copy_val_lt hc u)

lemma cast_copy_ne_zero (hc : 1 ≤ c) {u : Fin c} (hu : u.val ≠ 0) :
    ((u.val : ℕ) : ZMod (2 * c - 1)) ≠ 0 := by
  intro h
  apply hu
  rw [← cast_copy_val hc u]
  exact (ZMod.val_eq_zero _).mpr h

/-! Evaluation lemmas for `lab`, `labInv`, `pim`. -/

lemma lab_s0_u0 {u : Fin c} {s : Fin 2} (hs : s.val = 0) (hu : u.val = 0) :
    lab (u, s) = none := by
  simp only [lab]
  rw [if_pos hs, if_pos hu]

lemma lab_s0_u1 {u : Fin c} {s : Fin 2} (hs : s.val = 0) (hu : u.val ≠ 0) :
    lab (u, s) = some ((u.val : ℕ) : ZMod (2 * c - 1)) := by
  simp only [lab]
  rw [if_pos hs, if_neg hu]

lemma lab_s1 {u : Fin c} {s : Fin 2} (hs : s.val ≠ 0) :
    lab (u, s) = some (-((u.val : ℕ) : ZMod (2 * c - 1))) := by
  simp only [lab]
  rw [if_neg hs]

lemma pim_none (a : ZMod (2 * c - 1)) : pim a none = some a := rfl

lemma pim_some_eq {a x : ZMod (2 * c - 1)} (h : x = a) : pim a (some x) = none := by
  simp only [pim]
  rw [if_pos h]

lemma pim_some_ne {a x : ZMod (2 * c - 1)} (h : x ≠ a) :
    pim a (some x) = some (2 * a - x) := by
  simp only [pim]
  rw [if_neg h]

lemma labInv_none (hc : 1 ≤ c) : labInv hc none = (⟨0, hc⟩, ⟨0, by omega⟩) := rfl

lemma labInv_some_lt (hc : 1 ≤ c) {x : ZMod (2 * c - 1)} (h : x.val < c) (hx : x ≠ 0) :
    labInv hc (some x) = (⟨x.val, h⟩, ⟨0, by omega⟩) := by
  simp only [labInv]
  rw [dif_pos h, if_neg hx]

lemma labInv_some_zero (hc : 1 ≤ c) :
    labInv hc (some (0 : ZMod (2 * c - 1))) = (⟨0, hc⟩, ⟨1, by omega⟩) := by
  have hv : (0 : ZMod (2 * c - 1)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
  have h0 : (0 : ZMod (2 * c - 1)).val < c := by omega
  simp only [labInv]
  rw [dif_pos h0]
  simp only [if_true]
  refine congrArg₂ Prod.mk (Fin.ext ?_) rfl
  exact hv

lemma labInv_some_ge (hc : 1 ≤ c) {x : ZMod (2 * c - 1)} (h : ¬ x.val < c) :
    labInv hc (some x) = (⟨2 * c - 1 - x.val, by omega⟩, ⟨1, by omega⟩) := by
  simp only [labInv]
  rw [dif_neg h]

/-! Round trips. -/

lemma labInv_lab (hc : 1 ≤ c) (P : Fin c × Fin 2) :
    labInv hc (lab P) = P := by
  have hnz : NeZero (2 * c - 1) := ⟨by omega⟩
  obtain ⟨u, s⟩ := P
  have hs2 := s.isLt
  by_cases hs0 : s.val = 0
  · by_cases hu0 : u.val = 0
    · rw [lab_s0_u0 hs0 hu0, labInv_none hc]
      exact congrArg₂ Prod.mk (Fin.ext (by simpa using hu0.symm))
        (Fin.ext (by simpa using hs0.symm))
    · rw [lab_s0_u1 hs0 hu0]
      have hval : ((u.val : ℕ) : ZMod (2 * c - 1)).val = u.val := cast_copy_val hc u
      have hlt : ((u.val : ℕ) : ZMod (2 * c - 1)).val < c := by
        rw [hval]; exact u.isLt
      rw [labInv_some_lt hc hlt (cast_copy_ne_zero hc hu0)]
      exact congrArg₂ Prod.mk (Fin.ext (by simpa using hval))
        (Fin.ext (by simpa using hs0.symm))
  · by_cases hu0 : u.val = 0
    · have hcast : ((u.val : ℕ) : ZMod (2 * c - 1)) = 0 := by
        rw [hu0]; exact Nat.cast_zero
      rw [lab_s1 hs0, hcast, neg_zero, labInv_some_zero hc]
      exact congrArg₂ Prod.mk (Fin.ext (by simpa using hu0.symm))
        (Fin.ext (by simpa using (show s.val = 1 by omega).symm))
    · rw [lab_s1 hs0]
      have hval : ((u.val : ℕ) : ZMod (2 * c - 1)).val = u.val := cast_copy_val hc u
      have hnegval : (-((u.val : ℕ) : ZMod (2 * c - 1))).val = 2 * c - 1 - u.val := by
        rw [ZMod.neg_val, if_neg (cast_copy_ne_zero hc hu0), hval]
      have hnlt : ¬ (-((u.val : ℕ) : ZMod (2 * c - 1))).val < c := by
        rw [hnegval]
        have := u.isLt
        omega
      rw [labInv_some_ge hc hnlt]
      refine congrArg₂ Prod.mk (Fin.ext ?_) (Fin.ext (by simpa using (show s.val = 1 by omega).symm))
      show 2 * c - 1 - (-((u.val : ℕ) : ZMod (2 * c - 1))).val = u.val
      rw [hnegval]
      have := u.isLt
      omega

lemma lab_inj (hc : 1 ≤ c) {P P' : Fin c × Fin 2} (h : lab P = lab P') : P = P' := by
  rw [← labInv_lab hc P, ← labInv_lab hc P', h]

lemma lab_labInv (hc : 1 ≤ c) (Q : Option (ZMod (2 * c - 1))) :
    lab (labInv hc Q) = Q := by
  have hnz : NeZero (2 * c - 1) := ⟨by omega⟩
  have hbij : Function.Bijective (lab (c := c)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun P P' h => lab_inj hc h, ?_⟩
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_option, ZMod.card]
    omega
  obtain ⟨P, hP⟩ := hbij.2 Q
  rw [← hP, labInv_lab hc]

/-- Crux: the round-0 partner of a label is the label of the *same copy*, other side. -/
lemma pim_zero_lab (hc : 1 ≤ c) (u : Fin c) (s : Fin 2) :
    pim 0 (lab (u, s)) = lab (u, flip2 s) := by
  have hs2 := s.isLt
  by_cases hs0 : s.val = 0
  · have hflip : (flip2 s).val ≠ 0 := by simp only [flip2]; omega
    by_cases hu0 : u.val = 0
    · rw [lab_s0_u0 hs0 hu0, lab_s1 hflip, pim_none]
      have hcast : ((u.val : ℕ) : ZMod (2 * c - 1)) = 0 := by
        rw [hu0]; exact Nat.cast_zero
      rw [hcast, neg_zero]
    · have hx0 : ((u.val : ℕ) : ZMod (2 * c - 1)) ≠ 0 := cast_copy_ne_zero hc hu0
      rw [lab_s0_u1 hs0 hu0, lab_s1 hflip, pim_some_ne hx0]
      congr 1
      ring
  · have hflip0 : (flip2 s).val = 0 := by simp only [flip2]; omega
    by_cases hu0 : u.val = 0
    · have hcast : ((u.val : ℕ) : ZMod (2 * c - 1)) = 0 := by
        rw [hu0]; exact Nat.cast_zero
      rw [lab_s1 hs0, hcast, neg_zero, lab_s0_u0 hflip0 hu0, pim_some_eq rfl]
    · have hx0 : ((u.val : ℕ) : ZMod (2 * c - 1)) ≠ 0 := cast_copy_ne_zero hc hu0
      have hnx0 : -((u.val : ℕ) : ZMod (2 * c - 1)) ≠ 0 := by simpa using hx0
      rw [lab_s1 hs0, lab_s0_u1 hflip0 hu0, pim_some_ne hnx0]
      congr 1
      ring

/-- For a nonzero round, the partner super-vertex lies in a different copy. -/
lemma cross_copy_ne (hc : 1 ≤ c) {a : ZMod (2 * c - 1)} (ha : a ≠ 0)
    (u : Fin c) (s : Fin 2) :
    (labInv hc (pim a (lab (u, s)))).1 ≠ u := by
  intro hEq
  have hlabP' : lab (labInv hc (pim a (lab (u, s)))) = pim a (lab (u, s)) :=
    lab_labInv hc _
  have hP'eq : labInv hc (pim a (lab (u, s)))
      = (u, (labInv hc (pim a (lab (u, s)))).2) := by
    exact Prod.ext hEq rfl
  rcases fin2_eq_or_flip s (labInv hc (pim a (lab (u, s)))).2 with h1 | h1
  · have hcontra : pim a (lab (u, s)) = lab (u, s) := by
      rw [← hlabP', hP'eq, h1]
    exact pim_ne hc a _ hcontra
  · have hcontra : pim a (lab (u, s)) = pim 0 (lab (u, s)) := by
      rw [← hlabP', hP'eq, h1, ← pim_zero_lab hc]
    exact ha (pim_arg_inj hc _ hcontra)

/-- Coverage: for distinct copies there is a nonzero round matching the labels. -/
lemma cross_exists (hc : 1 ≤ c) {u u' : Fin c} (hne : u ≠ u') (s s' : Fin 2) :
    ∃ a : ZMod (2 * c - 1), a ≠ 0 ∧ pim a (lab (u, s)) = lab (u', s') := by
  have hXY : lab (u, s) ≠ lab (u', s') := by
    intro h
    exact hne (congrArg Prod.fst (lab_inj hc h))
  refine ⟨solveA (lab (u, s)) (lab (u', s')), ?_, pim_solveA hc hXY⟩
  intro h0
  have h1 : lab (u', s') = lab (u, flip2 s) := by
    rw [← pim_zero_lab hc, ← h0, pim_solveA hc hXY]
  exact hne (congrArg Prod.fst (lab_inj hc h1)).symm

end Lab

/-! ### Positions: shifts in `ZMod k` -/

section Pos

variable {k : ℕ}

/-- Convert `ZMod k` back to `Fin k`. -/
def toF (hk : 0 < k) (z : ZMod k) : Fin k :=
  ⟨z.val, by have : NeZero k := ⟨by omega⟩; exact ZMod.val_lt z⟩

lemma toF_val_cast (hk : 0 < k) (i : Fin k) : toF hk ((i.val : ℕ) : ZMod k) = i :=
  Fin.ext (ZMod.val_cast_of_lt i.isLt)

lemma cast_toF (hk : 0 < k) (z : ZMod k) : (((toF hk z).val : ℕ) : ZMod k) = z := by
  have : NeZero k := ⟨by omega⟩
  exact ZMod.natCast_zmod_val z

lemma toF_inj (hk : 0 < k) {z z' : ZMod k} (h : toF hk z = toF hk z') : z = z' := by
  rw [← cast_toF hk z, ← cast_toF hk z', h]

/-- Shift a position by `β`, in the direction given by `b`. -/
def move (hk : 0 < k) : Bool → ZMod k → Fin k → Fin k
  | false, β, i => toF hk ((i.val : ZMod k) + β)
  | true, β, i => toF hk ((i.val : ZMod k) - β)

lemma move_move (hk : 0 < k) (b : Bool) (β : ZMod k) (i : Fin k) :
    move hk (!b) β (move hk b β i) = i := by
  cases b
  · show toF hk (((toF hk ((i.val : ZMod k) + β)).val : ZMod k) - β) = i
    rw [cast_toF, show ((i.val : ZMod k) + β) - β = ((i.val : ℕ) : ZMod k) from by ring,
      toF_val_cast]
  · show toF hk (((toF hk ((i.val : ZMod k) - β)).val : ZMod k) + β) = i
    rw [cast_toF, show ((i.val : ZMod k) - β) + β = ((i.val : ℕ) : ZMod k) from by ring,
      toF_val_cast]

lemma move_ne (hk : 0 < k) {β : ZMod k} (hβ : β ≠ 0) (b : Bool) (i : Fin k) :
    move hk b β i ≠ i := by
  intro h
  apply hβ
  cases b
  · have h' : toF hk ((i.val : ZMod k) + β) = toF hk ((i.val : ℕ) : ZMod k) := by
      rw [toF_val_cast]; exact h
    have := toF_inj hk h'
    linear_combination this
  · have h' : toF hk ((i.val : ZMod k) - β) = toF hk ((i.val : ℕ) : ZMod k) := by
      rw [toF_val_cast]; exact h
    have := toF_inj hk h'
    linear_combination -this

lemma move_inj (hk : 0 < k) (b : Bool) {β β' : ZMod k} (i : Fin k)
    (h : move hk b β i = move hk b β' i) : β = β' := by
  cases b
  · have := toF_inj hk (z := (i.val : ZMod k) + β) (z' := (i.val : ZMod k) + β') h
    linear_combination this
  · have := toF_inj hk (z := (i.val : ZMod k) - β) (z' := (i.val : ZMod k) - β') h
    linear_combination -this

/-- The shift needed to move `i` to `j` in direction `b`. -/
def moveSolve (b : Bool) (i j : Fin k) : ZMod k :=
  if b then (i.val : ZMod k) - (j.val : ZMod k) else (j.val : ZMod k) - (i.val : ZMod k)

lemma move_moveSolve (hk : 0 < k) (b : Bool) (i j : Fin k) :
    move hk b (moveSolve b i j) i = j := by
  cases b
  · show toF hk ((i.val : ZMod k) + ((j.val : ZMod k) - (i.val : ZMod k))) = j
    rw [show (i.val : ZMod k) + ((j.val : ZMod k) - (i.val : ZMod k))
        = ((j.val : ℕ) : ZMod k) from by ring, toF_val_cast]
  · show toF hk ((i.val : ZMod k) - ((i.val : ZMod k) - (j.val : ZMod k))) = j
    rw [show (i.val : ZMod k) - ((i.val : ZMod k) - (j.val : ZMod k))
        = ((j.val : ℕ) : ZMod k) from by ring, toF_val_cast]

lemma moveSolve_ne_zero (hk : 0 < k) (b : Bool) {i j : Fin k} (hij : i ≠ j) :
    moveSolve b i j ≠ 0 := by
  have hcast : ((i.val : ℕ) : ZMod k) ≠ ((j.val : ℕ) : ZMod k) := by
    intro h
    exact hij (by rw [← toF_val_cast hk i, ← toF_val_cast hk j, h])
  cases b
  · show (j.val : ZMod k) - (i.val : ZMod k) ≠ 0
    exact fun h => hcast (by linear_combination -h)
  · show (i.val : ZMod k) - (j.val : ZMod k) ≠ 0
    exact fun h => hcast (by linear_combination h)

end Pos

/-! ### The two factor families -/

section Factors

variable {c k : ℕ}

/-- Within-copy factor with shift `d`: flip the side, shift the position. -/
def withinF (hk : 0 < k) (d : ZMod k) (v : V c k) : V c k :=
  (v.1, flip2 v.2.1, move hk (sideBool v.2.1) d v.2.2)

/-- Cross-copy factor for round `a` and shift `β`: move to the round-robin partner
super-vertex, shifting the position in the direction given by the orientation. -/
def crossF (hc : 1 ≤ c) (hk : 0 < k) (a : ZMod (2 * c - 1)) (β : ZMod k) (v : V c k) :
    V c k :=
  ((labInv hc (pim a (lab (v.1, v.2.1)))).1,
   (labInv hc (pim a (lab (v.1, v.2.1)))).2,
   move hk (orient a (lab (v.1, v.2.1))) β v.2.2)

lemma withinF_invol (hk : 0 < k) (d : ZMod k) (v : V c k) :
    withinF hk d (withinF hk d v) = v := by
  obtain ⟨u, s, i⟩ := v
  simp only [withinF]
  rw [sideBool_flip2, move_move, flip2_flip2]

lemma withinF_adj (hk : 0 < k) {d : ZMod k} (hd : d ≠ 0) (v : V c k) :
    (compl c k).Adj v (withinF hk d v) := by
  rw [adj_iff]
  right
  exact ⟨fun h => flip2_ne v.2.1 h.symm, fun h => move_ne hk hd (sideBool v.2.1) v.2.2 h.symm⟩

lemma withinF_inj_d (hk : 0 < k) {d d' : ZMod k} (v : V c k)
    (h : withinF hk d v = withinF hk d' v) : d = d' := by
  have h3 : move hk (sideBool v.2.1) d v.2.2 = move hk (sideBool v.2.1) d' v.2.2 :=
    congrArg (fun z : V c k => z.2.2) h
  exact move_inj hk _ v.2.2 h3

lemma crossF_invol (hc : 1 ≤ c) (hk : 0 < k) (a : ZMod (2 * c - 1)) (β : ZMod k)
    (v : V c k) : crossF hc hk a β (crossF hc hk a β v) = v := by
  obtain ⟨u, s, i⟩ := v
  simp only [crossF, Prod.mk.eta]
  rw [lab_labInv hc, pim_invol, orient_pim hc, move_move, labInv_lab hc]

lemma crossF_adj (hc : 1 ≤ c) (hk : 0 < k) {a : ZMod (2 * c - 1)} (ha : a ≠ 0)
    (β : ZMod k) (v : V c k) : (compl c k).Adj v (crossF hc hk a β v) := by
  rw [adj_iff]
  left
  exact fun h => cross_copy_ne hc ha v.1 v.2.1 h.symm

lemma crossF_inj_params (hc : 1 ≤ c) (hk : 0 < k) {a a' : ZMod (2 * c - 1)}
    {β β' : ZMod k} (v : V c k)
    (h : crossF hc hk a β v = crossF hc hk a' β' v) : a = a' ∧ β = β' := by
  have h1 : (labInv hc (pim a (lab (v.1, v.2.1)))).1
      = (labInv hc (pim a' (lab (v.1, v.2.1)))).1 := congrArg (fun z : V c k => z.1) h
  have h2 : (labInv hc (pim a (lab (v.1, v.2.1)))).2
      = (labInv hc (pim a' (lab (v.1, v.2.1)))).2 := congrArg (fun z : V c k => z.2.1) h
  have hP : labInv hc (pim a (lab (v.1, v.2.1))) = labInv hc (pim a' (lab (v.1, v.2.1))) :=
    Prod.ext h1 h2
  have hpim : pim a (lab (v.1, v.2.1)) = pim a' (lab (v.1, v.2.1)) := by
    rw [← lab_labInv hc (pim a (lab (v.1, v.2.1))),
      ← lab_labInv hc (pim a' (lab (v.1, v.2.1))), hP]
  have ha : a = a' := pim_arg_inj hc _ hpim
  subst ha
  have h3 : move hk (orient a (lab (v.1, v.2.1))) β v.2.2
      = move hk (orient a (lab (v.1, v.2.1))) β' v.2.2 :=
    congrArg (fun z : V c k => z.2.2) h
  exact ⟨rfl, move_inj hk _ v.2.2 h3⟩

end Factors

/-! ### Index packing and the full family -/

section Assemble

variable {c k : ℕ}

lemma N_split (hk : 2 ≤ k) (hc : 1 ≤ c) :
    2 * k * c - k - 1 = (k - 1) + (2 * c - 2) * k := by
  have e1 : 2 * k * c = 2 * (k * c) := by ring
  have e2 : (2 * c - 2) * k = 2 * (k * c) - 2 * k := by
    rw [Nat.sub_mul]
    congr 1
    ring
  have e3 : k ≤ k * c := Nat.le_mul_of_pos_right k (by omega)
  omega

/-- The packed family of factors. -/
def bigF (hc : 1 ≤ c) (hk : 0 < k) (t : Fin (2 * k * c - k - 1)) : V c k → V c k :=
  if t.val < k - 1 then withinF hk ((t.val + 1 : ℕ) : ZMod k)
  else crossF hc hk (((t.val - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
    (((t.val - (k - 1)) % k : ℕ) : ZMod k)

lemma bigF_lt (hc : 1 ≤ c) (hk : 0 < k) {t : Fin (2 * k * c - k - 1)}
    (ht : t.val < k - 1) :
    bigF hc hk t = withinF hk ((t.val + 1 : ℕ) : ZMod k) := by
  simp only [bigF]
  rw [if_pos ht]

lemma bigF_ge (hc : 1 ≤ c) (hk : 0 < k) {t : Fin (2 * k * c - k - 1)}
    (ht : ¬ t.val < k - 1) :
    bigF hc hk t = crossF hc hk (((t.val - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
      (((t.val - (k - 1)) % k : ℕ) : ZMod k) := by
  simp only [bigF]
  rw [if_neg ht]

/-- Decoding facts for a cross index. -/
lemma decode_cross (hk2 : 2 ≤ k) (hc : 1 ≤ c) {t : ℕ}
    (ht1 : ¬ t < k - 1) (ht2 : t < 2 * k * c - k - 1) :
    ((((t - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1)).val = (t - (k - 1)) / k + 1)
    ∧ ((((t - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1)) ≠ 0)
    ∧ ((((t - (k - 1)) % k : ℕ) : ZMod k).val = (t - (k - 1)) % k) := by
  have hN := N_split hk2 hc
  have hq : t - (k - 1) < (2 * c - 2) * k := by omega
  have hdiv : (t - (k - 1)) / k < 2 * c - 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
  have hlt : (t - (k - 1)) / k + 1 < 2 * c - 1 := by
    calc (t - (k - 1)) / k + 1 < (2 * c - 2) + 1 := Nat.add_lt_add_right hdiv 1
      _ ≤ 2 * c - 1 := by omega
  refine ⟨ZMod.val_cast_of_lt hlt, ?_, ZMod.val_cast_of_lt (Nat.mod_lt _ (by omega))⟩
  intro h0
  have hval := (ZMod.val_eq_zero _).mpr h0
  rw [ZMod.val_cast_of_lt hlt] at hval
  exact Nat.succ_ne_zero _ hval

end Assemble

/-! ### The main theorem -/

theorem proof :
    ∀ k c : ℕ, 2 ≤ k → 1 ≤ c →
      ∃ F : Fin (2 * k * c - k - 1) → V c k → V c k,
        (∀ t v, (compl c k).Adj v (F t v)) ∧
        (∀ t v, F t (F t v) = v) ∧
        (∀ v w, (compl c k).Adj v w → ∃! t, F t v = w) := by
  intro k c hk hc
  have hk0 : 0 < k := by omega
  have hnzk : NeZero k := ⟨by omega⟩
  have hnzc : NeZero (2 * c - 1) := ⟨by omega⟩
  have hN := N_split (c := c) hk hc
  refine ⟨bigF hc hk0, ?_, ?_, ?_⟩
  · -- adjacency
    intro t v
    by_cases ht : t.val < k - 1
    · rw [bigF_lt hc hk0 ht]
      apply withinF_adj hk0 _ v
      intro h0
      have hval : (((t.val + 1 : ℕ) : ZMod k)).val = 0 := (ZMod.val_eq_zero _).mpr h0
      rw [ZMod.val_cast_of_lt (show t.val + 1 < k by omega)] at hval
      omega
    · rw [bigF_ge hc hk0 ht]
      obtain ⟨hva, ha0, hvb⟩ := decode_cross hk hc ht t.isLt
      exact crossF_adj hc hk0 ha0 _ v
  · -- involution
    intro t v
    by_cases ht : t.val < k - 1
    · rw [bigF_lt hc hk0 ht]
      exact withinF_invol hk0 _ v
    · rw [bigF_ge hc hk0 ht]
      exact crossF_invol hc hk0 _ _ v
  · -- uniqueness
    intro v w hadj
    rw [adj_iff] at hadj
    by_cases hcopy : v.1 = w.1
    · -- within-copy edge
      obtain ⟨hss, hii⟩ : v.2.1 ≠ w.2.1 ∧ v.2.2 ≠ w.2.2 := by
        rcases hadj with h | h
        · exact absurd hcopy h
        · exact h
      set d := moveSolve (sideBool v.2.1) v.2.2 w.2.2 with hddef
      have hd0 : d ≠ 0 := moveSolve_ne_zero hk0 _ hii
      have hdval1 : 1 ≤ d.val := by
        rcases Nat.eq_zero_or_pos d.val with h0 | h0
        · exact absurd ((ZMod.val_eq_zero _).mp h0) hd0
        · exact h0
      have hdvalk : d.val < k := ZMod.val_lt d
      have hwd : withinF hk0 d v = w := by
        have hflip : flip2 v.2.1 = w.2.1 := by
          rcases fin2_eq_or_flip v.2.1 w.2.1 with h | h
          · exact absurd h.symm hss
          · exact h.symm
        exact Prod.ext hcopy (Prod.ext hflip (move_moveSolve hk0 _ _ _))
      have htv : d.val - 1 < 2 * k * c - k - 1 := by omega
      refine ⟨⟨d.val - 1, htv⟩, ?_, ?_⟩
      · show bigF hc hk0 ⟨d.val - 1, htv⟩ v = w
        have htlt' : (⟨d.val - 1, htv⟩ : Fin (2 * k * c - k - 1)).val < k - 1 := by
          show d.val - 1 < k - 1
          omega
        rw [bigF_lt hc hk0 htlt']
        have hcast : ((((⟨d.val - 1, htv⟩ : Fin (2 * k * c - k - 1)).val + 1 : ℕ))
            : ZMod k) = d := by
          show (((d.val - 1) + 1 : ℕ) : ZMod k) = d
          rw [show d.val - 1 + 1 = d.val from by omega, ZMod.natCast_zmod_val]
        rw [hcast]
        exact hwd
      · intro t' ht'
        by_cases ht'lt : t'.val < k - 1
        · rw [bigF_lt hc hk0 ht'lt] at ht'
          have hdd : ((t'.val + 1 : ℕ) : ZMod k) = d :=
            withinF_inj_d hk0 v (ht'.trans hwd.symm)
          have hval := congrArg ZMod.val hdd
          rw [ZMod.val_cast_of_lt (show t'.val + 1 < k by omega)] at hval
          apply Fin.ext
          show t'.val = d.val - 1
          omega
        · rw [bigF_ge hc hk0 ht'lt] at ht'
          obtain ⟨hva', ha0', hvb'⟩ := decode_cross hk hc ht'lt t'.isLt
          have h1 : (crossF hc hk0 (((t'.val - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
              (((t'.val - (k - 1)) % k : ℕ) : ZMod k) v).1 = w.1 :=
            congrArg Prod.fst ht'
          exact absurd (h1.trans hcopy.symm) (cross_copy_ne hc ha0' v.1 v.2.1)
    · -- cross-copy edge
      have hc2 : 2 ≤ c := by
        have h1 := v.1.isLt
        have h2 := w.1.isLt
        by_contra hcon
        exact hcopy (Fin.ext (by omega))
      obtain ⟨a, ha0, hpa⟩ := cross_exists hc hcopy v.2.1 w.2.1
      obtain ⟨β, hβmove⟩ :
          ∃ β, move hk0 (orient a (lab (v.1, v.2.1))) β v.2.2 = w.2.2 :=
        ⟨moveSolve _ _ _, move_moveSolve hk0 _ _ _⟩
      have hcross : crossF hc hk0 a β v = w := by
        show ((labInv hc (pim a (lab (v.1, v.2.1)))).1,
              (labInv hc (pim a (lab (v.1, v.2.1)))).2,
              move hk0 (orient a (lab (v.1, v.2.1))) β v.2.2) = w
        rw [hpa, labInv_lab hc]
        exact Prod.ext rfl (Prod.ext rfl hβmove)
      have hav1 : 1 ≤ a.val := by
        rcases Nat.eq_zero_or_pos a.val with h0 | h0
        · exact absurd ((ZMod.val_eq_zero _).mp h0) ha0
        · exact h0
      have hav2 : a.val < 2 * c - 1 := ZMod.val_lt a
      have hβv : β.val < k := ZMod.val_lt β
      set tq := β.val + (a.val - 1) * k with htq
      have hdiv : tq / k = a.val - 1 := by
        rw [htq, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt hβv, Nat.zero_add]
      have hmod : tq % k = β.val := by
        rw [htq, Nat.add_mul_mod_self_right β.val (a.val - 1) k, Nat.mod_eq_of_lt hβv]
      have hacast : ((tq / k + 1 : ℕ) : ZMod (2 * c - 1)) = a := by
        rw [hdiv, show a.val - 1 + 1 = a.val from by omega, ZMod.natCast_zmod_val]
      have hbcast : ((tq % k : ℕ) : ZMod k) = β := by
        rw [hmod, ZMod.natCast_zmod_val]
      have hbound1 : (a.val - 1) * k ≤ (2 * c - 3) * k :=
        Nat.mul_le_mul_right k (by omega)
      have hbound2 : (2 * c - 3) * k + k = (2 * c - 2) * k := by
        rw [show 2 * c - 2 = (2 * c - 3) + 1 from by omega, Nat.add_mul, Nat.one_mul]
      have htlt : (k - 1) + tq < 2 * k * c - k - 1 := by omega
      refine ⟨⟨(k - 1) + tq, htlt⟩, ?_, ?_⟩
      · show bigF hc hk0 ⟨(k - 1) + tq, htlt⟩ v = w
        have htge : ¬ ((⟨(k - 1) + tq, htlt⟩ : Fin (2 * k * c - k - 1)).val < k - 1) := by
          show ¬ ((k - 1) + tq < k - 1)
          omega
        rw [bigF_ge hc hk0 htge]
        show crossF hc hk0 ((((k - 1) + tq - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
          ((((k - 1) + tq - (k - 1)) % k : ℕ) : ZMod k) v = w
        rw [show (k - 1) + tq - (k - 1) = tq from by omega, hacast, hbcast]
        exact hcross
      · intro t' ht'
        by_cases ht'lt : t'.val < k - 1
        · rw [bigF_lt hc hk0 ht'lt] at ht'
          have h1 : (withinF hk0 ((t'.val + 1 : ℕ) : ZMod k) v).1 = w.1 :=
            congrArg Prod.fst ht'
          exact absurd h1 hcopy
        · rw [bigF_ge hc hk0 ht'lt] at ht'
          obtain ⟨hva', ha0', hvb'⟩ := decode_cross hk hc ht'lt t'.isLt
          have heq : crossF hc hk0
              (((t'.val - (k - 1)) / k + 1 : ℕ) : ZMod (2 * c - 1))
              (((t'.val - (k - 1)) % k : ℕ) : ZMod k) v = crossF hc hk0 a β v :=
            ht'.trans hcross.symm
          obtain ⟨haa, hbb⟩ := crossF_inj_params hc hk0 v heq
          have hva2 : (t'.val - (k - 1)) / k + 1 = a.val := by
            have hh := congrArg ZMod.val haa
            rw [hva'] at hh
            exact hh
          have hvb2 : (t'.val - (k - 1)) % k = β.val := by
            have hh := congrArg ZMod.val hbb
            rw [hvb'] at hh
            exact hh
          have hq'k : (t'.val - (k - 1)) / k = a.val - 1 := Nat.eq_sub_of_add_eq hva2
          have hdm : k * ((t'.val - (k - 1)) / k) + (t'.val - (k - 1)) % k
              = t'.val - (k - 1) := Nat.div_add_mod _ k
          have e5 : t'.val - (k - 1) = tq := by
            rw [← hdm, hq'k, hvb2, htq]
            ring
          apply Fin.ext
          show t'.val = (k - 1) + tq
          omega

end Submissions.GadgetComplementOneFactorization.GadgetFactor
