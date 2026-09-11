import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Finset.Card

/-! Exact local four-path restoration, with arbitrary lengths and intersections.
This is a component toward Gallai, not a proof of the full conjecture.
The two-cycle-plus-edge case also appears in Chu-Wang, arXiv:2510.12806v1, Lemma2.2.
The proof below is self-contained in pinned Mathlib; no external theorem is assumed. -/

namespace Submissions.Erdos583RootSixRestoration.Savcab.Edges

universe u

variable {V : Type u}

/-- The multiset of unordered consecutive pairs, counting multiplicities. -/
def edgeBag (p : List V) : Multiset (Sym2 V) :=
  List.rec (motive := fun _ => Multiset (Sym2 V)) 0
    (fun a tail acc => List.casesOn tail 0 (fun b _ => {s(a, b)} + acc)) p

@[simp] theorem edgeBag_nil : edgeBag ([] : List V) = 0 := rfl

@[simp] theorem edgeBag_singleton (a : V) : edgeBag [a] = 0 := rfl

@[simp] theorem edgeBag_cons_cons (a b : V) (r : List V) :
    edgeBag (a :: b :: r) = {s(a, b)} + edgeBag (b :: r) := rfl

@[simp] theorem edgeBag_pair (a b : V) : edgeBag [a, b] = {s(a, b)} := by
  simp only [edgeBag_cons_cons, edgeBag_singleton, add_zero]

/-- Split at one occurrence of `x`, retaining that occurrence in both pieces. -/
theorem edgeBag_split (l : List V) (x : V) (r : List V) :
    edgeBag (l ++ x :: r) = edgeBag (l ++ [x]) + edgeBag (x :: r) := by
  induction l with
  | nil =>
      simp only [List.nil_append, edgeBag_singleton, zero_add]
  | cons a l ih =>
      cases l with
      | nil =>
          simp only [List.cons_append, List.nil_append, edgeBag_cons_cons,
            edgeBag_singleton, add_zero]
      | cons b l =>
          calc
            edgeBag ((a :: b :: l) ++ x :: r) =
                {s(a, b)} + edgeBag ((b :: l) ++ x :: r) := rfl
            _ = {s(a, b)} +
                (edgeBag ((b :: l) ++ [x]) + edgeBag (x :: r)) :=
              congrArg (fun z : Multiset (Sym2 V) => {s(a, b)} + z) ih
            _ = edgeBag ((a :: b :: l) ++ [x]) + edgeBag (x :: r) := by
              change {s(a, b)} +
                  (edgeBag ((b :: l) ++ [x]) + edgeBag (x :: r)) =
                ({s(a, b)} + edgeBag ((b :: l) ++ [x])) + edgeBag (x :: r)
              exact (add_assoc _ _ _).symm

theorem edgeBag_split_append (l r : List V) (x : V) :
    edgeBag (l ++ [x] ++ r) = edgeBag (l ++ [x]) + edgeBag (x :: r) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    edgeBag_split l x r

/-- Splitting at an edge accounts separately for that edge. -/
theorem edgeBag_bridge (l : List V) (x y : V) (r : List V) :
    edgeBag (l ++ x :: y :: r) =
      edgeBag (l ++ [x]) + {s(x, y)} + edgeBag (y :: r) := by
  rw [edgeBag_split]
  simp only [edgeBag_cons_cons, add_assoc]

theorem edgeBag_append (l : List V) (x y : V) (r : List V) :
    edgeBag ((l ++ [x]) ++ (y :: r)) =
      edgeBag (l ++ [x]) + {s(x, y)} + edgeBag (y :: r) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    edgeBag_bridge l x y r

/-- Undirected edge multiplicities are unchanged by reversal. -/
@[simp] theorem edgeBag_reverse (p : List V) :
    edgeBag p.reverse = edgeBag p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      cases p with
      | nil => rfl
      | cons b r =>
          calc
            edgeBag (a :: b :: r).reverse =
                edgeBag (b :: r).reverse + {s(b, a)} := by
              simpa only [List.reverse_cons, List.append_assoc,
                List.cons_append, List.nil_append, edgeBag_singleton, add_zero] using
                edgeBag_bridge r.reverse b a []
            _ = edgeBag (b :: r) + {s(b, a)} :=
              congrArg (fun z : Multiset (Sym2 V) => z + {s(b, a)}) ih
            _ = {s(a, b)} + edgeBag (b :: r) := by
              rw [Sym2.eq_swap (a := b) (b := a), add_comm]
            _ = edgeBag (a :: b :: r) := rfl

/-- A zero-interior segment is allowed: `m = []` gives the edge `xy`. -/
theorem edgeBag_split_two (l m r : List V) (x y : V) :
    edgeBag (l ++ x :: (m ++ y :: r)) =
      edgeBag (l ++ [x]) + edgeBag (x :: (m ++ [y])) + edgeBag (y :: r) := by
  calc
    edgeBag (l ++ x :: (m ++ y :: r)) =
        edgeBag (l ++ [x]) + edgeBag ((x :: m) ++ y :: r) :=
      edgeBag_split l x (m ++ y :: r)
    _ = edgeBag (l ++ [x]) +
        (edgeBag ((x :: m) ++ [y]) + edgeBag (y :: r)) :=
      congrArg (fun z : Multiset (Sym2 V) => edgeBag (l ++ [x]) + z)
        (edgeBag_split (x :: m) y r)
    _ = edgeBag (l ++ [x]) + edgeBag (x :: (m ++ [y])) + edgeBag (y :: r) := by
      simpa only [List.cons_append] using
        (add_assoc (edgeBag (l ++ [x])) (edgeBag ((x :: m) ++ [y]))
          (edgeBag (y :: r))).symm

/-- Exchanging suffixes preserves the total edge multiset, without a simplicity claim. -/
theorem edgeBag_swap_tails (l₁ l₂ r₁ r₂ : List V) (x : V) :
    edgeBag (l₁ ++ x :: r₁) + edgeBag (l₂ ++ x :: r₂) =
      edgeBag (l₁ ++ x :: r₂) + edgeBag (l₂ ++ x :: r₁) := by
  calc
    _ = (edgeBag (l₁ ++ [x]) + edgeBag (x :: r₁)) +
        (edgeBag (l₂ ++ [x]) + edgeBag (x :: r₂)) :=
      congrArg₂ (· + ·) (edgeBag_split l₁ x r₁) (edgeBag_split l₂ x r₂)
    _ = (edgeBag (l₁ ++ [x]) + edgeBag (x :: r₂)) +
        (edgeBag (l₂ ++ [x]) + edgeBag (x :: r₁)) := by ac_rfl
    _ = _ :=
      (congrArg₂ (· + ·) (edgeBag_split l₁ x r₂) (edgeBag_split l₂ x r₁)).symm

/-- Convenience form for a path whose two ends have been displayed. -/
theorem edgeBag_prepend (a b c : V) (p : List V) :
    edgeBag (a :: ((b :: p) ++ [c])) =
      {s(a, b)} + edgeBag ((b :: p) ++ [c]) := rfl

end Submissions.Erdos583RootSixRestoration.Savcab.Edges

namespace Submissions.Erdos583RootSixRestoration.Savcab.Simple

universe u
variable {V : Type u}

/-- The two original pieces can be reversed separately around a fresh root. -/
theorem reverse_insert_nodup {a : V} {left right : List V}
    (hp : (left ++ right).Nodup) (ha : a ∉ left ++ right) :
    (left.reverse ++ [a] ++ right.reverse).Nodup := by
  obtain ⟨hl, hr, hd⟩ := List.nodup_append'.mp hp
  have hal : a ∉ left := fun hx => ha (List.mem_append.mpr (Or.inl hx))
  have har : a ∉ right := fun hx => ha (List.mem_append.mpr (Or.inr hx))
  have ht : (a :: right.reverse).Nodup :=
    List.nodup_cons.mpr ⟨by simpa only [List.mem_reverse] using har,
      List.nodup_reverse.mpr hr⟩
  have hd' : List.Disjoint left.reverse (a :: right.reverse) := by
    simp only [List.disjoint_cons_right, List.mem_reverse,
      List.disjoint_reverse_left, List.disjoint_reverse_right]
    exact ⟨hal, hd⟩
  have hn := (List.nodup_reverse.mpr hl).append ht hd'
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn

theorem reverse_insert_length (a : V) (left right : List V) :
    (left.reverse ++ [a] ++ right.reverse).length =
      left.length + 1 + right.length := by
  simp only [List.length_append, List.length_reverse, List.length_singleton]

theorem reverse_insert_length_ge_two (a : V) (left right : List V)
    (hl : 1 ≤ left.length) :
    2 ≤ (left.reverse ++ [a] ++ right.reverse).length := by
  rw [reverse_insert_length]
  exact Nat.le_trans (Nat.add_le_add_right hl 1)
    (Nat.le_add_right (left.length + 1) right.length)

/-- Direct wrapper for p = l ++ h :: r in P = (b :: p) ++ [c]. -/
theorem inside_first_nodup {a b h c : V} {l r : List V}
    (hp : ((b :: (l ++ (h :: r))) ++ [c]).Nodup)
    (ha : a ∉ (b :: (l ++ (h :: r))) ++ [c]) :
    (((b :: l) ++ [h]).reverse ++ [a] ++ (r ++ [c]).reverse).Nodup := by
  have hp' : (((b :: l) ++ [h]) ++ (r ++ [c])).Nodup := by
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using hp
  have ha' : a ∉ ((b :: l) ++ [h]) ++ (r ++ [c]) := by
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using ha
  exact reverse_insert_nodup hp' ha'

theorem inside_first_length_ge_two (a b h c : V) (l r : List V) :
    2 ≤ (((b :: l) ++ [h]).reverse ++ [a] ++ (r ++ [c]).reverse).length := by
  apply reverse_insert_length_ge_two
  have hb : b ∈ (b :: l) ++ [h] := by simp
  exact Nat.succ_le_of_lt (List.length_pos_of_mem hb)

/-- After writing the right suffix as x :: m, its head differs from h. -/
theorem split_last_ne_head {h x : V} {l m : List V}
    (hp : ((l ++ [h]) ++ (x :: m)).Nodup) : h ≠ x := by
  exact (List.nodup_append.mp hp).2.2 h (by simp) x (by simp)

theorem four_vertex_nodup {w a h x : V}
    (hwa : w ≠ a) (hwh : w ≠ h) (hwx : w ≠ x)
    (hah : a ≠ h) (hax : a ≠ x) (hhx : h ≠ x) :
    ([w, a, h, x] : List V).Nodup := by
  simp [List.nodup_cons, hwa, hwh, hwx, hah, hax, hhx]

theorem choose_other_endpoint {d e x : V} (hde : d ≠ e) :
    ∃ w, (w = d ∨ w = e) ∧ w ≠ x := by
  classical
  by_cases hdx : d = x
  · refine ⟨e, Or.inr rfl, ?_⟩
    intro hex
    exact hde (hdx.trans hex.symm)
  · exact ⟨d, Or.inl rfl, hdx⟩

/-- Only the four indicated role inequalities are needed from the eight-role
Nodup premise in the full restoration theorem.  The chosen neighbor x may
coincide with any other role, including the free endpoint t. -/
theorem short_return_exists {a h d e x : V}
    (hroles : ([a, h, d, e] : List V).Nodup)
    (hax : a ≠ x) (hhx : h ≠ x) :
    ∃ w, (w = d ∨ w = e) ∧ w ≠ x ∧
      ([w, a, h, x] : List V).Nodup ∧ 2 ≤ ([w, a, h, x] : List V).length := by
  have ha := (List.nodup_cons.mp hroles).1
  have hr := (List.nodup_cons.mp hroles).2
  have hh := (List.nodup_cons.mp hr).1
  have hde : d ≠ e := by
    simpa using (List.nodup_cons.mp (List.nodup_cons.mp hr).2).1
  have hah : a ≠ h := by
    intro heq
    exact ha (by simp [heq])
  obtain ⟨w, hw, hwx⟩ := choose_other_endpoint (x := x) hde
  have hwm : w ∈ [d, e] := by simpa using hw
  have haw : a ≠ w := by
    intro heq
    subst w
    exact ha (List.mem_cons_of_mem h hwm)
  have hhw : h ≠ w := by
    intro heq
    subst w
    exact hh hwm
  refine ⟨w, hw, hwx, four_vertex_nodup haw.symm hhw.symm hwx hah hax hhx, ?_⟩
  simp

end Submissions.Erdos583RootSixRestoration.Savcab.Simple

namespace Submissions.Erdos583RootSixRestoration.Savcab.Edges

universe u

variable {V : Type u}

/-- Append an edge to a displayed final vertex. -/
theorem edgeBag_append_singleton (l : List V) (x a : V) :
    edgeBag ((l ++ [x]) ++ [a]) = edgeBag (l ++ [x]) + {s(x, a)} := by
  simpa only [edgeBag_singleton, add_zero] using edgeBag_append l x a []

/-- Reversing a head-displayed path makes that head available for a final root edge. -/
theorem edgeBag_reverse_append_root (a b : V) (p : List V) :
    edgeBag ((b :: p).reverse ++ [a]) = {s(a, b)} + edgeBag (b :: p) := by
  simpa only [List.reverse_cons, edgeBag_cons_cons] using
    edgeBag_reverse (a :: b :: p)

/-- A root edge prepended to a reversed path uses the displayed old final vertex. -/
theorem edgeBag_prepend_reverse (l : List V) (x a : V) :
    edgeBag (a :: (l ++ [x]).reverse) = {s(a, x)} + edgeBag (l ++ [x]) := by
  calc
    edgeBag (a :: (l ++ [x]).reverse) =
        edgeBag (((l ++ [x]) ++ [a]).reverse) := by
      simp only [List.reverse_append, List.reverse_singleton,
        List.cons_append, List.nil_append]
    _ = edgeBag ((l ++ [x]) ++ [a]) := edgeBag_reverse _
    _ = edgeBag (l ++ [x]) + {s(x, a)} := edgeBag_append_singleton l x a
    _ = {s(a, x)} + edgeBag (l ++ [x]) := by
      rw [Sym2.eq_swap (a := x) (b := a), add_comm]

/-- Exact accounting for cutting `hx` and routing the reversed pieces through `a`.

The old path is `b ... h - x ... c`.  The replacement is
`h ... b - a - c ... x`.  The removed edge is placed on the left of the
identity, so no multiset subtraction or absence premise is required.
-/
theorem edgeBag_pout (a b c h x : V) (l m r : List V)
    (hend : x :: m = r ++ [c]) :
    edgeBag ((((b :: l) ++ [h]).reverse ++ [a]) ++
        (x :: m).reverse) + {s(h, x)} =
      edgeBag (((b :: l) ++ [h]) ++ (x :: m)) +
        {s(a, b)} + {s(a, c)} := by
  have hleft :
      edgeBag (((b :: l) ++ [h]).reverse ++ [a]) =
        {s(a, b)} + edgeBag ((b :: l) ++ [h]) := by
    simpa only [List.cons_append] using edgeBag_reverse_append_root a b (l ++ [h])
  have hright :
      edgeBag (a :: (x :: m).reverse) =
        {s(a, c)} + edgeBag (x :: m) := by
    rw [hend]
    exact edgeBag_prepend_reverse r c a
  have hold :
      edgeBag (((b :: l) ++ [h]) ++ (x :: m)) =
        edgeBag ((b :: l) ++ [h]) + {s(h, x)} + edgeBag (x :: m) :=
    edgeBag_append (b :: l) h x m
  calc
    edgeBag ((((b :: l) ++ [h]).reverse ++ [a]) ++
        (x :: m).reverse) + {s(h, x)} =
        (({s(a, b)} + edgeBag ((b :: l) ++ [h])) +
          ({s(a, c)} + edgeBag (x :: m))) + {s(h, x)} := by
      rw [edgeBag_split_append, hleft, hright]
    _ = (edgeBag ((b :: l) ++ [h]) + {s(h, x)} +
        edgeBag (x :: m)) + {s(a, b)} + {s(a, c)} := by
      simp only [add_comm, add_left_comm, add_assoc]
    _ = edgeBag (((b :: l) ++ [h]) ++ (x :: m)) +
        {s(a, b)} + {s(a, c)} :=
      congrArg (fun z : Multiset (Sym2 V) => z + {s(a, b)} + {s(a, c)}) hold.symm

end Submissions.Erdos583RootSixRestoration.Savcab.Edges

namespace Submissions.Erdos583RootSixRestoration.Savcab.Construction

universe u
variable {V : Type u}

open Submissions.Erdos583RootSixRestoration.Savcab.Edges
open Submissions.Erdos583RootSixRestoration.Savcab.Simple

def Good (p : List V) : Prop := p.Nodup ∧ 2 ≤ p.length

def FourPaths (edges : Multiset (Sym2 V)) : Prop :=
  ∃ p₁ p₂ p₃ p₄ : List V,
    Good p₁ ∧ Good p₂ ∧ Good p₃ ∧ Good p₄ ∧
    edgeBag p₁ + edgeBag p₂ + edgeBag p₃ + edgeBag p₄ = edges

theorem prepend_good {a b : V} {p : List V}
    (hp : (b :: p).Nodup) (ha : a ∉ b :: p) : Good (a :: b :: p) := by
  refine ⟨List.nodup_cons.mpr ⟨ha, hp⟩, ?_⟩
  simp

theorem prepend_reverse_good {a b c : V} {p : List V}
    (hp : ((b :: p) ++ [c]).Nodup) (ha : a ∉ (b :: p) ++ [c]) :
    Good (a :: ((b :: p) ++ [c]).reverse) := by
  refine ⟨List.nodup_cons.mpr ⟨by simpa only [List.mem_reverse] using ha,
    List.nodup_reverse.mpr hp⟩, ?_⟩
  simp

theorem outside_first_good {a h b c : V} {p : List V}
    (hp : ((b :: p) ++ [c]).Nodup) (ha : a ∉ (b :: p) ++ [c])
    (hh : h ∉ (b :: p) ++ [c]) (hha : h ≠ a) :
    Good (h :: a :: ((b :: p) ++ [c]).reverse) := by
  refine ⟨List.nodup_cons.mpr ⟨?_, (prepend_reverse_good hp ha).1⟩, ?_⟩
  · simpa only [List.mem_cons, List.mem_reverse, not_or] using And.intro hha hh
  · simp

theorem edgeBag_prepend_reverse (a b c : V) (p : List V) :
    edgeBag (a :: ((b :: p) ++ [c]).reverse) =
      {s(a, c)} + edgeBag ((b :: p) ++ [c]) := by
  have hr : ((b :: p) ++ [c]).reverse = c :: (b :: p).reverse := by simp
  calc
    _ = {s(a, c)} + edgeBag ((b :: p) ++ [c]).reverse := by rw [hr]; rfl
    _ = _ := congrArg (fun z : Multiset (Sym2 V) => {s(a, c)} + z)
      (edgeBag_reverse _)

theorem outside_restore {a h b c d e f t : V} {p q r : List V}
    (hp : ((b :: p) ++ [c]).Nodup)
    (hq : ((d :: q) ++ [e]).Nodup)
    (ht : ((f :: r) ++ [t]).Nodup)
    (haP : a ∉ (b :: p) ++ [c])
    (haQ : a ∉ (d :: q) ++ [e])
    (haT : a ∉ (f :: r) ++ [t])
    (hhP : h ∉ (b :: p) ++ [c])
    (hha : h ≠ a) (hda : d ≠ a) (hdb : d ≠ b) (hab : a ≠ b) :
    FourPaths (edgeBag ((b :: p) ++ [c]) + edgeBag ((d :: q) ++ [e]) +
      edgeBag ((f :: r) ++ [t]) + {s(a, h)} +
      {s(a, b)} + {s(a, c)} + {s(a, d)} + {s(a, e)} + {s(a, f)}) := by
  refine ⟨h :: a :: ((b :: p) ++ [c]).reverse,
    a :: ((d :: q) ++ [e]).reverse, [d, a, b], a :: ((f :: r) ++ [t]),
    outside_first_good hp haP hhP hha, prepend_reverse_good hq haQ, ?_,
    prepend_good ht haT, ?_⟩
  · simp [Good, List.nodup_cons, hda, hdb, hab]
  · rw [edgeBag_cons_cons, edgeBag_prepend_reverse, edgeBag_prepend_reverse,
      edgeBag_prepend]
    simp only [edgeBag_cons_cons]
    rw [Sym2.eq_swap (a := h) (b := a), Sym2.eq_swap (a := d) (b := a)]
    ac_rfl

theorem inside_restore {a h b c w y f t x : V} {l m s q r : List V}
    (hend : x :: m = s ++ [c])
    (hp : (((b :: l) ++ [h]) ++ (x :: m)).Nodup)
    (hq : ((y :: q) ++ [w]).Nodup)
    (ht : ((f :: r) ++ [t]).Nodup)
    (haP : a ∉ ((b :: l) ++ [h]) ++ (x :: m))
    (haQ : a ∉ (y :: q) ++ [w])
    (haT : a ∉ (f :: r) ++ [t])
    (hshort : ([w, a, h, x] : List V).Nodup) :
    FourPaths (edgeBag (((b :: l) ++ [h]) ++ (x :: m)) +
      edgeBag ((y :: q) ++ [w]) + edgeBag ((f :: r) ++ [t]) + {s(a, h)} +
      {s(a, b)} + {s(a, c)} + {s(a, w)} + {s(a, y)} + {s(a, f)}) := by
  refine ⟨((b :: l) ++ [h]).reverse ++ [a] ++ (x :: m).reverse,
    a :: ((y :: q) ++ [w]), [w, a, h, x], a :: ((f :: r) ++ [t]),
    ⟨reverse_insert_nodup hp haP, ?_⟩, prepend_good hq haQ, ⟨hshort, by simp⟩,
    prepend_good ht haT, ?_⟩
  · apply reverse_insert_length_ge_two
    simp
  · rw [edgeBag_prepend, edgeBag_prepend]
    simp only [edgeBag_cons_cons, edgeBag_singleton, add_zero]
    rw [Sym2.eq_swap (a := w) (b := a)]
    calc
      _ = (edgeBag (((b :: l) ++ [h]).reverse ++ [a] ++ (x :: m).reverse) +
          {s(h, x)}) + edgeBag ((y :: q) ++ [w]) + edgeBag ((f :: r) ++ [t]) +
          {s(a, h)} + {s(a, w)} + {s(a, y)} + {s(a, f)} := by ac_rfl
      _ = _ := by
        rw [edgeBag_pout a b c h x l m s hend]
        ac_rfl

/-- Four arbitrary original paths admit four nonempty simple replacement paths
after adding the five root edges. There are no cross-path intersection bounds. -/
theorem restore {a h b c d e f t : V} {p q r : List V}
    (roles : ([a, h, b, c, d, e, f, t] : List V).Nodup)
    (hp : ((b :: p) ++ [c]).Nodup)
    (hq : ((d :: q) ++ [e]).Nodup)
    (ht : ((f :: r) ++ [t]).Nodup)
    (haP : a ∉ (b :: p) ++ [c])
    (haQ : a ∉ (d :: q) ++ [e])
    (haT : a ∉ (f :: r) ++ [t]) :
    FourPaths (edgeBag ((b :: p) ++ [c]) + edgeBag ((d :: q) ++ [e]) +
      edgeBag ((f :: r) ++ [t]) + {s(a, h)} +
      {s(a, b)} + {s(a, c)} + {s(a, d)} + {s(a, e)} + {s(a, f)}) := by
  classical
  have hr := roles
  simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
    not_or, and_true] at hr
  by_cases hhP : h ∈ (b :: p) ++ [c]
  · have hhb : h ≠ b := by aesop
    have hhc : h ≠ c := by aesop
    have hhp : h ∈ p := by simpa [hhb, hhc] using hhP
    obtain ⟨l, s, rfl⟩ := List.mem_iff_append.mp hhp
    obtain ⟨x, m, hxm⟩ := List.exists_cons_of_ne_nil (show s ++ [c] ≠ [] by simp)
    have hPshape : ((b :: (l ++ h :: s)) ++ [c]) =
        ((b :: l) ++ [h]) ++ (x :: m) := by
      rw [← hxm]
      simp only [List.cons_append, List.append_assoc, List.nil_append]
    have hp' : (((b :: l) ++ [h]) ++ (x :: m)).Nodup := by rwa [← hPshape]
    have haP' : a ∉ ((b :: l) ++ [h]) ++ (x :: m) := by rwa [← hPshape]
    have hax : a ≠ x := by
      intro hax
      subst x
      exact haP' (by simp)
    have hhx : h ≠ x := split_last_ne_head hp'
    have hroles : ([a, h, d, e] : List V).Nodup := by
      simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
        not_or, and_true]
      aesop
    obtain ⟨w, hw, _, hn, _⟩ := short_return_exists hroles hax hhx
    rcases hw with hw | hw
    · subst w
      have hqrev : ((e :: q.reverse) ++ [d]).Nodup := by
        simpa only [List.reverse_append, List.reverse_cons, List.reverse_singleton,
          List.reverse_nil, List.cons_append, List.nil_append, List.append_assoc]
          using List.nodup_reverse.mpr hq
      have haqrev : a ∉ (e :: q.reverse) ++ [d] := by
        have h : a ∉ ((d :: q) ++ [e]).reverse := by
          simpa only [List.mem_reverse] using haQ
        simpa only [List.reverse_append, List.reverse_cons, List.reverse_singleton,
          List.reverse_nil, List.cons_append, List.nil_append, List.append_assoc] using h
      have hQedges : edgeBag ((e :: q.reverse) ++ [d]) =
          edgeBag ((d :: q) ++ [e]) := by
        simpa only [List.reverse_append, List.reverse_cons, List.reverse_singleton,
          List.reverse_nil, List.cons_append, List.nil_append, List.append_assoc]
          using edgeBag_reverse ((d :: q) ++ [e])
      have out := inside_restore hxm.symm hp' hqrev ht haP' haqrev haT hn
      simpa only [hPshape, hQedges] using out
    · subst w
      have out := inside_restore hxm.symm hp' hq ht haP' haQ haT hn
      simpa only [hPshape, add_comm, add_left_comm, add_assoc] using out
  · apply outside_restore hp hq ht haP haQ haT hhP <;> aesop

end Submissions.Erdos583RootSixRestoration.Savcab.Construction

namespace Submissions.Erdos583RootSixRestoration.Savcab.Bridge

def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V,
    p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b →
    ∃! p : List V, p ∈ paths ∧ PathUses p a b

abbrev edgeBag {V : Type} : List V → Multiset (Sym2 V) := Submissions.Erdos583RootSixRestoration.Savcab.Edges.edgeBag

def totalBag {V : Type} (ps : List (List V)) : Multiset (Sym2 V) :=
  ps.foldr (fun p acc => edgeBag p + acc) 0

variable {V : Type}

theorem totalBag_append (xs ys : List (List V)) :
    totalBag (xs ++ ys) = totalBag xs + totalBag ys := by
  induction xs with
  | nil => simp [totalBag]
  | cons p ps ih =>
      change edgeBag p + totalBag (ps ++ ys) = (edgeBag p + totalBag ps) + totalBag ys
      rw [ih, add_assoc]

theorem mem_edgeBag_cons {e : Sym2 V} {p : List V} (x : V)
    (he : e ∈ edgeBag p) : e ∈ edgeBag (x :: p) := by
  cases p with
  | nil => simpa [edgeBag] using he
  | cons y q => exact Multiset.mem_cons_of_mem he

theorem pathUses_mem_edgeBag {p : List V} {a b : V}
    (h : PathUses p a b) : s(a, b) ∈ edgeBag p := by
  obtain ⟨l, r, h | h⟩ := h
  · subst p
    induction l with
    | nil => simp [edgeBag]
    | cons x l ih => exact mem_edgeBag_cons x ih
  · subst p
    have hab : s(a, b) = s(b, a) := Sym2.eq_swap
    rw [hab]
    induction l with
    | nil => simp [edgeBag]
    | cons x l ih => exact mem_edgeBag_cons x ih

theorem edgeBag_mem_pathUses (p : List V) (a b : V) :
    s(a, b) ∈ edgeBag p → PathUses p a b := by
  induction p with
  | nil => simp [edgeBag]
  | cons x p ih =>
      cases p with
      | nil => simp [edgeBag]
      | cons y r =>
          intro he
          rcases Multiset.mem_cons.mp he with he | he
          · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨[], r, Or.inl rfl⟩
            · exact ⟨[], r, Or.inr rfl⟩
          · obtain ⟨l, t, hh | hh⟩ := ih he
            · exact ⟨x :: l, t, Or.inl (congrArg (List.cons x) hh)⟩
            · exact ⟨x :: l, t, Or.inr (congrArg (List.cons x) hh)⟩

theorem pathUses_iff_mem_edgeBag {p : List V} {a b : V} :
    PathUses p a b ↔ s(a, b) ∈ edgeBag p :=
  ⟨pathUses_mem_edgeBag, edgeBag_mem_pathUses p a b⟩

theorem isPath_of_edgeBag_adj {G : SimpleGraph V} {p : List V}
    (hp : p.Nodup)
    (hadj : ∀ a b, s(a, b) ∈ edgeBag p → G.Adj a b) : IsPath G p := by
  refine ⟨hp, ?_⟩
  change List.IsChain G.Adj p
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b l r hsplit
  exact hadj a b (pathUses_mem_edgeBag ⟨l, r, Or.inl hsplit⟩)

theorem mem_totalBag {e : Sym2 V} (ps : List (List V)) :
    e ∈ totalBag ps ↔ ∃ p ∈ ps, e ∈ edgeBag p := by
  induction ps with
  | nil => simp [totalBag]
  | cons p ps ih =>
      constructor
      · intro he
        rcases Multiset.mem_add.mp he with he | he
        · exact ⟨p, List.mem_cons_self, he⟩
        · obtain ⟨q, hq, hqe⟩ := ih.mp he
          exact ⟨q, List.mem_cons_of_mem p hq, hqe⟩
      · rintro ⟨q, hq, hqe⟩
        rcases List.mem_cons.mp hq with hq | hq
        · subst q
          exact Multiset.mem_add.mpr (Or.inl hqe)
        · exact Multiset.mem_add.mpr (Or.inr (ih.mpr ⟨q, hq, hqe⟩))

/-- The total multiset's Nodup property is the precise edge-ownership condition.
It is stronger than merely taking the set of all used edges. -/
theorem owner_unique_of_totalBag_nodup {e : Sym2 V} (ps : List (List V)) :
    (totalBag ps).Nodup → ∀ {p q : List V},
      p ∈ ps → q ∈ ps → e ∈ edgeBag p → e ∈ edgeBag q → p = q := by
  classical
  induction ps with
  | nil =>
      intro hn p q hp
      simp at hp
  | cons r rs ih =>
      intro hn p q hp hq hpe hqe
      obtain ⟨hr, hrs, hd⟩ := Multiset.nodup_add.mp hn
      rcases List.mem_cons.mp hp with hpr | hpr
      · subst p
        rcases List.mem_cons.mp hq with hqr | hqr
        · exact hqr.symm
        · exact False.elim ((Multiset.disjoint_left.mp hd) hpe
            ((mem_totalBag rs).mpr ⟨q, hqr, hqe⟩))
      · rcases List.mem_cons.mp hq with hqr | hqr
        · subst q
          exact False.elim ((Multiset.disjoint_left.mp hd) hqe
            ((mem_totalBag rs).mpr ⟨p, hpr, hpe⟩))
        · exact ih hrs hpr hqr hpe hqe

/-- A faithful bridge to the canonical definitions.  E must represent exactly
G's adjacency relation and must retain multiplicity one; neither condition is
replaced by a one-sided edge cover.  The output cardinality needs no assertion
that the list of output paths is itself Nodup. -/
theorem decomposition_of_totalBag [DecidableEq V]
    (G : SimpleGraph V) (ps : List (List V)) (E : Multiset (Sym2 V))
    (hE : E.Nodup)
    (hgraph : ∀ a b, s(a, b) ∈ E ↔ G.Adj a b)
    (hsum : totalBag ps = E)
    (hpaths : ∀ p ∈ ps, p.Nodup) :
    IsPathDecomposition G ps.toFinset ∧ ps.toFinset.card ≤ ps.length := by
  classical
  have hn : (totalBag ps).Nodup := by
    rw [hsum]
    exact hE
  constructor
  · refine ⟨?_, ?_⟩
    · intro p hp
      have hpm : p ∈ ps := List.mem_toFinset.mp hp
      apply isPath_of_edgeBag_adj (hpaths p hpm)
      intro a b he
      apply (hgraph a b).mp
      rw [← hsum]
      exact (mem_totalBag ps).mpr ⟨p, hpm, he⟩
    · intro a b hab
      have he : s(a, b) ∈ totalBag ps := by
        rw [hsum]
        exact (hgraph a b).mpr hab
      obtain ⟨p, hpm, hpe⟩ := (mem_totalBag ps).mp he
      refine ⟨p, ⟨List.mem_toFinset.mpr hpm, edgeBag_mem_pathUses p a b hpe⟩, ?_⟩
      intro q hq
      exact owner_unique_of_totalBag_nodup ps hn
        (List.mem_toFinset.mp hq.1) hpm (pathUses_mem_edgeBag hq.2) hpe
  · exact List.toFinset_card_le ps

/-- The proper-path facts delivered by the restoration theorem are preserved
as well, although the canonical decomposition definition does not require them. -/
theorem decomposition_of_totalBag_proper [DecidableEq V]
    (G : SimpleGraph V) (ps : List (List V)) (E : Multiset (Sym2 V))
    (hE : E.Nodup)
    (hgraph : ∀ a b, s(a, b) ∈ E ↔ G.Adj a b)
    (hsum : totalBag ps = E)
    (hpaths : ∀ p ∈ ps, p.Nodup ∧ 2 ≤ p.length) :
    ∃ paths : Finset (List V), paths.card ≤ ps.length ∧
      IsPathDecomposition G paths ∧ ∀ p ∈ paths, 2 ≤ p.length := by
  obtain ⟨hdecomp, hcard⟩ := decomposition_of_totalBag G ps E hE hgraph hsum
    (fun p hp => (hpaths p hp).1)
  refine ⟨ps.toFinset, hcard, hdecomp, ?_⟩
  intro p hp
  exact (hpaths p (List.mem_toFinset.mp hp)).2

end Submissions.Erdos583RootSixRestoration.Savcab.Bridge

namespace Submissions.Erdos583RootSixRestoration.Savcab

open Submissions.Erdos583RootSixRestoration.Savcab.Construction
open Submissions.Erdos583RootSixRestoration.Savcab.Bridge

def restoredEdges {V : Type} (rest : List (List V))
    (a h b c d e f t : V) (p q r : List V) : Multiset (Sym2 V) :=
  totalBag rest + (edgeBag ((b :: p) ++ [c]) + edgeBag ((d :: q) ++ [e]) +
    edgeBag ((f :: r) ++ [t]) + {s(a, h)} +
    {s(a, b)} + {s(a, c)} + {s(a, d)} + {s(a, e)} + {s(a, f)})

/-- An unrestricted local replacement of three root-avoiding paths and a
singleton root edge after adding five fresh root edges, at unchanged count. -/
theorem restoration {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (rest : List (List V))
    (a h b c d e f t : V) (p q r : List V)
    (roles : ([a, h, b, c, d, e, f, t] : List V).Nodup)
    (hp : ((b :: p) ++ [c]).Nodup)
    (hq : ((d :: q) ++ [e]).Nodup)
    (ht : ((f :: r) ++ [t]).Nodup)
    (haP : a ∉ (b :: p) ++ [c])
    (haQ : a ∉ (d :: q) ++ [e])
    (haT : a ∉ (f :: r) ++ [t])
    (hrest : ∀ path ∈ rest, path.Nodup)
    (hedges : (restoredEdges rest a h b c d e f t p q r).Nodup)
    (hgraph : ∀ x y, s(x, y) ∈ restoredEdges rest a h b c d e f t p q r ↔ G.Adj x y) :
    ∃ paths : Finset (List V), paths.card ≤ rest.length + 4 ∧
      IsPathDecomposition G paths := by
  obtain ⟨p₁, p₂, p₃, p₄, h₁, h₂, h₃, h₄, heq⟩ :=
    Submissions.Erdos583RootSixRestoration.Savcab.Construction.restore roles hp hq ht haP haQ haT
  have hsum : totalBag (rest ++ [p₁, p₂, p₃, p₄]) =
      restoredEdges rest a h b c d e f t p q r := by
    rw [totalBag_append]
    simp only [totalBag, List.foldr_cons, List.foldr_nil, add_zero, restoredEdges]
    rw [← heq]
    simp only [Submissions.Erdos583RootSixRestoration.Savcab.Bridge.edgeBag]
    ac_rfl
  have hpaths : ∀ path ∈ rest ++ [p₁, p₂, p₃, p₄], path.Nodup := by
    intro path hpath
    rcases List.mem_append.mp hpath with hpath | hpath
    · exact hrest path hpath
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
      rcases hpath with rfl | rfl | rfl | rfl
      · exact h₁.1
      · exact h₂.1
      · exact h₃.1
      · exact h₄.1
  obtain ⟨hdecomp, hcard⟩ := decomposition_of_totalBag G
    (rest ++ [p₁, p₂, p₃, p₄]) (restoredEdges rest a h b c d e f t p q r)
    hedges hgraph hsum hpaths
  refine ⟨(rest ++ [p₁, p₂, p₃, p₄]).toFinset, ?_, hdecomp⟩
  simpa only [List.length_append, List.length_cons, List.length_nil] using hcard

end Submissions.Erdos583RootSixRestoration.Savcab
