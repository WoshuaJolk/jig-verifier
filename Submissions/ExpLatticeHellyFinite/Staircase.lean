import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Order.Compare
import Mathlib.Order.Fin.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


/-! Turn a positive solution of affine difference equations into a convex-hull
witness. A shared first coordinate makes the omitted baseline weight positive. -/

namespace JigP5.AffineIntruder

theorem positive_baseline_weight {ι κ : Type*} [Fintype ι]
    (p : ι → κ → ℝ) (b q : κ → ℝ) (w : ι → ℝ)
    (i₀ i₁ : ι) (j₀ : κ) (hi : i₁ ≠ i₀)
    (hw : ∀ i, 0 < w i)
    (heq : ∀ j, ∑ i, w i * (p i j - b j) = q j - b j)
    (hq : q j₀ = p i₀ j₀) (hbase : b j₀ < p i₀ j₀)
    (hrest : ∀ i, i ≠ i₀ → p i₀ j₀ < p i j₀) :
    0 < 1 - ∑ i, w i := by
  classical
  have hsum : 0 < ∑ i, w i * (p i j₀ - p i₀ j₀) := by
    apply Finset.sum_pos'
    · intro i _
      apply mul_nonneg (hw i).le
      by_cases h : i = i₀
      · simp [h]
      · exact (sub_pos.mpr (hrest i h)).le
    · exact ⟨i₁, Finset.mem_univ _, mul_pos (hw i₁) (sub_pos.mpr (hrest i₁ hi))⟩
  have hid : (1 - ∑ i, w i) * (p i₀ j₀ - b j₀) =
      ∑ i, w i * (p i j₀ - p i₀ j₀) := by
    have h := heq j₀
    rw [hq] at h
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h ⊢
    nlinarith
  by_contra h
  have hle : 1 - ∑ i, w i ≤ 0 := le_of_not_gt h
  have hprod := mul_nonpos_of_nonpos_of_nonneg hle (sub_pos.mpr hbase).le
  rw [hid] at hprod
  exact (not_lt_of_ge hprod) hsum

theorem mem_hull {ι κ : Type*} [Fintype ι]
    (p : ι → κ → ℝ) (b q : κ → ℝ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hbase : 0 ≤ 1 - ∑ i, w i)
    (heq : ∀ j, ∑ i, w i * (p i j - b j) = q j - b j) :
    q ∈ convexHull ℝ (insert b (Set.range p)) := by
  classical
  let weights : Option ι → ℝ := fun i => i.elim (1 - ∑ i, w i) w
  let points : Option ι → κ → ℝ := fun i => i.elim b p
  apply mem_convexHull_of_exists_fintype weights points
  · intro i
    cases i with
    | none => exact hbase
    | some i => exact hw i
  · simp [weights, Fintype.sum_option]
  · intro i
    cases i with
    | none => exact Set.mem_insert _ _
    | some i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
  · ext j
    have h := heq j
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
    simp only [Fintype.sum_option, points, weights, Option.elim_none,
      Option.elim_some, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    nlinarith

end JigP5.AffineIntruder


/-!
Finite transitive-color bound for Jig #5. The hypothesis explicitly bounds every
monochromatic chain; this file supplies only the finite rank/counting argument.
No lattice or geometric claim is assumed proved by this helper.
-/

namespace JigP5.TransitiveColorBound

variable {α C : Type*}

/-- A finite set comparable under the strict relation `R`. -/
def Chain (R : α → α → Prop) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → R x y ∨ R y x

private lemma chain_insert [DecidableEq α] {R : α → α → Prop}
    {s : Finset α} {x : α} (hs : Chain R s) (htop : ∀ u ∈ s, R u x) :
    Chain R (insert x s) := by
  intro u hu v hv huv
  rcases Finset.mem_insert.mp hu with huEq | huS
  · subst u
    rcases Finset.mem_insert.mp hv with hvEq | hvS
    · subst v
      exact False.elim (huv rfl)
    · exact Or.inr (htop v hvS)
  · rcases Finset.mem_insert.mp hv with hvEq | hvS
    · subst v
      exact Or.inl (htop u huS)
    · exact hs u huS v hvS huv

private noncomputable def predChains [Fintype α] (R : α → α → Prop) (x : α) :
    Finset (Finset α) := by
  classical
  exact Finset.univ.filter fun s => Chain R s ∧ ∀ u ∈ s, R u x

private lemma mem_predChains [Fintype α] {R : α → α → Prop} {x : α}
    {s : Finset α} : s ∈ predChains R x ↔ Chain R s ∧ ∀ u ∈ s, R u x := by
  classical
  simp [predChains]

private noncomputable def rank [Fintype α] (R : α → α → Prop) (x : α) : ℕ :=
  (predChains R x).sup Finset.card

private lemma rank_attained [Fintype α] (R : α → α → Prop) (x : α) :
    ∃ s : Finset α, Chain R s ∧ (∀ u ∈ s, R u x) ∧ rank R x = s.card := by
  classical
  have hnonempty : (predChains R x).Nonempty := by
    refine ⟨∅, mem_predChains.mpr ⟨?_, ?_⟩⟩
    · intro u hu
      simp at hu
    · intro u hu
      simp at hu
  obtain ⟨s, hs, hmax⟩ :=
    Finset.exists_max_image (predChains R x) Finset.card hnonempty
  refine ⟨s, (mem_predChains.mp hs).1, (mem_predChains.mp hs).2, ?_⟩
  unfold rank
  exact le_antisymm (Finset.sup_le hmax) (Finset.le_sup hs)

private lemma rank_lt_bound [Fintype α] {R : α → α → Prop} {B : ℕ}
    (hirr : ∀ x, ¬R x x)
    (hbound : ∀ s : Finset α, Chain R s → s.card ≤ B) (x : α) :
    rank R x < B := by
  classical
  obtain ⟨s, hs, htop, hrank⟩ := rank_attained R x
  have hx : x ∉ s := fun hx => hirr x (htop x hx)
  have hcard := hbound (insert x s) (chain_insert hs htop)
  rw [Finset.card_insert_of_notMem hx] at hcard
  rw [hrank]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hcard

private lemma rank_lt_of_rel [Fintype α] {R : α → α → Prop}
    (htrans : Transitive R) (hirr : ∀ x, ¬R x x) {x y : α} (hxy : R x y) :
    rank R x < rank R y := by
  classical
  obtain ⟨s, hs, htop, hrank⟩ := rank_attained R x
  have hx : x ∉ s := fun hx => hirr x (htop x hx)
  have hmem : insert x s ∈ predChains R y := by
    apply mem_predChains.mpr
    refine ⟨chain_insert hs htop, ?_⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hxy
    · exact htrans (htop u hu) hxy
  calc
    rank R x = s.card := hrank
    _ < (insert x s).card := by
      rw [Finset.card_insert_of_notMem hx]
      exact Nat.lt_succ_self _
    _ ≤ rank R y := Finset.le_sup hmem

/-- Finitely many transitive colors, with every color chain bounded by `B`,
bound the entire finite set by `B ^ card C`. -/
theorem card_le_pow [Fintype α] [Fintype C] (R : C → α → α → Prop) (B : ℕ)
    (htrans : ∀ c, Transitive (R c)) (hirr : ∀ c x, ¬R c x x)
    (hcover : ∀ x y : α, x ≠ y → ∃ c, R c x y ∨ R c y x)
    (hbound : ∀ c (s : Finset α), Chain (R c) s → s.card ≤ B) :
    Fintype.card α ≤ B ^ Fintype.card C := by
  classical
  let signature : α → C → Fin B := fun x c =>
    ⟨rank (R c) x, rank_lt_bound (hirr c) (hbound c) x⟩
  have hinj : Function.Injective signature := by
    intro x y hsig
    by_contra hne
    obtain ⟨c, hc⟩ := hcover x y hne
    have heq : rank (R c) x = rank (R c) y :=
      congrArg Fin.val (congrFun hsig c)
    rcases hc with hxy | hyx
    · exact (ne_of_lt (rank_lt_of_rel (htrans c) (hirr c) hxy)) heq
    · exact (ne_of_lt (rank_lt_of_rel (htrans c) (hirr c) hyx)) heq.symm
  have hcard := Fintype.card_le_of_injective signature hinj
  simpa using hcard


end JigP5.TransitiveColorBound


/-!
The finite transitive comparison colors used in the candidate Jig #5 proof.
This establishes only the combinatorial relations; no geometric chain bound
or convex-hull transport is asserted here.
-/

namespace JigP5.IncrementColors

abbrev Exponents := Fin 3 → ℤ
abbrev Color := Fin 4 → Fin 4 → Ordering

/-- Adjoin the zero exponent of the homogeneous coordinate 1. -/
def homogeneous (n : Exponents) : Fin 4 → ℤ := Fin.cons 0 n

@[simp] theorem homogeneous_zero (n : Exponents) : homogeneous n 0 = 0 := by
  simp [homogeneous]

@[simp] theorem homogeneous_succ (n : Exponents) (i : Fin 3) :
    homogeneous n i.succ = n i := by
  simp [homogeneous]

def increment (x y : Exponents) (i : Fin 4) : ℤ :=
  homogeneous y i - homogeneous x i

def color (x y : Exponents) : Color :=
  fun i j => cmp (increment x y i) (increment x y j)

def Rel (c : Color) (x y : Exponents) : Prop := x ≠ y ∧ color x y = c

theorem card_color : Fintype.card Color = 3 ^ 16 := by
  have hordering : Fintype.card Ordering = 3 := by decide
  calc
    Fintype.card Color = (Fintype.card Ordering ^ 4) ^ 4 := by
      simp [Color, Fintype.card_fun]
    _ = 3 ^ 16 := by rw [hordering, ← pow_mul]

@[simp] theorem color_self (x : Exponents) :
    color x x = fun _ _ => Ordering.eq := by
  funext i j
  simp [color, increment]

/-- The all-equalities color can occur only for equal exponent vectors. -/
theorem eq_of_color_eq_self {x y z : Exponents} (h : color x y = color z z) :
    x = y := by
  funext i
  have hi := congrFun (congrFun h i.succ) 0
  have hzero : y i = x i := by
    simpa [color, increment, cmp_eq_eq_iff] using hi
  exact hzero.symm

private lemma cmp_add_same {p q r s : ℤ} {o : Ordering}
    (h₁ : cmp p q = o) (h₂ : cmp r s = o) : cmp (p + r) (q + s) = o := by
  cases o with
  | lt =>
    apply (cmp_eq_lt_iff _ _).mpr
    exact add_lt_add ((cmp_eq_lt_iff _ _).mp h₁) ((cmp_eq_lt_iff _ _).mp h₂)
  | eq =>
    apply (cmp_eq_eq_iff _ _).mpr
    exact congrArg₂ (· + ·) ((cmp_eq_eq_iff _ _).mp h₁) ((cmp_eq_eq_iff _ _).mp h₂)
  | gt =>
    apply (cmp_eq_gt_iff _ _).mpr
    exact add_lt_add ((cmp_eq_gt_iff _ _).mp h₁) ((cmp_eq_gt_iff _ _).mp h₂)

private lemma increment_add (x y z : Exponents) (i : Fin 4) :
    increment x z i = increment x y i + increment y z i := by
  unfold increment
  simpa only [add_comm] using
    (sub_add_sub_cancel (homogeneous z i) (homogeneous y i) (homogeneous x i)).symm

/-- A fixed comparison color is closed under successive increments. -/
theorem rel_transitive (c : Color) : Transitive (Rel c) := by
  intro x y z hxy hyz
  have hcolor : color x z = c := by
    funext i j
    have h₁ := congrFun (congrFun hxy.2 i) j
    have h₂ := congrFun (congrFun hyz.2 i) j
    change cmp (increment x z i) (increment x z j) = c i j
    rw [increment_add x y z i, increment_add x y z j]
    exact cmp_add_same h₁ h₂
  refine ⟨?_, hcolor⟩
  intro hxz
  apply hxy.1
  apply eq_of_color_eq_self (z := x)
  calc
    color x y = c := hxy.2
    _ = color x z := hcolor.symm
    _ = color x x := congrArg (color x) hxz.symm

theorem rel_irreflexive (c : Color) (x : Exponents) : ¬Rel c x x :=
  fun h => h.1 rfl

theorem rel_cover (x y : Exponents) (hxy : x ≠ y) :
    ∃ c : Color, Rel c x y ∨ Rel c y x :=
  ⟨color x y, Or.inl ⟨hxy, rfl⟩⟩


end JigP5.IncrementColors


/-! Enumerate a finite chain of an arbitrary strict transitive relation. -/

namespace JigP5.SortedChain

theorem enumerate {α : Type*} (R : α → α → Prop)
    (htrans : Transitive R) (hirr : ∀ x, ¬R x x) (s : Finset α)
    (hchain : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → R x y ∨ R y x) :
    ∃ e : Fin s.card → α, Function.Injective e ∧
      (∀ i, e i ∈ s) ∧ (∀ i j, i < j → R (e i) (e j)) := by
  classical
  let r : s → s → Prop := fun x y => R x.val y.val
  letI : IsStrictTotalOrder s r := {
    irrefl := fun x => hirr x.val
    trans := fun x y z hxy hyz => htrans hxy hyz
    trichotomous := fun x y => by
      intro hxy hyx
      by_contra h
      have hne : x.val ≠ y.val := fun heq => h (Subtype.ext heq)
      rcases hchain x.val x.property y.val y.property hne with hrel | hrel
      · exact hxy hrel
      · exact hyx hrel
  }
  letI : LinearOrder s := linearOrderOfSTO r
  let e : Fin s.card ≃o s := Fintype.orderIsoFinOfCardEq s (by simp)
  refine ⟨fun i => (e i).val, ?_, fun i => (e i).property, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i j hij
    exact e.strictMono hij

end JigP5.SortedChain


/-! Exact root vocabulary and return from integer to nonnegative exponents. -/

namespace JigP5.LatticeBasics

def expLattice (d : ℕ) (a : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = a ^ n}

def integerLattice (d : ℕ) (a : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℤ, x i = a ^ n}

def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

lemma hull_coordinate_ge_one {d : ℕ} {a : ℝ} (ha : 1 < a)
    {V : Set (Fin d → ℝ)} (hV : V ⊆ expLattice d a)
    {q : Fin d → ℝ} (hq : q ∈ convexHull ℝ V) (j : Fin d) : 1 ≤ q j := by
  have hsub : V ⊆ {x : Fin d → ℝ | 1 ≤ x j} := by
    intro x hx
    obtain ⟨n, hn⟩ := hV hx j
    change 1 ≤ x j
    rw [hn]
    exact one_le_pow₀ ha.le
  have hconv : Convex ℝ {x : Fin d → ℝ | 1 ≤ x j} := by
    intro x hx y hy u v hu hv huv
    change 1 ≤ u * x j + v * y j
    have hx' : 1 ≤ x j := hx
    have hy' : 1 ≤ y j := hy
    nlinarith
  exact convexHull_min hsub hconv hq

lemma hull_integer_is_natural {d : ℕ} {a : ℝ} (ha : 1 < a)
    {V : Set (Fin d → ℝ)} (hV : V ⊆ expLattice d a)
    {q : Fin d → ℝ} (hq : q ∈ convexHull ℝ V)
    (hlat : q ∈ integerLattice d a) : q ∈ expLattice d a := by
  intro j
  obtain ⟨n, hn⟩ := hlat j
  have hge : 1 ≤ a ^ n := hn ▸ hull_coordinate_ge_one ha hV hq j
  have hnonneg : 0 ≤ n := (one_le_zpow_iff_right₀ ha).mp hge
  refine ⟨n.toNat, ?_⟩
  rw [hn, ← zpow_natCast, Int.toNat_of_nonneg hnonneg]

/-- A lattice point in a hull of other listed vertices contradicts the exact
four-clause empty-polytope predicate, even if it was already listed elsewhere. -/
lemma no_intruder {d : ℕ} {a : ℝ} (ha : 1 < a)
    {V U : Set (Fin d → ℝ)} (hV : IsEmptyPolytope (expLattice d a) V)
    (hUV : U ⊆ V) {q : Fin d → ℝ} (hull : q ∈ convexHull ℝ U)
    (hlat : q ∈ integerLattice d a) (hq : q ∉ U) : False := by
  have hqVhull : q ∈ convexHull ℝ V := convexHull_mono hUV hull
  have hqL := hull_integer_is_natural ha hV.2.1 hqVhull hlat
  have hqV : q ∈ V := hV.2.2.2 ⟨hqVhull, hqL⟩
  apply hV.2.2.1 q hqV
  apply convexHull_mono (s := U) ?_ hull
  intro u hu
  refine ⟨hUV hu, ?_⟩
  intro heq
  exact hq (heq ▸ hu)

end JigP5.LatticeBasics


/-!
Conditional root reduction for Jig #5. The hypothesis explicitly bounds every
enumerated monochromatic exponent chain lying in the vertex set. The geometric
proof of that hypothesis is deliberately not asserted by this helper.

Source review: the four local imports were read before use. They contain only
the stated definitions and proof scripts, with no admitted theorem or external
execution path. They still require ordinary compilation and the final audit.
-/

namespace JigP5.RootBound

open IncrementColors LatticeBasics

/-- Evaluate an integer exponent vector in the common base. -/
noncomputable def evaluate (a : ℝ) (n : Exponents) : Fin 3 → ℝ := fun j => a ^ (n j)

/-- The finite combinatorial step, independent of exponential coordinates. -/
theorem card_le_of_chain_bound {α : Type*} [Fintype α]
    (encode : α → Exponents) (hinj : Function.Injective encode) (B : ℕ)
    (hchain : ∀ (L : ℕ) (c : Color) (n : Fin L → Exponents),
      Function.Injective n → (∀ i, n i ∈ Set.range encode) →
      (∀ i j, i < j → Rel c (n i) (n j)) → L ≤ B) :
    Fintype.card α ≤ B ^ (3 ^ 16) := by
  classical
  let R : Color → α → α → Prop := fun c x y => Rel c (encode x) (encode y)
  have htrans (c : Color) : Transitive (R c) := by
    intro x y z hxy hyz
    exact rel_transitive c hxy hyz
  have hirr (c : Color) (x : α) : ¬R c x x := rel_irreflexive c (encode x)
  have hcover (x y : α) (hxy : x ≠ y) : ∃ c, R c x y ∨ R c y x := by
    exact rel_cover (encode x) (encode y) (fun h => hxy (hinj h))
  have hbound (c : Color) (s : Finset α)
      (hs : TransitiveColorBound.Chain (R c) s) : s.card ≤ B := by
    obtain ⟨e, he, _, horder⟩ :=
      SortedChain.enumerate (R c) (htrans c) (hirr c) s hs
    exact hchain s.card c (fun i => encode (e i)) (hinj.comp he)
      (fun i => ⟨e i, rfl⟩) horder
  have h := TransitiveColorBound.card_le_pow R B htrans hirr hcover hbound
  simpa only [card_color] using h

/-- Every finite vertex set in the lattice admits an injective encoding by
integer exponents. No uniqueness assumption on a chosen exponent is needed:
evaluation is a left inverse to the encoding. -/
theorem exists_exponent_encoding (a : ℝ) (V : Set (Fin 3 → ℝ))
    (hVL : V ⊆ expLattice 3 a) :
    ∃ encode : V → Exponents, Function.Injective encode ∧
      ∀ v : V, evaluate a (encode v) = v.val := by
  classical
  have hex (v : V) (j : Fin 3) : ∃ n : ℕ, v.val j = a ^ n := hVL v.property j
  choose p hp using hex
  let encode : V → Exponents := fun v j => (p v j : ℤ)
  have heval (v : V) : evaluate a (encode v) = v.val := by
    funext j
    change a ^ ((p v j : ℕ) : ℤ) = v.val j
    rw [zpow_natCast]
    exact (hp v j).symm
  refine ⟨encode, ?_, heval⟩
  intro v w h
  apply Subtype.ext
  calc
    v.val = evaluate a (encode v) := (heval v).symm
    _ = evaluate a (encode w) := congrArg (evaluate a) h
    _ = w.val := heval w

/-- A bound on all enumerated monochromatic exponent chains yields the desired
cardinality bound on an arbitrary finite lattice vertex set. -/
theorem ncard_le_of_chain_bound (a : ℝ) (V : Set (Fin 3 → ℝ))
    (hfinite : V.Finite) (hVL : V ⊆ expLattice 3 a) (B : ℕ)
    (hchain : ∀ (L : ℕ) (c : Color) (n : Fin L → Exponents),
      Function.Injective n → (∀ i, evaluate a (n i) ∈ V) →
      (∀ i j, i < j → Rel c (n i) (n j)) → L ≤ B) :
    V.ncard ≤ B ^ (3 ^ 16) := by
  classical
  letI : Fintype V := hfinite.fintype
  obtain ⟨encode, hinj, heval⟩ := exists_exponent_encoding a V hVL
  have hcard : Fintype.card V ≤ B ^ (3 ^ 16) := by
    apply card_le_of_chain_bound encode hinj B
    intro L c n hn hmem horder
    apply hchain L c n hn ?_ horder
    intro i
    obtain ⟨v, hv⟩ := hmem i
    rw [← hv, heval v]
    exact v.property
  simpa only [Set.fintypeCard_eq_ncard] using hcard

/-- Convenience wrapper retaining the exact four-clause root predicate. -/
theorem empty_ncard_le (a : ℝ) (V : Set (Fin 3 → ℝ))
    (hV : IsEmptyPolytope (expLattice 3 a) V) (B : ℕ)
    (hchain : ∀ (L : ℕ) (c : Color) (n : Fin L → Exponents),
      Function.Injective n → (∀ i, evaluate a (n i) ∈ V) →
      (∀ i j, i < j → Rel c (n i) (n j)) → L ≤ B) :
    V.ncard ≤ B ^ (3 ^ 16) :=
  ncard_le_of_chain_bound a V hV.1 hV.2.1 B hchain

theorem exists_positive_power_four {a : ℝ} (ha : 1 < a) :
    ∃ K : ℕ, 0 < K ∧ (4 : ℝ) ≤ a ^ K := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (4 : ℝ) ha
  have hKpos : 0 < K := by
    by_contra h
    have hzero : K = 0 := Nat.eq_zero_of_not_pos h
    rw [hzero, pow_zero] at hK
    norm_num at hK
  exact ⟨K, hKpos, hK.le⟩


end JigP5.RootBound


/-!
Algebraic normalization of a homogeneous increment-color chain for Jig #5.
The distinct increments of one reference pair are sorted, and tied coordinates
are grouped exactly. This file does not assert projective convex-hull transport.
-/

namespace JigP5.NormalizeChain

variable {ι : Type*} [LinearOrder ι]

/-- A homogeneous comparison chain factors into a baseline, a common scalar
shift, and at most three strictly ordered variable coordinate classes.

The index type is arbitrary: instantiate it with a finite increasing sequence.
The final strict-monotonicity clause includes consecutive classes as a special
case, by taking `j.castSucc` and `j.succ`.
-/
theorem normalize (H : ι → Fin 4 → ℤ) (z o : ι)
    (hfirst : ∀ i, z ≤ i) (_hzo : z < o)
    (hcmp : ∀ s t, s < t → ∀ j k : Fin 4,
      cmp (H t j - H s j) (H t k - H s k) =
        cmp (H o j - H z j) (H o k - H z k)) :
    ∃ m : ℕ, m ≤ 3 ∧
      ∃ (rep : Fin (m + 1) → Fin 4) (cls : Fin 4 → Fin (m + 1))
        (b : Fin 4 → ℤ) (shift : ι → ℤ) (f : Fin (m + 1) → ι → ℤ),
        (∀ j, cls (rep j) = j) ∧
        (∀ i, f 0 i = 0) ∧
        (∀ j, f j z = 0) ∧
        (∀ j k, j < k → StrictMono (fun i => f k i - f j i)) ∧
        (∀ i l, H i l = b l + shift i + f (cls l) i) := by
  classical
  let δ : Fin 4 → ℤ := fun j => H o j - H z j
  let S : Finset ℤ := Finset.univ.image δ
  have hmem (j : Fin 4) : δ j ∈ S :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨δ 0, hmem 0⟩
  have hcard : S.card ≤ 4 := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
      _ = 4 := by simp
  let m : ℕ := S.card - 1
  have hsize : S.card = m + 1 := by dsimp [m]; omega
  have hm : m ≤ 3 := by dsimp [m]; omega
  let e : Fin (m + 1) ≃o S := S.orderIsoOfFin hsize
  have hex (j : Fin (m + 1)) : ∃ l : Fin 4, δ l = (e j).val := by
    have hj : (e j).val ∈ S := (e j).property
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hj
    exact ⟨l, hl⟩
  choose rep hrep using hex
  let cls : Fin 4 → Fin (m + 1) := fun l => e.symm ⟨δ l, hmem l⟩
  have hclass_value (l : Fin 4) : (e (cls l)).val = δ l := by
    dsimp [cls]
    rw [e.apply_symm_apply]
  have hclass_rep (j : Fin (m + 1)) : cls (rep j) = j := by
    apply e.injective
    apply Subtype.ext
    rw [hclass_value, hrep]
  have hrep_mono : StrictMono (fun j => δ (rep j)) := by
    intro j k hjk
    change δ (rep j) < δ (rep k)
    rw [hrep j, hrep k]
    exact e.strictMono hjk
  have htie (i : ι) (l : Fin 4) :
      H i l - H z l = H i (rep (cls l)) - H z (rep (cls l)) := by
    rcases lt_or_eq_of_le (hfirst i) with hi | hi
    · have hv : δ l = δ (rep (cls l)) := by
        rw [hrep, hclass_value]
      have hc := hcmp z i hi l (rep (cls l))
      change cmp (H i l - H z l)
        (H i (rep (cls l)) - H z (rep (cls l))) =
          cmp (δ l) (δ (rep (cls l))) at hc
      rw [hv, cmp_self_eq_eq] at hc
      exact (cmp_eq_eq_iff _ _).mp hc
    · subst i
      simp
  let shift : ι → ℤ := fun i => H i (rep 0) - H z (rep 0)
  let f : Fin (m + 1) → ι → ℤ :=
    fun j i => H i (rep j) - H z (rep j) - shift i
  refine ⟨m, hm, rep, cls, H z, shift, f, hclass_rep, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [f, shift]
    omega
  · intro j
    simp [f, shift]
  · intro j k hjk s t hst
    have hδ : δ (rep j) < δ (rep k) := hrep_mono hjk
    have hc := hcmp s t hst (rep j) (rep k)
    have hincr : H t (rep j) - H s (rep j) < H t (rep k) - H s (rep k) := by
      apply (cmp_eq_lt_iff _ _).mp
      exact hc.trans ((cmp_eq_lt_iff _ _).mpr hδ)
    dsimp [f, shift]
    omega
  · intro i l
    have hi := htie i l
    dsimp [f, shift]
    omega


end JigP5.NormalizeChain


/-! Integer-valued strict monotonicity gives one unit of growth per index. -/

namespace JigP5.IntegerGaps

theorem strictMono_gap {L : ℕ} {f : Fin L → ℤ} (hf : StrictMono f)
    (i j : Fin L) (hij : i ≤ j) :
    f i + ((j.val - i.val : ℕ) : ℤ) ≤ f j := by
  cases L with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hg : Monotone (fun k : Fin (n + 1) => f k - (k.val : ℤ)) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro k
      have hstep := hf k.castSucc_lt_succ
      change f k.castSucc - (k.val : ℤ) ≤ f k.succ - ((k.val + 1 : ℕ) : ℤ)
      omega
    have h := hg hij
    have hval : i.val ≤ j.val := hij
    dsimp only at h
    omega

theorem strictMono_from_zero {L : ℕ} {f : Fin (L + 1) → ℤ}
    (hf : StrictMono f) (j : Fin (L + 1)) : (j.val : ℤ) ≤ f j - f 0 := by
  have h := strictMono_gap hf 0 j (Fin.zero_le j)
  simp only [Fin.val_zero, Nat.sub_zero] at h
  omega

theorem selected_gap {L K p q : ℕ} {f : Fin L → ℤ} (hf : StrictMono f)
    (hp : 2 * K * p < L) (hq : 2 * K * q < L) (hpq : p ≤ q) :
    ((2 * K * (q - p) : ℕ) : ℤ) ≤
      f ⟨2 * K * q, hq⟩ - f ⟨2 * K * p, hp⟩ := by
  have hij : (⟨2 * K * p, hp⟩ : Fin L) ≤ ⟨2 * K * q, hq⟩ :=
    Nat.mul_le_mul_left (2 * K) hpq
  have h := strictMono_gap hf ⟨2 * K * p, hp⟩ ⟨2 * K * q, hq⟩ hij
  change f ⟨2 * K * p, hp⟩ + ((2 * K * q - 2 * K * p : ℕ) : ℤ) ≤
    f ⟨2 * K * q, hq⟩ at h
  rw [← Nat.mul_sub_left_distrib] at h
  omega


end JigP5.IntegerGaps


/-! Positive endpoint weights for three ordered exponential coordinates. -/

open scoped BigOperators

namespace JigP5.OneDimensionalWeights

theorem positive_weights {a : ℝ} (ha : 1 < a) {t₀ t₁ t₂ : ℤ}
    (h₀₁ : t₀ < t₁) (h₁₂ : t₁ < t₂) :
    ∃ weights : Fin 2 → ℝ, (∀ i, 0 < weights i) ∧ (∑ i, weights i) = 1 ∧
      weights 0 * a ^ t₀ + weights 1 * a ^ t₂ = a ^ t₁ := by
  have hp₀₁ : a ^ t₀ < a ^ t₁ := zpow_lt_zpow_right₀ ha h₀₁
  have hp₁₂ : a ^ t₁ < a ^ t₂ := zpow_lt_zpow_right₀ ha h₁₂
  have hden : 0 < a ^ t₂ - a ^ t₀ := sub_pos.mpr (lt_trans hp₀₁ hp₁₂)
  let u : ℝ := (a ^ t₁ - a ^ t₀) / (a ^ t₂ - a ^ t₀)
  have hu₀ : 0 < u := div_pos (sub_pos.mpr hp₀₁) hden
  have hu₁ : u < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have heq : u * (a ^ t₂ - a ^ t₀) = a ^ t₁ - a ^ t₀ := by
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨![1 - u, u], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change 0 < 1 - u
      exact sub_pos.mpr hu₁
    · change 0 < u
      exact hu₀
  · simp
  · change (1 - u) * a ^ t₀ + u * a ^ t₂ = a ^ t₁
    nlinarith [heq]


end JigP5.OneDimensionalWeights


/-!
The small positive linear system used by the exponential-lattice staircase argument.
This file is a helper theorem, not the full Jig #5 proof. The proof uses Cramer's
rule and explicit two- and three-dimensional determinant estimates.
-/

namespace ExpLatticePositiveSystem

private lemma small_pair_mul {x y : ℝ} (hy0 : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hsmall : x ≤ 1 / 4 ∨ y ≤ 1 / 4) : x * y ≤ 1 / 4 := by
  rcases hsmall with hx | hy
  · calc
      x * y ≤ (1 / 4 : ℝ) * 1 := mul_le_mul hx hy1 hy0 (by norm_num)
      _ = 1 / 4 := by norm_num
  · calc
      x * y ≤ (1 : ℝ) * (1 / 4) := mul_le_mul hx1 hy hy0 (by norm_num)
      _ = 1 / 4 := by norm_num

private lemma det_pos_two (A : Matrix (Fin 2) (Fin 2) ℝ)
    (h0 : ∀ i j, 0 ≤ A i j) (h1 : ∀ i j, A i j ≤ 1)
    (hd : ∀ i, 15 / 16 ≤ A i i)
    (hp : ∀ i j, i ≠ j → A i j ≤ 1 / 4 ∨ A j i ≤ 1 / 4) :
    0 < A.det := by
  have hdiag := mul_le_mul (hd 0) (hd 1) (by norm_num : (0 : ℝ) ≤ 15 / 16) (h0 0 0)
  have hoff := small_pair_mul (h0 1 0) (h1 0 1) (h1 1 0) (hp 0 1 (by decide))
  rw [Matrix.det_fin_two]
  norm_num at hdiag
  linarith

private lemma det_pos_three (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h0 : ∀ i j, 0 ≤ A i j) (h1 : ∀ i j, A i j ≤ 1)
    (hd : ∀ i, 15 / 16 ≤ A i i)
    (hp : ∀ i j, i ≠ j → A i j ≤ 1 / 4 ∨ A j i ≤ 1 / 4) :
    0 < A.det := by
  have hpair (i j : Fin 3) (hij : i ≠ j) : A i j * A j i ≤ 1 / 4 :=
    small_pair_mul (h0 j i) (h1 i j) (h1 j i) (hp i j hij)
  have hdiag : (15 / 16 : ℝ) ^ 3 ≤ A 0 0 * A 1 1 * A 2 2 := by
    calc
      (15 / 16 : ℝ) ^ 3 = (15 / 16 * (15 / 16)) * (15 / 16) := by ring
      _ ≤ A 0 0 * A 1 1 * A 2 2 :=
        mul_le_mul
          (mul_le_mul (hd 0) (hd 1) (by norm_num) (h0 0 0))
          (hd 2) (by norm_num) (mul_nonneg (h0 0 0) (h0 1 1))
  have hn₁ : A 0 0 * A 1 2 * A 2 1 ≤ 1 / 4 := by
    calc
      A 0 0 * A 1 2 * A 2 1 = (A 1 2 * A 2 1) * A 0 0 := by ring
      _ ≤ (1 / 4 : ℝ) * 1 := mul_le_mul (hpair 1 2 (by decide)) (h1 0 0) (h0 0 0) (by norm_num)
      _ = 1 / 4 := by norm_num
  have hn₂ : A 0 1 * A 1 0 * A 2 2 ≤ 1 / 4 := by
    calc
      A 0 1 * A 1 0 * A 2 2 ≤ (1 / 4 : ℝ) * 1 :=
        mul_le_mul (hpair 0 1 (by decide)) (h1 2 2) (h0 2 2) (by norm_num)
      _ = 1 / 4 := by norm_num
  have hn₃ : A 0 2 * A 1 1 * A 2 0 ≤ 1 / 4 := by
    calc
      A 0 2 * A 1 1 * A 2 0 = (A 0 2 * A 2 0) * A 1 1 := by ring
      _ ≤ (1 / 4 : ℝ) * 1 := mul_le_mul (hpair 0 2 (by decide)) (h1 1 1) (h0 1 1) (by norm_num)
      _ = 1 / 4 := by norm_num
  have hp₁ : 0 ≤ A 0 1 * A 1 2 * A 2 0 :=
    mul_nonneg (mul_nonneg (h0 0 1) (h0 1 2)) (h0 2 0)
  have hp₂ : 0 ≤ A 0 2 * A 1 0 * A 2 1 :=
    mul_nonneg (mul_nonneg (h0 0 2) (h0 1 0)) (h0 2 1)
  rw [Matrix.det_fin_three]
  norm_num at hdiag
  linarith

private lemma det_pos {n : ℕ} (hn : n = 2 ∨ n = 3) (A : Matrix (Fin n) (Fin n) ℝ)
    (h0 : ∀ i j, 0 ≤ A i j) (h1 : ∀ i j, A i j ≤ 1)
    (hd : ∀ i, 15 / 16 ≤ A i i)
    (hp : ∀ i j, i ≠ j → A i j ≤ 1 / 4 ∨ A j i ≤ 1 / 4) :
    0 < A.det := by
  rcases hn with rfl | rfl
  · exact det_pos_two A h0 h1 hd hp
  · exact det_pos_three A h0 h1 hd hp

/-- In dimensions two and three, a matrix close to the identity maps some strictly
positive vector to every vector whose entries lie in `[15/16,1]`. -/
theorem positive_system {n : ℕ} (hn : n = 2 ∨ n = 3)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hdiag : ∀ i, 15 / 16 ≤ A i i ∧ A i i ≤ 1)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j ∧ A i j ≤ 1 / 4)
    (hb : ∀ i, 15 / 16 ≤ b i ∧ b i ≤ 1) :
    ∃ β : Fin n → ℝ, (∀ i, 0 < β i) ∧ A.mulVec β = b := by
  have h0 (i j : Fin n) : 0 ≤ A i j := by
    by_cases hij : i = j
    · subst j
      exact (by norm_num : (0 : ℝ) ≤ 15 / 16).trans (hdiag i).1
    · exact (hoff i j hij).1
  have h1 (i j : Fin n) : A i j ≤ 1 := by
    by_cases hij : i = j
    · subst j
      exact (hdiag i).2
    · exact (hoff i j hij).2.trans (by norm_num)
  have hb0 (i : Fin n) : 0 ≤ b i :=
    (by norm_num : (0 : ℝ) ≤ 15 / 16).trans (hb i).1
  have hdet : 0 < A.det :=
    det_pos hn A h0 h1 (fun i => (hdiag i).1)
      (fun i j hij => Or.inl (hoff i j hij).2)
  have hcramer (c : Fin n) : 0 < (A.updateCol c b).det := by
    apply det_pos hn
    · intro i j
      by_cases hj : j = c
      · subst j
        simpa only [Matrix.updateCol_self] using hb0 i
      · simpa only [Matrix.updateCol_ne hj] using h0 i j
    · intro i j
      by_cases hj : j = c
      · subst j
        simpa only [Matrix.updateCol_self] using (hb i).2
      · simpa only [Matrix.updateCol_ne hj] using h1 i j
    · intro i
      by_cases hi : i = c
      · subst i
        simpa only [Matrix.updateCol_self] using (hb c).1
      · simpa only [Matrix.updateCol_ne hi] using (hdiag i).1
    · intro i j hij
      by_cases hj : j = c
      · subst j
        right
        simpa only [Matrix.updateCol_ne hij] using (hoff c i hij.symm).2
      · left
        simpa only [Matrix.updateCol_ne hj] using (hoff i j hij).2
  refine ⟨A.det⁻¹ • A.cramer b, ?_, ?_⟩
  · intro i
    change 0 < A.det⁻¹ * A.cramer b i
    rw [Matrix.cramer_apply]
    exact mul_pos (inv_pos.mpr hdet) (hcramer i)
  · rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul]
    simp [ne_of_gt hdet]


end ExpLatticePositiveSystem


/-! Algebraic bounds for the candidate exponential-lattice staircase intruder.
This file is a helper; the full finiteness theorem is not asserted here. -/

namespace StaircaseBounds

lemma negative_power_le_quarter {a : ℝ} (ha : 1 < a) {K : ℤ}
    (hK : 4 ≤ a ^ K) : a ^ (-K) ≤ (1 / 4 : ℝ) := by
  rw [zpow_neg]
  simpa using (inv_le_inv₀ (zpow_pos (lt_trans zero_lt_one ha) K)
    (by norm_num : (0 : ℝ) < 4)).mpr hK

lemma negative_power_le_sixteenth {a : ℝ} (ha : 1 < a) {K t : ℤ}
    (hK : 4 ≤ a ^ K) (ht : 2 * K ≤ t) : a ^ (-t) ≤ (1 / 16 : ℝ) := by
  have ha0 : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
  have hp : 16 ≤ a ^ (2 * K) := by
    have heq : a ^ (2 * K) = a ^ K * a ^ K := by
      rw [show 2 * K = K + K by omega, zpow_add₀ ha0]
    rw [heq]
    nlinarith
  have hpt : 16 ≤ a ^ t := hp.trans (zpow_le_zpow_right₀ ha.le ht)
  rw [zpow_neg]
  simpa using (inv_le_inv₀ (zpow_pos (lt_trans zero_lt_one ha) t)
    (by norm_num : (0 : ℝ) < 16)).mpr hpt

def exponents (r : Fin 3 → Fin 3 → ℤ) (i : Fin 3) : Fin 3 → ℤ :=
  ![r 0 i, r 0 i + r 1 i, r 0 i + r 1 i + r 2 i]

def intruder (r : Fin 3 → Fin 3 → ℤ) (K : ℤ) : Fin 3 → ℤ :=
  ![r 0 0, r 0 0 + r 1 1 - K, r 0 0 + r 1 1 + r 2 2 - 2 * K]

lemma exponent_bounds (r : Fin 3 → Fin 3 → ℤ) (K : ℤ) (hK : 0 < K)
    (hpos : ∀ l i, 2 * K ≤ r l i)
    (hgap : ∀ l i j, i < j → r l i + 2 * K ≤ r l j) :
    (∀ i j, 0 ≤ exponents r i j) ∧
    (∀ i, 2 * K ≤ exponents r i i) ∧
    (∀ j, 2 * K ≤ intruder r K j) ∧
    (∀ i j, i ≠ j → intruder r K i - exponents r i i +
      exponents r i j - intruder r K j ≤ -K) := by
  have hp00 := hpos 0 0
  have hp01 := hpos 0 1
  have hp02 := hpos 0 2
  have hp10 := hpos 1 0
  have hp11 := hpos 1 1
  have hp12 := hpos 1 2
  have hp20 := hpos 2 0
  have hp21 := hpos 2 1
  have hp22 := hpos 2 2
  have hg101 := hgap 1 0 1 (by decide)
  have hg112 := hgap 1 1 2 (by decide)
  have hg201 := hgap 2 0 1 (by decide)
  have hg212 := hgap 2 1 2 (by decide)
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [exponents] <;> omega
  constructor
  · intro i
    fin_cases i <;> simp [exponents] <;> omega
  constructor
  · intro j
    fin_cases j <;> simp [intruder] <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | (simp [intruder, exponents]; omega)

noncomputable def coefficient {m : ℕ} (a : ℝ) (n : Fin m → Fin m → ℤ)
    (E : Fin m → ℤ) (j i : Fin m) : ℝ :=
  a ^ (E i - n i i + n i j - E j) - a ^ (E i - n i i - E j)

lemma coefficient_bounds {m : ℕ} (a : ℝ) (ha : 1 < a) (K : ℤ)
    (hK : 4 ≤ a ^ K) (n : Fin m → Fin m → ℤ) (E : Fin m → ℤ)
    (hn : ∀ i j, 0 ≤ n i j) (hdiag : ∀ i, 2 * K ≤ n i i)
    (hE : ∀ j, 2 * K ≤ E j)
    (hoff : ∀ i j, i ≠ j → E i - n i i + n i j - E j ≤ -K) :
    (∀ i, (15 / 16 : ℝ) ≤ coefficient a n E i i ∧ coefficient a n E i i ≤ 1) ∧
    (∀ j i, j ≠ i → 0 ≤ coefficient a n E j i ∧ coefficient a n E j i ≤ 1 / 4) ∧
    (∀ j, (15 / 16 : ℝ) ≤ 1 - a ^ (-E j) ∧ 1 - a ^ (-E j) ≤ 1) := by
  have ha0 := lt_trans zero_lt_one ha
  constructor
  · intro i
    have hsmall := negative_power_le_sixteenth ha hK (hdiag i)
    have hp := zpow_pos ha0 (-n i i)
    have heq : coefficient a n E i i = 1 - a ^ (-n i i) := by
      unfold coefficient
      rw [show E i - n i i + n i i - E i = 0 by omega,
        show E i - n i i - E i = -n i i by omega, zpow_zero]
    rw [heq]
    constructor <;> linarith
  constructor
  · intro j i hij
    have hlo : a ^ (E i - n i i - E j) ≤ a ^ (E i - n i i + n i j - E j) :=
      zpow_le_zpow_right₀ ha.le (by have := hn i j; omega)
    have hhi : a ^ (E i - n i i + n i j - E j) ≤ a ^ (-K) :=
      zpow_le_zpow_right₀ ha.le (hoff i j hij.symm)
    have hp := zpow_pos ha0 (E i - n i i - E j)
    have hsmall := negative_power_le_quarter ha hK
    unfold coefficient
    constructor <;> linarith
  · intro j
    have hsmall := negative_power_le_sixteenth ha hK (hE j)
    have hp := zpow_pos ha0 (-E j)
    constructor <;> linarith

end StaircaseBounds


/-!
Draft local imports above are assembly conveniences. The final submission must
concatenate the audited helper bodies, not import another submission module.
-/

open scoped BigOperators

namespace StaircaseSimplex

def withBaseline {m : ℕ} (n : Fin m → Fin m → ℤ) : Option (Fin m) → Fin m → ℤ :=
  fun o => o.elim (fun _ => 0) n

/-- The common linear-algebra assembly for the two- and three-coordinate cases.
The final four hypotheses give a shared first coordinate, a positive baseline
weight, and a second coordinate distinguishing the intruder from that vertex. -/
theorem staircase_of_exponent_bounds {m : ℕ} (hm : m = 2 ∨ m = 3)
    (a : ℝ) (ha : 1 < a) (K : ℤ) (hpow : 4 ≤ a ^ K)
    (n : Fin m → Fin m → ℤ) (E : Fin m → ℤ)
    (hn : ∀ i j, 0 ≤ n i j) (hdiag : ∀ i, 2 * K ≤ n i i)
    (hE : ∀ j, 2 * K ≤ E j)
    (hoff : ∀ i j, i ≠ j → E i - n i i + n i j - E j ≤ -K)
    (i₀ i₁ j₀ j₁ : Fin m) (hi : i₁ ≠ i₀)
    (hfirst : E j₀ = n i₀ j₀) (hbaseexp : 0 < n i₀ j₀)
    (hrestexp : ∀ i, i ≠ i₀ → n i₀ j₀ < n i j₀)
    (hsecondexp : n i₀ j₁ < E j₁) :
    ∃ wgt : Option (Fin m) → ℝ,
      (∀ i, 0 < wgt i) ∧ (∑ i, wgt i = 1) ∧
      (∀ j, ∑ i, wgt i * a ^ (withBaseline n i j) = a ^ (E j)) ∧
      (fun j => a ^ (E j)) ∈
        convexHull ℝ (insert (fun _ : Fin m => (1 : ℝ))
          (Set.range (fun i j => a ^ (n i j)))) ∧
      (fun j => a ^ (E j)) ∉
        insert (fun _ : Fin m => (1 : ℝ))
          (Set.range (fun i j => a ^ (n i j))) := by
  have haPos : 0 < a := lt_trans zero_lt_one ha
  have ha0 : a ≠ 0 := ne_of_gt haPos
  let p : Fin m → Fin m → ℝ := fun i j => a ^ (n i j)
  let q : Fin m → ℝ := fun j => a ^ (E j)
  let M : Matrix (Fin m) (Fin m) ℝ := StaircaseBounds.coefficient a n E
  obtain ⟨hMd, hMo, hb⟩ :=
    StaircaseBounds.coefficient_bounds a ha K hpow n E hn hdiag hE hoff
  obtain ⟨β, hβ, hsolve⟩ := ExpLatticePositiveSystem.positive_system hm
    M (fun j => 1 - a ^ (-E j)) hMd hMo hb
  let w : Fin m → ℝ := fun i => a ^ (E i - n i i) * β i
  have hw (i : Fin m) : 0 < w i := mul_pos (zpow_pos haPos _) (hβ i)
  have hcancel (s t : ℤ) : a ^ s * a ^ (t - s) = a ^ t := by
    rw [← zpow_add₀ ha0]
    congr 1
    ring
  have hcoef (i j : Fin m) :
      a ^ (E j) * M j i = a ^ (E i - n i i) * (a ^ (n i j) - 1) := by
    dsimp [M, StaircaseBounds.coefficient]
    rw [mul_sub, hcancel, hcancel, zpow_add₀ ha0]
    ring
  have hterm (i j : Fin m) :
      w i * (p i j - 1) = a ^ (E j) * (M j i * β i) := by
    change (a ^ (E i - n i i) * β i) * (a ^ (n i j) - 1) = _
    calc
      _ = (a ^ (E i - n i i) * (a ^ (n i j) - 1)) * β i := by ring
      _ = (a ^ (E j) * M j i) * β i := by rw [hcoef]
      _ = a ^ (E j) * (M j i * β i) := by ring
  have heq (j : Fin m) : ∑ i, w i * (p i j - 1) = q j - 1 := by
    have hrow : ∑ i, M j i * β i = 1 - a ^ (-E j) := by
      simpa only [Matrix.mulVec_apply_eq_sum] using congrFun hsolve j
    change (∑ i, w i * (p i j - 1)) = a ^ (E j) - 1
    calc
      _ = ∑ i, a ^ (E j) * (M j i * β i) :=
        Finset.sum_congr rfl (fun i _ => hterm i j)
      _ = a ^ (E j) * (∑ i, M j i * β i) := by rw [Finset.mul_sum]
      _ = a ^ (E j) * (1 - a ^ (-E j)) := by rw [hrow]
      _ = a ^ (E j) - 1 := by
        rw [mul_sub, mul_one, ← zpow_add₀ ha0]
        simp
  have hqfirst : q j₀ = p i₀ j₀ := congrArg (fun t : ℤ => a ^ t) hfirst
  have hbase : (1 : ℝ) < p i₀ j₀ := by
    simpa only [zpow_zero] using zpow_lt_zpow_right₀ ha hbaseexp
  have hrest (i : Fin m) (hi : i ≠ i₀) : p i₀ j₀ < p i j₀ :=
    zpow_lt_zpow_right₀ ha (hrestexp i hi)
  have hwbase : 0 < 1 - ∑ i, w i :=
    JigP5.AffineIntruder.positive_baseline_weight p (fun _ => 1) q w
      i₀ i₁ j₀ hi hw heq hqfirst hbase hrest
  have hqsecond : p i₀ j₁ < q j₁ := zpow_lt_zpow_right₀ ha hsecondexp
  have hqbase : q ≠ (fun _ => 1) := by
    intro h
    exact (ne_of_gt hbase) (hqfirst.symm.trans (congrFun h j₀))
  have hqpoint (i : Fin m) : q ≠ p i := by
    intro h
    by_cases hi : i = i₀
    · subst i
      exact (ne_of_gt hqsecond) (congrFun h j₁)
    · have he : p i₀ j₀ = p i j₀ := hqfirst.symm.trans (congrFun h j₀)
      exact (ne_of_lt (hrest i hi)) he
  let wgt : Option (Fin m) → ℝ := fun o => o.elim (1 - ∑ i, w i) w
  refine ⟨wgt, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | none => exact hwbase
    | some i => exact hw i
  · simp [wgt, Fintype.sum_option]
  · intro j
    have h : (∑ i, w i * p i j) - (∑ i, w i) = q j - 1 := by
      simpa only [mul_sub, Finset.sum_sub_distrib, mul_one] using heq j
    simp only [Fintype.sum_option, wgt, withBaseline, Option.elim_none,
      Option.elim_some, zpow_zero, mul_one]
    change (1 - ∑ i, w i) + (∑ i, w i * p i j) = q j
    linarith
  · exact JigP5.AffineIntruder.mem_hull p (fun _ => 1) q w
      (fun i => (hw i).le) hwbase.le heq
  · change q ∉ insert (fun _ => 1) (Set.range p)
    rintro (h | h)
    · exact hqbase h
    · obtain ⟨i, hi⟩ := h
      exact hqpoint i hi.symm

def vertexExponents (r : Fin 3 → Fin 3 → ℤ) : Option (Fin 3) → Fin 3 → ℤ :=
  withBaseline (StaircaseBounds.exponents r)

/-- Positive normalized weights for the three-coordinate staircase intruder. -/
theorem staircase_three (a : ℝ) (ha : 1 < a) (K : ℤ) (hK : 0 < K)
    (hpow : 4 ≤ a ^ K) (r : Fin 3 → Fin 3 → ℤ)
    (hpos : ∀ l i, 2 * K ≤ r l i)
    (hgap : ∀ l i j, i < j → r l i + 2 * K ≤ r l j) :
    ∃ wgt : Option (Fin 3) → ℝ,
      (∀ i, 0 < wgt i) ∧ (∑ i, wgt i = 1) ∧
      (∀ j, ∑ i, wgt i * a ^ (vertexExponents r i j) =
        a ^ (StaircaseBounds.intruder r K j)) ∧
      (fun j => a ^ (StaircaseBounds.intruder r K j)) ∈
        convexHull ℝ (insert (fun _ : Fin 3 => (1 : ℝ))
          (Set.range (fun i j => a ^ (StaircaseBounds.exponents r i j)))) ∧
      (fun j => a ^ (StaircaseBounds.intruder r K j)) ∉
        insert (fun _ : Fin 3 => (1 : ℝ))
          (Set.range (fun i j => a ^ (StaircaseBounds.exponents r i j))) := by
  obtain ⟨hn, hdiag, hE, hoff⟩ := StaircaseBounds.exponent_bounds r K hK hpos hgap
  apply staircase_of_exponent_bounds (Or.inr rfl) a ha K hpow
    (StaircaseBounds.exponents r) (StaircaseBounds.intruder r K)
    hn hdiag hE hoff 0 1 0 1 (by decide)
  · rfl
  · change 0 < r 0 0
    have := hpos 0 0
    omega
  · intro i hi
    change r 0 0 < r 0 i
    have := hgap 0 0 i (by omega)
    omega
  · change r 0 0 + r 1 0 < r 0 0 + r 1 1 - K
    have := hgap 1 0 1 (by decide)
    omega

def exponentsTwo (r : Fin 2 → Fin 2 → ℤ) (i : Fin 2) : Fin 2 → ℤ :=
  ![r 0 i, r 0 i + r 1 i]

def intruderTwo (r : Fin 2 → Fin 2 → ℤ) (K : ℤ) : Fin 2 → ℤ :=
  ![r 0 0, r 0 0 + r 1 1 - K]

def vertexExponentsTwo (r : Fin 2 → Fin 2 → ℤ) : Option (Fin 2) → Fin 2 → ℤ :=
  withBaseline (exponentsTwo r)

lemma exponent_bounds_two (r : Fin 2 → Fin 2 → ℤ) (K : ℤ) (hK : 0 < K)
    (hpos : ∀ l i, 2 * K ≤ r l i)
    (hgap : ∀ l i j, i < j → r l i + 2 * K ≤ r l j) :
    (∀ i j, 0 ≤ exponentsTwo r i j) ∧
    (∀ i, 2 * K ≤ exponentsTwo r i i) ∧
    (∀ j, 2 * K ≤ intruderTwo r K j) ∧
    (∀ i j, i ≠ j → intruderTwo r K i - exponentsTwo r i i +
      exponentsTwo r i j - intruderTwo r K j ≤ -K) := by
  have hp00 := hpos 0 0
  have hp01 := hpos 0 1
  have hp10 := hpos 1 0
  have hp11 := hpos 1 1
  have hg := hgap 1 0 1 (by decide)
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [exponentsTwo] <;> omega
  constructor
  · intro i
    fin_cases i <;> simp [exponentsTwo] <;> omega
  constructor
  · intro j
    fin_cases j <;> simp [intruderTwo] <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [intruderTwo, exponentsTwo] at hij ⊢ <;> omega

/-- Positive normalized weights for the two-coordinate staircase intruder. -/
theorem staircase_two (a : ℝ) (ha : 1 < a) (K : ℤ) (hK : 0 < K)
    (hpow : 4 ≤ a ^ K) (r : Fin 2 → Fin 2 → ℤ)
    (hpos : ∀ l i, 2 * K ≤ r l i)
    (hgap : ∀ l i j, i < j → r l i + 2 * K ≤ r l j) :
    ∃ wgt : Option (Fin 2) → ℝ,
      (∀ i, 0 < wgt i) ∧ (∑ i, wgt i = 1) ∧
      (∀ j, ∑ i, wgt i * a ^ (vertexExponentsTwo r i j) =
        a ^ (intruderTwo r K j)) ∧
      (fun j => a ^ (intruderTwo r K j)) ∈
        convexHull ℝ (insert (fun _ : Fin 2 => (1 : ℝ))
          (Set.range (fun i j => a ^ (exponentsTwo r i j)))) ∧
      (fun j => a ^ (intruderTwo r K j)) ∉
        insert (fun _ : Fin 2 => (1 : ℝ))
          (Set.range (fun i j => a ^ (exponentsTwo r i j))) := by
  obtain ⟨hn, hdiag, hE, hoff⟩ := exponent_bounds_two r K hK hpos hgap
  apply staircase_of_exponent_bounds (Or.inl rfl) a ha K hpow
    (exponentsTwo r) (intruderTwo r K) hn hdiag hE hoff 0 1 0 1 (by decide)
  · rfl
  · change 0 < r 0 0
    have := hpos 0 0
    omega
  · intro i hi
    change r 0 0 < r 0 i
    have := hgap 0 0 i (by omega)
    omega
  · change r 0 0 + r 1 0 < r 0 0 + r 1 1 - K
    have := hgap 1 0 1 (by decide)
    omega


end StaircaseSimplex


/-! Extract the small positive staircase simplex from an integer monotone chain. -/

open scoped BigOperators

namespace JigP5.NormalizedStaircase

/-- The sampled nonbaseline index; the chain has more than `6*K` terms. -/
def pick {m L : ℕ} (K : ℕ) (hm : m ≤ 3) (hL : 6 * K < L + 1)
    (i : Fin m) : Fin (L + 1) :=
  ⟨2 * K * (i.val + 1), by
    have hi : i.val + 1 ≤ 3 := by omega
    have h := Nat.mul_le_mul_left (2 * K) hi
    omega⟩

def selection {m L : ℕ} (K : ℕ) (hm : m ≤ 3) (hL : 6 * K < L + 1) :
    Option (Fin m) → Fin (L + 1) := fun i => i.elim 0 (pick K hm hL)

def differences {m L : ℕ} (K : ℕ) (hm : m ≤ 3) (hL : 6 * K < L + 1)
    (f : Fin (m + 1) → Fin (L + 1) → ℤ) (l i : Fin m) : ℤ :=
  f l.succ (pick K hm hL i) - f l.castSucc (pick K hm hL i)

lemma difference_bounds {m L K : ℕ} (hm : m ≤ 3) (hL : 6 * K < L + 1)
    (f : Fin (m + 1) → Fin (L + 1) → ℤ)
    (hz : ∀ j, f j 0 = 0)
    (hmono : ∀ j k, j < k → StrictMono (fun i => f k i - f j i)) :
    (∀ l i, 2 * (K : ℤ) ≤ differences K hm hL f l i) ∧
    (∀ l i j, i < j → differences K hm hL f l i + 2 * (K : ℤ) ≤
      differences K hm hL f l j) := by
  have hg (l : Fin m) : StrictMono (fun i => f l.succ i - f l.castSucc i) :=
    hmono _ _ l.castSucc_lt_succ
  constructor
  · intro l i
    have h := IntegerGaps.strictMono_gap (hg l) 0 (pick K hm hL i) (Fin.zero_le _)
    simp only [Fin.val_zero, Nat.sub_zero, hz, sub_self, zero_add] at h
    have hlow : 2 * K ≤ 2 * K * (i.val + 1) := by nlinarith
    have hlow' : 2 * (K : ℤ) ≤ ((2 * K * (i.val + 1) : ℕ) : ℤ) := by exact_mod_cast hlow
    exact hlow'.trans h
  · intro l i j hij
    have hpq : i.val + 1 ≤ j.val + 1 := by omega
    have h := IntegerGaps.selected_gap (hg l)
      (pick K hm hL i).isLt (pick K hm hL j).isLt hpq
    have hlow : 2 * K ≤ 2 * K * ((j.val + 1) - (i.val + 1)) := by
      have hdiff : 1 ≤ (j.val + 1) - (i.val + 1) := by omega
      nlinarith
    have hlow' : 2 * (K : ℤ) ≤ ((2 * K * ((j.val + 1) - (i.val + 1)) : ℕ) : ℤ) := by
      exact_mod_cast hlow
    change _ ≤ differences K hm hL f l j - differences K hm hL f l i at h
    omega

/-- Convert a reduced staircase witness to homogeneous normalized coordinates. -/
lemma add_zero_coordinate {m L : ℕ} (a : ℝ)
    (f : Fin (m + 1) → Fin (L + 1) → ℤ)
    (s : Option (Fin m) → Fin (L + 1))
    (hf0 : ∀ i, f 0 i = 0)
    (n : Fin m → Fin m → ℤ) (E : Fin m → ℤ)
    (hcoord : ∀ i j, f j.succ (s i) = StaircaseSimplex.withBaseline n i j)
    (weights : Option (Fin m) → ℝ) (hsum : ∑ i, weights i = 1)
    (heq : ∀ j, ∑ i, weights i * a ^ (StaircaseSimplex.withBaseline n i j) = a ^ E j)
    (hne : (fun j => a ^ E j) ∉
      insert (fun _ : Fin m => (1 : ℝ)) (Set.range (fun i j => a ^ n i j))) :
    (∀ j, ∑ i, weights i * a ^ (f j (s i)) = a ^ (Fin.cons (α := fun _ => ℤ) 0 E j)) ∧
    (∀ i, (fun j : Fin (m + 1) => a ^ (Fin.cons (α := fun _ => ℤ) 0 E j : ℤ)) ≠ (fun j => a ^ (f j (s i)))) := by
  constructor
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [hf0, hsum]
    · simp only [Fin.cons_succ, hcoord]
      exact heq j
  · intro i hi
    apply hne
    cases i with
    | none =>
      left
      ext j
      have h := congrFun hi j.succ
      simpa [hcoord, StaircaseSimplex.withBaseline] using h
    | some i =>
      right
      refine ⟨i, ?_⟩
      ext j
      have h := congrFun hi j.succ
      simpa [hcoord, StaircaseSimplex.withBaseline] using h.symm

theorem normalized_two {L K : ℕ} (a : ℝ) (ha : 1 < a) (hK : 0 < K)
    (hpow : 4 ≤ a ^ (K : ℤ)) (hL : 6 * K < L + 1)
    (f : Fin 3 → Fin (L + 1) → ℤ) (hf0 : ∀ i, f 0 i = 0)
    (hz : ∀ j, f j 0 = 0)
    (hmono : ∀ j k, j < k → StrictMono (fun i => f k i - f j i)) :
    ∃ (s : Option (Fin 2) → Fin (L + 1)) (E : Fin 3 → ℤ)
      (weights : Option (Fin 2) → ℝ),
      E 0 = 0 ∧ (∀ i, 0 < weights i) ∧ (∑ i, weights i = 1) ∧
      (∀ j, ∑ i, weights i * a ^ (f j (s i)) = a ^ E j) ∧
      (∀ i, (fun j => a ^ E j) ≠ (fun j => a ^ (f j (s i)))) := by
  let r := differences K (by decide : 2 ≤ 3) hL f
  let s := selection K (by decide : 2 ≤ 3) hL
  obtain ⟨hp, hg⟩ := difference_bounds (by decide : 2 ≤ 3) hL f hz hmono
  obtain ⟨weights, hweights, hsum, heq, _, hne⟩ := StaircaseSimplex.staircase_two a ha
    (K : ℤ) (by exact_mod_cast hK) hpow r hp hg
  have hcoord (i : Option (Fin 2)) (j : Fin 2) :
      f j.succ (s i) = StaircaseSimplex.withBaseline (StaircaseSimplex.exponentsTwo r) i j := by
    cases i with
    | none => simp [s, selection, hz, StaircaseSimplex.withBaseline]
    | some i =>
      have h := hf0 (pick K (by decide : 2 ≤ 3) hL i)
      fin_cases j <;>
        simp [s, selection, StaircaseSimplex.withBaseline, StaircaseSimplex.exponentsTwo,
          r, differences] <;> omega
  obtain ⟨hE, hne'⟩ := add_zero_coordinate a f s hf0 _ _ hcoord weights hsum heq hne
  exact ⟨s, Fin.cons 0 (StaircaseSimplex.intruderTwo r (K : ℤ)), weights,
    rfl, hweights, hsum, hE, hne'⟩

theorem normalized_three {L K : ℕ} (a : ℝ) (ha : 1 < a) (hK : 0 < K)
    (hpow : 4 ≤ a ^ (K : ℤ)) (hL : 6 * K < L + 1)
    (f : Fin 4 → Fin (L + 1) → ℤ) (hf0 : ∀ i, f 0 i = 0)
    (hz : ∀ j, f j 0 = 0)
    (hmono : ∀ j k, j < k → StrictMono (fun i => f k i - f j i)) :
    ∃ (s : Option (Fin 3) → Fin (L + 1)) (E : Fin 4 → ℤ)
      (weights : Option (Fin 3) → ℝ),
      E 0 = 0 ∧ (∀ i, 0 < weights i) ∧ (∑ i, weights i = 1) ∧
      (∀ j, ∑ i, weights i * a ^ (f j (s i)) = a ^ E j) ∧
      (∀ i, (fun j => a ^ E j) ≠ (fun j => a ^ (f j (s i)))) := by
  let r := differences K (by decide : 3 ≤ 3) hL f
  let s := selection K (by decide : 3 ≤ 3) hL
  obtain ⟨hp, hg⟩ := difference_bounds (by decide : 3 ≤ 3) hL f hz hmono
  obtain ⟨weights, hweights, hsum, heq, _, hne⟩ := StaircaseSimplex.staircase_three a ha
    (K : ℤ) (by exact_mod_cast hK) hpow r hp hg
  have hcoord (i : Option (Fin 3)) (j : Fin 3) :
      f j.succ (s i) = StaircaseSimplex.withBaseline (StaircaseBounds.exponents r) i j := by
    cases i with
    | none => simp [s, selection, hz, StaircaseSimplex.withBaseline]
    | some i =>
      have h := hf0 (pick K (by decide : 3 ≤ 3) hL i)
      fin_cases j <;>
        simp [s, selection, StaircaseSimplex.withBaseline, StaircaseBounds.exponents,
          r, differences] <;> omega
  obtain ⟨hE, hne'⟩ := add_zero_coordinate a f s hf0 _ _ hcoord weights hsum heq hne
  exact ⟨s, Fin.cons 0 (StaircaseBounds.intruder r (K : ℤ)), weights,
    rfl, hweights, hsum, hE, hne'⟩

theorem normalized_one {L K : ℕ} (a : ℝ) (ha : 1 < a) (hK : 0 < K)
    (hL : 6 * K < L + 1)
    (f : Fin 2 → Fin (L + 1) → ℤ) (hf0 : ∀ i, f 0 i = 0)
    (hz : ∀ j, f j 0 = 0)
    (hmono : ∀ j k, j < k → StrictMono (fun i => f k i - f j i)) :
    ∃ (s : Option (Fin 1) → Fin (L + 1)) (E : Fin 2 → ℤ)
      (weights : Option (Fin 1) → ℝ),
      E 0 = 0 ∧ (∀ i, 0 < weights i) ∧ (∑ i, weights i = 1) ∧
      (∀ j, ∑ i, weights i * a ^ (f j (s i)) = a ^ E j) ∧
      (∀ i, (fun j => a ^ E j) ≠ (fun j => a ^ (f j (s i)))) := by
  let mid : Fin (L + 1) := ⟨1, by omega⟩
  let last : Fin (L + 1) := ⟨2, by omega⟩
  have hm : StrictMono (f 1) := by simpa only [hf0, sub_zero] using hmono 0 1 (by decide)
  have ht1 : f 1 0 < f 1 mid := hm (by change 0 < 1; decide)
  have ht2 : f 1 mid < f 1 last := hm (by change 1 < 2; decide)
  obtain ⟨w, hw, hsum, heq⟩ := OneDimensionalWeights.positive_weights ha ht1 ht2
  let s : Option (Fin 1) → Fin (L + 1) := fun i => i.elim 0 (fun _ => last)
  let E : Fin 2 → ℤ := ![0, f 1 mid]
  let weights : Option (Fin 1) → ℝ := fun i => i.elim (w 0) (fun _ => w 1)
  have hs : ∑ i, weights i = 1 := by simpa [weights, Fintype.sum_option, Fin.sum_univ_two] using hsum
  refine ⟨s, E, weights, rfl, ?_, hs, ?_, ?_⟩
  · intro i
    cases i with
    | none => exact hw 0
    | some i => exact hw 1
  · intro j
    fin_cases j
    · simpa [E, hf0] using hs
    · simpa [weights, s, E, Fintype.sum_option] using heq
  · intro i hi
    have hi' := congrFun hi 1
    cases i with
    | none =>
      have hlt := zpow_lt_zpow_right₀ ha ht1
      exact (ne_of_gt hlt) (by simpa [E, s] using hi')
    | some i =>
      have hlt := zpow_lt_zpow_right₀ ha ht2
      exact (ne_of_lt hlt) (by simpa [E, s] using hi')

theorem normalized {m L K : ℕ} (hm : m = 1 ∨ m = 2 ∨ m = 3)
    (a : ℝ) (ha : 1 < a) (hK : 0 < K)
    (hpow : 4 ≤ a ^ (K : ℤ)) (hL : 6 * K < L + 1)
    (f : Fin (m + 1) → Fin (L + 1) → ℤ) (hf0 : ∀ i, f 0 i = 0)
    (hz : ∀ j, f j 0 = 0)
    (hmono : ∀ j k, j < k → StrictMono (fun i => f k i - f j i)) :
    ∃ (s : Option (Fin m) → Fin (L + 1)) (E : Fin (m + 1) → ℤ)
      (weights : Option (Fin m) → ℝ),
      E 0 = 0 ∧ (∀ i, 0 < weights i) ∧ (∑ i, weights i = 1) ∧
      (∀ j, ∑ i, weights i * a ^ (f j (s i)) = a ^ E j) ∧
      (∀ i, (fun j => a ^ E j) ≠ (fun j => a ^ (f j (s i)))) := by
  rcases hm with rfl | rfl | rfl
  · exact normalized_one a ha hK hL f hf0 hz hmono
  · exact normalized_two a ha hK hpow hL f hf0 hz hmono
  · exact normalized_three a ha hK hpow hL f hf0 hz hmono

end JigP5.NormalizedStaircase


/-! Inverse projective transport by an explicit reweighting of integer powers. -/

open scoped BigOperators

namespace ExpLatticeProjectiveLift

/-- The displayed denominator identity normalizes the new convex weights.
No assumption that the original weights sum to one is needed. -/
theorem projective_lift {ι : Type*} [Fintype ι]
    (a : ℝ) (ha : 0 < a) (b : Fin 3 → ℤ) (c : ι → ℤ)
    (f : ι → Fin 3 → ℤ) (E : Fin 3 → ℤ) (E₀ : ℤ) (wgt : ι → ℝ)
    (hwgt : ∀ i, 0 ≤ wgt i)
    (hdenom : ∑ i, wgt i * a ^ (-c i) = a ^ E₀)
    (hcoords : ∀ j, ∑ i, wgt i * a ^ (f i j) = a ^ (E j)) :
    (fun j => a ^ (b j + E j - E₀)) ∈
      convexHull ℝ (Set.range (fun i j => a ^ (b j + c i + f i j))) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  let μ : ι → ℝ := fun i => wgt i * a ^ (-c i) * a ^ (-E₀)
  have hμ (i : ι) : 0 ≤ μ i :=
    mul_nonneg (mul_nonneg (hwgt i) (zpow_pos ha _).le) (zpow_pos ha _).le
  have hsum : ∑ i, μ i = 1 := by
    change (∑ i, (wgt i * a ^ (-c i)) * a ^ (-E₀)) = 1
    rw [← Finset.sum_mul, hdenom, ← zpow_add₀ ha0]
    simp
  have hterm (i : ι) (j : Fin 3) :
      μ i * a ^ (b j + c i + f i j) =
        a ^ (b j - E₀) * (wgt i * a ^ (f i j)) := by
    dsimp [μ]
    calc
      wgt i * a ^ (-c i) * a ^ (-E₀) * a ^ (b j + c i + f i j) =
          wgt i * (a ^ (-c i) * a ^ (-E₀) * a ^ (b j + c i + f i j)) := by ring
      _ = wgt i * a ^ ((-c i) + (-E₀) + (b j + c i + f i j)) := by
        rw [← zpow_add₀ ha0, ← zpow_add₀ ha0]
      _ = wgt i * a ^ ((b j - E₀) + f i j) := by
        congr 2
        ring
      _ = a ^ (b j - E₀) * (wgt i * a ^ (f i j)) := by
        rw [zpow_add₀ ha0]
        ring
  have hcoord (j : Fin 3) :
      ∑ i, μ i * a ^ (b j + c i + f i j) = a ^ (b j + E j - E₀) := by
    calc
      _ = ∑ i, a ^ (b j - E₀) * (wgt i * a ^ (f i j)) :=
        Finset.sum_congr rfl (fun i _ => hterm i j)
      _ = a ^ (b j - E₀) * (∑ i, wgt i * a ^ (f i j)) := by rw [Finset.mul_sum]
      _ = a ^ (b j - E₀) * a ^ (E j) := by rw [hcoords j]
      _ = a ^ (b j + E j - E₀) := by
        rw [← zpow_add₀ ha0]
        congr 1
        ring
  refine mem_convexHull_of_exists_fintype μ
    (fun i j => a ^ (b j + c i + f i j)) hμ hsum (fun i => Set.mem_range_self i) ?_
  ext j
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord j


end ExpLatticeProjectiveLift


/-!
Draft local import: concatenate the audited ProjectiveLift body for submission.

Source review for this bridge: NormalizeChain.lean SHA-256
eb26138bf9f375457b3eca2b3352a2e1f2253b1ad04815e23f2e323c244a2db7
and ProjectiveLift.lean SHA-256
c788e8776e591ea8a5e5fdb513df705687965b022569092e4803472b2903f7e8.
Both complete authored sources were read as untrusted mathematical input. Their
normalization and reweighting definitions have no new axioms, admissions, custom
elaborators, IO commands, or external execution paths. This is source review,
not a claim that these drafts or all transitive Mathlib imports were verified.
-/

open scoped BigOperators

namespace JigP5.NormalizedIntruder

noncomputable def originalPoint {ι : Type*} (a : ℝ) (H : ι → Fin 4 → ℤ) (i : ι) : Fin 3 → ℝ :=
  fun j => a ^ (H i j.succ)

def liftedExponent {m : ℕ} (b : Fin 4 → ℤ) (cls : Fin 4 → Fin (m + 1))
    (E : Fin (m + 1) → ℤ) : Fin 3 → ℤ :=
  fun j => b j.succ - b 0 + E (cls j.succ) - E (cls 0)

noncomputable def liftedPoint {m : ℕ} (a : ℝ) (b : Fin 4 → ℤ)
    (cls : Fin 4 → Fin (m + 1)) (E : Fin (m + 1) → ℤ) : Fin 3 → ℝ :=
  fun j => a ^ (liftedExponent b cls E j)

/-- Lift a normalized coordinate combination into the original affine chart.
The coordinate identity for `cls 0` normalizes the reweighted coefficients.
No independent assumption that the given coefficients sum to one is needed. -/
theorem normalized_lift_mem_hull {ι : Type*} [Fintype ι] {m : ℕ}
    (a : ℝ) (ha : 0 < a) (H : ι → Fin 4 → ℤ)
    (b : Fin 4 → ℤ) (shift : ι → ℤ) (f : Fin (m + 1) → ι → ℤ)
    (cls : Fin 4 → Fin (m + 1))
    (hH0 : ∀ i, H i 0 = 0)
    (hfactor : ∀ i l, H i l = b l + shift i + f (cls l) i)
    (E : Fin (m + 1) → ℤ) (wgt : ι → ℝ) (hwgt : ∀ i, 0 ≤ wgt i)
    (hcoords : ∀ j, ∑ i, wgt i * a ^ (f j i) = a ^ (E j)) :
    liftedPoint a b cls E ∈ convexHull ℝ (Set.range (originalPoint a H)) := by
  have hc (i : ι) : -(shift i + b 0) = f (cls 0) i := by
    have h := hfactor i 0
    rw [hH0 i] at h
    omega
  have hdenom : ∑ i, wgt i * a ^ (-(shift i + b 0)) = a ^ (E (cls 0)) := by
    simpa only [hc] using hcoords (cls 0)
  have hp :
      (fun (i : ι) (j : Fin 3) => a ^ ((b j.succ - b 0) + (shift i + b 0) +
        f (cls j.succ) i)) = originalPoint a H := by
    funext i j
    change a ^ ((b j.succ - b 0) + (shift i + b 0) + f (cls j.succ) i) =
      a ^ (H i j.succ)
    congr 1
    have h := hfactor i j.succ
    omega
  have h := ExpLatticeProjectiveLift.projective_lift a ha
    (fun j => b j.succ - b 0) (fun i => shift i + b 0)
    (fun i j => f (cls j.succ) i) (fun j => E (cls j.succ)) (E (cls 0))
    wgt hwgt hdenom (fun j => hcoords (cls j.succ))
  rw [hp] at h
  exact h

/-- The normalized point and its original affine lift identify the same selected
vertex. The class-zero normalization removes the homogeneous scalar ambiguity,
and representatives ensure no normalized coordinate is lost through ties. -/
theorem lift_eq_iff {ι : Type*} {m : ℕ}
    (a : ℝ) (ha : 1 < a) (H : ι → Fin 4 → ℤ)
    (b : Fin 4 → ℤ) (shift : ι → ℤ) (f : Fin (m + 1) → ι → ℤ)
    (cls : Fin 4 → Fin (m + 1)) (rep : Fin (m + 1) → Fin 4)
    (hclass : ∀ j, cls (rep j) = j) (hf0 : ∀ i, f 0 i = 0)
    (hH0 : ∀ i, H i 0 = 0)
    (hfactor : ∀ i l, H i l = b l + shift i + f (cls l) i)
    (E : Fin (m + 1) → ℤ) (hE0 : E 0 = 0) (i : ι) :
    liftedPoint a b cls E = originalPoint a H i ↔
      (fun j => a ^ (E j)) = (fun j => a ^ (f j i)) := by
  have hinj : Function.Injective (fun z : ℤ => a ^ z) :=
    zpow_right_injective₀ (lt_trans zero_lt_one ha) (ne_of_gt ha)
  constructor
  · intro h
    have hexp (l : Fin 4) : b l - b 0 + E (cls l) - E (cls 0) = H i l := by
      refine Fin.cases ?_ (fun j => ?_) l
      · simp [hH0 i]
      · exact hinj (congrFun h j)
    have hscalar : b 0 + shift i + E (cls 0) = 0 := by
      have he := hexp (rep 0)
      have hf := hfactor i (rep 0)
      rw [hclass 0, hE0] at he
      rw [hclass 0, hf0 i] at hf
      omega
    have hEq (j : Fin (m + 1)) : E j = f j i := by
      have he := hexp (rep j)
      have hf := hfactor i (rep j)
      rw [hclass j] at he hf
      omega
    funext j
    rw [hEq j]
  · intro h
    have hEq (j : Fin (m + 1)) : E j = f j i := hinj (congrFun h j)
    funext j
    change a ^ (b j.succ - b 0 + E (cls j.succ) - E (cls 0)) = a ^ (H i j.succ)
    congr 1
    simp only [hEq]
    have hz := hfactor i 0
    have hj := hfactor i j.succ
    rw [hH0 i] at hz
    omega

/-- A normalized intruder gives an explicit integer-power point in the original
hull which differs from every original selected vertex. -/
theorem normalized_intruder {ι : Type*} [Fintype ι] {m : ℕ}
    (a : ℝ) (ha : 1 < a) (H : ι → Fin 4 → ℤ)
    (b : Fin 4 → ℤ) (shift : ι → ℤ) (f : Fin (m + 1) → ι → ℤ)
    (cls : Fin 4 → Fin (m + 1)) (rep : Fin (m + 1) → Fin 4)
    (hclass : ∀ j, cls (rep j) = j) (hf0 : ∀ i, f 0 i = 0)
    (hH0 : ∀ i, H i 0 = 0)
    (hfactor : ∀ i l, H i l = b l + shift i + f (cls l) i)
    (E : Fin (m + 1) → ℤ) (hE0 : E 0 = 0)
    (wgt : ι → ℝ) (hwgt : ∀ i, 0 ≤ wgt i)
    (hcoords : ∀ j, ∑ i, wgt i * a ^ (f j i) = a ^ (E j))
    (hdistinct : ∀ i, (fun j => a ^ (E j)) ≠ (fun j => a ^ (f j i))) :
    ∃ q : Fin 3 → ℤ,
      (fun j => a ^ (q j)) ∈ convexHull ℝ (Set.range (originalPoint a H)) ∧
      ∀ i, (fun j => a ^ (q j)) ≠ originalPoint a H i := by
  refine ⟨liftedExponent b cls E, ?_, ?_⟩
  · exact normalized_lift_mem_hull a (lt_trans zero_lt_one ha) H b shift f cls
      hH0 hfactor E wgt hwgt hcoords
  · intro i h
    exact hdistinct i ((lift_eq_iff a ha H b shift f cls rep hclass hf0 hH0
      hfactor E hE0 i).mp h)


end JigP5.NormalizedIntruder


/-!
Candidate full Jig #5 proof assembly. The transitive color bound, exact chain
normalization, positive simplex construction, projective lift, and return to
nonnegative exponents are all explicit imported helper theorems.

Source review before assembly covered the current complete local helper bodies,
including their degenerate-coordinate cases and the exact four-clause lattice
predicate. This source contains no admitted step. Compilation, final source
assembly, the canonical bridge, and transitive axiom inspection remain required
before this draft is described as a machine-checked solution.
-/

namespace JigP5.ChainBound

open IncrementColors LatticeBasics

/-- Every monochromatic injective exponent chain in an empty vertex set has
length at most `6*K`, for any positive K with `a^K ≥ 4`. -/
theorem chain_length_le (a : ℝ) (ha : 1 < a) (K : ℕ) (hK : 0 < K)
    (hpow : (4 : ℝ) ≤ a ^ (K : ℤ)) (V : Set (Fin 3 → ℝ))
    (hV : IsEmptyPolytope (expLattice 3 a) V)
    (L : ℕ) (c : Color) (n : Fin L → Exponents)
    (hinj : Function.Injective n) (hmem : ∀ i, RootBound.evaluate a (n i) ∈ V)
    (hrel : ∀ i j, i < j → Rel c (n i) (n j)) : L ≤ 6 * K := by
  classical
  by_contra hbad
  have hL : 6 * K < L := Nat.lt_of_not_ge hbad
  cases L with
  | zero => omega
  | succ l =>
    let one : Fin (l + 1) := ⟨1, by omega⟩
    have h01 : (0 : Fin (l + 1)) < one := by change (0 : ℕ) < 1; decide
    let H : Fin (l + 1) → Fin 4 → ℤ := fun i => homogeneous (n i)
    have hH0 (i : Fin (l + 1)) : H i 0 = 0 := by simp [H]
    have hcmp (s t : Fin (l + 1)) (hst : s < t) (j k : Fin 4) :
        cmp (H t j - H s j) (H t k - H s k) =
          cmp (H one j - H 0 j) (H one k - H 0 k) := by
      have hc : color (n s) (n t) = color (n 0) (n one) :=
        (hrel s t hst).2.trans (hrel 0 one h01).2.symm
      exact congrFun (congrFun hc j) k
    obtain ⟨m, hm, rep, cls, b, shift, f, hclass, hf0, hz, hmono, hfactor⟩ :=
      NormalizeChain.normalize H 0 one (fun i => Fin.zero_le i) h01 hcmp
    have hmpos : 0 < m := by
      by_contra hmnot
      have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmnot
      subst m
      have hcls (j : Fin 4) : cls j = 0 := by
        apply Fin.ext
        have hj := (cls j).isLt
        change (cls j).val = 0
        omega
      have hshift (i : Fin (l + 1)) : b 0 + shift i = 0 := by
        have h := hfactor i 0
        rw [hH0 i, hcls 0, hf0 i] at h
        omega
      have hconstant (i : Fin (l + 1)) (j : Fin 4) : H i j = b j - b 0 := by
        have h := hfactor i j
        rw [hcls j, hf0 i] at h
        have hs := hshift i
        omega
      have heq : n 0 = n one := by
        funext j
        have h := (hconstant 0 j.succ).trans (hconstant one j.succ).symm
        simpa [H] using h
      exact (ne_of_lt h01) (hinj heq)
    have hmcases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    obtain ⟨s, E, weights, hE0, hweights, _, hcoords, hdistinct⟩ :=
      NormalizedStaircase.normalized hmcases a ha hK hpow hL f hf0 hz hmono
    obtain ⟨q, hqhull, hqdistinct⟩ :=
      NormalizedIntruder.normalized_intruder a ha (fun i => H (s i))
        b (fun i => shift (s i)) (fun j i => f j (s i)) cls rep
        hclass (fun i => hf0 (s i)) (fun i => hH0 (s i))
        (fun i j => hfactor (s i) j) E hE0 weights (fun i => (hweights i).le)
        hcoords hdistinct
    have hpoint (i : Option (Fin m)) :
        NormalizedIntruder.originalPoint a (fun i => H (s i)) i =
          RootBound.evaluate a (n (s i)) := by
      funext j
      simp [NormalizedIntruder.originalPoint, RootBound.evaluate, H]
    have hUV : Set.range (NormalizedIntruder.originalPoint a (fun i => H (s i))) ⊆ V := by
      rintro _ ⟨i, rfl⟩
      rw [hpoint i]
      exact hmem (s i)
    apply no_intruder ha hV hUV hqhull
    · intro j
      exact ⟨q j, rfl⟩
    · rintro ⟨i, hi⟩
      exact hqdistinct i hi.symm

/-- The exact intended three-dimensional finiteness proposition, using the
faithful four-clause definition from `LatticeBasics`. -/
theorem finite_bound :
    ∀ a : ℝ, 1 < a → ∃ N : ℕ, ∀ V : Set (Fin 3 → ℝ),
      IsEmptyPolytope (expLattice 3 a) V → V.ncard ≤ N := by
  intro a ha
  obtain ⟨K, hK, hpowNat⟩ := RootBound.exists_positive_power_four ha
  have hpow : (4 : ℝ) ≤ a ^ (K : ℤ) := by
    simpa only [zpow_natCast] using hpowNat
  refine ⟨(6 * K) ^ (3 ^ 16), ?_⟩
  intro V hV
  apply RootBound.empty_ncard_le a V hV (6 * K)
  intro L c n hinj hmem hrel
  exact chain_length_le a ha K hK hpow V hV L c n hinj hmem hrel


end JigP5.ChainBound

namespace Submissions.ExpLatticeHellyFinite.Staircase

/-- Every three-dimensional exponential lattice has a finite empty-polytope bound. -/
theorem proof :
    ∀ a : ℝ, 1 < a → ∃ N : ℕ, ∀ V : Set (Fin 3 → ℝ),
      JigP5.LatticeBasics.IsEmptyPolytope (JigP5.LatticeBasics.expLattice 3 a) V →
        V.ncard ≤ N :=
  JigP5.ChainBound.finite_bound

end Submissions.ExpLatticeHellyFinite.Staircase
