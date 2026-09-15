import Init

namespace Submissions.J5P16RecursiveCompression.Proof

namespace Saved

inductive Block where
  | left | middle | right
  deriving DecidableEq

inductive Petal where
  | first | second | third
  deriving DecidableEq

def original {X : Type} (U V R W : X → Prop) : Petal → Block × X → Prop
  | .first, (.left, a) => U a
  | .second, (.left, a) => V a
  | .third, (.left, _) => False
  | _, (.middle, a) => R a
  | .first, (.right, _) => False
  | .second, (.right, _) => False
  | .third, (.right, a) => W a

def compress {X : Type} (F : Block × X → Prop) (x y : X)
    (p : Block × X) : Prop :=
  (F p ∧ p ≠ (.left, x)) ∨ (p = (.right, y) ∧ F (.left, x))

def image {X : Type} (U V R W : X → Prop) (x y : X) :
    Petal → Block × X → Prop
  | .first, (.left, a) => U a ∧ a ≠ x
  | .second, (.left, a) => V a ∧ a ≠ x
  | .third, (.left, _) => False
  | _, (.middle, a) => R a
  | .first, (.right, a) => a = y
  | .second, (.right, a) => a = y
  | .third, (.right, a) => W a

def core {X : Type} (R : X → Prop) (y : X) : Block × X → Prop
  | (.left, _) => False
  | (.middle, a) => R a
  | (.right, a) => a = y

theorem actual_compression {X : Type} (U V R W : X → Prop) (x y : X)
    (hxU : U x) (hxV : V x) :
    ∀ i p, image U V R W x y i p ↔ compress (original U V R W i) x y p := by
  intro i p
  rcases p with ⟨b, a⟩
  cases i <;> cases b <;> simp [image, compress, original, hxU, hxV]

theorem pair_intersections {X : Type} (U V R W : X → Prop) (x y : X)
    (inter : ∀ a, (U a ∧ V a) ↔ a = x) (hyW : W y) :
    ∀ i j, i ≠ j → ∀ p,
      (image U V R W x y i p ∧ image U V R W x y j p) ↔ core R y p := by
  have noUV : ∀ a, ¬ ((U a ∧ a ≠ x) ∧ (V a ∧ a ≠ x)) := by
    intro a h
    exact h.1.2 ((inter a).mp ⟨h.1.1, h.2.1⟩)
  have noVU : ∀ a, ¬ ((V a ∧ a ≠ x) ∧ (U a ∧ a ≠ x)) := by
    intro a h
    exact h.1.2 ((inter a).mp ⟨h.2.1, h.1.1⟩)
  intro i j hij p
  rcases p with ⟨b, a⟩
  cases i <;> cases j <;> cases b <;>
    simp_all [image, core]

theorem distinct_images {X : Type} (U V R W : X → Prop) (x y : X)
    (inter : ∀ a, (U a ∧ V a) ↔ a = x)
    (outsideU : ∃ u, U u ∧ u ≠ x) (outsideV : ∃ v, V v ∧ v ≠ x) :
    ∀ i j, image U V R W x y i = image U V R W x y j → i = j := by
  rcases outsideU with ⟨u, hu, hux⟩
  rcases outsideV with ⟨v, hv, hvx⟩
  have hnu : ¬ V u := by
    intro h
    exact hux ((inter u).mp ⟨hu, h⟩)
  have hnv : ¬ U v := by
    intro h
    exact hvx ((inter v).mp ⟨h, hv⟩)
  intro i j h
  cases i <;> cases j <;> try rfl
  all_goals
    have h_u := congrArg (fun f => f (.left, u)) h
    have h_v := congrArg (fun f => f (.left, v)) h
    simp_all [image]

theorem compression_certificate {X : Type} (U V R W : X → Prop) (x y : X)
    (inter : ∀ a, (U a ∧ V a) ↔ a = x) (hyW : W y)
    (outsideU : ∃ u, U u ∧ u ≠ x) (outsideV : ∃ v, V v ∧ v ≠ x) :
    (∀ i p, image U V R W x y i p ↔ compress (original U V R W i) x y p) ∧
    (∀ i j, image U V R W x y i = image U V R W x y j → i = j) ∧
    (∀ i j, i ≠ j → ∀ p,
      (image U V R W x y i p ∧ image U V R W x y j p) ↔ core R y p) := by
  have hx := (inter x).mpr rfl
  exact ⟨actual_compression U V R W x y hx.1 hx.2,
    distinct_images U V R W x y inter outsideU outsideV,
    pair_intersections U V R W x y inter hyW⟩

end Saved

def original {X : Type} (U V R W : X → Prop) : Ordering → Ordering × X → Prop
  | .lt, (.lt, a) => U a
  | .eq, (.lt, a) => V a
  | .gt, (.lt, _) => False
  | _, (.eq, a) => R a
  | .lt, (.gt, _) => False
  | .eq, (.gt, _) => False
  | .gt, (.gt, a) => W a

def compress {X : Type} (F : Ordering × X → Prop) (x y : X)
    (p : Ordering × X) : Prop :=
  (F p ∧ p ≠ (.lt, x)) ∨ (p = (.gt, y) ∧ F (.lt, x))

def image {X : Type} (U V R W : X → Prop) (x y : X) :
    Ordering → Ordering × X → Prop
  | .lt, (.lt, a) => U a ∧ a ≠ x
  | .eq, (.lt, a) => V a ∧ a ≠ x
  | .gt, (.lt, _) => False
  | _, (.eq, a) => R a
  | .lt, (.gt, a) => a = y
  | .eq, (.gt, a) => a = y
  | .gt, (.gt, a) => W a

def core {X : Type} (R : X → Prop) (y : X) : Ordering × X → Prop
  | (.lt, _) => False
  | (.eq, a) => R a
  | (.gt, a) => a = y

def toBlock : Ordering → Saved.Block
  | .lt => .left
  | .eq => .middle
  | .gt => .right

def fromBlock : Saved.Block → Ordering
  | .left => .lt
  | .middle => .eq
  | .right => .gt

def toPetal : Ordering → Saved.Petal
  | .lt => .first
  | .eq => .second
  | .gt => .third

def fromPetal : Saved.Petal → Ordering
  | .first => .lt
  | .second => .eq
  | .third => .gt

theorem from_to_block (b : Ordering) : fromBlock (toBlock b) = b := by
  cases b <;> rfl
theorem to_from_block (b : Saved.Block) : toBlock (fromBlock b) = b := by
  cases b <;> rfl
theorem from_to_petal (i : Ordering) : fromPetal (toPetal i) = i := by
  cases i <;> rfl
theorem to_from_petal (i : Saved.Petal) : toPetal (fromPetal i) = i := by
  cases i <;> rfl

theorem solves {X : Type} (U V R W : X → Prop) (x y : X)
    (inter : ∀ a, (U a ∧ V a) ↔ a = x) (hyW : W y)
    (outsideU : ∃ u, U u ∧ u ≠ x) (outsideV : ∃ v, V v ∧ v ≠ x) :
    (∀ i p, image U V R W x y i p ↔ compress (original U V R W i) x y p) ∧
    (∀ i j, image U V R W x y i = image U V R W x y j → i = j) ∧
    (∀ i j, i ≠ j → ∀ p,
      (image U V R W x y i p ∧ image U V R W x y j p) ↔ core R y p) := by
  have h := Saved.compression_certificate U V R W x y inter hyW outsideU outsideV
  refine ⟨?_, ?_, ?_⟩
  · intro i p
    rcases p with ⟨b, a⟩
    have hactual := h.1 (toPetal i) (toBlock b, a)
    cases i <;> cases b <;>
      simpa [image, compress, original, toPetal, toBlock,
        Saved.image, Saved.compress, Saved.original] using hactual
  · intro i j hij
    have hsaved : Saved.image U V R W x y (toPetal i) =
        Saved.image U V R W x y (toPetal j) := by
      funext p
      rcases p with ⟨b, a⟩
      have hpoint := congrArg (fun f => f (fromBlock b, a)) hij
      cases i <;> cases j <;> cases b <;>
        simpa [image, fromBlock, toPetal, Saved.image] using hpoint
    have hlabels := congrArg fromPetal (h.2.1 (toPetal i) (toPetal j) hsaved)
    simpa only [from_to_petal] using hlabels
  · intro i j hij p
    rcases p with ⟨b, a⟩
    have hne : toPetal i ≠ toPetal j := by
      intro heq
      apply hij
      have hlabels := congrArg fromPetal heq
      simpa only [from_to_petal] using hlabels
    have hinter := h.2.2 (toPetal i) (toPetal j) hne (toBlock b, a)
    cases i <;> cases j <;> cases b <;>
      simpa [image, core, toPetal, toBlock, Saved.image, Saved.core] using hinter

end Submissions.J5P16RecursiveCompression.Proof
