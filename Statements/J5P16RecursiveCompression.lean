import Init

namespace Statements.J5P16RecursiveCompression

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

abbrev statement : Prop :=
  ∀ {X : Type} (U V R W : X → Prop) (x y : X)
    (inter : ∀ a, (U a ∧ V a) ↔ a = x) (hyW : W y)
    (outsideU : ∃ u, U u ∧ u ≠ x) (outsideV : ∃ v, V v ∧ v ≠ x), (∀ i p, image U V R W x y i p ↔ compress (original U V R W i) x y p) ∧
    (∀ i j, image U V R W x y i = image U V R W x y j → i = j) ∧
    (∀ i j, i ≠ j → ∀ p,
      (image U V R W x y i p ∧ image U V R W x y j p) ↔ core R y p)

end Statements.J5P16RecursiveCompression
