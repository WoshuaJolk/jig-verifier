import Mathlib
namespace Statements.E811BinaryRootProfile
open Finset
abbrev Profile := Fin 6 → Fin 6

def Binary (p : Profile) : Prop := ∃ c : Fin 6, c ≠ 0 ∧ ∀ u, p u = 0 ∨ p u = c

/-- Two disjoint rainbow triangles, with every edge between them colored zero. -/
def root : Fin 6 → Fin 6 → Fin 6 :=
  ![![0,0,0,0,0,4], ![0,0,0,0,0,5], ![0,0,0,1,2,0],
    ![0,0,1,0,3,0], ![0,0,2,3,0,0], ![4,5,0,0,0,0]]

def edge (p q : Profile) (c : Fin 6) (x y : Fin 8) : Fin 6 :=
  if hx : x.val < 6 then
    if hy : y.val < 6 then root ⟨x.val,hx⟩ ⟨y.val,hy⟩
    else if y.val = 6 then p ⟨x.val,hx⟩ else q ⟨x.val,hx⟩
  else if hy : y.val < 6 then
    if x.val = 6 then p ⟨y.val,hy⟩ else q ⟨y.val,hy⟩
  else if x = y then 0 else c

def Compatible (p q : Profile) (c : Fin 6) : Prop :=
  (∀ v : Fin 6 → Fin 8, Function.Injective v →
    ¬ Function.Injective (fun i : Fin 6 => edge p q c (v i) (v (i+1)))) ∧
  (∀ v : Fin 5 → Fin 8, Function.Injective v →
    ¬ Function.Injective (![edge p q c (v 0) (v 1), edge p q c (v 1) (v 2),
      edge p q c (v 2) (v 0), edge p q c (v 0) (v 3),
      edge p q c (v 3) (v 4), edge p q c (v 4) (v 0)] : Fin 6 → Fin 6))

/-- An iid one-fresh profile law with a symmetric two-fresh extension,
exact marked-coordinate and marked-edge balance, and allowed-pattern support,
cannot be concentrated on the binary profiles. -/
abbrev statement : Prop :=
  ∀ (mass : Profile → ℝ) (pair : Profile → Profile → Fin 6 → ℝ),
    (∀ p, 0 ≤ mass p) → (∑ p, mass p) = 1 →
    (∀ p, ¬ Binary p → mass p = 0) →
    (∀ p q c, 0 ≤ pair p q c) →
    (∀ p q c, pair p q c = pair q p c) →
    (∀ p q, (∑ c, pair p q c) = mass p * mass q) →
    (∀ p q c, ¬ Compatible p q c → pair p q c = 0) →
    (∀ p c, (∑ q, pair p q c) = mass p / 6) →
    (∀ p u c, (∑ q, ∑ e, if q u = c then pair p q e else 0) = mass p / 6) →
    False

theorem target : statement := sorry
end Statements.E811BinaryRootProfile
