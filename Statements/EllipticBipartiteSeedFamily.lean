import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# EllipticBipartiteSeedFamily

Proposed infinite seed theorem arising from elliptic normal curves.

For every even dimension `k = 2r ≥ 4` and every even half-order
`n = 2N ≥ k + 4`, the explicit balanced translate/anti-translate incidence
pattern below has a tight exact `(k+1)`-spanning Hermitian representation in
`ℂ^k`. Its bipartite graph is connected, `k`-regular, and decomposes into `k`
perfect matchings. The total seed order is `m = 2n`, hence
`m ≡ 0 (mod 4)` and `m ≥ 2k + 8`.
-/

namespace Statements.EllipticBipartiteSeedFamily

/-- The even translate offsets. -/
def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

/-- The odd anti-translate offsets
`1,3,...,2r-3,2r+1`. -/
def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

/-- Balanced translate/anti-translate incidence. -/
def CrossAdj {r N : ℕ} (i j : ZMod (2 * N)) : Prop :=
  (∃ c : Fin r, j = i + cOffset c) ∨
  (∃ d : Fin r, j = -i + dOffset d)

/-- Finite-index version of the cyclic incidence relation. -/
def CrossAdjFin {r N : ℕ} (i j : Fin (2 * N)) : Prop :=
  CrossAdj (r := r) (N := N) (i.val : ZMod (2 * N)) (j.val : ZMod (2 * N))

def Tight {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ S : Finset ι, S.card + 1 ≤ k →
    LinearIndependent ℂ fun i : (S : Set ι) => v i.1

def KPlusOneSpanning {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ S : Finset ι, S.card = k + 1 →
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i.1) = ⊤

/-- The elliptic normal curve seed family. -/
abbrev statement : Prop :=
  ∀ r N : ℕ, 2 ≤ r → r + 2 ≤ N →
    let k := 2 * r
    let n := 2 * N
    ∃ a b : Fin n → EuclideanSpace ℂ (Fin k),
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (∀ i j, inner ℂ (a i) (b j) = 0 ↔
        CrossAdjFin (r := r) (N := N) i j) ∧
      (∀ i j, i ≠ j →
        inner ℂ (a i) (a j) ≠ 0 ∧ inner ℂ (b i) (b j) ≠ 0) ∧
      Tight (Sum.elim a b) ∧
      KPlusOneSpanning (Sum.elim a b)

theorem target : statement := sorry

end Statements.EllipticBipartiteSeedFamily
