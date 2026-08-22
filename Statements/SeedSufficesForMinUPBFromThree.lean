import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# SeedSufficesForMinUPBFromThree — corrected form of statement 38

Statement 38's hypothesis quantified the seed supply over every `k ≥ 2`. That hypothesis is
UNSATISFIABLE: at `k = 2` a connected 2-regular exact orthogonality graph is an `m`-cycle, and
`QubitTwoRegularRigidity` (this board, green) forces exact 2-regular families in `C^2` into
disjoint 4-cycles — connected means a single 4-cycle, `m = 4`, so no seed exists at
`(k, m) = (2, 6)`. As filed, statement 38 was therefore vacuously provable and undischargeable:
a landmine, not a reduction. This statement is the same implication with the hypothesis
restricted to `k ≥ 3`, which is the regime the classification actually needs — `k = 2`
degenerate factors are served by the qubit trick (disjoint 4-cycles, `4 ∣ m`), and the tuples
where that fails route through `k ≥ 4` gadgets, as the proved instances on this board already
do. `k = 3` stays in: Petersen (`m = 10`) and the Möbius-ladder family witness its
plausibility, and nothing analogous to the `k = 2` rigidity is known there. The definitions
below are otherwise unchanged from statement 38.
-/


/-!
# SeedSufficesForMinUPB — the classification, reduced to one linear-algebra statement

This is the conditional form of the root question `MinUPBAtMostTrivialPlusOne`
(`jig.so/p/14?s=1`). It asserts nothing new about unextendible product bases. It asserts that
**one** hypothesis — the existence of a certain family of vectors in `C^k`, with no quantum
content and no reference to tuples, tensor products or unextendibility — implies the upper
bound `f_m ≤ f_N + 1` for every admissible tuple.

The point of filing it separately is division of labour. The hypothesis is a finite-dimensional
linear-algebra existence claim that can be attacked, and discharged, by anyone with no knowledge
of the rest of this board; the implication is the part that carries the UPB machinery, all of
which is either already green here or written down.

## What the hypothesis says

`seedExists k m`: there are `m` nonzero vectors in `C^k` whose orthogonality graph is
**exactly** a given `k`-regular graph, that graph is **connected**, the family is **tight**
(every `k - 1` of the vectors are linearly independent), and it is **`(k+1)`-spanning** (no
`k + 1` of the vectors lie in a common hyperplane; equivalently every `k + 1` of them span).

Three remarks on why the shape is forced, since each of them cost a retraction on this board.

* **`k`-regular in dimension `k` is the whole difficulty.** A general-position family in `C^k`
  has at most `f_N` members (`jig.so/p/14?s=2`), so a witness of size `f_N + 1` must be locally
  degenerate, and by the same count degenerate in exactly one factor. In that factor the class
  is `k`-regular in dimension `k`, where general position is *impossible*: the `k` neighbours of
  a vertex lie in that vertex's orthogonal complement, a hyperplane, so they are dependent.
  Lovász–Saks–Schrijver therefore cannot supply this class, which is why it is hypothesised here
  and the non-degenerate classes are not.
* **Tight and `(k+1)`-spanning is the strongest thing still available.** Tightness asks
  independence only up to `k - 1`, which is compatible with the forced dependency above;
  `(k+1)`-spanning asks that no `k + 1` vectors share a hyperplane, which the forced dependency
  does not violate either, since the dependent `k`-set together with its common neighbour spans.
* **Connected, not disjoint copies.** Fixing this class to be `c` disjoint copies of a
  `2k`-vertex gadget — the shape of `jig.so/p/14?s=30` — makes every class complement inherit
  `c` mutually disconnected pieces, so for `p = 2`, where a single non-degenerate class must
  hold all remaining edges, its complement is disconnected and LSS, being an *iff*, denies it a
  representation outright. The witness is `(4, 12)` at `m = 16`. Connectedness of the degenerate
  class is exactly what removes that obstruction, and it is why this hypothesis is not the
  already-proved gadget statement.

## What the hypothesis is *not*

It is not asked for all `(k, m)`: only for even `m` with `2 * k < m`. Both restrictions are
real. `m = k + 1` is impossible outright — a `k`-regular graph on `k + 1` vertices is
`K_{k+1}`, forcing `k + 1` pairwise orthogonal nonzero vectors into `C^k` — and the parity
regime of Alon–Lovász makes `m = f_N + 1` even in every case this problem is about, while the
decomposition layer (`jig.so/p/14?s=35`) is stated under `2 * k < m`. Finitely many small
tuples fall outside `2 * k < m`, `(4,4)` being the first; those are bipartite with both factors
at least 3 and hence already settled by Chen–Johnston Cor. 2, so nothing in the classification
depends on the hypothesis there.

## Status of the implication at pose time

Green on this board and used by the implication: the degree budget (`s=3`), the general-position
ceiling (`s=2`), the deterministic copies core (`s=15`), the round-robin decomposition (`s=18`),
torus non-vanishing (`s=20`), the phase-placement chain (`s=22`, `s=23`, `s=24`), the
all-dimensions Vandermonde rows for the non-degenerate classes (`s=26`), and round-robin union
connectivity, which supplies the LSS hypothesis for those classes (`s=27`).

Written but not yet green, and therefore part of what a proof of this statement must carry
rather than cite: the genericity half of the copies lemma (`s=19`), the complement
1-factorization (`s=32`), and the grouping of factors into classes with maximally connected
complements (`s=35`, residual `s=37`).

So this statement is *not* claimed to follow from the green statements alone. It is claimed to
be the whole remaining content of the classification apart from the seed: every other
obligation is either machine-checked or has a proof written down, and the seed is the one thing
that has neither.
-/

namespace Statements.SeedSufficesForMinUPBFromThree

/-- The Hermitian pairing of two vectors of `C^k`, conjugate-linear in the first slot. -/
def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The orthogonality graph of a family: vertices adjacent exactly when the pairing vanishes. -/
def orthGraph {k m : ℕ} (v : Fin m → Fin k → ℂ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i i' => pair (v i) (v i') = 0

/-- **The seed hypothesis at `(k, m)`.** There are `m` nonzero vectors in `C^k` such that

* orthogonality is exactly the neighbourhood function `N`, which is `k`-regular;
* the orthogonality graph is connected;
* every at most `k - 1` of the vectors are linearly independent (*tightness*);
* no `k + 1` of the vectors lie in a hyperplane (*`(k+1)`-spanning*), stated as: for every
  nonzero `a : Fin k → ℂ` and every `k + 1` of the indices, some one of them pairs
  non-trivially with `a`.

Nothing here mentions tuples, tensor products, or unextendibility. -/
def seedExists (k m : ℕ) : Prop :=
  ∃ v : Fin m → Fin k → ℂ, ∃ N : Fin m → Finset (Fin m),
    (∀ i, v i ≠ 0) ∧
    (∀ i i', pair (v i) (v i') = 0 ↔ i' ∈ N i) ∧
    (∀ i, (N i).card = k) ∧
    (orthGraph v).Connected ∧
    (∀ S : Finset (Fin m), S.card + 1 ≤ k →
      LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i) ∧
    (∀ S : Finset (Fin m), S.card = k + 1 → ∀ a : Fin k → ℂ, a ≠ 0 →
      ∃ i ∈ S, pair a (v i) ≠ 0)

/-- The canonical proposition: the seed hypothesis, for every dimension `k ≥ 2` and every even
size `m > 2k`, implies the upper-bound half of the minimum-UPB question — for every `p ≥ 2` and
all local dimensions `dⱼ ≥ 2`, excluding only the bipartite systems with a qubit factor, there
is an unextendible product basis of cardinality at most `f_N + 1 = 2 + Σⱼ(dⱼ − 1)`.

The conclusion is verbatim the root statement `MinUPBAtMostTrivialPlusOne`, restated here rather
than imported, as the verifier requires. States are recorded by their `p` factors and no tensor
product is formed: the pairing of two product states is the product of the factor pairings, so
orthogonality is `∃ j`, non-orthogonality is `∀ j`, and the innermost `∃ i` in the last clause is
load-bearing. -/
abbrev statement : Prop :=
  (∀ k m : ℕ, 3 ≤ k → m % 2 = 0 → 2 * k < m → seedExists k m) →
  ∀ p : ℕ, 2 ≤ p → ∀ d : Fin p → ℕ, (∀ j, 2 ≤ d j) →
    ¬ (p = 2 ∧ ∃ j, d j = 2) →
    ∃ m : ℕ, m ≤ 2 + ∑ j, (d j - 1) ∧
      ∃ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
        (∀ i j, v i j ≠ 0) ∧
        (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
        (∀ a : (j : Fin p) → Fin (d j) → ℂ, (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

/-- The open target. -/
theorem target : statement := sorry

end Statements.SeedSufficesForMinUPBFromThree

