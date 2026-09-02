import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingResidueWindowDead — one residue class per generator does not bound windows

The Window Bound (`ErdosMultiplesDoublingWindow`) says that for `n ≥ max A` every window
`(x, x+n]` holds at most `2 M(n)` multiples of `A`. The multiples of `a` in `(x, x+n]` are the
`i ∈ [1, n]` with `i ≡ −x (mod a)`, so the Window Bound is the special case `r_a = −x mod a`
of the *residue-class* inequality

  `#{ i ∈ [1, n] : ∃ a ∈ A, i ≡ r_a (mod a) } ≤ 2 · #{ i ∈ [1, n] : ∃ a ∈ A, a ∣ i }`,

with one residue class per generator. A natural proof shape for the Window Bound is to prove
this per-generator inequality for *arbitrary* residues, since it only counts one class per
generator and never uses that the classes come from a common shift.

This statement is the theorem that the arbitrary-residue inequality is **false**, even for
primitive `A`. Mechanism: for `A = d · S` with `S` a set of primes, choosing residues that are
pairwise distinct modulo `d` makes the classes pairwise disjoint (any two of them intersect only
in a common class modulo `d`), so the shifted count is the full sum `∑_p #{i ≤ n : i ≡ r_p (dp)}
≈ (n/d) ∑ 1/p`, while the aligned multiples are all multiples of `d`, so `M(n) ≤ n/d`. As
`∑_{p ≤ P} 1/p → ∞`, the ratio of the two sides is unbounded, growing like `log log P`.

Witness: `A = 17 · {primes ≤ 59}` (17 generators), `n = 1946`, residues `1, 2, …, 16, 0` in
increasing order of the generators: `M(1946) = 100` and the shifted union has `201 > 200`
elements.

What survives (`residual_of`): the Window Bound itself, whose residues `−x mod a` are
*compatible* (they agree on every `gcd(a, b)`); any proof of it must use that compatibility.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingResidueWindowDead

/-- There is a primitive `A`, `n ≥ max A` and residues `r_a` for which the union of the classes
`i ≡ r_a (mod a)` in `[1, n]` has more than `2 M(n)` elements. -/
abbrev statement : Prop :=
  ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    (∀ b ∈ A, ∀ c ∈ A, b ∣ c → b = c) ∧
    ∃ r : ℕ → ℕ, ∃ n : ℕ, (∀ a ∈ A, a ≤ n) ∧
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, k % a = r a)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingResidueWindowDead
