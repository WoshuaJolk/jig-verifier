import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite

namespace Statements.Erdos117FiniteStemAssembly

open QuotientGroup Subgroup

universe u v

/-- Exact assembly of the finiteness paragraph in Lecomte,
arXiv:2608.20507v1, Lemma 2.1, source lines 78--83.

The two equivalences are the isoclinism data from source line 80.
Finiteness of `G/Z(G)` is the output of Neumann used in line 78, finiteness
of `G'` is the output of Schur used in line 83, and `Z(H) ≤ H'` is the stem
condition supplied by Hall in lines 78--83. -/
abbrev statement : Prop :=
  ∀ (G : Type u) (H : Type v) (_ : Group G) (_ : Group H),
    Finite (G ⧸ center G) →
    Finite (commutator G) →
    ((G ⧸ center G) ≃* (H ⧸ center H)) →
    (commutator G ≃* commutator H) →
    center H ≤ commutator H →
    Finite H

theorem target : statement := sorry

end Statements.Erdos117FiniteStemAssembly
