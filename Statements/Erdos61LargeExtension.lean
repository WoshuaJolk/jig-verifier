import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

namespace Statements.Erdos61LargeExtension

open SimpleGraph

noncomputable def extensions {α β : Type*} [Fintype β]
    (H : SimpleGraph α) (G : SimpleGraph β) (v : α)
    (φ : H.induce {a | a ≠ v} ↪g G) : Finset β := by
  classical
  exact Finset.univ.filter fun x =>
    (∀ u : {a : α // a ≠ v}, x ≠ φ u) ∧
    (∀ u : {a : α // a ≠ v}, G.Adj x (φ u) ↔ H.Adj v u.val)

abbrev statement : Prop :=
  ∀ {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H : SimpleGraph α) (G : SimpleGraph β) (v : α) (r : ℕ),
    Fintype.card α ≤ r → r ≤ Fintype.card β →
    (∀ S : Finset β, S.card = r → ∃ e : H ↪g G, ∀ a : α, e a ∈ S) →
      ∃ φ : H.induce {a | a ≠ v} ↪g G,
        Fintype.card β ≤ (extensions H G v φ).card * r ^ Fintype.card α

end Statements.Erdos61LargeExtension
