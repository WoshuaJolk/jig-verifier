import Init

namespace Statements.FiniteHypergraphCoreRemoval

def active (edge vertices : List Nat) : Bool :=
  edge.all (fun x => vertices.contains x)

def live (edges : List (List Nat)) (vertices : List Nat) : List (List Nat) :=
  edges.filter (fun edge => active edge vertices)

def degree (edges : List (List Nat)) (vertices : List Nat) (x : Nat) : Nat :=
  (live edges vertices).countP (fun edge => edge.contains x)

def difference (vertices core : List Nat) : List Nat :=
  vertices.filter (fun x => !(core.contains x))

abbrev statement : Prop :=
  ∀ (edges : List (List Nat)) (M L : Nat) (vertices : List Nat),
    (∀ edge ∈ edges, edge ≠ []) →
    ∃ core : List Nat,
      List.Sublist core vertices ∧
      (∀ x ∈ core, L < M * degree edges core x) ∧
      M * (live edges (difference vertices core)).length ≤
        L * (difference vertices core).length

theorem target : statement := sorry

end Statements.FiniteHypergraphCoreRemoval
