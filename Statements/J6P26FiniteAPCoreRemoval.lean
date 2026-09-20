import Init

namespace Statements.J6P26FiniteAPCoreRemoval

def active (edge vertices : List Nat) : Bool :=
  edge.all (fun x => vertices.contains x)

def live (edges : List (List Nat)) (vertices : List Nat) : List (List Nat) :=
  edges.filter (fun edge => active edge vertices)

def degree (edges : List (List Nat)) (vertices : List Nat) (x : Nat) : Nat :=
  (live edges vertices).countP (fun edge => edge.contains x)

def difference (vertices core : List Nat) : List Nat :=
  vertices.filter (fun x => !(core.contains x))

def uniqueEdges : List (List Nat) → List (List Nat)
  | [] => []
  | edge :: edges =>
    let rest := uniqueEdges edges
    if edge ∈ rest then rest else edge :: rest

def rawAPEdges (N : Nat) : List (List Nat) :=
  (List.range (N + 1)).flatMap fun a =>
    (List.range (N + 1)).flatMap fun d =>
      if 0 < d ∧ a + 2 * d ≤ N then [[a, a + d, a + 2 * d]] else []

def apEdges (N : Nat) : List (List Nat) := uniqueEdges (rawAPEdges N)

abbrev statement : Prop :=
  ∀ (N M L : Nat) (vertices : List Nat)
    (hv : vertices.Nodup),
    ∃ core : List Nat,
      List.Sublist core vertices ∧
      (∀ x ∈ core, L < M * degree (apEdges N) core x) ∧
      M * (live (apEdges N) (difference vertices core)).length ≤
        L * (difference vertices core).length

end Statements.J6P26FiniteAPCoreRemoval
