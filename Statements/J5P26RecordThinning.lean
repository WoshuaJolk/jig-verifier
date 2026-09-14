import Init

namespace Statements.J5P26RecordThinning

def vertices : List Nat := [0,1,2,4,5,7,8,9,14,16,17,18]

def triples : List (Nat × Nat × Nat) := [(0,1,2),(0,2,3),(0,3,6),(0,5,8),(0,6,9),(0,7,11),(1,3,5),(1,4,7),(1,7,10),(2,4,6),(2,6,8),(2,7,9),(3,7,8),(4,5,7),(5,6,7),(8,9,11),(9,10,11)]

def fourFree : Bool :=
  !((List.range 19).any (fun a => (List.range 7).any (fun d =>
    decide (0<d ∧ a+3*d<19) && (List.range 4).all (fun j => vertices.contains (a+j*d)))))

def hasMono (mask : Nat) : Bool :=
  triples.any (fun e => (mask.testBit e.1 == mask.testBit e.2.1) &&
    (mask.testBit e.2.1 == mask.testBit e.2.2))

def colors : List Nat := [0,2,1,2,2,1,2,1,1,2,1,1]

abbrev statement : Prop :=
  (vertices.length=12 ∧ vertices.Pairwise (fun x y => x<y) ∧
    vertices.all (fun x => decide (x<19))=true ∧ fourFree=true) ∧
  (triples =
    (List.range 12).flatMap (fun i => (List.range 12).flatMap (fun j =>
      (List.range 12).flatMap (fun k =>
        if i<j ∧ j<k ∧ vertices[i]! + vertices[k]! = 2*vertices[j]!
        then [(i,j,k)] else [])))) ∧
  (∀ mask : Fin 4096, hasMono mask.val=true) ∧
  (colors.length=12 ∧
    colors.all (fun x => decide (x<3))=true ∧
    triples.all (fun e => !((colors[e.1]! == colors[e.2.1]!) &&
      (colors[e.2.1]! == colors[e.2.2]!)))=true)

end Statements.J5P26RecordThinning
