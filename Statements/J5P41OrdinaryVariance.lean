import Init

namespace Statements.J5P41OrdinaryVariance

def rowEnergy (a : Int) (xs : List Int) : Int :=
  (xs.map (fun x => (x-a)*(x-a))).sum

def pairEnergy : List Int → Int
  | [] => 0
  | x::xs => rowEnergy x xs + pairEnergy xs

def ordinarySums : List Int → List Int
  | [] => []
  | x::xs => (x+x)::((xs.map (fun y => x+y)) ++ ordinarySums xs)

def witness : List Int := [0,1,4,10,12,17,31]

def scaledDisplacements : List Int := [0,-36,-58,-59,-88,-96,-41]

/- Includes doubled summands, so it checks the ordinary Sidon definition. -/

abbrev statement : Prop :=
  ((ordinarySums witness).Nodup) ∧
  (scaledDisplacements = (witness.zipIdx.map (fun p => 7*p.1-43*(p.2 : Int)))) ∧
  (pairEnergy scaledDisplacements = 44590 ∧ 7*44590 > 774*343) ∧
  (¬ (ordinarySums [0,6,8,13,27,39,40]).Nodup)

end Statements.J5P41OrdinaryVariance
