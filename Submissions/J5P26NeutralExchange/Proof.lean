import Init

namespace Submissions.J5P26NeutralExchange.Proof

def path : Array (List Nat) := #[[0,1,2,4,5,9,10,12,14],[0,1,3,4,5,9,10,12,14],[0,1,3,4,9,10,12,13,14],[0,1,3,7,9,10,12,13,14],[0,1,3,6,7,10,12,13,14],[0,1,3,6,7,8,10,13,14]]
def finalSet : List Nat := [0,1,3,6,7,8,10,11,13,14]

abbrev APFree (s : List Nat) : Prop :=
  ∀ a : Fin 15, ∀ d : Fin 5, 0 < d.val → a.val+3*d.val < 15 →
    (s.contains a.val && s.contains (a.val+d.val) &&
      s.contains (a.val+2*d.val) && s.contains (a.val+3*d.val)) = false

def step (i : Fin 6) : List Nat := path[i.val]!

theorem path_free : ∀ i : Fin 6, APFree (step i) := by
  unfold APFree step path
  decide

theorem path_sizes : ∀ i : Fin 6,
    (step i).length = 9 ∧ (step i).Pairwise (fun x y => x ≠ y) := by
  unfold step path
  decide

theorem single_swaps : ∀ i : Fin 5,
    ((path[i.val]!).filter (fun x => !(path[i.val+1]!).contains x)).length = 1 ∧
    ((path[i.val+1]!).filter (fun x => !(path[i.val]!).contains x)).length = 1 := by
  unfold path
  decide

theorem final_gain : APFree finalSet ∧ finalSet.length = 10 ∧
    finalSet.Pairwise (fun x y => x ≠ y) ∧
    (∀ x : Fin 15, (path[5]!).contains x.val = true → finalSet.contains x.val = true) ∧
    (path[5]!).contains 11 = false ∧ finalSet.contains 11 = true := by
  unfold APFree finalSet path
  decide

theorem solves :
  (∀ i : Fin 6, APFree (step i)) ∧
  (∀ i : Fin 6,
    (step i).length = 9 ∧ (step i).Pairwise (fun x y => x ≠ y)) ∧
  (∀ i : Fin 5,
    ((path[i.val]!).filter (fun x => !(path[i.val+1]!).contains x)).length = 1 ∧
    ((path[i.val+1]!).filter (fun x => !(path[i.val]!).contains x)).length = 1) ∧
  (APFree finalSet ∧ finalSet.length = 10 ∧
    finalSet.Pairwise (fun x y => x ≠ y) ∧
    (∀ x : Fin 15, (path[5]!).contains x.val = true → finalSet.contains x.val = true) ∧
    (path[5]!).contains 11 = false ∧ finalSet.contains 11 = true) := by
  exact ⟨@path_free, @path_sizes, @single_swaps, @final_gain⟩

end Submissions.J5P26NeutralExchange.Proof
