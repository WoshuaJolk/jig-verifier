import Commons.ColeskiE811Sig20260909_K4SemanticsOnly
import Commons.ColeskiE811Sig20260909_K5SemanticsOnly

/- BEGIN bundled local module TablePermutations -/

namespace ColeskiTablePermutations
open ColeskiK4Coverage ColeskiK5Coverage

noncomputable def fromList (n : Nat) (f : Nat → Nat)
    (hp : ((List.range n).map f).Perm (List.range n)) : Equiv.Perm (Fin n) := by
  have bound (i : Fin n) : f i.val < n := by
    have hm : f i.val ∈ (List.range n).map f := List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
    exact List.mem_range.mp (hp.mem_iff.mp hm)
  let g : Fin n → Fin n := fun i => ⟨f i.val, bound i⟩
  have hnodup : ((List.range n).map f).Nodup := hp.nodup_iff.mpr (List.nodup_range (n := n))
  have hinj : Function.Injective g := by
    intro i j h
    apply Fin.ext
    exact (List.nodup_map_iff_inj_on (List.nodup_range (n := n))).mp hnodup
      i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
      (congrArg Fin.val h)
  exact Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hinj,rfl⟩)

theorem fromList_apply (n : Nat) (f : Nat → Nat)
    (hp : ((List.range n).map f).Perm (List.range n)) (i : Fin n) :
    (fromList n f hp i).val = f i.val := by rfl

noncomputable def colorPerm (i : Fin 60) : Equiv.Perm (Fin 6) :=
  fromList 6 (digit colorPermutations[i.val]!) (color_permutations_valid i)

noncomputable def vertexPerm (i : Fin 120) : Equiv.Perm (Fin 5) :=
  fromList 5 (digit vertexPermutations5[i.val]!) (vertex_permutations5_valid i)

theorem colorPerm_apply (i : Fin 60) (a : Fin 6) :
    (colorPerm i a).val = digit colorPermutations[i.val]! a.val := by rfl

theorem vertexPerm_apply (i : Fin 120) (a : Fin 5) :
    (vertexPerm i a).val = digit vertexPermutations5[i.val]! a.val := by rfl

theorem colorPerm_preserves (i : Fin 60) (a b c : Fin 6) :
    good (colorPerm i a) (colorPerm i b) (colorPerm i c) = good a b c :=
  color_permutations_good i a b c
end ColeskiTablePermutations
#print axioms ColeskiTablePermutations.fromList_apply
#print axioms ColeskiTablePermutations.colorPerm_preserves

/- END bundled local module TablePermutations -/
