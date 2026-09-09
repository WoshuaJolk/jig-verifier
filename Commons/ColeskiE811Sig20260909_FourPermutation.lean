import Commons.ColeskiE811Sig20260909_TablePermutations

/- BEGIN bundled local module FourPermutation -/

namespace ColeskiFourPermutation
open ColeskiK4Coverage ColeskiTablePermutations

def initialEmbedding (n : Nat) : Fin n ↪ Fin (n+1) :=
  ⟨Fin.castSucc, by intro a b h; exact Fin.ext (congrArg (fun x : Fin (n+1) => x.val) h)⟩

noncomputable def liftInitial {n : Nat} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  p.viaEmbedding (initialEmbedding n)

theorem liftInitial_apply {n : Nat} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    liftInitial p i.castSucc = (p i).castSucc := by
  exact Equiv.Perm.viaEmbedding_apply p (initialEmbedding n) i

theorem liftInitial_last {n : Nat} (p : Equiv.Perm (Fin n)) :
    liftInitial p (Fin.last n) = Fin.last n := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i,hi⟩
  have h : i.val = n := congrArg (fun x : Fin (n+1) => x.val) hi
  omega

noncomputable def vertexPerm4 (v : Fin 24) : Equiv.Perm (Fin 4) :=
  fromList 4 (digit vertexPermutations[v.val]!) (vertex_permutations_valid v)

theorem vertexPerm4_apply (v : Fin 24) (i : Fin 4) :
    (vertexPerm4 v i).val = digit vertexPermutations[v.val]! i.val := by rfl
end ColeskiFourPermutation
#print axioms ColeskiFourPermutation.liftInitial_apply
#print axioms ColeskiFourPermutation.liftInitial_last
#print axioms ColeskiFourPermutation.vertexPerm4_apply

/- END bundled local module FourPermutation -/
