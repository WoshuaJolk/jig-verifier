import Mathlib

/- BEGIN bundled local module DeletionPermutation -/

namespace ColeskiDeletionPermutation

noncomputable def deletionEquiv {n : Nat} (z : Fin (n+1)) :
    Fin n ≃ {u : Fin (n+1) // u ≠ z} := by
  refine Equiv.ofBijective (fun i => ⟨z.succAbove i,Fin.succAbove_ne z i⟩) ⟨?_,?_⟩
  · intro i j h
    exact Fin.succAbove_right_injective (congrArg Subtype.val h)
  · intro u
    obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq u.property
    exact ⟨i,Subtype.ext hi⟩

theorem deletionEquiv_apply {n : Nat} (z : Fin (n+1)) (i : Fin n) :
    ((deletionEquiv z) i).val = z.succAbove i := by rfl

noncomputable def complementMap {n : Nat} (p : Equiv.Perm (Fin (n+1))) (z : Fin (n+1)) :
    {u : Fin (n+1) // u ≠ z} ≃ {u : Fin (n+1) // u ≠ p z} :=
  p.subtypeEquiv (by intro a; simp only [ne_eq,p.injective.eq_iff])

noncomputable def deletionPerm {n : Nat} (p : Equiv.Perm (Fin (n+1))) (z : Fin (n+1)) :
    Equiv.Perm (Fin n) :=
  (deletionEquiv z).trans ((complementMap p z).trans (deletionEquiv (p z)).symm)

theorem embed_permute {n : Nat} (p : Equiv.Perm (Fin (n+1))) (z : Fin (n+1)) (i : Fin n) :
    (p z).succAbove (deletionPerm p z i) = p (z.succAbove i) := by
  change ((deletionEquiv (p z)) (deletionPerm p z i)).val = _
  simp only [deletionPerm,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

theorem embed_inverse {n : Nat} (p : Equiv.Perm (Fin (n+1))) (z : Fin (n+1)) (i : Fin n) :
    z.succAbove ((deletionPerm p z)⁻¹ i) = p⁻¹ ((p z).succAbove i) := by
  apply p.injective
  rw [← embed_permute p z ((deletionPerm p z)⁻¹ i)]
  simp
end ColeskiDeletionPermutation
#print axioms ColeskiDeletionPermutation.embed_permute
#print axioms ColeskiDeletionPermutation.embed_inverse

/- END bundled local module DeletionPermutation -/
