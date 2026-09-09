import Commons.ColeskiE811Sig20260909_ColorRigidity

/- BEGIN bundled local module ColorCompleteness -/

namespace ColeskiColorRigidity
open ColeskiK4Coverage ColeskiTablePermutations
set_option maxHeartbeats 0

theorem determined_by_three (p q : Equiv.Perm (Fin 6))
    (hp : ∀ a b c, good (p a) (p b) (p c) = good a b c)
    (hq : ∀ a b c, good (q a) (q b) (q c) = good a b c)
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) : p = q := by
  have h3 : p 3 = q 3 := by
    apply unique_other_mate (p 0) (p 1) (p 2) (p 3) (q 3)
    all_goals try first | exact p.injective.ne (by decide) | exact hp 0 1 2 | exact hp 0 1 3
    · rw [h0]; exact q.injective.ne (by decide)
    · rw [h1]; exact q.injective.ne (by decide)
    · rw [h2]; exact q.injective.ne (by decide)
    · rw [h0,h1]; exact hq 0 1 3
  have h4 : p 4 = q 4 := by
    apply unique_other_mate (p 0) (p 2) (p 1) (p 4) (q 4)
    all_goals try first | exact p.injective.ne (by decide) | exact hp 0 2 1 | exact hp 0 2 4
    · rw [h0]; exact q.injective.ne (by decide)
    · rw [h2]; exact q.injective.ne (by decide)
    · rw [h1]; exact q.injective.ne (by decide)
    · rw [h0,h2]; exact hq 0 2 4
  have h5 : p 5 = q 5 := by
    obtain ⟨j,hj⟩ := q.surjective (p 5)
    fin_cases j
    · exact False.elim ((p.injective.ne (by decide : (0 : Fin 6) ≠ 5)) (h0.trans hj))
    · exact False.elim ((p.injective.ne (by decide : (1 : Fin 6) ≠ 5)) (h1.trans hj))
    · exact False.elim ((p.injective.ne (by decide : (2 : Fin 6) ≠ 5)) (h2.trans hj))
    · exact False.elim ((p.injective.ne (by decide : (3 : Fin 6) ≠ 5)) (h3.trans hj))
    · exact False.elim ((p.injective.ne (by decide : (4 : Fin 6) ≠ 5)) (h4.trans hj))
    · exact hj.symm
  apply Equiv.ext
  intro x
  fin_cases x <;> assumption

theorem color_table_surjective (p : Equiv.Perm (Fin 6))
    (hp : ∀ a b c, good (p a) (p b) (p c) = good a b c) :
    ∃ i : Fin 60, p = colorPerm i := by
  obtain ⟨i,h0,h1,h2⟩ := triple_table (p 0) (p 1) (p 2)
    (p.injective.ne (by decide)) (p.injective.ne (by decide))
    (p.injective.ne (by decide)) (hp 0 1 2)
  refine ⟨i,determined_by_three p (colorPerm i) hp (colorPerm_preserves i) ?_ ?_ ?_⟩
  · exact Fin.ext h0.symm
  · exact Fin.ext h1.symm
  · exact Fin.ext h2.symm
end ColeskiColorRigidity
#print axioms ColeskiColorRigidity.color_table_surjective

/- END bundled local module ColorCompleteness -/
