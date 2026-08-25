import Mathlib.Tactic

namespace Submissions.Erdos243NonnegativeCenteredState.Worker03Descent

private theorem centered_eventually_zero
    (C E : ℕ → ℕ) (hrec : ∀ n, C (n + 1) + E n = C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  classical
  have hstep : ∀ n, C (n + 1) ≤ C n := fun n => by
    have := hrec n
    omega
  have hanti : Antitone C := antitone_nat_of_succ_le hstep
  let P : ℕ → Prop := fun m => ∃ n, C n = m
  have hP : ∃ m, P m := ⟨C 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hP
  have hconst : ∀ n, N ≤ n → C n = C N := by
    intro n hn
    apply Nat.le_antisymm (hanti hn)
    rw [hN]
    exact Nat.find_min' hP ⟨n, rfl⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  have hn1 : N ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hsame : C (n + 1) = C n :=
    (hconst (n + 1) hn1).trans (hconst n hn).symm
  have := hrec n
  omega

theorem proof :
    ∀ (a D C E : ℕ → ℕ),
      (∀ n, 1 < a n) →
      (∀ n, 0 < C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, (E n : ℤ) =
        (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ)) →
      ∃ N, ∀ n, N ≤ n → a (n + 1) = a n ^ 2 - a n + 1 := by
  intro a D C E ha hCpos hD hC hE
  have htail : ∀ n, C (n + 1) + E n = C n := by
    intro n
    apply Int.ofNat_inj.mp
    push_cast
    rw [hE]
    have hc := congrArg (fun x : ℕ => (x : ℤ)) (hC n)
    push_cast at hc
    nlinarith
  obtain ⟨N, hzero⟩ := centered_eventually_zero C E htail
  refine ⟨N, fun n hn ↦ ?_⟩
  have hz := hzero n hn
  have hz1 := hzero (n + 1) (hn.trans (Nat.le_succ n))
  have he := hE n
  have he1 := hE (n + 1)
  rw [hz] at he
  rw [hz1] at he1
  norm_num at he he1
  have hc := congrArg (fun x : ℕ => (x : ℤ)) (hC n)
  have hd := congrArg (fun x : ℕ => (x : ℤ)) (hD n)
  push_cast at hc hd
  have hprod :
      ((a (n + 1) : ℤ) - ((a n : ℤ) ^ 2 - (a n : ℤ) + 1)) *
        (C n : ℤ) = 0 := by
    nlinarith
  have hCne : (C n : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hCpos n))
  have hfactor := (mul_eq_zero.mp hprod).resolve_right hCne
  have hnat :
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
    nlinarith
  have hle : a n ≤ a n ^ 2 := by
    nlinarith [ha n]
  apply Int.ofNat_inj.mp
  rw [Nat.cast_add, Nat.cast_sub hle]
  push_cast
  exact hnat

end Submissions.Erdos243NonnegativeCenteredState.Worker03Descent
