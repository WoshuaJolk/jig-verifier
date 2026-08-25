import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic
namespace Submissions.Erdos11VerifiedBelow1001.CaseSplit
private theorem squarefree_123 : Squarefree (123 : ℕ) := by
  rw [show (123 : ℕ) = 3 * (41) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 3 by norm_num).squarefree,
      (show Nat.Prime 41 by norm_num).squarefree⟩

private theorem squarefree_145 : Squarefree (145 : ℕ) := by
  rw [show (145 : ℕ) = 5 * (29) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 5 by norm_num).squarefree,
      (show Nat.Prime 29 by norm_num).squarefree⟩

private theorem squarefree_249 : Squarefree (249 : ℕ) := by
  rw [show (249 : ℕ) = 3 * (83) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 3 by norm_num).squarefree,
      (show Nat.Prime 83 by norm_num).squarefree⟩

private theorem squarefree_330 : Squarefree (330 : ℕ) := by
  rw [show (330 : ℕ) = 2 * (3 * (5 * (11))) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 2 by norm_num).squarefree,
      (Nat.squarefree_mul (by norm_num)).2
      ⟨(show Nat.Prime 3 by norm_num).squarefree,
        (Nat.squarefree_mul (by norm_num)).2
        ⟨(show Nat.Prime 5 by norm_num).squarefree,
          (show Nat.Prime 11 by norm_num).squarefree⟩⟩⟩

private theorem squarefree_335 : Squarefree (335 : ℕ) := by
  rw [show (335 : ℕ) = 5 * (67) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 5 by norm_num).squarefree,
      (show Nat.Prime 67 by norm_num).squarefree⟩

private theorem squarefree_371 : Squarefree (371 : ℕ) := by
  rw [show (371 : ℕ) = 7 * (53) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 7 by norm_num).squarefree,
      (show Nat.Prime 53 by norm_num).squarefree⟩

private theorem squarefree_505 : Squarefree (505 : ℕ) := by
  rw [show (505 : ℕ) = 5 * (101) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 5 by norm_num).squarefree,
      (show Nat.Prime 101 by norm_num).squarefree⟩

private theorem squarefree_598 : Squarefree (598 : ℕ) := by
  rw [show (598 : ℕ) = 2 * (13 * (23)) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 2 by norm_num).squarefree,
      (Nat.squarefree_mul (by norm_num)).2
      ⟨(show Nat.Prime 13 by norm_num).squarefree,
        (show Nat.Prime 23 by norm_num).squarefree⟩⟩

private theorem squarefree_699 : Squarefree (699 : ℕ) := by
  rw [show (699 : ℕ) = 3 * (233) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 3 by norm_num).squarefree,
      (show Nat.Prime 233 by norm_num).squarefree⟩

private theorem squarefree_755 : Squarefree (755 : ℕ) := by
  rw [show (755 : ℕ) = 5 * (151) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 5 by norm_num).squarefree,
      (show Nat.Prime 151 by norm_num).squarefree⟩

private theorem squarefree_807 : Squarefree (807 : ℕ) := by
  rw [show (807 : ℕ) = 3 * (269) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 3 by norm_num).squarefree,
      (show Nat.Prime 269 by norm_num).squarefree⟩

private theorem squarefree_869 : Squarefree (869 : ℕ) := by
  rw [show (869 : ℕ) = 11 * (79) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 11 by norm_num).squarefree,
      (show Nat.Prime 79 by norm_num).squarefree⟩

private theorem squarefree_903 : Squarefree (903 : ℕ) := by
  rw [show (903 : ℕ) = 3 * (7 * (43)) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 3 by norm_num).squarefree,
      (Nat.squarefree_mul (by norm_num)).2
      ⟨(show Nat.Prime 7 by norm_num).squarefree,
        (show Nat.Prime 43 by norm_num).squarefree⟩⟩

private theorem squarefree_906 : Squarefree (906 : ℕ) := by
  rw [show (906 : ℕ) = 2 * (3 * (151)) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 2 by norm_num).squarefree,
      (Nat.squarefree_mul (by norm_num)).2
      ⟨(show Nat.Prime 3 by norm_num).squarefree,
        (show Nat.Prime 151 by norm_num).squarefree⟩⟩

private theorem squarefree_958 : Squarefree (958 : ℕ) := by
  rw [show (958 : ℕ) = 2 * (479) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 2 by norm_num).squarefree,
      (show Nat.Prime 479 by norm_num).squarefree⟩

private theorem squarefree_973 : Squarefree (973 : ℕ) := by
  rw [show (973 : ℕ) = 7 * (139) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 7 by norm_num).squarefree,
      (show Nat.Prime 139 by norm_num).squarefree⟩

private theorem squarefree_995 : Squarefree (995 : ℕ) := by
  rw [show (995 : ℕ) = 5 * (199) by norm_num]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨(show Nat.Prime 5 by norm_num).squarefree,
      (show Nat.Prime 199 by norm_num).squarefree⟩

theorem proof :
    ∀ n : ℕ, Odd n → 1 < n → n ≤ 1000 →
      ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  intro n hn hlo hhi
  rcases hn with ⟨t, rfl⟩
  have ht : t ≤ 499 := by omega
  interval_cases t
  case «0» => omega
  case «1» => exact ⟨2, 0, (show Nat.Prime 2 by norm_num).squarefree, by norm_num⟩
  case «2» => exact ⟨3, 1, (show Nat.Prime 3 by norm_num).squarefree, by norm_num⟩
  case «3» => exact ⟨5, 1, (show Nat.Prime 5 by norm_num).squarefree, by norm_num⟩
  case «4» => exact ⟨7, 1, (show Nat.Prime 7 by norm_num).squarefree, by norm_num⟩
  case «5» => exact ⟨7, 2, (show Nat.Prime 7 by norm_num).squarefree, by norm_num⟩
  case «6» => exact ⟨11, 1, (show Nat.Prime 11 by norm_num).squarefree, by norm_num⟩
  case «7» => exact ⟨13, 1, (show Nat.Prime 13 by norm_num).squarefree, by norm_num⟩
  case «8» => exact ⟨13, 2, (show Nat.Prime 13 by norm_num).squarefree, by norm_num⟩
  case «9» => exact ⟨17, 1, (show Nat.Prime 17 by norm_num).squarefree, by norm_num⟩
  case «10» => exact ⟨19, 1, (show Nat.Prime 19 by norm_num).squarefree, by norm_num⟩
  case «11» => exact ⟨19, 2, (show Nat.Prime 19 by norm_num).squarefree, by norm_num⟩
  case «12» => exact ⟨23, 1, (show Nat.Prime 23 by norm_num).squarefree, by norm_num⟩
  case «13» => exact ⟨23, 2, (show Nat.Prime 23 by norm_num).squarefree, by norm_num⟩
  case «14» => exact ⟨13, 4, (show Nat.Prime 13 by norm_num).squarefree, by norm_num⟩
  case «15» => exact ⟨29, 1, (show Nat.Prime 29 by norm_num).squarefree, by norm_num⟩
  case «16» => exact ⟨31, 1, (show Nat.Prime 31 by norm_num).squarefree, by norm_num⟩
  case «17» => exact ⟨31, 2, (show Nat.Prime 31 by norm_num).squarefree, by norm_num⟩
  case «18» => exact ⟨29, 3, (show Nat.Prime 29 by norm_num).squarefree, by norm_num⟩
  case «19» => exact ⟨37, 1, (show Nat.Prime 37 by norm_num).squarefree, by norm_num⟩
  case «20» => exact ⟨37, 2, (show Nat.Prime 37 by norm_num).squarefree, by norm_num⟩
  case «21» => exact ⟨41, 1, (show Nat.Prime 41 by norm_num).squarefree, by norm_num⟩
  case «22» => exact ⟨43, 1, (show Nat.Prime 43 by norm_num).squarefree, by norm_num⟩
  case «23» => exact ⟨43, 2, (show Nat.Prime 43 by norm_num).squarefree, by norm_num⟩
  case «24» => exact ⟨47, 1, (show Nat.Prime 47 by norm_num).squarefree, by norm_num⟩
  case «25» => exact ⟨47, 2, (show Nat.Prime 47 by norm_num).squarefree, by norm_num⟩
  case «26» => exact ⟨37, 4, (show Nat.Prime 37 by norm_num).squarefree, by norm_num⟩
  case «27» => exact ⟨53, 1, (show Nat.Prime 53 by norm_num).squarefree, by norm_num⟩
  case «28» => exact ⟨53, 2, (show Nat.Prime 53 by norm_num).squarefree, by norm_num⟩
  case «29» => exact ⟨43, 4, (show Nat.Prime 43 by norm_num).squarefree, by norm_num⟩
  case «30» => exact ⟨59, 1, (show Nat.Prime 59 by norm_num).squarefree, by norm_num⟩
  case «31» => exact ⟨61, 1, (show Nat.Prime 61 by norm_num).squarefree, by norm_num⟩
  case «32» => exact ⟨61, 2, (show Nat.Prime 61 by norm_num).squarefree, by norm_num⟩
  case «33» => exact ⟨59, 3, (show Nat.Prime 59 by norm_num).squarefree, by norm_num⟩
  case «34» => exact ⟨67, 1, (show Nat.Prime 67 by norm_num).squarefree, by norm_num⟩
  case «35» => exact ⟨67, 2, (show Nat.Prime 67 by norm_num).squarefree, by norm_num⟩
  case «36» => exact ⟨71, 1, (show Nat.Prime 71 by norm_num).squarefree, by norm_num⟩
  case «37» => exact ⟨73, 1, (show Nat.Prime 73 by norm_num).squarefree, by norm_num⟩
  case «38» => exact ⟨73, 2, (show Nat.Prime 73 by norm_num).squarefree, by norm_num⟩
  case «39» => exact ⟨71, 3, (show Nat.Prime 71 by norm_num).squarefree, by norm_num⟩
  case «40» => exact ⟨79, 1, (show Nat.Prime 79 by norm_num).squarefree, by norm_num⟩
  case «41» => exact ⟨79, 2, (show Nat.Prime 79 by norm_num).squarefree, by norm_num⟩
  case «42» => exact ⟨83, 1, (show Nat.Prime 83 by norm_num).squarefree, by norm_num⟩
  case «43» => exact ⟨83, 2, (show Nat.Prime 83 by norm_num).squarefree, by norm_num⟩
  case «44» => exact ⟨73, 4, (show Nat.Prime 73 by norm_num).squarefree, by norm_num⟩
  case «45» => exact ⟨89, 1, (show Nat.Prime 89 by norm_num).squarefree, by norm_num⟩
  case «46» => exact ⟨89, 2, (show Nat.Prime 89 by norm_num).squarefree, by norm_num⟩
  case «47» => exact ⟨79, 4, (show Nat.Prime 79 by norm_num).squarefree, by norm_num⟩
  case «48» => exact ⟨89, 3, (show Nat.Prime 89 by norm_num).squarefree, by norm_num⟩
  case «49» => exact ⟨97, 1, (show Nat.Prime 97 by norm_num).squarefree, by norm_num⟩
  case «50» => exact ⟨97, 2, (show Nat.Prime 97 by norm_num).squarefree, by norm_num⟩
  case «51» => exact ⟨101, 1, (show Nat.Prime 101 by norm_num).squarefree, by norm_num⟩
  case «52» => exact ⟨103, 1, (show Nat.Prime 103 by norm_num).squarefree, by norm_num⟩
  case «53» => exact ⟨103, 2, (show Nat.Prime 103 by norm_num).squarefree, by norm_num⟩
  case «54» => exact ⟨107, 1, (show Nat.Prime 107 by norm_num).squarefree, by norm_num⟩
  case «55» => exact ⟨109, 1, (show Nat.Prime 109 by norm_num).squarefree, by norm_num⟩
  case «56» => exact ⟨109, 2, (show Nat.Prime 109 by norm_num).squarefree, by norm_num⟩
  case «57» => exact ⟨113, 1, (show Nat.Prime 113 by norm_num).squarefree, by norm_num⟩
  case «58» => exact ⟨113, 2, (show Nat.Prime 113 by norm_num).squarefree, by norm_num⟩
  case «59» => exact ⟨103, 4, (show Nat.Prime 103 by norm_num).squarefree, by norm_num⟩
  case «60» => exact ⟨113, 3, (show Nat.Prime 113 by norm_num).squarefree, by norm_num⟩
  case «61» => exact ⟨107, 4, (show Nat.Prime 107 by norm_num).squarefree, by norm_num⟩
  case «62» => exact ⟨109, 4, (show Nat.Prime 109 by norm_num).squarefree, by norm_num⟩
  case «63» => exact ⟨123, 2, squarefree_123, by norm_num⟩
  case «64» => exact ⟨127, 1, (show Nat.Prime 127 by norm_num).squarefree, by norm_num⟩
  case «65» => exact ⟨127, 2, (show Nat.Prime 127 by norm_num).squarefree, by norm_num⟩
  case «66» => exact ⟨131, 1, (show Nat.Prime 131 by norm_num).squarefree, by norm_num⟩
  case «67» => exact ⟨131, 2, (show Nat.Prime 131 by norm_num).squarefree, by norm_num⟩
  case «68» => exact ⟨73, 6, (show Nat.Prime 73 by norm_num).squarefree, by norm_num⟩
  case «69» => exact ⟨137, 1, (show Nat.Prime 137 by norm_num).squarefree, by norm_num⟩
  case «70» => exact ⟨139, 1, (show Nat.Prime 139 by norm_num).squarefree, by norm_num⟩
  case «71» => exact ⟨139, 2, (show Nat.Prime 139 by norm_num).squarefree, by norm_num⟩
  case «72» => exact ⟨137, 3, (show Nat.Prime 137 by norm_num).squarefree, by norm_num⟩
  case «73» => exact ⟨139, 3, (show Nat.Prime 139 by norm_num).squarefree, by norm_num⟩
  case «74» => exact ⟨145, 2, squarefree_145, by norm_num⟩
  case «75» => exact ⟨149, 1, (show Nat.Prime 149 by norm_num).squarefree, by norm_num⟩
  case «76» => exact ⟨151, 1, (show Nat.Prime 151 by norm_num).squarefree, by norm_num⟩
  case «77» => exact ⟨151, 2, (show Nat.Prime 151 by norm_num).squarefree, by norm_num⟩
  case «78» => exact ⟨149, 3, (show Nat.Prime 149 by norm_num).squarefree, by norm_num⟩
  case «79» => exact ⟨157, 1, (show Nat.Prime 157 by norm_num).squarefree, by norm_num⟩
  case «80» => exact ⟨157, 2, (show Nat.Prime 157 by norm_num).squarefree, by norm_num⟩
  case «81» => exact ⟨131, 5, (show Nat.Prime 131 by norm_num).squarefree, by norm_num⟩
  case «82» => exact ⟨163, 1, (show Nat.Prime 163 by norm_num).squarefree, by norm_num⟩
  case «83» => exact ⟨163, 2, (show Nat.Prime 163 by norm_num).squarefree, by norm_num⟩
  case «84» => exact ⟨167, 1, (show Nat.Prime 167 by norm_num).squarefree, by norm_num⟩
  case «85» => exact ⟨167, 2, (show Nat.Prime 167 by norm_num).squarefree, by norm_num⟩
  case «86» => exact ⟨157, 4, (show Nat.Prime 157 by norm_num).squarefree, by norm_num⟩
  case «87» => exact ⟨173, 1, (show Nat.Prime 173 by norm_num).squarefree, by norm_num⟩
  case «88» => exact ⟨173, 2, (show Nat.Prime 173 by norm_num).squarefree, by norm_num⟩
  case «89» => exact ⟨163, 4, (show Nat.Prime 163 by norm_num).squarefree, by norm_num⟩
  case «90» => exact ⟨179, 1, (show Nat.Prime 179 by norm_num).squarefree, by norm_num⟩
  case «91» => exact ⟨181, 1, (show Nat.Prime 181 by norm_num).squarefree, by norm_num⟩
  case «92» => exact ⟨181, 2, (show Nat.Prime 181 by norm_num).squarefree, by norm_num⟩
  case «93» => exact ⟨179, 3, (show Nat.Prime 179 by norm_num).squarefree, by norm_num⟩
  case «94» => exact ⟨181, 3, (show Nat.Prime 181 by norm_num).squarefree, by norm_num⟩
  case «95» => exact ⟨127, 6, (show Nat.Prime 127 by norm_num).squarefree, by norm_num⟩
  case «96» => exact ⟨191, 1, (show Nat.Prime 191 by norm_num).squarefree, by norm_num⟩
  case «97» => exact ⟨193, 1, (show Nat.Prime 193 by norm_num).squarefree, by norm_num⟩
  case «98» => exact ⟨193, 2, (show Nat.Prime 193 by norm_num).squarefree, by norm_num⟩
  case «99» => exact ⟨197, 1, (show Nat.Prime 197 by norm_num).squarefree, by norm_num⟩
  case «100» => exact ⟨199, 1, (show Nat.Prime 199 by norm_num).squarefree, by norm_num⟩
  case «101» => exact ⟨199, 2, (show Nat.Prime 199 by norm_num).squarefree, by norm_num⟩
  case «102» => exact ⟨197, 3, (show Nat.Prime 197 by norm_num).squarefree, by norm_num⟩
  case «103» => exact ⟨199, 3, (show Nat.Prime 199 by norm_num).squarefree, by norm_num⟩
  case «104» => exact ⟨193, 4, (show Nat.Prime 193 by norm_num).squarefree, by norm_num⟩
  case «105» => exact ⟨179, 5, (show Nat.Prime 179 by norm_num).squarefree, by norm_num⟩
  case «106» => exact ⟨211, 1, (show Nat.Prime 211 by norm_num).squarefree, by norm_num⟩
  case «107» => exact ⟨211, 2, (show Nat.Prime 211 by norm_num).squarefree, by norm_num⟩
  case «108» => exact ⟨89, 7, (show Nat.Prime 89 by norm_num).squarefree, by norm_num⟩
  case «109» => exact ⟨211, 3, (show Nat.Prime 211 by norm_num).squarefree, by norm_num⟩
  case «110» => exact ⟨157, 6, (show Nat.Prime 157 by norm_num).squarefree, by norm_num⟩
  case «111» => exact ⟨191, 5, (show Nat.Prime 191 by norm_num).squarefree, by norm_num⟩
  case «112» => exact ⟨223, 1, (show Nat.Prime 223 by norm_num).squarefree, by norm_num⟩
  case «113» => exact ⟨223, 2, (show Nat.Prime 223 by norm_num).squarefree, by norm_num⟩
  case «114» => exact ⟨227, 1, (show Nat.Prime 227 by norm_num).squarefree, by norm_num⟩
  case «115» => exact ⟨229, 1, (show Nat.Prime 229 by norm_num).squarefree, by norm_num⟩
  case «116» => exact ⟨229, 2, (show Nat.Prime 229 by norm_num).squarefree, by norm_num⟩
  case «117» => exact ⟨233, 1, (show Nat.Prime 233 by norm_num).squarefree, by norm_num⟩
  case «118» => exact ⟨233, 2, (show Nat.Prime 233 by norm_num).squarefree, by norm_num⟩
  case «119» => exact ⟨223, 4, (show Nat.Prime 223 by norm_num).squarefree, by norm_num⟩
  case «120» => exact ⟨239, 1, (show Nat.Prime 239 by norm_num).squarefree, by norm_num⟩
  case «121» => exact ⟨241, 1, (show Nat.Prime 241 by norm_num).squarefree, by norm_num⟩
  case «122» => exact ⟨241, 2, (show Nat.Prime 241 by norm_num).squarefree, by norm_num⟩
  case «123» => exact ⟨239, 3, (show Nat.Prime 239 by norm_num).squarefree, by norm_num⟩
  case «124» => exact ⟨241, 3, (show Nat.Prime 241 by norm_num).squarefree, by norm_num⟩
  case «125» => exact ⟨249, 1, squarefree_249, by norm_num⟩
  case «126» => exact ⟨251, 1, (show Nat.Prime 251 by norm_num).squarefree, by norm_num⟩
  case «127» => exact ⟨251, 2, (show Nat.Prime 251 by norm_num).squarefree, by norm_num⟩
  case «128» => exact ⟨241, 4, (show Nat.Prime 241 by norm_num).squarefree, by norm_num⟩
  case «129» => exact ⟨257, 1, (show Nat.Prime 257 by norm_num).squarefree, by norm_num⟩
  case «130» => exact ⟨257, 2, (show Nat.Prime 257 by norm_num).squarefree, by norm_num⟩
  case «131» => exact ⟨199, 6, (show Nat.Prime 199 by norm_num).squarefree, by norm_num⟩
  case «132» => exact ⟨263, 1, (show Nat.Prime 263 by norm_num).squarefree, by norm_num⟩
  case «133» => exact ⟨263, 2, (show Nat.Prime 263 by norm_num).squarefree, by norm_num⟩
  case «134» => exact ⟨13, 8, (show Nat.Prime 13 by norm_num).squarefree, by norm_num⟩
  case «135» => exact ⟨269, 1, (show Nat.Prime 269 by norm_num).squarefree, by norm_num⟩
  case «136» => exact ⟨271, 1, (show Nat.Prime 271 by norm_num).squarefree, by norm_num⟩
  case «137» => exact ⟨271, 2, (show Nat.Prime 271 by norm_num).squarefree, by norm_num⟩
  case «138» => exact ⟨269, 3, (show Nat.Prime 269 by norm_num).squarefree, by norm_num⟩
  case «139» => exact ⟨277, 1, (show Nat.Prime 277 by norm_num).squarefree, by norm_num⟩
  case «140» => exact ⟨277, 2, (show Nat.Prime 277 by norm_num).squarefree, by norm_num⟩
  case «141» => exact ⟨281, 1, (show Nat.Prime 281 by norm_num).squarefree, by norm_num⟩
  case «142» => exact ⟨283, 1, (show Nat.Prime 283 by norm_num).squarefree, by norm_num⟩
  case «143» => exact ⟨283, 2, (show Nat.Prime 283 by norm_num).squarefree, by norm_num⟩
  case «144» => exact ⟨281, 3, (show Nat.Prime 281 by norm_num).squarefree, by norm_num⟩
  case «145» => exact ⟨283, 3, (show Nat.Prime 283 by norm_num).squarefree, by norm_num⟩
  case «146» => exact ⟨277, 4, (show Nat.Prime 277 by norm_num).squarefree, by norm_num⟩
  case «147» => exact ⟨293, 1, (show Nat.Prime 293 by norm_num).squarefree, by norm_num⟩
  case «148» => exact ⟨293, 2, (show Nat.Prime 293 by norm_num).squarefree, by norm_num⟩
  case «149» => exact ⟨283, 4, (show Nat.Prime 283 by norm_num).squarefree, by norm_num⟩
  case «150» => exact ⟨293, 3, (show Nat.Prime 293 by norm_num).squarefree, by norm_num⟩
  case «151» => exact ⟨271, 5, (show Nat.Prime 271 by norm_num).squarefree, by norm_num⟩
  case «152» => exact ⟨241, 6, (show Nat.Prime 241 by norm_num).squarefree, by norm_num⟩
  case «153» => exact ⟨179, 7, (show Nat.Prime 179 by norm_num).squarefree, by norm_num⟩
  case «154» => exact ⟨307, 1, (show Nat.Prime 307 by norm_num).squarefree, by norm_num⟩
  case «155» => exact ⟨307, 2, (show Nat.Prime 307 by norm_num).squarefree, by norm_num⟩
  case «156» => exact ⟨311, 1, (show Nat.Prime 311 by norm_num).squarefree, by norm_num⟩
  case «157» => exact ⟨313, 1, (show Nat.Prime 313 by norm_num).squarefree, by norm_num⟩
  case «158» => exact ⟨313, 2, (show Nat.Prime 313 by norm_num).squarefree, by norm_num⟩
  case «159» => exact ⟨317, 1, (show Nat.Prime 317 by norm_num).squarefree, by norm_num⟩
  case «160» => exact ⟨317, 2, (show Nat.Prime 317 by norm_num).squarefree, by norm_num⟩
  case «161» => exact ⟨307, 4, (show Nat.Prime 307 by norm_num).squarefree, by norm_num⟩
  case «162» => exact ⟨317, 3, (show Nat.Prime 317 by norm_num).squarefree, by norm_num⟩
  case «163» => exact ⟨311, 4, (show Nat.Prime 311 by norm_num).squarefree, by norm_num⟩
  case «164» => exact ⟨313, 4, (show Nat.Prime 313 by norm_num).squarefree, by norm_num⟩
  case «165» => exact ⟨330, 0, squarefree_330, by norm_num⟩
  case «166» => exact ⟨331, 1, (show Nat.Prime 331 by norm_num).squarefree, by norm_num⟩
  case «167» => exact ⟨331, 2, (show Nat.Prime 331 by norm_num).squarefree, by norm_num⟩
  case «168» => exact ⟨335, 1, squarefree_335, by norm_num⟩
  case «169» => exact ⟨337, 1, (show Nat.Prime 337 by norm_num).squarefree, by norm_num⟩
  case «170» => exact ⟨337, 2, (show Nat.Prime 337 by norm_num).squarefree, by norm_num⟩
  case «171» => exact ⟨311, 5, (show Nat.Prime 311 by norm_num).squarefree, by norm_num⟩
  case «172» => exact ⟨337, 3, (show Nat.Prime 337 by norm_num).squarefree, by norm_num⟩
  case «173» => exact ⟨331, 4, (show Nat.Prime 331 by norm_num).squarefree, by norm_num⟩
  case «174» => exact ⟨347, 1, (show Nat.Prime 347 by norm_num).squarefree, by norm_num⟩
  case «175» => exact ⟨349, 1, (show Nat.Prime 349 by norm_num).squarefree, by norm_num⟩
  case «176» => exact ⟨349, 2, (show Nat.Prime 349 by norm_num).squarefree, by norm_num⟩
  case «177» => exact ⟨353, 1, (show Nat.Prime 353 by norm_num).squarefree, by norm_num⟩
  case «178» => exact ⟨353, 2, (show Nat.Prime 353 by norm_num).squarefree, by norm_num⟩
  case «179» => exact ⟨103, 8, (show Nat.Prime 103 by norm_num).squarefree, by norm_num⟩
  case «180» => exact ⟨359, 1, (show Nat.Prime 359 by norm_num).squarefree, by norm_num⟩
  case «181» => exact ⟨359, 2, (show Nat.Prime 359 by norm_num).squarefree, by norm_num⟩
  case «182» => exact ⟨349, 4, (show Nat.Prime 349 by norm_num).squarefree, by norm_num⟩
  case «183» => exact ⟨359, 3, (show Nat.Prime 359 by norm_num).squarefree, by norm_num⟩
  case «184» => exact ⟨367, 1, (show Nat.Prime 367 by norm_num).squarefree, by norm_num⟩
  case «185» => exact ⟨367, 2, (show Nat.Prime 367 by norm_num).squarefree, by norm_num⟩
  case «186» => exact ⟨371, 1, squarefree_371, by norm_num⟩
  case «187» => exact ⟨373, 1, (show Nat.Prime 373 by norm_num).squarefree, by norm_num⟩
  case «188» => exact ⟨373, 2, (show Nat.Prime 373 by norm_num).squarefree, by norm_num⟩
  case «189» => exact ⟨347, 5, (show Nat.Prime 347 by norm_num).squarefree, by norm_num⟩
  case «190» => exact ⟨379, 1, (show Nat.Prime 379 by norm_num).squarefree, by norm_num⟩
  case «191» => exact ⟨379, 2, (show Nat.Prime 379 by norm_num).squarefree, by norm_num⟩
  case «192» => exact ⟨383, 1, (show Nat.Prime 383 by norm_num).squarefree, by norm_num⟩
  case «193» => exact ⟨383, 2, (show Nat.Prime 383 by norm_num).squarefree, by norm_num⟩
  case «194» => exact ⟨373, 4, (show Nat.Prime 373 by norm_num).squarefree, by norm_num⟩
  case «195» => exact ⟨389, 1, (show Nat.Prime 389 by norm_num).squarefree, by norm_num⟩
  case «196» => exact ⟨389, 2, (show Nat.Prime 389 by norm_num).squarefree, by norm_num⟩
  case «197» => exact ⟨379, 4, (show Nat.Prime 379 by norm_num).squarefree, by norm_num⟩
  case «198» => exact ⟨389, 3, (show Nat.Prime 389 by norm_num).squarefree, by norm_num⟩
  case «199» => exact ⟨397, 1, (show Nat.Prime 397 by norm_num).squarefree, by norm_num⟩
  case «200» => exact ⟨397, 2, (show Nat.Prime 397 by norm_num).squarefree, by norm_num⟩
  case «201» => exact ⟨401, 1, (show Nat.Prime 401 by norm_num).squarefree, by norm_num⟩
  case «202» => exact ⟨401, 2, (show Nat.Prime 401 by norm_num).squarefree, by norm_num⟩
  case «203» => exact ⟨151, 8, (show Nat.Prime 151 by norm_num).squarefree, by norm_num⟩
  case «204» => exact ⟨401, 3, (show Nat.Prime 401 by norm_num).squarefree, by norm_num⟩
  case «205» => exact ⟨409, 1, (show Nat.Prime 409 by norm_num).squarefree, by norm_num⟩
  case «206» => exact ⟨409, 2, (show Nat.Prime 409 by norm_num).squarefree, by norm_num⟩
  case «207» => exact ⟨383, 5, (show Nat.Prime 383 by norm_num).squarefree, by norm_num⟩
  case «208» => exact ⟨409, 3, (show Nat.Prime 409 by norm_num).squarefree, by norm_num⟩
  case «209» => exact ⟨163, 8, (show Nat.Prime 163 by norm_num).squarefree, by norm_num⟩
  case «210» => exact ⟨419, 1, (show Nat.Prime 419 by norm_num).squarefree, by norm_num⟩
  case «211» => exact ⟨421, 1, (show Nat.Prime 421 by norm_num).squarefree, by norm_num⟩
  case «212» => exact ⟨421, 2, (show Nat.Prime 421 by norm_num).squarefree, by norm_num⟩
  case «213» => exact ⟨419, 3, (show Nat.Prime 419 by norm_num).squarefree, by norm_num⟩
  case «214» => exact ⟨421, 3, (show Nat.Prime 421 by norm_num).squarefree, by norm_num⟩
  case «215» => exact ⟨367, 6, (show Nat.Prime 367 by norm_num).squarefree, by norm_num⟩
  case «216» => exact ⟨431, 1, (show Nat.Prime 431 by norm_num).squarefree, by norm_num⟩
  case «217» => exact ⟨433, 1, (show Nat.Prime 433 by norm_num).squarefree, by norm_num⟩
  case «218» => exact ⟨433, 2, (show Nat.Prime 433 by norm_num).squarefree, by norm_num⟩
  case «219» => exact ⟨431, 3, (show Nat.Prime 431 by norm_num).squarefree, by norm_num⟩
  case «220» => exact ⟨439, 1, (show Nat.Prime 439 by norm_num).squarefree, by norm_num⟩
  case «221» => exact ⟨439, 2, (show Nat.Prime 439 by norm_num).squarefree, by norm_num⟩
  case «222» => exact ⟨443, 1, (show Nat.Prime 443 by norm_num).squarefree, by norm_num⟩
  case «223» => exact ⟨443, 2, (show Nat.Prime 443 by norm_num).squarefree, by norm_num⟩
  case «224» => exact ⟨433, 4, (show Nat.Prime 433 by norm_num).squarefree, by norm_num⟩
  case «225» => exact ⟨449, 1, (show Nat.Prime 449 by norm_num).squarefree, by norm_num⟩
  case «226» => exact ⟨449, 2, (show Nat.Prime 449 by norm_num).squarefree, by norm_num⟩
  case «227» => exact ⟨439, 4, (show Nat.Prime 439 by norm_num).squarefree, by norm_num⟩
  case «228» => exact ⟨449, 3, (show Nat.Prime 449 by norm_num).squarefree, by norm_num⟩
  case «229» => exact ⟨457, 1, (show Nat.Prime 457 by norm_num).squarefree, by norm_num⟩
  case «230» => exact ⟨457, 2, (show Nat.Prime 457 by norm_num).squarefree, by norm_num⟩
  case «231» => exact ⟨461, 1, (show Nat.Prime 461 by norm_num).squarefree, by norm_num⟩
  case «232» => exact ⟨463, 1, (show Nat.Prime 463 by norm_num).squarefree, by norm_num⟩
  case «233» => exact ⟨463, 2, (show Nat.Prime 463 by norm_num).squarefree, by norm_num⟩
  case «234» => exact ⟨467, 1, (show Nat.Prime 467 by norm_num).squarefree, by norm_num⟩
  case «235» => exact ⟨467, 2, (show Nat.Prime 467 by norm_num).squarefree, by norm_num⟩
  case «236» => exact ⟨457, 4, (show Nat.Prime 457 by norm_num).squarefree, by norm_num⟩
  case «237» => exact ⟨467, 3, (show Nat.Prime 467 by norm_num).squarefree, by norm_num⟩
  case «238» => exact ⟨461, 4, (show Nat.Prime 461 by norm_num).squarefree, by norm_num⟩
  case «239» => exact ⟨463, 4, (show Nat.Prime 463 by norm_num).squarefree, by norm_num⟩
  case «240» => exact ⟨479, 1, (show Nat.Prime 479 by norm_num).squarefree, by norm_num⟩
  case «241» => exact ⟨479, 2, (show Nat.Prime 479 by norm_num).squarefree, by norm_num⟩
  case «242» => exact ⟨421, 6, (show Nat.Prime 421 by norm_num).squarefree, by norm_num⟩
  case «243» => exact ⟨479, 3, (show Nat.Prime 479 by norm_num).squarefree, by norm_num⟩
  case «244» => exact ⟨487, 1, (show Nat.Prime 487 by norm_num).squarefree, by norm_num⟩
  case «245» => exact ⟨487, 2, (show Nat.Prime 487 by norm_num).squarefree, by norm_num⟩
  case «246» => exact ⟨491, 1, (show Nat.Prime 491 by norm_num).squarefree, by norm_num⟩
  case «247» => exact ⟨491, 2, (show Nat.Prime 491 by norm_num).squarefree, by norm_num⟩
  case «248» => exact ⟨433, 6, (show Nat.Prime 433 by norm_num).squarefree, by norm_num⟩
  case «249» => exact ⟨491, 3, (show Nat.Prime 491 by norm_num).squarefree, by norm_num⟩
  case «250» => exact ⟨499, 1, (show Nat.Prime 499 by norm_num).squarefree, by norm_num⟩
  case «251» => exact ⟨499, 2, (show Nat.Prime 499 by norm_num).squarefree, by norm_num⟩
  case «252» => exact ⟨503, 1, (show Nat.Prime 503 by norm_num).squarefree, by norm_num⟩
  case «253» => exact ⟨503, 2, (show Nat.Prime 503 by norm_num).squarefree, by norm_num⟩
  case «254» => exact ⟨505, 2, squarefree_505, by norm_num⟩
  case «255» => exact ⟨509, 1, (show Nat.Prime 509 by norm_num).squarefree, by norm_num⟩
  case «256» => exact ⟨509, 2, (show Nat.Prime 509 by norm_num).squarefree, by norm_num⟩
  case «257» => exact ⟨499, 4, (show Nat.Prime 499 by norm_num).squarefree, by norm_num⟩
  case «258» => exact ⟨509, 3, (show Nat.Prime 509 by norm_num).squarefree, by norm_num⟩
  case «259» => exact ⟨503, 4, (show Nat.Prime 503 by norm_num).squarefree, by norm_num⟩
  case «260» => exact ⟨457, 6, (show Nat.Prime 457 by norm_num).squarefree, by norm_num⟩
  case «261» => exact ⟨521, 1, (show Nat.Prime 521 by norm_num).squarefree, by norm_num⟩
  case «262» => exact ⟨523, 1, (show Nat.Prime 523 by norm_num).squarefree, by norm_num⟩
  case «263» => exact ⟨523, 2, (show Nat.Prime 523 by norm_num).squarefree, by norm_num⟩
  case «264» => exact ⟨521, 3, (show Nat.Prime 521 by norm_num).squarefree, by norm_num⟩
  case «265» => exact ⟨523, 3, (show Nat.Prime 523 by norm_num).squarefree, by norm_num⟩
  case «266» => exact ⟨277, 8, (show Nat.Prime 277 by norm_num).squarefree, by norm_num⟩
  case «267» => exact ⟨503, 5, (show Nat.Prime 503 by norm_num).squarefree, by norm_num⟩
  case «268» => exact ⟨521, 4, (show Nat.Prime 521 by norm_num).squarefree, by norm_num⟩
  case «269» => exact ⟨523, 4, (show Nat.Prime 523 by norm_num).squarefree, by norm_num⟩
  case «270» => exact ⟨509, 5, (show Nat.Prime 509 by norm_num).squarefree, by norm_num⟩
  case «271» => exact ⟨541, 1, (show Nat.Prime 541 by norm_num).squarefree, by norm_num⟩
  case «272» => exact ⟨541, 2, (show Nat.Prime 541 by norm_num).squarefree, by norm_num⟩
  case «273» => exact ⟨419, 7, (show Nat.Prime 419 by norm_num).squarefree, by norm_num⟩
  case «274» => exact ⟨547, 1, (show Nat.Prime 547 by norm_num).squarefree, by norm_num⟩
  case «275» => exact ⟨547, 2, (show Nat.Prime 547 by norm_num).squarefree, by norm_num⟩
  case «276» => exact ⟨521, 5, (show Nat.Prime 521 by norm_num).squarefree, by norm_num⟩
  case «277» => exact ⟨547, 3, (show Nat.Prime 547 by norm_num).squarefree, by norm_num⟩
  case «278» => exact ⟨541, 4, (show Nat.Prime 541 by norm_num).squarefree, by norm_num⟩
  case «279» => exact ⟨557, 1, (show Nat.Prime 557 by norm_num).squarefree, by norm_num⟩
  case «280» => exact ⟨557, 2, (show Nat.Prime 557 by norm_num).squarefree, by norm_num⟩
  case «281» => exact ⟨547, 4, (show Nat.Prime 547 by norm_num).squarefree, by norm_num⟩
  case «282» => exact ⟨563, 1, (show Nat.Prime 563 by norm_num).squarefree, by norm_num⟩
  case «283» => exact ⟨563, 2, (show Nat.Prime 563 by norm_num).squarefree, by norm_num⟩
  case «284» => exact ⟨313, 8, (show Nat.Prime 313 by norm_num).squarefree, by norm_num⟩
  case «285» => exact ⟨569, 1, (show Nat.Prime 569 by norm_num).squarefree, by norm_num⟩
  case «286» => exact ⟨571, 1, (show Nat.Prime 571 by norm_num).squarefree, by norm_num⟩
  case «287» => exact ⟨571, 2, (show Nat.Prime 571 by norm_num).squarefree, by norm_num⟩
  case «288» => exact ⟨569, 3, (show Nat.Prime 569 by norm_num).squarefree, by norm_num⟩
  case «289» => exact ⟨577, 1, (show Nat.Prime 577 by norm_num).squarefree, by norm_num⟩
  case «290» => exact ⟨577, 2, (show Nat.Prime 577 by norm_num).squarefree, by norm_num⟩
  case «291» => exact ⟨71, 9, (show Nat.Prime 71 by norm_num).squarefree, by norm_num⟩
  case «292» => exact ⟨577, 3, (show Nat.Prime 577 by norm_num).squarefree, by norm_num⟩
  case «293» => exact ⟨571, 4, (show Nat.Prime 571 by norm_num).squarefree, by norm_num⟩
  case «294» => exact ⟨587, 1, (show Nat.Prime 587 by norm_num).squarefree, by norm_num⟩
  case «295» => exact ⟨587, 2, (show Nat.Prime 587 by norm_num).squarefree, by norm_num⟩
  case «296» => exact ⟨577, 4, (show Nat.Prime 577 by norm_num).squarefree, by norm_num⟩
  case «297» => exact ⟨593, 1, (show Nat.Prime 593 by norm_num).squarefree, by norm_num⟩
  case «298» => exact ⟨593, 2, (show Nat.Prime 593 by norm_num).squarefree, by norm_num⟩
  case «299» => exact ⟨598, 0, squarefree_598, by norm_num⟩
  case «300» => exact ⟨599, 1, (show Nat.Prime 599 by norm_num).squarefree, by norm_num⟩
  case «301» => exact ⟨601, 1, (show Nat.Prime 601 by norm_num).squarefree, by norm_num⟩
  case «302» => exact ⟨601, 2, (show Nat.Prime 601 by norm_num).squarefree, by norm_num⟩
  case «303» => exact ⟨599, 3, (show Nat.Prime 599 by norm_num).squarefree, by norm_num⟩
  case «304» => exact ⟨607, 1, (show Nat.Prime 607 by norm_num).squarefree, by norm_num⟩
  case «305» => exact ⟨607, 2, (show Nat.Prime 607 by norm_num).squarefree, by norm_num⟩
  case «306» => exact ⟨101, 9, (show Nat.Prime 101 by norm_num).squarefree, by norm_num⟩
  case «307» => exact ⟨613, 1, (show Nat.Prime 613 by norm_num).squarefree, by norm_num⟩
  case «308» => exact ⟨613, 2, (show Nat.Prime 613 by norm_num).squarefree, by norm_num⟩
  case «309» => exact ⟨617, 1, (show Nat.Prime 617 by norm_num).squarefree, by norm_num⟩
  case «310» => exact ⟨619, 1, (show Nat.Prime 619 by norm_num).squarefree, by norm_num⟩
  case «311» => exact ⟨619, 2, (show Nat.Prime 619 by norm_num).squarefree, by norm_num⟩
  case «312» => exact ⟨617, 3, (show Nat.Prime 617 by norm_num).squarefree, by norm_num⟩
  case «313» => exact ⟨619, 3, (show Nat.Prime 619 by norm_num).squarefree, by norm_num⟩
  case «314» => exact ⟨613, 4, (show Nat.Prime 613 by norm_num).squarefree, by norm_num⟩
  case «315» => exact ⟨599, 5, (show Nat.Prime 599 by norm_num).squarefree, by norm_num⟩
  case «316» => exact ⟨631, 1, (show Nat.Prime 631 by norm_num).squarefree, by norm_num⟩
  case «317» => exact ⟨631, 2, (show Nat.Prime 631 by norm_num).squarefree, by norm_num⟩
  case «318» => exact ⟨509, 7, (show Nat.Prime 509 by norm_num).squarefree, by norm_num⟩
  case «319» => exact ⟨631, 3, (show Nat.Prime 631 by norm_num).squarefree, by norm_num⟩
  case «320» => exact ⟨577, 6, (show Nat.Prime 577 by norm_num).squarefree, by norm_num⟩
  case «321» => exact ⟨641, 1, (show Nat.Prime 641 by norm_num).squarefree, by norm_num⟩
  case «322» => exact ⟨643, 1, (show Nat.Prime 643 by norm_num).squarefree, by norm_num⟩
  case «323» => exact ⟨643, 2, (show Nat.Prime 643 by norm_num).squarefree, by norm_num⟩
  case «324» => exact ⟨647, 1, (show Nat.Prime 647 by norm_num).squarefree, by norm_num⟩
  case «325» => exact ⟨647, 2, (show Nat.Prime 647 by norm_num).squarefree, by norm_num⟩
  case «326» => exact ⟨397, 8, (show Nat.Prime 397 by norm_num).squarefree, by norm_num⟩
  case «327» => exact ⟨653, 1, (show Nat.Prime 653 by norm_num).squarefree, by norm_num⟩
  case «328» => exact ⟨653, 2, (show Nat.Prime 653 by norm_num).squarefree, by norm_num⟩
  case «329» => exact ⟨643, 4, (show Nat.Prime 643 by norm_num).squarefree, by norm_num⟩
  case «330» => exact ⟨659, 1, (show Nat.Prime 659 by norm_num).squarefree, by norm_num⟩
  case «331» => exact ⟨661, 1, (show Nat.Prime 661 by norm_num).squarefree, by norm_num⟩
  case «332» => exact ⟨661, 2, (show Nat.Prime 661 by norm_num).squarefree, by norm_num⟩
  case «333» => exact ⟨659, 3, (show Nat.Prime 659 by norm_num).squarefree, by norm_num⟩
  case «334» => exact ⟨661, 3, (show Nat.Prime 661 by norm_num).squarefree, by norm_num⟩
  case «335» => exact ⟨607, 6, (show Nat.Prime 607 by norm_num).squarefree, by norm_num⟩
  case «336» => exact ⟨641, 5, (show Nat.Prime 641 by norm_num).squarefree, by norm_num⟩
  case «337» => exact ⟨673, 1, (show Nat.Prime 673 by norm_num).squarefree, by norm_num⟩
  case «338» => exact ⟨673, 2, (show Nat.Prime 673 by norm_num).squarefree, by norm_num⟩
  case «339» => exact ⟨677, 1, (show Nat.Prime 677 by norm_num).squarefree, by norm_num⟩
  case «340» => exact ⟨677, 2, (show Nat.Prime 677 by norm_num).squarefree, by norm_num⟩
  case «341» => exact ⟨619, 6, (show Nat.Prime 619 by norm_num).squarefree, by norm_num⟩
  case «342» => exact ⟨683, 1, (show Nat.Prime 683 by norm_num).squarefree, by norm_num⟩
  case «343» => exact ⟨683, 2, (show Nat.Prime 683 by norm_num).squarefree, by norm_num⟩
  case «344» => exact ⟨673, 4, (show Nat.Prime 673 by norm_num).squarefree, by norm_num⟩
  case «345» => exact ⟨683, 3, (show Nat.Prime 683 by norm_num).squarefree, by norm_num⟩
  case «346» => exact ⟨691, 1, (show Nat.Prime 691 by norm_num).squarefree, by norm_num⟩
  case «347» => exact ⟨691, 2, (show Nat.Prime 691 by norm_num).squarefree, by norm_num⟩
  case «348» => exact ⟨569, 7, (show Nat.Prime 569 by norm_num).squarefree, by norm_num⟩
  case «349» => exact ⟨691, 3, (show Nat.Prime 691 by norm_num).squarefree, by norm_num⟩
  case «350» => exact ⟨699, 1, squarefree_699, by norm_num⟩
  case «351» => exact ⟨701, 1, (show Nat.Prime 701 by norm_num).squarefree, by norm_num⟩
  case «352» => exact ⟨701, 2, (show Nat.Prime 701 by norm_num).squarefree, by norm_num⟩
  case «353» => exact ⟨691, 4, (show Nat.Prime 691 by norm_num).squarefree, by norm_num⟩
  case «354» => exact ⟨701, 3, (show Nat.Prime 701 by norm_num).squarefree, by norm_num⟩
  case «355» => exact ⟨709, 1, (show Nat.Prime 709 by norm_num).squarefree, by norm_num⟩
  case «356» => exact ⟨709, 2, (show Nat.Prime 709 by norm_num).squarefree, by norm_num⟩
  case «357» => exact ⟨683, 5, (show Nat.Prime 683 by norm_num).squarefree, by norm_num⟩
  case «358» => exact ⟨709, 3, (show Nat.Prime 709 by norm_num).squarefree, by norm_num⟩
  case «359» => exact ⟨463, 8, (show Nat.Prime 463 by norm_num).squarefree, by norm_num⟩
  case «360» => exact ⟨719, 1, (show Nat.Prime 719 by norm_num).squarefree, by norm_num⟩
  case «361» => exact ⟨719, 2, (show Nat.Prime 719 by norm_num).squarefree, by norm_num⟩
  case «362» => exact ⟨709, 4, (show Nat.Prime 709 by norm_num).squarefree, by norm_num⟩
  case «363» => exact ⟨719, 3, (show Nat.Prime 719 by norm_num).squarefree, by norm_num⟩
  case «364» => exact ⟨727, 1, (show Nat.Prime 727 by norm_num).squarefree, by norm_num⟩
  case «365» => exact ⟨727, 2, (show Nat.Prime 727 by norm_num).squarefree, by norm_num⟩
  case «366» => exact ⟨701, 5, (show Nat.Prime 701 by norm_num).squarefree, by norm_num⟩
  case «367» => exact ⟨733, 1, (show Nat.Prime 733 by norm_num).squarefree, by norm_num⟩
  case «368» => exact ⟨733, 2, (show Nat.Prime 733 by norm_num).squarefree, by norm_num⟩
  case «369» => exact ⟨227, 9, (show Nat.Prime 227 by norm_num).squarefree, by norm_num⟩
  case «370» => exact ⟨739, 1, (show Nat.Prime 739 by norm_num).squarefree, by norm_num⟩
  case «371» => exact ⟨739, 2, (show Nat.Prime 739 by norm_num).squarefree, by norm_num⟩
  case «372» => exact ⟨743, 1, (show Nat.Prime 743 by norm_num).squarefree, by norm_num⟩
  case «373» => exact ⟨743, 2, (show Nat.Prime 743 by norm_num).squarefree, by norm_num⟩
  case «374» => exact ⟨733, 4, (show Nat.Prime 733 by norm_num).squarefree, by norm_num⟩
  case «375» => exact ⟨743, 3, (show Nat.Prime 743 by norm_num).squarefree, by norm_num⟩
  case «376» => exact ⟨751, 1, (show Nat.Prime 751 by norm_num).squarefree, by norm_num⟩
  case «377» => exact ⟨751, 2, (show Nat.Prime 751 by norm_num).squarefree, by norm_num⟩
  case «378» => exact ⟨755, 1, squarefree_755, by norm_num⟩
  case «379» => exact ⟨757, 1, (show Nat.Prime 757 by norm_num).squarefree, by norm_num⟩
  case «380» => exact ⟨757, 2, (show Nat.Prime 757 by norm_num).squarefree, by norm_num⟩
  case «381» => exact ⟨761, 1, (show Nat.Prime 761 by norm_num).squarefree, by norm_num⟩
  case «382» => exact ⟨761, 2, (show Nat.Prime 761 by norm_num).squarefree, by norm_num⟩
  case «383» => exact ⟨751, 4, (show Nat.Prime 751 by norm_num).squarefree, by norm_num⟩
  case «384» => exact ⟨761, 3, (show Nat.Prime 761 by norm_num).squarefree, by norm_num⟩
  case «385» => exact ⟨769, 1, (show Nat.Prime 769 by norm_num).squarefree, by norm_num⟩
  case «386» => exact ⟨769, 2, (show Nat.Prime 769 by norm_num).squarefree, by norm_num⟩
  case «387» => exact ⟨773, 1, (show Nat.Prime 773 by norm_num).squarefree, by norm_num⟩
  case «388» => exact ⟨773, 2, (show Nat.Prime 773 by norm_num).squarefree, by norm_num⟩
  case «389» => exact ⟨523, 8, (show Nat.Prime 523 by norm_num).squarefree, by norm_num⟩
  case «390» => exact ⟨773, 3, (show Nat.Prime 773 by norm_num).squarefree, by norm_num⟩
  case «391» => exact ⟨751, 5, (show Nat.Prime 751 by norm_num).squarefree, by norm_num⟩
  case «392» => exact ⟨769, 4, (show Nat.Prime 769 by norm_num).squarefree, by norm_num⟩
  case «393» => exact ⟨659, 7, (show Nat.Prime 659 by norm_num).squarefree, by norm_num⟩
  case «394» => exact ⟨787, 1, (show Nat.Prime 787 by norm_num).squarefree, by norm_num⟩
  case «395» => exact ⟨787, 2, (show Nat.Prime 787 by norm_num).squarefree, by norm_num⟩
  case «396» => exact ⟨761, 5, (show Nat.Prime 761 by norm_num).squarefree, by norm_num⟩
  case «397» => exact ⟨787, 3, (show Nat.Prime 787 by norm_num).squarefree, by norm_num⟩
  case «398» => exact ⟨733, 6, (show Nat.Prime 733 by norm_num).squarefree, by norm_num⟩
  case «399» => exact ⟨797, 1, (show Nat.Prime 797 by norm_num).squarefree, by norm_num⟩
  case «400» => exact ⟨797, 2, (show Nat.Prime 797 by norm_num).squarefree, by norm_num⟩
  case «401» => exact ⟨787, 4, (show Nat.Prime 787 by norm_num).squarefree, by norm_num⟩
  case «402» => exact ⟨797, 3, (show Nat.Prime 797 by norm_num).squarefree, by norm_num⟩
  case «403» => exact ⟨743, 6, (show Nat.Prime 743 by norm_num).squarefree, by norm_num⟩
  case «404» => exact ⟨807, 1, squarefree_807, by norm_num⟩
  case «405» => exact ⟨809, 1, (show Nat.Prime 809 by norm_num).squarefree, by norm_num⟩
  case «406» => exact ⟨811, 1, (show Nat.Prime 811 by norm_num).squarefree, by norm_num⟩
  case «407» => exact ⟨811, 2, (show Nat.Prime 811 by norm_num).squarefree, by norm_num⟩
  case «408» => exact ⟨809, 3, (show Nat.Prime 809 by norm_num).squarefree, by norm_num⟩
  case «409» => exact ⟨811, 3, (show Nat.Prime 811 by norm_num).squarefree, by norm_num⟩
  case «410» => exact ⟨757, 6, (show Nat.Prime 757 by norm_num).squarefree, by norm_num⟩
  case «411» => exact ⟨821, 1, (show Nat.Prime 821 by norm_num).squarefree, by norm_num⟩
  case «412» => exact ⟨823, 1, (show Nat.Prime 823 by norm_num).squarefree, by norm_num⟩
  case «413» => exact ⟨823, 2, (show Nat.Prime 823 by norm_num).squarefree, by norm_num⟩
  case «414» => exact ⟨827, 1, (show Nat.Prime 827 by norm_num).squarefree, by norm_num⟩
  case «415» => exact ⟨829, 1, (show Nat.Prime 829 by norm_num).squarefree, by norm_num⟩
  case «416» => exact ⟨829, 2, (show Nat.Prime 829 by norm_num).squarefree, by norm_num⟩
  case «417» => exact ⟨827, 3, (show Nat.Prime 827 by norm_num).squarefree, by norm_num⟩
  case «418» => exact ⟨829, 3, (show Nat.Prime 829 by norm_num).squarefree, by norm_num⟩
  case «419» => exact ⟨823, 4, (show Nat.Prime 823 by norm_num).squarefree, by norm_num⟩
  case «420» => exact ⟨839, 1, (show Nat.Prime 839 by norm_num).squarefree, by norm_num⟩
  case «421» => exact ⟨839, 2, (show Nat.Prime 839 by norm_num).squarefree, by norm_num⟩
  case «422» => exact ⟨829, 4, (show Nat.Prime 829 by norm_num).squarefree, by norm_num⟩
  case «423» => exact ⟨839, 3, (show Nat.Prime 839 by norm_num).squarefree, by norm_num⟩
  case «424» => exact ⟨593, 8, (show Nat.Prime 593 by norm_num).squarefree, by norm_num⟩
  case «425» => exact ⟨787, 6, (show Nat.Prime 787 by norm_num).squarefree, by norm_num⟩
  case «426» => exact ⟨821, 5, (show Nat.Prime 821 by norm_num).squarefree, by norm_num⟩
  case «427» => exact ⟨853, 1, (show Nat.Prime 853 by norm_num).squarefree, by norm_num⟩
  case «428» => exact ⟨853, 2, (show Nat.Prime 853 by norm_num).squarefree, by norm_num⟩
  case «429» => exact ⟨857, 1, (show Nat.Prime 857 by norm_num).squarefree, by norm_num⟩
  case «430» => exact ⟨859, 1, (show Nat.Prime 859 by norm_num).squarefree, by norm_num⟩
  case «431» => exact ⟨859, 2, (show Nat.Prime 859 by norm_num).squarefree, by norm_num⟩
  case «432» => exact ⟨863, 1, (show Nat.Prime 863 by norm_num).squarefree, by norm_num⟩
  case «433» => exact ⟨863, 2, (show Nat.Prime 863 by norm_num).squarefree, by norm_num⟩
  case «434» => exact ⟨853, 4, (show Nat.Prime 853 by norm_num).squarefree, by norm_num⟩
  case «435» => exact ⟨863, 3, (show Nat.Prime 863 by norm_num).squarefree, by norm_num⟩
  case «436» => exact ⟨857, 4, (show Nat.Prime 857 by norm_num).squarefree, by norm_num⟩
  case «437» => exact ⟨859, 4, (show Nat.Prime 859 by norm_num).squarefree, by norm_num⟩
  case «438» => exact ⟨869, 3, squarefree_869, by norm_num⟩
  case «439» => exact ⟨877, 1, (show Nat.Prime 877 by norm_num).squarefree, by norm_num⟩
  case «440» => exact ⟨877, 2, (show Nat.Prime 877 by norm_num).squarefree, by norm_num⟩
  case «441» => exact ⟨881, 1, (show Nat.Prime 881 by norm_num).squarefree, by norm_num⟩
  case «442» => exact ⟨883, 1, (show Nat.Prime 883 by norm_num).squarefree, by norm_num⟩
  case «443» => exact ⟨883, 2, (show Nat.Prime 883 by norm_num).squarefree, by norm_num⟩
  case «444» => exact ⟨887, 1, (show Nat.Prime 887 by norm_num).squarefree, by norm_num⟩
  case «445» => exact ⟨887, 2, (show Nat.Prime 887 by norm_num).squarefree, by norm_num⟩
  case «446» => exact ⟨877, 4, (show Nat.Prime 877 by norm_num).squarefree, by norm_num⟩
  case «447» => exact ⟨887, 3, (show Nat.Prime 887 by norm_num).squarefree, by norm_num⟩
  case «448» => exact ⟨881, 4, (show Nat.Prime 881 by norm_num).squarefree, by norm_num⟩
  case «449» => exact ⟨883, 4, (show Nat.Prime 883 by norm_num).squarefree, by norm_num⟩
  case «450» => exact ⟨773, 7, (show Nat.Prime 773 by norm_num).squarefree, by norm_num⟩
  case «451» => exact ⟨887, 4, (show Nat.Prime 887 by norm_num).squarefree, by norm_num⟩
  case «452» => exact ⟨903, 1, squarefree_903, by norm_num⟩
  case «453» => exact ⟨906, 0, squarefree_906, by norm_num⟩
  case «454» => exact ⟨907, 1, (show Nat.Prime 907 by norm_num).squarefree, by norm_num⟩
  case «455» => exact ⟨907, 2, (show Nat.Prime 907 by norm_num).squarefree, by norm_num⟩
  case «456» => exact ⟨911, 1, (show Nat.Prime 911 by norm_num).squarefree, by norm_num⟩
  case «457» => exact ⟨911, 2, (show Nat.Prime 911 by norm_num).squarefree, by norm_num⟩
  case «458» => exact ⟨853, 6, (show Nat.Prime 853 by norm_num).squarefree, by norm_num⟩
  case «459» => exact ⟨911, 3, (show Nat.Prime 911 by norm_num).squarefree, by norm_num⟩
  case «460» => exact ⟨919, 1, (show Nat.Prime 919 by norm_num).squarefree, by norm_num⟩
  case «461» => exact ⟨919, 2, (show Nat.Prime 919 by norm_num).squarefree, by norm_num⟩
  case «462» => exact ⟨797, 7, (show Nat.Prime 797 by norm_num).squarefree, by norm_num⟩
  case «463» => exact ⟨919, 3, (show Nat.Prime 919 by norm_num).squarefree, by norm_num⟩
  case «464» => exact ⟨673, 8, (show Nat.Prime 673 by norm_num).squarefree, by norm_num⟩
  case «465» => exact ⟨929, 1, (show Nat.Prime 929 by norm_num).squarefree, by norm_num⟩
  case «466» => exact ⟨929, 2, (show Nat.Prime 929 by norm_num).squarefree, by norm_num⟩
  case «467» => exact ⟨919, 4, (show Nat.Prime 919 by norm_num).squarefree, by norm_num⟩
  case «468» => exact ⟨929, 3, (show Nat.Prime 929 by norm_num).squarefree, by norm_num⟩
  case «469» => exact ⟨937, 1, (show Nat.Prime 937 by norm_num).squarefree, by norm_num⟩
  case «470» => exact ⟨937, 2, (show Nat.Prime 937 by norm_num).squarefree, by norm_num⟩
  case «471» => exact ⟨941, 1, (show Nat.Prime 941 by norm_num).squarefree, by norm_num⟩
  case «472» => exact ⟨941, 2, (show Nat.Prime 941 by norm_num).squarefree, by norm_num⟩
  case «473» => exact ⟨883, 6, (show Nat.Prime 883 by norm_num).squarefree, by norm_num⟩
  case «474» => exact ⟨947, 1, (show Nat.Prime 947 by norm_num).squarefree, by norm_num⟩
  case «475» => exact ⟨947, 2, (show Nat.Prime 947 by norm_num).squarefree, by norm_num⟩
  case «476» => exact ⟨937, 4, (show Nat.Prime 937 by norm_num).squarefree, by norm_num⟩
  case «477» => exact ⟨953, 1, (show Nat.Prime 953 by norm_num).squarefree, by norm_num⟩
  case «478» => exact ⟨953, 2, (show Nat.Prime 953 by norm_num).squarefree, by norm_num⟩
  case «479» => exact ⟨958, 0, squarefree_958, by norm_num⟩
  case «480» => exact ⟨953, 3, (show Nat.Prime 953 by norm_num).squarefree, by norm_num⟩
  case «481» => exact ⟨947, 4, (show Nat.Prime 947 by norm_num).squarefree, by norm_num⟩
  case «482» => exact ⟨709, 8, (show Nat.Prime 709 by norm_num).squarefree, by norm_num⟩
  case «483» => exact ⟨839, 7, (show Nat.Prime 839 by norm_num).squarefree, by norm_num⟩
  case «484» => exact ⟨967, 1, (show Nat.Prime 967 by norm_num).squarefree, by norm_num⟩
  case «485» => exact ⟨967, 2, (show Nat.Prime 967 by norm_num).squarefree, by norm_num⟩
  case «486» => exact ⟨971, 1, (show Nat.Prime 971 by norm_num).squarefree, by norm_num⟩
  case «487» => exact ⟨971, 2, (show Nat.Prime 971 by norm_num).squarefree, by norm_num⟩
  case «488» => exact ⟨973, 2, squarefree_973, by norm_num⟩
  case «489» => exact ⟨977, 1, (show Nat.Prime 977 by norm_num).squarefree, by norm_num⟩
  case «490» => exact ⟨977, 2, (show Nat.Prime 977 by norm_num).squarefree, by norm_num⟩
  case «491» => exact ⟨967, 4, (show Nat.Prime 967 by norm_num).squarefree, by norm_num⟩
  case «492» => exact ⟨983, 1, (show Nat.Prime 983 by norm_num).squarefree, by norm_num⟩
  case «493» => exact ⟨983, 2, (show Nat.Prime 983 by norm_num).squarefree, by norm_num⟩
  case «494» => exact ⟨733, 8, (show Nat.Prime 733 by norm_num).squarefree, by norm_num⟩
  case «495» => exact ⟨983, 3, (show Nat.Prime 983 by norm_num).squarefree, by norm_num⟩
  case «496» => exact ⟨991, 1, (show Nat.Prime 991 by norm_num).squarefree, by norm_num⟩
  case «497» => exact ⟨991, 2, (show Nat.Prime 991 by norm_num).squarefree, by norm_num⟩
  case «498» => exact ⟨995, 1, squarefree_995, by norm_num⟩
  case «499» => exact ⟨997, 1, (show Nat.Prime 997 by norm_num).squarefree, by norm_num⟩

end Submissions.Erdos11VerifiedBelow1001.CaseSplit
