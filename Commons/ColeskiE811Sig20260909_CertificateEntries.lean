import Commons.ColeskiE811Sig20260909_BitmapCoverage
import Commons.ColeskiE811Sig20260909_SixAllowed
import Commons.ColeskiE811Sig20260909_K6Check

/- BEGIN bundled local module CertificateEntries -/

namespace ColeskiCertificateEntries
open ColeskiBitmapCoverage ColeskiSixAllowed ColeskiK6Check

abbrev Entry := Nat × Array Nat

theorem entries_positive (r : Nat) (entries : List Entry) (bits : Nat)
    (hb : bitmap (entries.map Prod.fst) = bits)
    (hp : entries.all (fun e => checkPositive r e.1 e.2) = true)
    (a : Nat) (ha : bits.testBit a = true) :
    ∃ ws : Array Nat, checkPositive r a ws = true := by
  have hm : a ∈ entries.map Prod.fst := by
    apply (bitmap_member _ _).mp
    simpa only [hb] using ha
  obtain ⟨e,he,hea⟩ := List.mem_map.mp hm
  refine ⟨e.2,?_⟩
  rw [← hea]
  exact List.all_eq_true.mp hp e he

theorem covered_positive (r : Nat) (entries : List Entry) (bits : Nat)
    (hb : bitmap (entries.map Prod.fst) = bits)
    (hp : entries.all (fun e => checkPositive r e.1 e.2) = true)
    (cover : ∀ a : Fin 7776, allowedExtension6 r a.val = bits.testBit a.val)
    (a : Fin 7776) (ha : allowedExtension6 r a.val = true) :
    ∃ ws : Array Nat, checkPositive r a.val ws = true := by
  apply entries_positive r entries bits hb hp a.val
  rw [← cover a]
  exact ha
end ColeskiCertificateEntries
#print axioms ColeskiCertificateEntries.covered_positive

/- END bundled local module CertificateEntries -/
