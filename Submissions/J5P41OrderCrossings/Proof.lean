import Init

/- A literal ordinary Sidon set. The crossing certificate uses its actual
   adjacent-start difference curves. Real linear interpolation is a separate
   paper argument; no statement about the canonical asymptotic is asserted. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Submissions.J5P41OrderCrossings.Proof

def mark : Nat → Int
  | 0 => 0 | 1 => 14 | 2 => 23 | 3 => 51 | 4 => 68 | 5 => 69
  | 6 => 72 | 7 => 84 | 8 => 94 | 9 => 125 | 10 => 132
  | 11 => 159 | 12 => 161 | 13 => 167 | 14 => 172 | 15 => 191
  | 16 => 211 | _ => 0

def decode (z : Int) : Nat :=
  (if z < 212 then
  (if z < 145 then
    (if z < 95 then
      (if z < 69 then
        (if z < 37 then
          (if z < 23 then
            (if z < 14 then
              0 else
              1) else
            (if z < 28 then
              2 else
              18)) else
          (if z < 51 then
            (if z < 46 then
              19 else
              36) else
            (if z < 65 then
              3 else
              (if z < 68 then
                20 else
                4)))) else
        (if z < 84 then
          (if z < 74 then
            (if z < 72 then
              5 else
              6) else
            (if z < 82 then
              37 else
              (if z < 83 then
                21 else
                22))) else
          (if z < 91 then
            (if z < 86 then
              7 else
              23) else
            (if z < 92 then
              38 else
              (if z < 94 then
                39 else
                8))))) else
      (if z < 125 then
        (if z < 108 then
          (if z < 102 then
            (if z < 98 then
              40 else
              24) else
            (if z < 107 then
              54 else
              41)) else
          (if z < 119 then
            (if z < 117 then
              25 else
              42) else
            (if z < 120 then
              55 else
              (if z < 123 then
                56 else
                57)))) else
        (if z < 138 then
          (if z < 135 then
            (if z < 132 then
              9 else
              10) else
            (if z < 136 then
              58 else
              (if z < 137 then
                72 else
                73))) else
          (if z < 140 then
            (if z < 139 then
              90 else
              26) else
            (if z < 141 then
              74 else
              (if z < 144 then
                91 else
                108)))))) else
    (if z < 181 then
      (if z < 162 then
        (if z < 153 then
          (if z < 148 then
            (if z < 146 then
              59 else
              27) else
            (if z < 152 then
              43 else
              75)) else
          (if z < 156 then
            (if z < 155 then
              92 else
              44) else
            (if z < 159 then
              109 else
              (if z < 161 then
                11 else
                12)))) else
        (if z < 172 then
          (if z < 166 then
            (if z < 163 then
              76 else
              93) else
            (if z < 167 then
              110 else
              (if z < 168 then
                13 else
                126))) else
          (if z < 175 then
            (if z < 173 then
              14 else
              28) else
            (if z < 176 then
              29 else
              (if z < 178 then
                60 else
                127))))) else
      (if z < 194 then
        (if z < 186 then
          (if z < 183 then
            (if z < 182 then
              30 else
              45) else
            (if z < 184 then
              61 else
              46)) else
          (if z < 190 then
            (if z < 188 then
              31 else
              144) else
            (if z < 191 then
              47 else
              (if z < 193 then
                15 else
                77)))) else
        (if z < 204 then
          (if z < 197 then
            (if z < 195 then
              94 else
              48) else
            (if z < 200 then
              111 else
              (if z < 201 then
                78 else
                95))) else
          (if z < 209 then
            (if z < 205 then
              112 else
              32) else
            (if z < 210 then
              128 else
              (if z < 211 then
                62 else
                16))))))) else
  (if z < 279 then
    (if z < 241 then
      (if z < 228 then
        (if z < 219 then
          (if z < 216 then
            (if z < 214 then
              63 else
              49) else
            (if z < 218 then
              129 else
              64)) else
          (if z < 225 then
            (if z < 223 then
              145 else
              65) else
            (if z < 226 then
              33 else
              (if z < 227 then
                146 else
                79)))) else
        (if z < 234 then
          (if z < 230 then
            (if z < 229 then
              96 else
              80) else
            (if z < 231 then
              97 else
              (if z < 233 then
                113 else
                114))) else
          (if z < 236 then
            (if z < 235 then
              50 else
              81) else
            (if z < 239 then
              98 else
              (if z < 240 then
                115 else
                82))))) else
      (if z < 256 then
        (if z < 245 then
          (if z < 243 then
            (if z < 242 then
              99 else
              66) else
            (if z < 244 then
              130 else
              116)) else
          (if z < 251 then
            (if z < 250 then
              131 else
              162) else
            (if z < 253 then
              132 else
              (if z < 255 then
                147 else
                148)))) else
        (if z < 262 then
          (if z < 259 then
            (if z < 257 then
              133 else
              163) else
            (if z < 260 then
              83 else
              (if z < 261 then
                100 else
                149))) else
          (if z < 264 then
            (if z < 263 then
              67 else
              117) else
            (if z < 266 then
              180 else
              (if z < 275 then
                150 else
                134)))))) else
    (if z < 326 then
      (if z < 295 then
        (if z < 285 then
          (if z < 283 then
            (if z < 280 then
              84 else
              101) else
            (if z < 284 then
              118 else
              164)) else
          (if z < 291 then
            (if z < 286 then
              151 else
              165) else
            (if z < 292 then
              181 else
              (if z < 293 then
                166 else
                182)))) else
        (if z < 316 then
          (if z < 299 then
            (if z < 297 then
              135 else
              167) else
            (if z < 304 then
              183 else
              (if z < 305 then
                184 else
                152))) else
          (if z < 320 then
            (if z < 318 then
              168 else
              198) else
            (if z < 322 then
              199 else
              (if z < 323 then
                216 else
                185))))) else
      (if z < 352 then
        (if z < 336 then
          (if z < 331 then
            (if z < 328 then
              200 else
              217) else
            (if z < 333 then
              201 else
              (if z < 334 then
                218 else
                234))) else
          (if z < 343 then
            (if z < 339 then
              169 else
              235) else
            (if z < 344 then
              186 else
              (if z < 350 then
                252 else
                202)))) else
        (if z < 378 then
          (if z < 363 then
            (if z < 358 then
              219 else
              236) else
            (if z < 370 then
              253 else
              (if z < 372 then
                203 else
                220))) else
          (if z < 383 then
            (if z < 382 then
              237 else
              270) else
            (if z < 402 then
              254 else
              (if z < 422 then
                271 else
                288))))))))

theorem decodeCorrect : ∀ i j : Fin 17,
    decode (mark i.val + mark j.val) =
    17 * min i.val j.val + max i.val j.val := by
  decide +kernel

theorem ordinarySidon : ∀ i j l n : Fin 17,
    mark i.val + mark j.val = mark l.val + mark n.val →
    ((i = l ∧ j = n) ∨ (i = n ∧ j = l)) := by
  intro i j l n h
  have e := congrArg decode h
  rw [decodeCorrect i j, decodeCorrect l n] at e
  have hi := i.isLt
  have hj := j.isLt
  have hl := l.isLt
  have hn := n.isLt
  simp only [Fin.ext_iff]
  by_cases hij : i.val ≤ j.val <;> by_cases hln : l.val ≤ n.val <;>
    simp [Nat.min_def, Nat.max_def, hij, hln] at e <;> omega

theorem orderedBounded :
    (∀ i j : Fin 17, i < j → mark i.val < mark j.val) ∧
    (∀ i : Fin 17, 0 ≤ mark i.val ∧ mark i.val < 212) ∧
    (212 : Nat) ≤ 17 * 17 := by
  decide +kernel

def curve (i r : Nat) : Int := mark (i + r) - mark i

theorem sevenProperSignChanges : ∀ r : Fin 15,
    r.val ∈ ([1, 3, 7, 8, 9, 10, 13] : List Nat) →
    (curve 1 r.val - curve 0 r.val) *
      (curve 1 (r.val + 1) - curve 0 (r.val + 1)) < 0 := by
  decide +kernel

theorem solves :
  (∀ i j l n : Fin 17,
    mark i.val + mark j.val = mark l.val + mark n.val →
    ((i = l ∧ j = n) ∨ (i = n ∧ j = l))) ∧
  ((∀ i j : Fin 17, i < j → mark i.val < mark j.val) ∧
    (∀ i : Fin 17, 0 ≤ mark i.val ∧ mark i.val < 212) ∧
    (212 : Nat) ≤ 17 * 17) ∧
  (∀ r : Fin 15,
    r.val ∈ ([1, 3, 7, 8, 9, 10, 13] : List Nat) →
    (curve 1 r.val - curve 0 r.val) *
      (curve 1 (r.val + 1) - curve 0 (r.val + 1)) < 0) := by
  exact ⟨@ordinarySidon, @orderedBounded, @sevenProperSignChanges⟩

end Submissions.J5P41OrderCrossings.Proof
