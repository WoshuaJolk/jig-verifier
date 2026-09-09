import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup00
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup01
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup02
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup03
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup04
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup05
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup06
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup07
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup08
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup09
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup10
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup11
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup12
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup13
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup14
import Commons.ColeskiE811Sig20260909_SignatureWeightDataGroup15
import Commons.ColeskiE811Sig20260909_FlagSignatureInvariance

/- BEGIN bundled local module SignatureWeights -/


namespace ColeskiSignatureWeights

open ColeskiFlagSignature ColeskiPatternAction ColeskiPaletteAction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lookupLoop (keys : Array Nat) (values : Array Int) (key : Nat) : Nat → Nat → Nat → Int
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        let found := keys[mid]!
        if key = found then values[mid]!
        else if key < found then lookupLoop keys values key fuel lo mid
        else lookupLoop keys values key fuel (mid + 1) hi
      else 0

def signatureWeight (key : Nat) : Int :=
  if key <= 1151182766095761106 then
    if key <= 578448709955487916 then
      if key <= 289165966610860626 then
        if key <= 143392264960169797 then
          if key <= 72154795145391826 then
            if key <= 36291507363614928 then
              if key <= 36291507363614928 then
                lookupLoop ColeskiSignatureWeightData00.keys ColeskiSignatureWeightData00.values key 8 0 ColeskiSignatureWeightData00.keys.size
              else 0
            else
              if key <= 72154795145391826 then
                lookupLoop ColeskiSignatureWeightData01.keys ColeskiSignatureWeightData01.values key 8 0 ColeskiSignatureWeightData01.keys.size
              else 0
          else
            if key <= 111804402282765741 then
              if key <= 111804402282765741 then
                lookupLoop ColeskiSignatureWeightData02.keys ColeskiSignatureWeightData02.values key 8 0 ColeskiSignatureWeightData02.keys.size
              else 0
            else
              if key <= 143392264960169797 then
                lookupLoop ColeskiSignatureWeightData03.keys ColeskiSignatureWeightData03.values key 8 0 ColeskiSignatureWeightData03.keys.size
              else 0
        else
          if key <= 215674950219530020 then
            if key <= 175346520843300648 then
              if key <= 175346520843300648 then
                lookupLoop ColeskiSignatureWeightData04.keys ColeskiSignatureWeightData04.values key 8 0 ColeskiSignatureWeightData04.keys.size
              else 0
            else
              if key <= 215674950219530020 then
                lookupLoop ColeskiSignatureWeightData05.keys ColeskiSignatureWeightData05.values key 8 0 ColeskiSignatureWeightData05.keys.size
              else 0
          else
            if key <= 255444854197302031 then
              if key <= 255444854197302031 then
                lookupLoop ColeskiSignatureWeightData06.keys ColeskiSignatureWeightData06.values key 8 0 ColeskiSignatureWeightData06.keys.size
              else 0
            else
              if key <= 289165966610860626 then
                lookupLoop ColeskiSignatureWeightData07.keys ColeskiSignatureWeightData07.values key 8 0 ColeskiSignatureWeightData07.keys.size
              else 0
      else
        if key <= 433533740991375522 then
          if key <= 355067602767899083 then
            if key <= 321438690492528665 then
              if key <= 321438690492528665 then
                lookupLoop ColeskiSignatureWeightData08.keys ColeskiSignatureWeightData08.values key 8 0 ColeskiSignatureWeightData08.keys.size
              else 0
            else
              if key <= 355067602767899083 then
                lookupLoop ColeskiSignatureWeightData09.keys ColeskiSignatureWeightData09.values key 8 0 ColeskiSignatureWeightData09.keys.size
              else 0
          else
            if key <= 393378820874879123 then
              if key <= 393378820874879123 then
                lookupLoop ColeskiSignatureWeightData10.keys ColeskiSignatureWeightData10.values key 8 0 ColeskiSignatureWeightData10.keys.size
              else 0
            else
              if key <= 433533740991375522 then
                lookupLoop ColeskiSignatureWeightData11.keys ColeskiSignatureWeightData11.values key 8 0 ColeskiSignatureWeightData11.keys.size
              else 0
        else
          if key <= 505239618171933283 then
            if key <= 469393156442486662 then
              if key <= 469393156442486662 then
                lookupLoop ColeskiSignatureWeightData12.keys ColeskiSignatureWeightData12.values key 8 0 ColeskiSignatureWeightData12.keys.size
              else 0
            else
              if key <= 505239618171933283 then
                lookupLoop ColeskiSignatureWeightData13.keys ColeskiSignatureWeightData13.values key 8 0 ColeskiSignatureWeightData13.keys.size
              else 0
          else
            if key <= 539812614285275873 then
              if key <= 539812614285275873 then
                lookupLoop ColeskiSignatureWeightData14.keys ColeskiSignatureWeightData14.values key 8 0 ColeskiSignatureWeightData14.keys.size
              else 0
            else
              if key <= 578448709955487916 then
                lookupLoop ColeskiSignatureWeightData15.keys ColeskiSignatureWeightData15.values key 8 0 ColeskiSignatureWeightData15.keys.size
              else 0
    else
      if key <= 858791864860574977 then
        if key <= 718777616162977825 then
          if key <= 646893776107528108 then
            if key <= 611385987490943634 then
              if key <= 611385987490943634 then
                lookupLoop ColeskiSignatureWeightData16.keys ColeskiSignatureWeightData16.values key 8 0 ColeskiSignatureWeightData16.keys.size
              else 0
            else
              if key <= 646893776107528108 then
                lookupLoop ColeskiSignatureWeightData17.keys ColeskiSignatureWeightData17.values key 8 0 ColeskiSignatureWeightData17.keys.size
              else 0
          else
            if key <= 679860744102506824 then
              if key <= 679860744102506824 then
                lookupLoop ColeskiSignatureWeightData18.keys ColeskiSignatureWeightData18.values key 8 0 ColeskiSignatureWeightData18.keys.size
              else 0
            else
              if key <= 718777616162977825 then
                lookupLoop ColeskiSignatureWeightData19.keys ColeskiSignatureWeightData19.values key 8 0 ColeskiSignatureWeightData19.keys.size
              else 0
        else
          if key <= 790459294418314286 then
            if key <= 752649232925418792 then
              if key <= 752649232925418792 then
                lookupLoop ColeskiSignatureWeightData20.keys ColeskiSignatureWeightData20.values key 8 0 ColeskiSignatureWeightData20.keys.size
              else 0
            else
              if key <= 790459294418314286 then
                lookupLoop ColeskiSignatureWeightData21.keys ColeskiSignatureWeightData21.values key 8 0 ColeskiSignatureWeightData21.keys.size
              else 0
          else
            if key <= 824796200336133759 then
              if key <= 824796200336133759 then
                lookupLoop ColeskiSignatureWeightData22.keys ColeskiSignatureWeightData22.values key 8 0 ColeskiSignatureWeightData22.keys.size
              else 0
            else
              if key <= 858791864860574977 then
                lookupLoop ColeskiSignatureWeightData23.keys ColeskiSignatureWeightData23.values key 8 0 ColeskiSignatureWeightData23.keys.size
              else 0
      else
        if key <= 1005318289076264815 then
          if key <= 934799263205123972 then
            if key <= 898028193258689013 then
              if key <= 898028193258689013 then
                lookupLoop ColeskiSignatureWeightData24.keys ColeskiSignatureWeightData24.values key 8 0 ColeskiSignatureWeightData24.keys.size
              else 0
            else
              if key <= 934799263205123972 then
                lookupLoop ColeskiSignatureWeightData25.keys ColeskiSignatureWeightData25.values key 8 0 ColeskiSignatureWeightData25.keys.size
              else 0
          else
            if key <= 973836322666501666 then
              if key <= 973836322666501666 then
                lookupLoop ColeskiSignatureWeightData26.keys ColeskiSignatureWeightData26.values key 8 0 ColeskiSignatureWeightData26.keys.size
              else 0
            else
              if key <= 1005318289076264815 then
                lookupLoop ColeskiSignatureWeightData27.keys ColeskiSignatureWeightData27.values key 8 0 ColeskiSignatureWeightData27.keys.size
              else 0
        else
          if key <= 1075871292305223611 then
            if key <= 1041973371551871382 then
              if key <= 1041973371551871382 then
                lookupLoop ColeskiSignatureWeightData28.keys ColeskiSignatureWeightData28.values key 8 0 ColeskiSignatureWeightData28.keys.size
              else 0
            else
              if key <= 1075871292305223611 then
                lookupLoop ColeskiSignatureWeightData29.keys ColeskiSignatureWeightData29.values key 8 0 ColeskiSignatureWeightData29.keys.size
              else 0
          else
            if key <= 1109610068406727484 then
              if key <= 1109610068406727484 then
                lookupLoop ColeskiSignatureWeightData30.keys ColeskiSignatureWeightData30.values key 8 0 ColeskiSignatureWeightData30.keys.size
              else 0
            else
              if key <= 1151182766095761106 then
                lookupLoop ColeskiSignatureWeightData31.keys ColeskiSignatureWeightData31.values key 8 0 ColeskiSignatureWeightData31.keys.size
              else 0
  else
    if key <= 1724237071039677872 then
      if key <= 1433129542249622276 then
        if key <= 1288545984959503311 then
          if key <= 1220552231791629135 then
            if key <= 1185594843492414445 then
              if key <= 1185594843492414445 then
                lookupLoop ColeskiSignatureWeightData32.keys ColeskiSignatureWeightData32.values key 8 0 ColeskiSignatureWeightData32.keys.size
              else 0
            else
              if key <= 1220552231791629135 then
                lookupLoop ColeskiSignatureWeightData33.keys ColeskiSignatureWeightData33.values key 8 0 ColeskiSignatureWeightData33.keys.size
              else 0
          else
            if key <= 1255224408984023636 then
              if key <= 1255224408984023636 then
                lookupLoop ColeskiSignatureWeightData34.keys ColeskiSignatureWeightData34.values key 8 0 ColeskiSignatureWeightData34.keys.size
              else 0
            else
              if key <= 1288545984959503311 then
                lookupLoop ColeskiSignatureWeightData35.keys ColeskiSignatureWeightData35.values key 8 0 ColeskiSignatureWeightData35.keys.size
              else 0
        else
          if key <= 1360794502156797865 then
            if key <= 1324640092133570028 then
              if key <= 1324640092133570028 then
                lookupLoop ColeskiSignatureWeightData36.keys ColeskiSignatureWeightData36.values key 8 0 ColeskiSignatureWeightData36.keys.size
              else 0
            else
              if key <= 1360794502156797865 then
                lookupLoop ColeskiSignatureWeightData37.keys ColeskiSignatureWeightData37.values key 8 0 ColeskiSignatureWeightData37.keys.size
              else 0
          else
            if key <= 1394441054577990756 then
              if key <= 1394441054577990756 then
                lookupLoop ColeskiSignatureWeightData38.keys ColeskiSignatureWeightData38.values key 8 0 ColeskiSignatureWeightData38.keys.size
              else 0
            else
              if key <= 1433129542249622276 then
                lookupLoop ColeskiSignatureWeightData39.keys ColeskiSignatureWeightData39.values key 8 0 ColeskiSignatureWeightData39.keys.size
              else 0
      else
        if key <= 1576589746525453780 then
          if key <= 1508712568176665416 then
            if key <= 1472780815442282038 then
              if key <= 1472780815442282038 then
                lookupLoop ColeskiSignatureWeightData40.keys ColeskiSignatureWeightData40.values key 8 0 ColeskiSignatureWeightData40.keys.size
              else 0
            else
              if key <= 1508712568176665416 then
                lookupLoop ColeskiSignatureWeightData41.keys ColeskiSignatureWeightData41.values key 8 0 ColeskiSignatureWeightData41.keys.size
              else 0
          else
            if key <= 1541604839680944139 then
              if key <= 1541604839680944139 then
                lookupLoop ColeskiSignatureWeightData42.keys ColeskiSignatureWeightData42.values key 8 0 ColeskiSignatureWeightData42.keys.size
              else 0
            else
              if key <= 1576589746525453780 then
                lookupLoop ColeskiSignatureWeightData43.keys ColeskiSignatureWeightData43.values key 8 0 ColeskiSignatureWeightData43.keys.size
              else 0
        else
          if key <= 1644031572046325489 then
            if key <= 1609933751771441030 then
              if key <= 1609933751771441030 then
                lookupLoop ColeskiSignatureWeightData44.keys ColeskiSignatureWeightData44.values key 8 0 ColeskiSignatureWeightData44.keys.size
              else 0
            else
              if key <= 1644031572046325489 then
                lookupLoop ColeskiSignatureWeightData45.keys ColeskiSignatureWeightData45.values key 8 0 ColeskiSignatureWeightData45.keys.size
              else 0
          else
            if key <= 1684446533994060057 then
              if key <= 1684446533994060057 then
                lookupLoop ColeskiSignatureWeightData46.keys ColeskiSignatureWeightData46.values key 8 0 ColeskiSignatureWeightData46.keys.size
              else 0
            else
              if key <= 1724237071039677872 then
                lookupLoop ColeskiSignatureWeightData47.keys ColeskiSignatureWeightData47.values key 8 0 ColeskiSignatureWeightData47.keys.size
              else 0
    else
      if key <= 2012513677478953954 then
        if key <= 1870266085746602144 then
          if key <= 1796114123056254481 then
            if key <= 1763040816796124638 then
              if key <= 1763040816796124638 then
                lookupLoop ColeskiSignatureWeightData48.keys ColeskiSignatureWeightData48.values key 8 0 ColeskiSignatureWeightData48.keys.size
              else 0
            else
              if key <= 1796114123056254481 then
                lookupLoop ColeskiSignatureWeightData49.keys ColeskiSignatureWeightData49.values key 8 0 ColeskiSignatureWeightData49.keys.size
              else 0
          else
            if key <= 1835653008682811866 then
              if key <= 1835653008682811866 then
                lookupLoop ColeskiSignatureWeightData50.keys ColeskiSignatureWeightData50.values key 8 0 ColeskiSignatureWeightData50.keys.size
              else 0
            else
              if key <= 1870266085746602144 then
                lookupLoop ColeskiSignatureWeightData51.keys ColeskiSignatureWeightData51.values key 8 0 ColeskiSignatureWeightData51.keys.size
              else 0
        else
          if key <= 1937654278614014790 then
            if key <= 1902692339432626859 then
              if key <= 1902692339432626859 then
                lookupLoop ColeskiSignatureWeightData52.keys ColeskiSignatureWeightData52.values key 8 0 ColeskiSignatureWeightData52.keys.size
              else 0
            else
              if key <= 1937654278614014790 then
                lookupLoop ColeskiSignatureWeightData53.keys ColeskiSignatureWeightData53.values key 8 0 ColeskiSignatureWeightData53.keys.size
              else 0
          else
            if key <= 1974562565196750453 then
              if key <= 1974562565196750453 then
                lookupLoop ColeskiSignatureWeightData54.keys ColeskiSignatureWeightData54.values key 8 0 ColeskiSignatureWeightData54.keys.size
              else 0
            else
              if key <= 2012513677478953954 then
                lookupLoop ColeskiSignatureWeightData55.keys ColeskiSignatureWeightData55.values key 8 0 ColeskiSignatureWeightData55.keys.size
              else 0
      else
        if key <= 2158477235482371288 then
          if key <= 2084999167782043745 then
            if key <= 2047211335662148786 then
              if key <= 2047211335662148786 then
                lookupLoop ColeskiSignatureWeightData56.keys ColeskiSignatureWeightData56.values key 8 0 ColeskiSignatureWeightData56.keys.size
              else 0
            else
              if key <= 2084999167782043745 then
                lookupLoop ColeskiSignatureWeightData57.keys ColeskiSignatureWeightData57.values key 8 0 ColeskiSignatureWeightData57.keys.size
              else 0
          else
            if key <= 2121454847005016203 then
              if key <= 2121454847005016203 then
                lookupLoop ColeskiSignatureWeightData58.keys ColeskiSignatureWeightData58.values key 8 0 ColeskiSignatureWeightData58.keys.size
              else 0
            else
              if key <= 2158477235482371288 then
                lookupLoop ColeskiSignatureWeightData59.keys ColeskiSignatureWeightData59.values key 8 0 ColeskiSignatureWeightData59.keys.size
              else 0
        else
          if key <= 2231916632763597129 then
            if key <= 2197176340934636861 then
              if key <= 2197176340934636861 then
                lookupLoop ColeskiSignatureWeightData60.keys ColeskiSignatureWeightData60.values key 8 0 ColeskiSignatureWeightData60.keys.size
              else 0
            else
              if key <= 2231916632763597129 then
                lookupLoop ColeskiSignatureWeightData61.keys ColeskiSignatureWeightData61.values key 8 0 ColeskiSignatureWeightData61.keys.size
              else 0
          else
            if key <= 2273373657626775218 then
              if key <= 2273373657626775218 then
                lookupLoop ColeskiSignatureWeightData62.keys ColeskiSignatureWeightData62.values key 8 0 ColeskiSignatureWeightData62.keys.size
              else 0
            else
              if key <= 2305840576048631548 then
                lookupLoop ColeskiSignatureWeightData63.keys ColeskiSignatureWeightData63.values key 8 0 ColeskiSignatureWeightData63.keys.size
              else 0

noncomputable def coefficientFor (x : FivePattern) (flag : FiveFlag) : ℝ :=
  (signatureWeight (signature x flag) : ℝ)

theorem coefficientFor_transport (g : G) (x : FivePattern) (flag : FiveFlag) :
    coefficientFor (g • x) (g • flag) = coefficientFor x flag := by
  unfold coefficientFor
  rw [signature_transport]

end ColeskiSignatureWeights

#print axioms ColeskiSignatureWeights.coefficientFor_transport

/- END bundled local module SignatureWeights -/
