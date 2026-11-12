import SolitonClassification.Rotating.FirstResidualIntegerSquares60
namespace SolitonClassification.Rotating.FirstResidualInteger60
open Candidate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false


private theorem extendBound (P : ℕ → Prop) (n : ℕ)
    (h : ∀i<n,P i) (hn : P n) : ∀i<n+1,P i := by
  intro i hi
  by_cases hlt : i<n
  · exact h i hlt
  · have he : i=n := by omega
    simpa only [he] using hn


theorem residualRank0 : residuals[0]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 60 BenchState60.table squares := by decide +kernel

theorem residualRank1 : residuals[1]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 61 BenchState60.table squares := by decide +kernel

theorem residualRank2 : residuals[2]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 62 BenchState60.table squares := by decide +kernel

theorem residualRank3 : residuals[3]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 63 BenchState60.table squares := by decide +kernel

theorem residualRank4 : residuals[4]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 64 BenchState60.table squares := by decide +kernel

theorem residualRank5 : residuals[5]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 65 BenchState60.table squares := by decide +kernel

theorem residualRank6 : residuals[6]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 66 BenchState60.table squares := by decide +kernel

theorem residualRank7 : residuals[7]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 67 BenchState60.table squares := by decide +kernel

theorem residualRank8 : residuals[8]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 68 BenchState60.table squares := by decide +kernel

theorem residualRank9 : residuals[9]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 69 BenchState60.table squares := by decide +kernel

theorem residualRank10 : residuals[10]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 70 BenchState60.table squares := by decide +kernel

theorem residualRank11 : residuals[11]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 71 BenchState60.table squares := by decide +kernel

theorem residualRank12 : residuals[12]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 72 BenchState60.table squares := by decide +kernel

theorem residualRank13 : residuals[13]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 73 BenchState60.table squares := by decide +kernel

theorem residualRank14 : residuals[14]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 74 BenchState60.table squares := by decide +kernel

theorem residualRank15 : residuals[15]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 75 BenchState60.table squares := by decide +kernel

theorem residualRank16 : residuals[16]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 76 BenchState60.table squares := by decide +kernel

theorem residualRank17 : residuals[17]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 77 BenchState60.table squares := by decide +kernel

theorem residualRank18 : residuals[18]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 78 BenchState60.table squares := by decide +kernel

theorem residualRank19 : residuals[19]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 79 BenchState60.table squares := by decide +kernel

theorem residualRank20 : residuals[20]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 80 BenchState60.table squares := by decide +kernel

theorem residualRank21 : residuals[21]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 81 BenchState60.table squares := by decide +kernel

theorem residualRank22 : residuals[22]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 82 BenchState60.table squares := by decide +kernel

theorem residualRank23 : residuals[23]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 83 BenchState60.table squares := by decide +kernel

theorem residualRank24 : residuals[24]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 84 BenchState60.table squares := by decide +kernel

theorem residualRank25 : residuals[25]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 85 BenchState60.table squares := by decide +kernel

theorem residualRank26 : residuals[26]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 86 BenchState60.table squares := by decide +kernel

theorem residualRank27 : residuals[27]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 87 BenchState60.table squares := by decide +kernel

theorem residualRank28 : residuals[28]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 88 BenchState60.table squares := by decide +kernel

theorem residualRank29 : residuals[29]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 89 BenchState60.table squares := by decide +kernel

theorem residualRank30 : residuals[30]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 90 BenchState60.table squares := by decide +kernel

theorem residualRank31 : residuals[31]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 91 BenchState60.table squares := by decide +kernel

theorem residualRank32 : residuals[32]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 92 BenchState60.table squares := by decide +kernel

theorem residualRank33 : residuals[33]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 93 BenchState60.table squares := by decide +kernel

theorem residualRank34 : residuals[34]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 94 BenchState60.table squares := by decide +kernel

theorem residualRank35 : residuals[35]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 95 BenchState60.table squares := by decide +kernel

theorem residualRank36 : residuals[36]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 96 BenchState60.table squares := by decide +kernel

theorem residualRank37 : residuals[37]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 97 BenchState60.table squares := by decide +kernel

theorem residualRank38 : residuals[38]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 98 BenchState60.table squares := by decide +kernel

theorem residualRank39 : residuals[39]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 99 BenchState60.table squares := by decide +kernel

theorem residualRank40 : residuals[40]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 100 BenchState60.table squares := by decide +kernel

theorem residualRank41 : residuals[41]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 101 BenchState60.table squares := by decide +kernel

theorem residualRank42 : residuals[42]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 102 BenchState60.table squares := by decide +kernel

theorem residualRank43 : residuals[43]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 103 BenchState60.table squares := by decide +kernel

theorem residualRank44 : residuals[44]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 104 BenchState60.table squares := by decide +kernel

theorem residualRank45 : residuals[45]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 105 BenchState60.table squares := by decide +kernel

theorem residualRank46 : residuals[46]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 106 BenchState60.table squares := by decide +kernel

theorem residualRank47 : residuals[47]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 107 BenchState60.table squares := by decide +kernel

theorem residualRank48 : residuals[48]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 108 BenchState60.table squares := by decide +kernel

theorem residualRank49 : residuals[49]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 109 BenchState60.table squares := by decide +kernel

theorem residualRank50 : residuals[50]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 110 BenchState60.table squares := by decide +kernel

theorem residualRank51 : residuals[51]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 111 BenchState60.table squares := by decide +kernel

theorem residualRank52 : residuals[52]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 112 BenchState60.table squares := by decide +kernel

theorem residualRank53 : residuals[53]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 113 BenchState60.table squares := by decide +kernel

theorem residualRank54 : residuals[54]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 114 BenchState60.table squares := by decide +kernel

theorem residualRank55 : residuals[55]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 115 BenchState60.table squares := by decide +kernel

theorem residualRank56 : residuals[56]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 116 BenchState60.table squares := by decide +kernel

theorem residualRank57 : residuals[57]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 117 BenchState60.table squares := by decide +kernel

theorem residualRank58 : residuals[58]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 118 BenchState60.table squares := by decide +kernel

theorem residualRank59 : residuals[59]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 119 BenchState60.table squares := by decide +kernel

theorem residualRank60 : residuals[60]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 120 BenchState60.table squares := by decide +kernel

theorem residualRank61 : residuals[61]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 121 BenchState60.table squares := by decide +kernel

theorem residualRank62 : residuals[62]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 122 BenchState60.table squares := by decide +kernel

theorem residualRank63 : residuals[63]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 123 BenchState60.table squares := by decide +kernel

theorem residualRank64 : residuals[64]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 124 BenchState60.table squares := by decide +kernel

theorem residualRank65 : residuals[65]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 125 BenchState60.table squares := by decide +kernel

theorem residualRank66 : residuals[66]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 126 BenchState60.table squares := by decide +kernel

theorem residualRank67 : residuals[67]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 127 BenchState60.table squares := by decide +kernel

theorem residualRank68 : residuals[68]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 128 BenchState60.table squares := by decide +kernel

theorem residualRank69 : residuals[69]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 129 BenchState60.table squares := by decide +kernel

theorem residualRank70 : residuals[70]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 130 BenchState60.table squares := by decide +kernel

theorem residualRank71 : residuals[71]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 131 BenchState60.table squares := by decide +kernel

theorem residualRank72 : residuals[72]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 132 BenchState60.table squares := by decide +kernel

theorem residualRank73 : residuals[73]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 133 BenchState60.table squares := by decide +kernel

theorem residualRank74 : residuals[74]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 134 BenchState60.table squares := by decide +kernel

theorem residualRank75 : residuals[75]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 135 BenchState60.table squares := by decide +kernel

theorem residualRank76 : residuals[76]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 136 BenchState60.table squares := by decide +kernel

theorem residualRank77 : residuals[77]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 137 BenchState60.table squares := by decide +kernel

theorem residualRank78 : residuals[78]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 138 BenchState60.table squares := by decide +kernel

theorem residualRank79 : residuals[79]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 139 BenchState60.table squares := by decide +kernel

theorem residualRank80 : residuals[80]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 140 BenchState60.table squares := by decide +kernel

theorem residualRank81 : residuals[81]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 141 BenchState60.table squares := by decide +kernel

theorem residualRank82 : residuals[82]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 142 BenchState60.table squares := by decide +kernel

theorem residualRank83 : residuals[83]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 143 BenchState60.table squares := by decide +kernel

theorem residualRank84 : residuals[84]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 144 BenchState60.table squares := by decide +kernel

theorem residualRank85 : residuals[85]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 145 BenchState60.table squares := by decide +kernel

theorem residualRank86 : residuals[86]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 146 BenchState60.table squares := by decide +kernel

theorem residualRank87 : residuals[87]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 147 BenchState60.table squares := by decide +kernel

theorem residualRank88 : residuals[88]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 148 BenchState60.table squares := by decide +kernel

theorem residualRank89 : residuals[89]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 149 BenchState60.table squares := by decide +kernel

theorem residualRank90 : residuals[90]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 150 BenchState60.table squares := by decide +kernel

theorem residualRank91 : residuals[91]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 151 BenchState60.table squares := by decide +kernel

theorem residualRank92 : residuals[92]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 152 BenchState60.table squares := by decide +kernel

theorem residualRank93 : residuals[93]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 153 BenchState60.table squares := by decide +kernel

theorem residualRank94 : residuals[94]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 154 BenchState60.table squares := by decide +kernel

theorem residualRank95 : residuals[95]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 155 BenchState60.table squares := by decide +kernel

theorem residualRank96 : residuals[96]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 156 BenchState60.table squares := by decide +kernel

theorem residualRank97 : residuals[97]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 157 BenchState60.table squares := by decide +kernel

theorem residualRank98 : residuals[98]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 158 BenchState60.table squares := by decide +kernel

theorem residualRank99 : residuals[99]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 159 BenchState60.table squares := by decide +kernel

theorem residualRank100 : residuals[100]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 160 BenchState60.table squares := by decide +kernel

theorem residualRank101 : residuals[101]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 161 BenchState60.table squares := by decide +kernel

theorem residualRank102 : residuals[102]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 162 BenchState60.table squares := by decide +kernel

theorem residualRank103 : residuals[103]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 163 BenchState60.table squares := by decide +kernel

theorem residualRank104 : residuals[104]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 164 BenchState60.table squares := by decide +kernel

theorem residualRank105 : residuals[105]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 165 BenchState60.table squares := by decide +kernel

theorem residualRank106 : residuals[106]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 166 BenchState60.table squares := by decide +kernel

theorem residualRank107 : residuals[107]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 167 BenchState60.table squares := by decide +kernel

theorem residualRank108 : residuals[108]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 168 BenchState60.table squares := by decide +kernel

theorem residualRank109 : residuals[109]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 169 BenchState60.table squares := by decide +kernel

theorem residualRank110 : residuals[110]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 170 BenchState60.table squares := by decide +kernel

theorem residualRank111 : residuals[111]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 171 BenchState60.table squares := by decide +kernel

theorem residualRank112 : residuals[112]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 172 BenchState60.table squares := by decide +kernel

theorem residualRank113 : residuals[113]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 173 BenchState60.table squares := by decide +kernel

theorem residualRank114 : residuals[114]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 174 BenchState60.table squares := by decide +kernel

theorem residualRank115 : residuals[115]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 175 BenchState60.table squares := by decide +kernel

theorem residualRank116 : residuals[116]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 176 BenchState60.table squares := by decide +kernel

theorem residualRank117 : residuals[117]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 177 BenchState60.table squares := by decide +kernel

theorem residualRank118 : residuals[118]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 178 BenchState60.table squares := by decide +kernel

theorem residualRank119 : residuals[119]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 179 BenchState60.table squares := by decide +kernel

theorem residualRank120 : residuals[120]?.getD (Vector.ofFn zeroFixedVector)=
  fixedResidualNext mesh 180 BenchState60.table squares := by decide +kernel

theorem residuals_checked : StateResidualValid mesh 60 180 BenchState60.table squares residuals := by
  let P : ℕ → Prop := fun n=>residuals[n]?.getD (Vector.ofFn zeroFixedVector)=
    fixedResidualNext mesh (60+n) BenchState60.table squares
  have hall : ∀n<121,P n := (extendBound P 120 (extendBound P 119 (extendBound P 118 (extendBound P 117 (extendBound P 116 (extendBound P 115 (extendBound P 114 (extendBound P 113 (extendBound P 112 (extendBound P 111 (extendBound P 110 (extendBound P 109 (extendBound P 108 (extendBound P 107 (extendBound P 106 (extendBound P 105 (extendBound P 104 (extendBound P 103 (extendBound P 102 (extendBound P 101 (extendBound P 100 (extendBound P 99 (extendBound P 98 (extendBound P 97 (extendBound P 96 (extendBound P 95 (extendBound P 94 (extendBound P 93 (extendBound P 92 (extendBound P 91 (extendBound P 90 (extendBound P 89 (extendBound P 88 (extendBound P 87 (extendBound P 86 (extendBound P 85 (extendBound P 84 (extendBound P 83 (extendBound P 82 (extendBound P 81 (extendBound P 80 (extendBound P 79 (extendBound P 78 (extendBound P 77 (extendBound P 76 (extendBound P 75 (extendBound P 74 (extendBound P 73 (extendBound P 72 (extendBound P 71 (extendBound P 70 (extendBound P 69 (extendBound P 68 (extendBound P 67 (extendBound P 66 (extendBound P 65 (extendBound P 64 (extendBound P 63 (extendBound P 62 (extendBound P 61 (extendBound P 60 (extendBound P 59 (extendBound P 58 (extendBound P 57 (extendBound P 56 (extendBound P 55 (extendBound P 54 (extendBound P 53 (extendBound P 52 (extendBound P 51 (extendBound P 50 (extendBound P 49 (extendBound P 48 (extendBound P 47 (extendBound P 46 (extendBound P 45 (extendBound P 44 (extendBound P 43 (extendBound P 42 (extendBound P 41 (extendBound P 40 (extendBound P 39 (extendBound P 38 (extendBound P 37 (extendBound P 36 (extendBound P 35 (extendBound P 34 (extendBound P 33 (extendBound P 32 (extendBound P 31 (extendBound P 30 (extendBound P 29 (extendBound P 28 (extendBound P 27 (extendBound P 26 (extendBound P 25 (extendBound P 24 (extendBound P 23 (extendBound P 22 (extendBound P 21 (extendBound P 20 (extendBound P 19 (extendBound P 18 (extendBound P 17 (extendBound P 16 (extendBound P 15 (extendBound P 14 (extendBound P 13 (extendBound P 12 (extendBound P 11 (extendBound P 10 (extendBound P 9 (extendBound P 8 (extendBound P 7 (extendBound P 6 (extendBound P 5 (extendBound P 4 (extendBound P 3 (extendBound P 2 (extendBound P 1 (extendBound P 0 (fun i hi => (Nat.not_lt_zero i hi).elim) residualRank0) residualRank1) residualRank2) residualRank3) residualRank4) residualRank5) residualRank6) residualRank7) residualRank8) residualRank9) residualRank10) residualRank11) residualRank12) residualRank13) residualRank14) residualRank15) residualRank16) residualRank17) residualRank18) residualRank19) residualRank20) residualRank21) residualRank22) residualRank23) residualRank24) residualRank25) residualRank26) residualRank27) residualRank28) residualRank29) residualRank30) residualRank31) residualRank32) residualRank33) residualRank34) residualRank35) residualRank36) residualRank37) residualRank38) residualRank39) residualRank40) residualRank41) residualRank42) residualRank43) residualRank44) residualRank45) residualRank46) residualRank47) residualRank48) residualRank49) residualRank50) residualRank51) residualRank52) residualRank53) residualRank54) residualRank55) residualRank56) residualRank57) residualRank58) residualRank59) residualRank60) residualRank61) residualRank62) residualRank63) residualRank64) residualRank65) residualRank66) residualRank67) residualRank68) residualRank69) residualRank70) residualRank71) residualRank72) residualRank73) residualRank74) residualRank75) residualRank76) residualRank77) residualRank78) residualRank79) residualRank80) residualRank81) residualRank82) residualRank83) residualRank84) residualRank85) residualRank86) residualRank87) residualRank88) residualRank89) residualRank90) residualRank91) residualRank92) residualRank93) residualRank94) residualRank95) residualRank96) residualRank97) residualRank98) residualRank99) residualRank100) residualRank101) residualRank102) residualRank103) residualRank104) residualRank105) residualRank106) residualRank107) residualRank108) residualRank109) residualRank110) residualRank111) residualRank112) residualRank113) residualRank114) residualRank115) residualRank116) residualRank117) residualRank118) residualRank119) residualRank120)
  intro n hn
  have hm : n.val-60<121 := by have := n.isLt; omega
  have heq : 60+(n.val-60)=n.val := by omega
  simpa only [P,heq] using hall (n.val-60) hm


end SolitonClassification.Rotating.FirstResidualInteger60
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Integer residual high-degree ranks audit passed."
