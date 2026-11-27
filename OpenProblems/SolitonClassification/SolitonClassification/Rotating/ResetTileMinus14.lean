import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0896
import SolitonClassification.Rotating.ResetPackedMinus0912
import SolitonClassification.Rotating.ResetPackedMinus0928
import SolitonClassification.Rotating.ResetPackedMinus0944
namespace SolitonClassification.Rotating.DyadicReset.TileMinus14
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p896,GridMinus.atNode 896,GridMinus.atNode 897,NodeMinus14.w0,CompactMinus0896.checked896,CompactMinus0896.small896,CompactMinus0896.nodes896,NodeMinus14.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p897,GridMinus.atNode 897,GridMinus.atNode 898,NodeMinus14.w1,CompactMinus0896.checked897,CompactMinus0896.small897,CompactMinus0896.nodes897,NodeMinus14.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p898,GridMinus.atNode 898,GridMinus.atNode 899,NodeMinus14.w2,CompactMinus0896.checked898,CompactMinus0896.small898,CompactMinus0896.nodes898,NodeMinus14.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p899,GridMinus.atNode 899,GridMinus.atNode 900,NodeMinus14.w3,CompactMinus0896.checked899,CompactMinus0896.small899,CompactMinus0896.nodes899,NodeMinus14.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p900,GridMinus.atNode 900,GridMinus.atNode 901,NodeMinus14.w4,CompactMinus0896.checked900,CompactMinus0896.small900,CompactMinus0896.nodes900,NodeMinus14.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p901,GridMinus.atNode 901,GridMinus.atNode 902,NodeMinus14.w5,CompactMinus0896.checked901,CompactMinus0896.small901,CompactMinus0896.nodes901,NodeMinus14.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p902,GridMinus.atNode 902,GridMinus.atNode 903,NodeMinus14.w6,CompactMinus0896.checked902,CompactMinus0896.small902,CompactMinus0896.nodes902,NodeMinus14.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p903,GridMinus.atNode 903,GridMinus.atNode 904,NodeMinus14.w7,CompactMinus0896.checked903,CompactMinus0896.small903,CompactMinus0896.nodes903,NodeMinus14.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p904,GridMinus.atNode 904,GridMinus.atNode 905,NodeMinus14.w8,CompactMinus0896.checked904,CompactMinus0896.small904,CompactMinus0896.nodes904,NodeMinus14.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p905,GridMinus.atNode 905,GridMinus.atNode 906,NodeMinus14.w9,CompactMinus0896.checked905,CompactMinus0896.small905,CompactMinus0896.nodes905,NodeMinus14.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p906,GridMinus.atNode 906,GridMinus.atNode 907,NodeMinus14.w10,CompactMinus0896.checked906,CompactMinus0896.small906,CompactMinus0896.nodes906,NodeMinus14.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p907,GridMinus.atNode 907,GridMinus.atNode 908,NodeMinus14.w11,CompactMinus0896.checked907,CompactMinus0896.small907,CompactMinus0896.nodes907,NodeMinus14.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p908,GridMinus.atNode 908,GridMinus.atNode 909,NodeMinus14.w12,CompactMinus0896.checked908,CompactMinus0896.small908,CompactMinus0896.nodes908,NodeMinus14.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p909,GridMinus.atNode 909,GridMinus.atNode 910,NodeMinus14.w13,CompactMinus0896.checked909,CompactMinus0896.small909,CompactMinus0896.nodes909,NodeMinus14.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p910,GridMinus.atNode 910,GridMinus.atNode 911,NodeMinus14.w14,CompactMinus0896.checked910,CompactMinus0896.small910,CompactMinus0896.nodes910,NodeMinus14.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0896.p911,GridMinus.atNode 911,GridMinus.atNode 912,NodeMinus14.w15,CompactMinus0896.checked911,CompactMinus0896.small911,CompactMinus0896.nodes911,NodeMinus14.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p912,GridMinus.atNode 912,GridMinus.atNode 913,NodeMinus14.w16,CompactMinus0912.checked912,CompactMinus0912.small912,CompactMinus0912.nodes912,NodeMinus14.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p913,GridMinus.atNode 913,GridMinus.atNode 914,NodeMinus14.w17,CompactMinus0912.checked913,CompactMinus0912.small913,CompactMinus0912.nodes913,NodeMinus14.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p914,GridMinus.atNode 914,GridMinus.atNode 915,NodeMinus14.w18,CompactMinus0912.checked914,CompactMinus0912.small914,CompactMinus0912.nodes914,NodeMinus14.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p915,GridMinus.atNode 915,GridMinus.atNode 916,NodeMinus14.w19,CompactMinus0912.checked915,CompactMinus0912.small915,CompactMinus0912.nodes915,NodeMinus14.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p916,GridMinus.atNode 916,GridMinus.atNode 917,NodeMinus14.w20,CompactMinus0912.checked916,CompactMinus0912.small916,CompactMinus0912.nodes916,NodeMinus14.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p917,GridMinus.atNode 917,GridMinus.atNode 918,NodeMinus14.w21,CompactMinus0912.checked917,CompactMinus0912.small917,CompactMinus0912.nodes917,NodeMinus14.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p918,GridMinus.atNode 918,GridMinus.atNode 919,NodeMinus14.w22,CompactMinus0912.checked918,CompactMinus0912.small918,CompactMinus0912.nodes918,NodeMinus14.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p919,GridMinus.atNode 919,GridMinus.atNode 920,NodeMinus14.w23,CompactMinus0912.checked919,CompactMinus0912.small919,CompactMinus0912.nodes919,NodeMinus14.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p920,GridMinus.atNode 920,GridMinus.atNode 921,NodeMinus14.w24,CompactMinus0912.checked920,CompactMinus0912.small920,CompactMinus0912.nodes920,NodeMinus14.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p921,GridMinus.atNode 921,GridMinus.atNode 922,NodeMinus14.w25,CompactMinus0912.checked921,CompactMinus0912.small921,CompactMinus0912.nodes921,NodeMinus14.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p922,GridMinus.atNode 922,GridMinus.atNode 923,NodeMinus14.w26,CompactMinus0912.checked922,CompactMinus0912.small922,CompactMinus0912.nodes922,NodeMinus14.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p923,GridMinus.atNode 923,GridMinus.atNode 924,NodeMinus14.w27,CompactMinus0912.checked923,CompactMinus0912.small923,CompactMinus0912.nodes923,NodeMinus14.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p924,GridMinus.atNode 924,GridMinus.atNode 925,NodeMinus14.w28,CompactMinus0912.checked924,CompactMinus0912.small924,CompactMinus0912.nodes924,NodeMinus14.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p925,GridMinus.atNode 925,GridMinus.atNode 926,NodeMinus14.w29,CompactMinus0912.checked925,CompactMinus0912.small925,CompactMinus0912.nodes925,NodeMinus14.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p926,GridMinus.atNode 926,GridMinus.atNode 927,NodeMinus14.w30,CompactMinus0912.checked926,CompactMinus0912.small926,CompactMinus0912.nodes926,NodeMinus14.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0912.p927,GridMinus.atNode 927,GridMinus.atNode 928,NodeMinus14.w31,CompactMinus0912.checked927,CompactMinus0912.small927,CompactMinus0912.nodes927,NodeMinus14.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p928,GridMinus.atNode 928,GridMinus.atNode 929,NodeMinus14.w32,CompactMinus0928.checked928,CompactMinus0928.small928,CompactMinus0928.nodes928,NodeMinus14.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p929,GridMinus.atNode 929,GridMinus.atNode 930,NodeMinus14.w33,CompactMinus0928.checked929,CompactMinus0928.small929,CompactMinus0928.nodes929,NodeMinus14.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p930,GridMinus.atNode 930,GridMinus.atNode 931,NodeMinus14.w34,CompactMinus0928.checked930,CompactMinus0928.small930,CompactMinus0928.nodes930,NodeMinus14.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p931,GridMinus.atNode 931,GridMinus.atNode 932,NodeMinus14.w35,CompactMinus0928.checked931,CompactMinus0928.small931,CompactMinus0928.nodes931,NodeMinus14.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p932,GridMinus.atNode 932,GridMinus.atNode 933,NodeMinus14.w36,CompactMinus0928.checked932,CompactMinus0928.small932,CompactMinus0928.nodes932,NodeMinus14.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p933,GridMinus.atNode 933,GridMinus.atNode 934,NodeMinus14.w37,CompactMinus0928.checked933,CompactMinus0928.small933,CompactMinus0928.nodes933,NodeMinus14.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p934,GridMinus.atNode 934,GridMinus.atNode 935,NodeMinus14.w38,CompactMinus0928.checked934,CompactMinus0928.small934,CompactMinus0928.nodes934,NodeMinus14.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p935,GridMinus.atNode 935,GridMinus.atNode 936,NodeMinus14.w39,CompactMinus0928.checked935,CompactMinus0928.small935,CompactMinus0928.nodes935,NodeMinus14.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p936,GridMinus.atNode 936,GridMinus.atNode 937,NodeMinus14.w40,CompactMinus0928.checked936,CompactMinus0928.small936,CompactMinus0928.nodes936,NodeMinus14.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p937,GridMinus.atNode 937,GridMinus.atNode 938,NodeMinus14.w41,CompactMinus0928.checked937,CompactMinus0928.small937,CompactMinus0928.nodes937,NodeMinus14.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p938,GridMinus.atNode 938,GridMinus.atNode 939,NodeMinus14.w42,CompactMinus0928.checked938,CompactMinus0928.small938,CompactMinus0928.nodes938,NodeMinus14.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p939,GridMinus.atNode 939,GridMinus.atNode 940,NodeMinus14.w43,CompactMinus0928.checked939,CompactMinus0928.small939,CompactMinus0928.nodes939,NodeMinus14.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p940,GridMinus.atNode 940,GridMinus.atNode 941,NodeMinus14.w44,CompactMinus0928.checked940,CompactMinus0928.small940,CompactMinus0928.nodes940,NodeMinus14.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p941,GridMinus.atNode 941,GridMinus.atNode 942,NodeMinus14.w45,CompactMinus0928.checked941,CompactMinus0928.small941,CompactMinus0928.nodes941,NodeMinus14.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p942,GridMinus.atNode 942,GridMinus.atNode 943,NodeMinus14.w46,CompactMinus0928.checked942,CompactMinus0928.small942,CompactMinus0928.nodes942,NodeMinus14.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0928.p943,GridMinus.atNode 943,GridMinus.atNode 944,NodeMinus14.w47,CompactMinus0928.checked943,CompactMinus0928.small943,CompactMinus0928.nodes943,NodeMinus14.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p944,GridMinus.atNode 944,GridMinus.atNode 945,NodeMinus14.w48,CompactMinus0944.checked944,CompactMinus0944.small944,CompactMinus0944.nodes944,NodeMinus14.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p945,GridMinus.atNode 945,GridMinus.atNode 946,NodeMinus14.w49,CompactMinus0944.checked945,CompactMinus0944.small945,CompactMinus0944.nodes945,NodeMinus14.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p946,GridMinus.atNode 946,GridMinus.atNode 947,NodeMinus14.w50,CompactMinus0944.checked946,CompactMinus0944.small946,CompactMinus0944.nodes946,NodeMinus14.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p947,GridMinus.atNode 947,GridMinus.atNode 948,NodeMinus14.w51,CompactMinus0944.checked947,CompactMinus0944.small947,CompactMinus0944.nodes947,NodeMinus14.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p948,GridMinus.atNode 948,GridMinus.atNode 949,NodeMinus14.w52,CompactMinus0944.checked948,CompactMinus0944.small948,CompactMinus0944.nodes948,NodeMinus14.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p949,GridMinus.atNode 949,GridMinus.atNode 950,NodeMinus14.w53,CompactMinus0944.checked949,CompactMinus0944.small949,CompactMinus0944.nodes949,NodeMinus14.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p950,GridMinus.atNode 950,GridMinus.atNode 951,NodeMinus14.w54,CompactMinus0944.checked950,CompactMinus0944.small950,CompactMinus0944.nodes950,NodeMinus14.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p951,GridMinus.atNode 951,GridMinus.atNode 952,NodeMinus14.w55,CompactMinus0944.checked951,CompactMinus0944.small951,CompactMinus0944.nodes951,NodeMinus14.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p952,GridMinus.atNode 952,GridMinus.atNode 953,NodeMinus14.w56,CompactMinus0944.checked952,CompactMinus0944.small952,CompactMinus0944.nodes952,NodeMinus14.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p953,GridMinus.atNode 953,GridMinus.atNode 954,NodeMinus14.w57,CompactMinus0944.checked953,CompactMinus0944.small953,CompactMinus0944.nodes953,NodeMinus14.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p954,GridMinus.atNode 954,GridMinus.atNode 955,NodeMinus14.w58,CompactMinus0944.checked954,CompactMinus0944.small954,CompactMinus0944.nodes954,NodeMinus14.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p955,GridMinus.atNode 955,GridMinus.atNode 956,NodeMinus14.w59,CompactMinus0944.checked955,CompactMinus0944.small955,CompactMinus0944.nodes955,NodeMinus14.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p956,GridMinus.atNode 956,GridMinus.atNode 957,NodeMinus14.w60,CompactMinus0944.checked956,CompactMinus0944.small956,CompactMinus0944.nodes956,NodeMinus14.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p957,GridMinus.atNode 957,GridMinus.atNode 958,NodeMinus14.w61,CompactMinus0944.checked957,CompactMinus0944.small957,CompactMinus0944.nodes957,NodeMinus14.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p958,GridMinus.atNode 958,GridMinus.atNode 959,NodeMinus14.w62,CompactMinus0944.checked958,CompactMinus0944.small958,CompactMinus0944.nodes958,NodeMinus14.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0944.p959,GridMinus.atNode 959,GridMinus.atNode 960,NodeMinus14.w63,CompactMinus0944.checked959,CompactMinus0944.small959,CompactMinus0944.nodes959,NodeMinus14.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (896+j) ∧
    (atRow j).right=GridMinus.atNode (896+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus14
