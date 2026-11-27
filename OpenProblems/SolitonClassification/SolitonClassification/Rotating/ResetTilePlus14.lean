import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0896
import SolitonClassification.Rotating.ResetPackedPlus0912
import SolitonClassification.Rotating.ResetPackedPlus0928
import SolitonClassification.Rotating.ResetPackedPlus0944
namespace SolitonClassification.Rotating.DyadicReset.TilePlus14
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p896,GridPlus.atNode 896,GridPlus.atNode 897,NodePlus14.w0,CompactPlus0896.checked896,CompactPlus0896.small896,CompactPlus0896.nodes896,NodePlus14.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p897,GridPlus.atNode 897,GridPlus.atNode 898,NodePlus14.w1,CompactPlus0896.checked897,CompactPlus0896.small897,CompactPlus0896.nodes897,NodePlus14.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p898,GridPlus.atNode 898,GridPlus.atNode 899,NodePlus14.w2,CompactPlus0896.checked898,CompactPlus0896.small898,CompactPlus0896.nodes898,NodePlus14.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p899,GridPlus.atNode 899,GridPlus.atNode 900,NodePlus14.w3,CompactPlus0896.checked899,CompactPlus0896.small899,CompactPlus0896.nodes899,NodePlus14.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p900,GridPlus.atNode 900,GridPlus.atNode 901,NodePlus14.w4,CompactPlus0896.checked900,CompactPlus0896.small900,CompactPlus0896.nodes900,NodePlus14.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p901,GridPlus.atNode 901,GridPlus.atNode 902,NodePlus14.w5,CompactPlus0896.checked901,CompactPlus0896.small901,CompactPlus0896.nodes901,NodePlus14.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p902,GridPlus.atNode 902,GridPlus.atNode 903,NodePlus14.w6,CompactPlus0896.checked902,CompactPlus0896.small902,CompactPlus0896.nodes902,NodePlus14.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p903,GridPlus.atNode 903,GridPlus.atNode 904,NodePlus14.w7,CompactPlus0896.checked903,CompactPlus0896.small903,CompactPlus0896.nodes903,NodePlus14.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p904,GridPlus.atNode 904,GridPlus.atNode 905,NodePlus14.w8,CompactPlus0896.checked904,CompactPlus0896.small904,CompactPlus0896.nodes904,NodePlus14.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p905,GridPlus.atNode 905,GridPlus.atNode 906,NodePlus14.w9,CompactPlus0896.checked905,CompactPlus0896.small905,CompactPlus0896.nodes905,NodePlus14.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p906,GridPlus.atNode 906,GridPlus.atNode 907,NodePlus14.w10,CompactPlus0896.checked906,CompactPlus0896.small906,CompactPlus0896.nodes906,NodePlus14.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p907,GridPlus.atNode 907,GridPlus.atNode 908,NodePlus14.w11,CompactPlus0896.checked907,CompactPlus0896.small907,CompactPlus0896.nodes907,NodePlus14.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p908,GridPlus.atNode 908,GridPlus.atNode 909,NodePlus14.w12,CompactPlus0896.checked908,CompactPlus0896.small908,CompactPlus0896.nodes908,NodePlus14.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p909,GridPlus.atNode 909,GridPlus.atNode 910,NodePlus14.w13,CompactPlus0896.checked909,CompactPlus0896.small909,CompactPlus0896.nodes909,NodePlus14.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p910,GridPlus.atNode 910,GridPlus.atNode 911,NodePlus14.w14,CompactPlus0896.checked910,CompactPlus0896.small910,CompactPlus0896.nodes910,NodePlus14.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0896.p911,GridPlus.atNode 911,GridPlus.atNode 912,NodePlus14.w15,CompactPlus0896.checked911,CompactPlus0896.small911,CompactPlus0896.nodes911,NodePlus14.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p912,GridPlus.atNode 912,GridPlus.atNode 913,NodePlus14.w16,CompactPlus0912.checked912,CompactPlus0912.small912,CompactPlus0912.nodes912,NodePlus14.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p913,GridPlus.atNode 913,GridPlus.atNode 914,NodePlus14.w17,CompactPlus0912.checked913,CompactPlus0912.small913,CompactPlus0912.nodes913,NodePlus14.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p914,GridPlus.atNode 914,GridPlus.atNode 915,NodePlus14.w18,CompactPlus0912.checked914,CompactPlus0912.small914,CompactPlus0912.nodes914,NodePlus14.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p915,GridPlus.atNode 915,GridPlus.atNode 916,NodePlus14.w19,CompactPlus0912.checked915,CompactPlus0912.small915,CompactPlus0912.nodes915,NodePlus14.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p916,GridPlus.atNode 916,GridPlus.atNode 917,NodePlus14.w20,CompactPlus0912.checked916,CompactPlus0912.small916,CompactPlus0912.nodes916,NodePlus14.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p917,GridPlus.atNode 917,GridPlus.atNode 918,NodePlus14.w21,CompactPlus0912.checked917,CompactPlus0912.small917,CompactPlus0912.nodes917,NodePlus14.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p918,GridPlus.atNode 918,GridPlus.atNode 919,NodePlus14.w22,CompactPlus0912.checked918,CompactPlus0912.small918,CompactPlus0912.nodes918,NodePlus14.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p919,GridPlus.atNode 919,GridPlus.atNode 920,NodePlus14.w23,CompactPlus0912.checked919,CompactPlus0912.small919,CompactPlus0912.nodes919,NodePlus14.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p920,GridPlus.atNode 920,GridPlus.atNode 921,NodePlus14.w24,CompactPlus0912.checked920,CompactPlus0912.small920,CompactPlus0912.nodes920,NodePlus14.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p921,GridPlus.atNode 921,GridPlus.atNode 922,NodePlus14.w25,CompactPlus0912.checked921,CompactPlus0912.small921,CompactPlus0912.nodes921,NodePlus14.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p922,GridPlus.atNode 922,GridPlus.atNode 923,NodePlus14.w26,CompactPlus0912.checked922,CompactPlus0912.small922,CompactPlus0912.nodes922,NodePlus14.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p923,GridPlus.atNode 923,GridPlus.atNode 924,NodePlus14.w27,CompactPlus0912.checked923,CompactPlus0912.small923,CompactPlus0912.nodes923,NodePlus14.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p924,GridPlus.atNode 924,GridPlus.atNode 925,NodePlus14.w28,CompactPlus0912.checked924,CompactPlus0912.small924,CompactPlus0912.nodes924,NodePlus14.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p925,GridPlus.atNode 925,GridPlus.atNode 926,NodePlus14.w29,CompactPlus0912.checked925,CompactPlus0912.small925,CompactPlus0912.nodes925,NodePlus14.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p926,GridPlus.atNode 926,GridPlus.atNode 927,NodePlus14.w30,CompactPlus0912.checked926,CompactPlus0912.small926,CompactPlus0912.nodes926,NodePlus14.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0912.p927,GridPlus.atNode 927,GridPlus.atNode 928,NodePlus14.w31,CompactPlus0912.checked927,CompactPlus0912.small927,CompactPlus0912.nodes927,NodePlus14.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p928,GridPlus.atNode 928,GridPlus.atNode 929,NodePlus14.w32,CompactPlus0928.checked928,CompactPlus0928.small928,CompactPlus0928.nodes928,NodePlus14.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p929,GridPlus.atNode 929,GridPlus.atNode 930,NodePlus14.w33,CompactPlus0928.checked929,CompactPlus0928.small929,CompactPlus0928.nodes929,NodePlus14.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p930,GridPlus.atNode 930,GridPlus.atNode 931,NodePlus14.w34,CompactPlus0928.checked930,CompactPlus0928.small930,CompactPlus0928.nodes930,NodePlus14.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p931,GridPlus.atNode 931,GridPlus.atNode 932,NodePlus14.w35,CompactPlus0928.checked931,CompactPlus0928.small931,CompactPlus0928.nodes931,NodePlus14.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p932,GridPlus.atNode 932,GridPlus.atNode 933,NodePlus14.w36,CompactPlus0928.checked932,CompactPlus0928.small932,CompactPlus0928.nodes932,NodePlus14.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p933,GridPlus.atNode 933,GridPlus.atNode 934,NodePlus14.w37,CompactPlus0928.checked933,CompactPlus0928.small933,CompactPlus0928.nodes933,NodePlus14.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p934,GridPlus.atNode 934,GridPlus.atNode 935,NodePlus14.w38,CompactPlus0928.checked934,CompactPlus0928.small934,CompactPlus0928.nodes934,NodePlus14.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p935,GridPlus.atNode 935,GridPlus.atNode 936,NodePlus14.w39,CompactPlus0928.checked935,CompactPlus0928.small935,CompactPlus0928.nodes935,NodePlus14.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p936,GridPlus.atNode 936,GridPlus.atNode 937,NodePlus14.w40,CompactPlus0928.checked936,CompactPlus0928.small936,CompactPlus0928.nodes936,NodePlus14.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p937,GridPlus.atNode 937,GridPlus.atNode 938,NodePlus14.w41,CompactPlus0928.checked937,CompactPlus0928.small937,CompactPlus0928.nodes937,NodePlus14.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p938,GridPlus.atNode 938,GridPlus.atNode 939,NodePlus14.w42,CompactPlus0928.checked938,CompactPlus0928.small938,CompactPlus0928.nodes938,NodePlus14.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p939,GridPlus.atNode 939,GridPlus.atNode 940,NodePlus14.w43,CompactPlus0928.checked939,CompactPlus0928.small939,CompactPlus0928.nodes939,NodePlus14.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p940,GridPlus.atNode 940,GridPlus.atNode 941,NodePlus14.w44,CompactPlus0928.checked940,CompactPlus0928.small940,CompactPlus0928.nodes940,NodePlus14.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p941,GridPlus.atNode 941,GridPlus.atNode 942,NodePlus14.w45,CompactPlus0928.checked941,CompactPlus0928.small941,CompactPlus0928.nodes941,NodePlus14.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p942,GridPlus.atNode 942,GridPlus.atNode 943,NodePlus14.w46,CompactPlus0928.checked942,CompactPlus0928.small942,CompactPlus0928.nodes942,NodePlus14.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0928.p943,GridPlus.atNode 943,GridPlus.atNode 944,NodePlus14.w47,CompactPlus0928.checked943,CompactPlus0928.small943,CompactPlus0928.nodes943,NodePlus14.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p944,GridPlus.atNode 944,GridPlus.atNode 945,NodePlus14.w48,CompactPlus0944.checked944,CompactPlus0944.small944,CompactPlus0944.nodes944,NodePlus14.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p945,GridPlus.atNode 945,GridPlus.atNode 946,NodePlus14.w49,CompactPlus0944.checked945,CompactPlus0944.small945,CompactPlus0944.nodes945,NodePlus14.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p946,GridPlus.atNode 946,GridPlus.atNode 947,NodePlus14.w50,CompactPlus0944.checked946,CompactPlus0944.small946,CompactPlus0944.nodes946,NodePlus14.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p947,GridPlus.atNode 947,GridPlus.atNode 948,NodePlus14.w51,CompactPlus0944.checked947,CompactPlus0944.small947,CompactPlus0944.nodes947,NodePlus14.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p948,GridPlus.atNode 948,GridPlus.atNode 949,NodePlus14.w52,CompactPlus0944.checked948,CompactPlus0944.small948,CompactPlus0944.nodes948,NodePlus14.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p949,GridPlus.atNode 949,GridPlus.atNode 950,NodePlus14.w53,CompactPlus0944.checked949,CompactPlus0944.small949,CompactPlus0944.nodes949,NodePlus14.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p950,GridPlus.atNode 950,GridPlus.atNode 951,NodePlus14.w54,CompactPlus0944.checked950,CompactPlus0944.small950,CompactPlus0944.nodes950,NodePlus14.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p951,GridPlus.atNode 951,GridPlus.atNode 952,NodePlus14.w55,CompactPlus0944.checked951,CompactPlus0944.small951,CompactPlus0944.nodes951,NodePlus14.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p952,GridPlus.atNode 952,GridPlus.atNode 953,NodePlus14.w56,CompactPlus0944.checked952,CompactPlus0944.small952,CompactPlus0944.nodes952,NodePlus14.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p953,GridPlus.atNode 953,GridPlus.atNode 954,NodePlus14.w57,CompactPlus0944.checked953,CompactPlus0944.small953,CompactPlus0944.nodes953,NodePlus14.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p954,GridPlus.atNode 954,GridPlus.atNode 955,NodePlus14.w58,CompactPlus0944.checked954,CompactPlus0944.small954,CompactPlus0944.nodes954,NodePlus14.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p955,GridPlus.atNode 955,GridPlus.atNode 956,NodePlus14.w59,CompactPlus0944.checked955,CompactPlus0944.small955,CompactPlus0944.nodes955,NodePlus14.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p956,GridPlus.atNode 956,GridPlus.atNode 957,NodePlus14.w60,CompactPlus0944.checked956,CompactPlus0944.small956,CompactPlus0944.nodes956,NodePlus14.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p957,GridPlus.atNode 957,GridPlus.atNode 958,NodePlus14.w61,CompactPlus0944.checked957,CompactPlus0944.small957,CompactPlus0944.nodes957,NodePlus14.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p958,GridPlus.atNode 958,GridPlus.atNode 959,NodePlus14.w62,CompactPlus0944.checked958,CompactPlus0944.small958,CompactPlus0944.nodes958,NodePlus14.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0944.p959,GridPlus.atNode 959,GridPlus.atNode 960,NodePlus14.w63,CompactPlus0944.checked959,CompactPlus0944.small959,CompactPlus0944.nodes959,NodePlus14.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (896+j) ∧
    (atRow j).right=GridPlus.atNode (896+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus14
