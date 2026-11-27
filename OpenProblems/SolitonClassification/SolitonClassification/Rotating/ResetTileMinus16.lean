import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1024
import SolitonClassification.Rotating.ResetPackedMinus1040
import SolitonClassification.Rotating.ResetPackedMinus1056
import SolitonClassification.Rotating.ResetPackedMinus1072
namespace SolitonClassification.Rotating.DyadicReset.TileMinus16
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1024,GridMinus.atNode 1024,GridMinus.atNode 1025,NodeMinus16.w0,CompactMinus1024.checked1024,CompactMinus1024.small1024,CompactMinus1024.nodes1024,NodeMinus16.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1025,GridMinus.atNode 1025,GridMinus.atNode 1026,NodeMinus16.w1,CompactMinus1024.checked1025,CompactMinus1024.small1025,CompactMinus1024.nodes1025,NodeMinus16.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1026,GridMinus.atNode 1026,GridMinus.atNode 1027,NodeMinus16.w2,CompactMinus1024.checked1026,CompactMinus1024.small1026,CompactMinus1024.nodes1026,NodeMinus16.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1027,GridMinus.atNode 1027,GridMinus.atNode 1028,NodeMinus16.w3,CompactMinus1024.checked1027,CompactMinus1024.small1027,CompactMinus1024.nodes1027,NodeMinus16.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1028,GridMinus.atNode 1028,GridMinus.atNode 1029,NodeMinus16.w4,CompactMinus1024.checked1028,CompactMinus1024.small1028,CompactMinus1024.nodes1028,NodeMinus16.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1029,GridMinus.atNode 1029,GridMinus.atNode 1030,NodeMinus16.w5,CompactMinus1024.checked1029,CompactMinus1024.small1029,CompactMinus1024.nodes1029,NodeMinus16.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1030,GridMinus.atNode 1030,GridMinus.atNode 1031,NodeMinus16.w6,CompactMinus1024.checked1030,CompactMinus1024.small1030,CompactMinus1024.nodes1030,NodeMinus16.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1031,GridMinus.atNode 1031,GridMinus.atNode 1032,NodeMinus16.w7,CompactMinus1024.checked1031,CompactMinus1024.small1031,CompactMinus1024.nodes1031,NodeMinus16.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1032,GridMinus.atNode 1032,GridMinus.atNode 1033,NodeMinus16.w8,CompactMinus1024.checked1032,CompactMinus1024.small1032,CompactMinus1024.nodes1032,NodeMinus16.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1033,GridMinus.atNode 1033,GridMinus.atNode 1034,NodeMinus16.w9,CompactMinus1024.checked1033,CompactMinus1024.small1033,CompactMinus1024.nodes1033,NodeMinus16.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1034,GridMinus.atNode 1034,GridMinus.atNode 1035,NodeMinus16.w10,CompactMinus1024.checked1034,CompactMinus1024.small1034,CompactMinus1024.nodes1034,NodeMinus16.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1035,GridMinus.atNode 1035,GridMinus.atNode 1036,NodeMinus16.w11,CompactMinus1024.checked1035,CompactMinus1024.small1035,CompactMinus1024.nodes1035,NodeMinus16.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1036,GridMinus.atNode 1036,GridMinus.atNode 1037,NodeMinus16.w12,CompactMinus1024.checked1036,CompactMinus1024.small1036,CompactMinus1024.nodes1036,NodeMinus16.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1037,GridMinus.atNode 1037,GridMinus.atNode 1038,NodeMinus16.w13,CompactMinus1024.checked1037,CompactMinus1024.small1037,CompactMinus1024.nodes1037,NodeMinus16.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1038,GridMinus.atNode 1038,GridMinus.atNode 1039,NodeMinus16.w14,CompactMinus1024.checked1038,CompactMinus1024.small1038,CompactMinus1024.nodes1038,NodeMinus16.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1024.p1039,GridMinus.atNode 1039,GridMinus.atNode 1040,NodeMinus16.w15,CompactMinus1024.checked1039,CompactMinus1024.small1039,CompactMinus1024.nodes1039,NodeMinus16.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1040,GridMinus.atNode 1040,GridMinus.atNode 1041,NodeMinus16.w16,CompactMinus1040.checked1040,CompactMinus1040.small1040,CompactMinus1040.nodes1040,NodeMinus16.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1041,GridMinus.atNode 1041,GridMinus.atNode 1042,NodeMinus16.w17,CompactMinus1040.checked1041,CompactMinus1040.small1041,CompactMinus1040.nodes1041,NodeMinus16.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1042,GridMinus.atNode 1042,GridMinus.atNode 1043,NodeMinus16.w18,CompactMinus1040.checked1042,CompactMinus1040.small1042,CompactMinus1040.nodes1042,NodeMinus16.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1043,GridMinus.atNode 1043,GridMinus.atNode 1044,NodeMinus16.w19,CompactMinus1040.checked1043,CompactMinus1040.small1043,CompactMinus1040.nodes1043,NodeMinus16.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1044,GridMinus.atNode 1044,GridMinus.atNode 1045,NodeMinus16.w20,CompactMinus1040.checked1044,CompactMinus1040.small1044,CompactMinus1040.nodes1044,NodeMinus16.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1045,GridMinus.atNode 1045,GridMinus.atNode 1046,NodeMinus16.w21,CompactMinus1040.checked1045,CompactMinus1040.small1045,CompactMinus1040.nodes1045,NodeMinus16.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1046,GridMinus.atNode 1046,GridMinus.atNode 1047,NodeMinus16.w22,CompactMinus1040.checked1046,CompactMinus1040.small1046,CompactMinus1040.nodes1046,NodeMinus16.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1047,GridMinus.atNode 1047,GridMinus.atNode 1048,NodeMinus16.w23,CompactMinus1040.checked1047,CompactMinus1040.small1047,CompactMinus1040.nodes1047,NodeMinus16.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1048,GridMinus.atNode 1048,GridMinus.atNode 1049,NodeMinus16.w24,CompactMinus1040.checked1048,CompactMinus1040.small1048,CompactMinus1040.nodes1048,NodeMinus16.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1049,GridMinus.atNode 1049,GridMinus.atNode 1050,NodeMinus16.w25,CompactMinus1040.checked1049,CompactMinus1040.small1049,CompactMinus1040.nodes1049,NodeMinus16.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1050,GridMinus.atNode 1050,GridMinus.atNode 1051,NodeMinus16.w26,CompactMinus1040.checked1050,CompactMinus1040.small1050,CompactMinus1040.nodes1050,NodeMinus16.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1051,GridMinus.atNode 1051,GridMinus.atNode 1052,NodeMinus16.w27,CompactMinus1040.checked1051,CompactMinus1040.small1051,CompactMinus1040.nodes1051,NodeMinus16.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1052,GridMinus.atNode 1052,GridMinus.atNode 1053,NodeMinus16.w28,CompactMinus1040.checked1052,CompactMinus1040.small1052,CompactMinus1040.nodes1052,NodeMinus16.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1053,GridMinus.atNode 1053,GridMinus.atNode 1054,NodeMinus16.w29,CompactMinus1040.checked1053,CompactMinus1040.small1053,CompactMinus1040.nodes1053,NodeMinus16.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1054,GridMinus.atNode 1054,GridMinus.atNode 1055,NodeMinus16.w30,CompactMinus1040.checked1054,CompactMinus1040.small1054,CompactMinus1040.nodes1054,NodeMinus16.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1040.p1055,GridMinus.atNode 1055,GridMinus.atNode 1056,NodeMinus16.w31,CompactMinus1040.checked1055,CompactMinus1040.small1055,CompactMinus1040.nodes1055,NodeMinus16.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1056,GridMinus.atNode 1056,GridMinus.atNode 1057,NodeMinus16.w32,CompactMinus1056.checked1056,CompactMinus1056.small1056,CompactMinus1056.nodes1056,NodeMinus16.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1057,GridMinus.atNode 1057,GridMinus.atNode 1058,NodeMinus16.w33,CompactMinus1056.checked1057,CompactMinus1056.small1057,CompactMinus1056.nodes1057,NodeMinus16.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1058,GridMinus.atNode 1058,GridMinus.atNode 1059,NodeMinus16.w34,CompactMinus1056.checked1058,CompactMinus1056.small1058,CompactMinus1056.nodes1058,NodeMinus16.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1059,GridMinus.atNode 1059,GridMinus.atNode 1060,NodeMinus16.w35,CompactMinus1056.checked1059,CompactMinus1056.small1059,CompactMinus1056.nodes1059,NodeMinus16.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1060,GridMinus.atNode 1060,GridMinus.atNode 1061,NodeMinus16.w36,CompactMinus1056.checked1060,CompactMinus1056.small1060,CompactMinus1056.nodes1060,NodeMinus16.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1061,GridMinus.atNode 1061,GridMinus.atNode 1062,NodeMinus16.w37,CompactMinus1056.checked1061,CompactMinus1056.small1061,CompactMinus1056.nodes1061,NodeMinus16.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1062,GridMinus.atNode 1062,GridMinus.atNode 1063,NodeMinus16.w38,CompactMinus1056.checked1062,CompactMinus1056.small1062,CompactMinus1056.nodes1062,NodeMinus16.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1063,GridMinus.atNode 1063,GridMinus.atNode 1064,NodeMinus16.w39,CompactMinus1056.checked1063,CompactMinus1056.small1063,CompactMinus1056.nodes1063,NodeMinus16.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1064,GridMinus.atNode 1064,GridMinus.atNode 1065,NodeMinus16.w40,CompactMinus1056.checked1064,CompactMinus1056.small1064,CompactMinus1056.nodes1064,NodeMinus16.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1065,GridMinus.atNode 1065,GridMinus.atNode 1066,NodeMinus16.w41,CompactMinus1056.checked1065,CompactMinus1056.small1065,CompactMinus1056.nodes1065,NodeMinus16.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1066,GridMinus.atNode 1066,GridMinus.atNode 1067,NodeMinus16.w42,CompactMinus1056.checked1066,CompactMinus1056.small1066,CompactMinus1056.nodes1066,NodeMinus16.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1067,GridMinus.atNode 1067,GridMinus.atNode 1068,NodeMinus16.w43,CompactMinus1056.checked1067,CompactMinus1056.small1067,CompactMinus1056.nodes1067,NodeMinus16.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1068,GridMinus.atNode 1068,GridMinus.atNode 1069,NodeMinus16.w44,CompactMinus1056.checked1068,CompactMinus1056.small1068,CompactMinus1056.nodes1068,NodeMinus16.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1069,GridMinus.atNode 1069,GridMinus.atNode 1070,NodeMinus16.w45,CompactMinus1056.checked1069,CompactMinus1056.small1069,CompactMinus1056.nodes1069,NodeMinus16.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1070,GridMinus.atNode 1070,GridMinus.atNode 1071,NodeMinus16.w46,CompactMinus1056.checked1070,CompactMinus1056.small1070,CompactMinus1056.nodes1070,NodeMinus16.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1056.p1071,GridMinus.atNode 1071,GridMinus.atNode 1072,NodeMinus16.w47,CompactMinus1056.checked1071,CompactMinus1056.small1071,CompactMinus1056.nodes1071,NodeMinus16.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1072,GridMinus.atNode 1072,GridMinus.atNode 1073,NodeMinus16.w48,CompactMinus1072.checked1072,CompactMinus1072.small1072,CompactMinus1072.nodes1072,NodeMinus16.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1073,GridMinus.atNode 1073,GridMinus.atNode 1074,NodeMinus16.w49,CompactMinus1072.checked1073,CompactMinus1072.small1073,CompactMinus1072.nodes1073,NodeMinus16.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1074,GridMinus.atNode 1074,GridMinus.atNode 1075,NodeMinus16.w50,CompactMinus1072.checked1074,CompactMinus1072.small1074,CompactMinus1072.nodes1074,NodeMinus16.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1075,GridMinus.atNode 1075,GridMinus.atNode 1076,NodeMinus16.w51,CompactMinus1072.checked1075,CompactMinus1072.small1075,CompactMinus1072.nodes1075,NodeMinus16.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1076,GridMinus.atNode 1076,GridMinus.atNode 1077,NodeMinus16.w52,CompactMinus1072.checked1076,CompactMinus1072.small1076,CompactMinus1072.nodes1076,NodeMinus16.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1077,GridMinus.atNode 1077,GridMinus.atNode 1078,NodeMinus16.w53,CompactMinus1072.checked1077,CompactMinus1072.small1077,CompactMinus1072.nodes1077,NodeMinus16.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1078,GridMinus.atNode 1078,GridMinus.atNode 1079,NodeMinus16.w54,CompactMinus1072.checked1078,CompactMinus1072.small1078,CompactMinus1072.nodes1078,NodeMinus16.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1079,GridMinus.atNode 1079,GridMinus.atNode 1080,NodeMinus16.w55,CompactMinus1072.checked1079,CompactMinus1072.small1079,CompactMinus1072.nodes1079,NodeMinus16.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1080,GridMinus.atNode 1080,GridMinus.atNode 1081,NodeMinus16.w56,CompactMinus1072.checked1080,CompactMinus1072.small1080,CompactMinus1072.nodes1080,NodeMinus16.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1081,GridMinus.atNode 1081,GridMinus.atNode 1082,NodeMinus16.w57,CompactMinus1072.checked1081,CompactMinus1072.small1081,CompactMinus1072.nodes1081,NodeMinus16.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1082,GridMinus.atNode 1082,GridMinus.atNode 1083,NodeMinus16.w58,CompactMinus1072.checked1082,CompactMinus1072.small1082,CompactMinus1072.nodes1082,NodeMinus16.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1083,GridMinus.atNode 1083,GridMinus.atNode 1084,NodeMinus16.w59,CompactMinus1072.checked1083,CompactMinus1072.small1083,CompactMinus1072.nodes1083,NodeMinus16.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1084,GridMinus.atNode 1084,GridMinus.atNode 1085,NodeMinus16.w60,CompactMinus1072.checked1084,CompactMinus1072.small1084,CompactMinus1072.nodes1084,NodeMinus16.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1085,GridMinus.atNode 1085,GridMinus.atNode 1086,NodeMinus16.w61,CompactMinus1072.checked1085,CompactMinus1072.small1085,CompactMinus1072.nodes1085,NodeMinus16.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1086,GridMinus.atNode 1086,GridMinus.atNode 1087,NodeMinus16.w62,CompactMinus1072.checked1086,CompactMinus1072.small1086,CompactMinus1072.nodes1086,NodeMinus16.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1072.p1087,GridMinus.atNode 1087,GridMinus.atNode 1088,NodeMinus16.w63,CompactMinus1072.checked1087,CompactMinus1072.small1087,CompactMinus1072.nodes1087,NodeMinus16.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1024+j) ∧
    (atRow j).right=GridMinus.atNode (1024+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus16
