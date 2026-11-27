import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1024
import SolitonClassification.Rotating.ResetPackedPlus1040
import SolitonClassification.Rotating.ResetPackedPlus1056
import SolitonClassification.Rotating.ResetPackedPlus1072
namespace SolitonClassification.Rotating.DyadicReset.TilePlus16
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1024,GridPlus.atNode 1024,GridPlus.atNode 1025,NodePlus16.w0,CompactPlus1024.checked1024,CompactPlus1024.small1024,CompactPlus1024.nodes1024,NodePlus16.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1025,GridPlus.atNode 1025,GridPlus.atNode 1026,NodePlus16.w1,CompactPlus1024.checked1025,CompactPlus1024.small1025,CompactPlus1024.nodes1025,NodePlus16.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1026,GridPlus.atNode 1026,GridPlus.atNode 1027,NodePlus16.w2,CompactPlus1024.checked1026,CompactPlus1024.small1026,CompactPlus1024.nodes1026,NodePlus16.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1027,GridPlus.atNode 1027,GridPlus.atNode 1028,NodePlus16.w3,CompactPlus1024.checked1027,CompactPlus1024.small1027,CompactPlus1024.nodes1027,NodePlus16.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1028,GridPlus.atNode 1028,GridPlus.atNode 1029,NodePlus16.w4,CompactPlus1024.checked1028,CompactPlus1024.small1028,CompactPlus1024.nodes1028,NodePlus16.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1029,GridPlus.atNode 1029,GridPlus.atNode 1030,NodePlus16.w5,CompactPlus1024.checked1029,CompactPlus1024.small1029,CompactPlus1024.nodes1029,NodePlus16.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1030,GridPlus.atNode 1030,GridPlus.atNode 1031,NodePlus16.w6,CompactPlus1024.checked1030,CompactPlus1024.small1030,CompactPlus1024.nodes1030,NodePlus16.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1031,GridPlus.atNode 1031,GridPlus.atNode 1032,NodePlus16.w7,CompactPlus1024.checked1031,CompactPlus1024.small1031,CompactPlus1024.nodes1031,NodePlus16.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1032,GridPlus.atNode 1032,GridPlus.atNode 1033,NodePlus16.w8,CompactPlus1024.checked1032,CompactPlus1024.small1032,CompactPlus1024.nodes1032,NodePlus16.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1033,GridPlus.atNode 1033,GridPlus.atNode 1034,NodePlus16.w9,CompactPlus1024.checked1033,CompactPlus1024.small1033,CompactPlus1024.nodes1033,NodePlus16.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1034,GridPlus.atNode 1034,GridPlus.atNode 1035,NodePlus16.w10,CompactPlus1024.checked1034,CompactPlus1024.small1034,CompactPlus1024.nodes1034,NodePlus16.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1035,GridPlus.atNode 1035,GridPlus.atNode 1036,NodePlus16.w11,CompactPlus1024.checked1035,CompactPlus1024.small1035,CompactPlus1024.nodes1035,NodePlus16.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1036,GridPlus.atNode 1036,GridPlus.atNode 1037,NodePlus16.w12,CompactPlus1024.checked1036,CompactPlus1024.small1036,CompactPlus1024.nodes1036,NodePlus16.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1037,GridPlus.atNode 1037,GridPlus.atNode 1038,NodePlus16.w13,CompactPlus1024.checked1037,CompactPlus1024.small1037,CompactPlus1024.nodes1037,NodePlus16.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1038,GridPlus.atNode 1038,GridPlus.atNode 1039,NodePlus16.w14,CompactPlus1024.checked1038,CompactPlus1024.small1038,CompactPlus1024.nodes1038,NodePlus16.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1024.p1039,GridPlus.atNode 1039,GridPlus.atNode 1040,NodePlus16.w15,CompactPlus1024.checked1039,CompactPlus1024.small1039,CompactPlus1024.nodes1039,NodePlus16.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1040,GridPlus.atNode 1040,GridPlus.atNode 1041,NodePlus16.w16,CompactPlus1040.checked1040,CompactPlus1040.small1040,CompactPlus1040.nodes1040,NodePlus16.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1041,GridPlus.atNode 1041,GridPlus.atNode 1042,NodePlus16.w17,CompactPlus1040.checked1041,CompactPlus1040.small1041,CompactPlus1040.nodes1041,NodePlus16.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1042,GridPlus.atNode 1042,GridPlus.atNode 1043,NodePlus16.w18,CompactPlus1040.checked1042,CompactPlus1040.small1042,CompactPlus1040.nodes1042,NodePlus16.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1043,GridPlus.atNode 1043,GridPlus.atNode 1044,NodePlus16.w19,CompactPlus1040.checked1043,CompactPlus1040.small1043,CompactPlus1040.nodes1043,NodePlus16.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1044,GridPlus.atNode 1044,GridPlus.atNode 1045,NodePlus16.w20,CompactPlus1040.checked1044,CompactPlus1040.small1044,CompactPlus1040.nodes1044,NodePlus16.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1045,GridPlus.atNode 1045,GridPlus.atNode 1046,NodePlus16.w21,CompactPlus1040.checked1045,CompactPlus1040.small1045,CompactPlus1040.nodes1045,NodePlus16.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1046,GridPlus.atNode 1046,GridPlus.atNode 1047,NodePlus16.w22,CompactPlus1040.checked1046,CompactPlus1040.small1046,CompactPlus1040.nodes1046,NodePlus16.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1047,GridPlus.atNode 1047,GridPlus.atNode 1048,NodePlus16.w23,CompactPlus1040.checked1047,CompactPlus1040.small1047,CompactPlus1040.nodes1047,NodePlus16.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1048,GridPlus.atNode 1048,GridPlus.atNode 1049,NodePlus16.w24,CompactPlus1040.checked1048,CompactPlus1040.small1048,CompactPlus1040.nodes1048,NodePlus16.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1049,GridPlus.atNode 1049,GridPlus.atNode 1050,NodePlus16.w25,CompactPlus1040.checked1049,CompactPlus1040.small1049,CompactPlus1040.nodes1049,NodePlus16.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1050,GridPlus.atNode 1050,GridPlus.atNode 1051,NodePlus16.w26,CompactPlus1040.checked1050,CompactPlus1040.small1050,CompactPlus1040.nodes1050,NodePlus16.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1051,GridPlus.atNode 1051,GridPlus.atNode 1052,NodePlus16.w27,CompactPlus1040.checked1051,CompactPlus1040.small1051,CompactPlus1040.nodes1051,NodePlus16.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1052,GridPlus.atNode 1052,GridPlus.atNode 1053,NodePlus16.w28,CompactPlus1040.checked1052,CompactPlus1040.small1052,CompactPlus1040.nodes1052,NodePlus16.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1053,GridPlus.atNode 1053,GridPlus.atNode 1054,NodePlus16.w29,CompactPlus1040.checked1053,CompactPlus1040.small1053,CompactPlus1040.nodes1053,NodePlus16.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1054,GridPlus.atNode 1054,GridPlus.atNode 1055,NodePlus16.w30,CompactPlus1040.checked1054,CompactPlus1040.small1054,CompactPlus1040.nodes1054,NodePlus16.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1040.p1055,GridPlus.atNode 1055,GridPlus.atNode 1056,NodePlus16.w31,CompactPlus1040.checked1055,CompactPlus1040.small1055,CompactPlus1040.nodes1055,NodePlus16.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1056,GridPlus.atNode 1056,GridPlus.atNode 1057,NodePlus16.w32,CompactPlus1056.checked1056,CompactPlus1056.small1056,CompactPlus1056.nodes1056,NodePlus16.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1057,GridPlus.atNode 1057,GridPlus.atNode 1058,NodePlus16.w33,CompactPlus1056.checked1057,CompactPlus1056.small1057,CompactPlus1056.nodes1057,NodePlus16.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1058,GridPlus.atNode 1058,GridPlus.atNode 1059,NodePlus16.w34,CompactPlus1056.checked1058,CompactPlus1056.small1058,CompactPlus1056.nodes1058,NodePlus16.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1059,GridPlus.atNode 1059,GridPlus.atNode 1060,NodePlus16.w35,CompactPlus1056.checked1059,CompactPlus1056.small1059,CompactPlus1056.nodes1059,NodePlus16.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1060,GridPlus.atNode 1060,GridPlus.atNode 1061,NodePlus16.w36,CompactPlus1056.checked1060,CompactPlus1056.small1060,CompactPlus1056.nodes1060,NodePlus16.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1061,GridPlus.atNode 1061,GridPlus.atNode 1062,NodePlus16.w37,CompactPlus1056.checked1061,CompactPlus1056.small1061,CompactPlus1056.nodes1061,NodePlus16.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1062,GridPlus.atNode 1062,GridPlus.atNode 1063,NodePlus16.w38,CompactPlus1056.checked1062,CompactPlus1056.small1062,CompactPlus1056.nodes1062,NodePlus16.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1063,GridPlus.atNode 1063,GridPlus.atNode 1064,NodePlus16.w39,CompactPlus1056.checked1063,CompactPlus1056.small1063,CompactPlus1056.nodes1063,NodePlus16.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1064,GridPlus.atNode 1064,GridPlus.atNode 1065,NodePlus16.w40,CompactPlus1056.checked1064,CompactPlus1056.small1064,CompactPlus1056.nodes1064,NodePlus16.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1065,GridPlus.atNode 1065,GridPlus.atNode 1066,NodePlus16.w41,CompactPlus1056.checked1065,CompactPlus1056.small1065,CompactPlus1056.nodes1065,NodePlus16.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1066,GridPlus.atNode 1066,GridPlus.atNode 1067,NodePlus16.w42,CompactPlus1056.checked1066,CompactPlus1056.small1066,CompactPlus1056.nodes1066,NodePlus16.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1067,GridPlus.atNode 1067,GridPlus.atNode 1068,NodePlus16.w43,CompactPlus1056.checked1067,CompactPlus1056.small1067,CompactPlus1056.nodes1067,NodePlus16.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1068,GridPlus.atNode 1068,GridPlus.atNode 1069,NodePlus16.w44,CompactPlus1056.checked1068,CompactPlus1056.small1068,CompactPlus1056.nodes1068,NodePlus16.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1069,GridPlus.atNode 1069,GridPlus.atNode 1070,NodePlus16.w45,CompactPlus1056.checked1069,CompactPlus1056.small1069,CompactPlus1056.nodes1069,NodePlus16.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1070,GridPlus.atNode 1070,GridPlus.atNode 1071,NodePlus16.w46,CompactPlus1056.checked1070,CompactPlus1056.small1070,CompactPlus1056.nodes1070,NodePlus16.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1056.p1071,GridPlus.atNode 1071,GridPlus.atNode 1072,NodePlus16.w47,CompactPlus1056.checked1071,CompactPlus1056.small1071,CompactPlus1056.nodes1071,NodePlus16.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1072,GridPlus.atNode 1072,GridPlus.atNode 1073,NodePlus16.w48,CompactPlus1072.checked1072,CompactPlus1072.small1072,CompactPlus1072.nodes1072,NodePlus16.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1073,GridPlus.atNode 1073,GridPlus.atNode 1074,NodePlus16.w49,CompactPlus1072.checked1073,CompactPlus1072.small1073,CompactPlus1072.nodes1073,NodePlus16.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1074,GridPlus.atNode 1074,GridPlus.atNode 1075,NodePlus16.w50,CompactPlus1072.checked1074,CompactPlus1072.small1074,CompactPlus1072.nodes1074,NodePlus16.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1075,GridPlus.atNode 1075,GridPlus.atNode 1076,NodePlus16.w51,CompactPlus1072.checked1075,CompactPlus1072.small1075,CompactPlus1072.nodes1075,NodePlus16.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1076,GridPlus.atNode 1076,GridPlus.atNode 1077,NodePlus16.w52,CompactPlus1072.checked1076,CompactPlus1072.small1076,CompactPlus1072.nodes1076,NodePlus16.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1077,GridPlus.atNode 1077,GridPlus.atNode 1078,NodePlus16.w53,CompactPlus1072.checked1077,CompactPlus1072.small1077,CompactPlus1072.nodes1077,NodePlus16.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1078,GridPlus.atNode 1078,GridPlus.atNode 1079,NodePlus16.w54,CompactPlus1072.checked1078,CompactPlus1072.small1078,CompactPlus1072.nodes1078,NodePlus16.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1079,GridPlus.atNode 1079,GridPlus.atNode 1080,NodePlus16.w55,CompactPlus1072.checked1079,CompactPlus1072.small1079,CompactPlus1072.nodes1079,NodePlus16.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1080,GridPlus.atNode 1080,GridPlus.atNode 1081,NodePlus16.w56,CompactPlus1072.checked1080,CompactPlus1072.small1080,CompactPlus1072.nodes1080,NodePlus16.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1081,GridPlus.atNode 1081,GridPlus.atNode 1082,NodePlus16.w57,CompactPlus1072.checked1081,CompactPlus1072.small1081,CompactPlus1072.nodes1081,NodePlus16.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1082,GridPlus.atNode 1082,GridPlus.atNode 1083,NodePlus16.w58,CompactPlus1072.checked1082,CompactPlus1072.small1082,CompactPlus1072.nodes1082,NodePlus16.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1083,GridPlus.atNode 1083,GridPlus.atNode 1084,NodePlus16.w59,CompactPlus1072.checked1083,CompactPlus1072.small1083,CompactPlus1072.nodes1083,NodePlus16.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1084,GridPlus.atNode 1084,GridPlus.atNode 1085,NodePlus16.w60,CompactPlus1072.checked1084,CompactPlus1072.small1084,CompactPlus1072.nodes1084,NodePlus16.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1085,GridPlus.atNode 1085,GridPlus.atNode 1086,NodePlus16.w61,CompactPlus1072.checked1085,CompactPlus1072.small1085,CompactPlus1072.nodes1085,NodePlus16.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1086,GridPlus.atNode 1086,GridPlus.atNode 1087,NodePlus16.w62,CompactPlus1072.checked1086,CompactPlus1072.small1086,CompactPlus1072.nodes1086,NodePlus16.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1072.p1087,GridPlus.atNode 1087,GridPlus.atNode 1088,NodePlus16.w63,CompactPlus1072.checked1087,CompactPlus1072.small1087,CompactPlus1072.nodes1087,NodePlus16.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1024+j) ∧
    (atRow j).right=GridPlus.atNode (1024+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus16
