import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0128
import SolitonClassification.Rotating.ResetPackedPlus0144
import SolitonClassification.Rotating.ResetPackedPlus0160
import SolitonClassification.Rotating.ResetPackedPlus0176
namespace SolitonClassification.Rotating.DyadicReset.TilePlus02
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p128,GridPlus.atNode 128,GridPlus.atNode 129,NodePlus02.w0,CompactPlus0128.checked128,CompactPlus0128.small128,CompactPlus0128.nodes128,NodePlus02.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p129,GridPlus.atNode 129,GridPlus.atNode 130,NodePlus02.w1,CompactPlus0128.checked129,CompactPlus0128.small129,CompactPlus0128.nodes129,NodePlus02.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p130,GridPlus.atNode 130,GridPlus.atNode 131,NodePlus02.w2,CompactPlus0128.checked130,CompactPlus0128.small130,CompactPlus0128.nodes130,NodePlus02.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p131,GridPlus.atNode 131,GridPlus.atNode 132,NodePlus02.w3,CompactPlus0128.checked131,CompactPlus0128.small131,CompactPlus0128.nodes131,NodePlus02.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p132,GridPlus.atNode 132,GridPlus.atNode 133,NodePlus02.w4,CompactPlus0128.checked132,CompactPlus0128.small132,CompactPlus0128.nodes132,NodePlus02.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p133,GridPlus.atNode 133,GridPlus.atNode 134,NodePlus02.w5,CompactPlus0128.checked133,CompactPlus0128.small133,CompactPlus0128.nodes133,NodePlus02.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p134,GridPlus.atNode 134,GridPlus.atNode 135,NodePlus02.w6,CompactPlus0128.checked134,CompactPlus0128.small134,CompactPlus0128.nodes134,NodePlus02.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p135,GridPlus.atNode 135,GridPlus.atNode 136,NodePlus02.w7,CompactPlus0128.checked135,CompactPlus0128.small135,CompactPlus0128.nodes135,NodePlus02.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p136,GridPlus.atNode 136,GridPlus.atNode 137,NodePlus02.w8,CompactPlus0128.checked136,CompactPlus0128.small136,CompactPlus0128.nodes136,NodePlus02.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p137,GridPlus.atNode 137,GridPlus.atNode 138,NodePlus02.w9,CompactPlus0128.checked137,CompactPlus0128.small137,CompactPlus0128.nodes137,NodePlus02.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p138,GridPlus.atNode 138,GridPlus.atNode 139,NodePlus02.w10,CompactPlus0128.checked138,CompactPlus0128.small138,CompactPlus0128.nodes138,NodePlus02.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p139,GridPlus.atNode 139,GridPlus.atNode 140,NodePlus02.w11,CompactPlus0128.checked139,CompactPlus0128.small139,CompactPlus0128.nodes139,NodePlus02.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p140,GridPlus.atNode 140,GridPlus.atNode 141,NodePlus02.w12,CompactPlus0128.checked140,CompactPlus0128.small140,CompactPlus0128.nodes140,NodePlus02.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p141,GridPlus.atNode 141,GridPlus.atNode 142,NodePlus02.w13,CompactPlus0128.checked141,CompactPlus0128.small141,CompactPlus0128.nodes141,NodePlus02.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p142,GridPlus.atNode 142,GridPlus.atNode 143,NodePlus02.w14,CompactPlus0128.checked142,CompactPlus0128.small142,CompactPlus0128.nodes142,NodePlus02.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0128.p143,GridPlus.atNode 143,GridPlus.atNode 144,NodePlus02.w15,CompactPlus0128.checked143,CompactPlus0128.small143,CompactPlus0128.nodes143,NodePlus02.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p144,GridPlus.atNode 144,GridPlus.atNode 145,NodePlus02.w16,CompactPlus0144.checked144,CompactPlus0144.small144,CompactPlus0144.nodes144,NodePlus02.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p145,GridPlus.atNode 145,GridPlus.atNode 146,NodePlus02.w17,CompactPlus0144.checked145,CompactPlus0144.small145,CompactPlus0144.nodes145,NodePlus02.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p146,GridPlus.atNode 146,GridPlus.atNode 147,NodePlus02.w18,CompactPlus0144.checked146,CompactPlus0144.small146,CompactPlus0144.nodes146,NodePlus02.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p147,GridPlus.atNode 147,GridPlus.atNode 148,NodePlus02.w19,CompactPlus0144.checked147,CompactPlus0144.small147,CompactPlus0144.nodes147,NodePlus02.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p148,GridPlus.atNode 148,GridPlus.atNode 149,NodePlus02.w20,CompactPlus0144.checked148,CompactPlus0144.small148,CompactPlus0144.nodes148,NodePlus02.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p149,GridPlus.atNode 149,GridPlus.atNode 150,NodePlus02.w21,CompactPlus0144.checked149,CompactPlus0144.small149,CompactPlus0144.nodes149,NodePlus02.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p150,GridPlus.atNode 150,GridPlus.atNode 151,NodePlus02.w22,CompactPlus0144.checked150,CompactPlus0144.small150,CompactPlus0144.nodes150,NodePlus02.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p151,GridPlus.atNode 151,GridPlus.atNode 152,NodePlus02.w23,CompactPlus0144.checked151,CompactPlus0144.small151,CompactPlus0144.nodes151,NodePlus02.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p152,GridPlus.atNode 152,GridPlus.atNode 153,NodePlus02.w24,CompactPlus0144.checked152,CompactPlus0144.small152,CompactPlus0144.nodes152,NodePlus02.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p153,GridPlus.atNode 153,GridPlus.atNode 154,NodePlus02.w25,CompactPlus0144.checked153,CompactPlus0144.small153,CompactPlus0144.nodes153,NodePlus02.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p154,GridPlus.atNode 154,GridPlus.atNode 155,NodePlus02.w26,CompactPlus0144.checked154,CompactPlus0144.small154,CompactPlus0144.nodes154,NodePlus02.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p155,GridPlus.atNode 155,GridPlus.atNode 156,NodePlus02.w27,CompactPlus0144.checked155,CompactPlus0144.small155,CompactPlus0144.nodes155,NodePlus02.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p156,GridPlus.atNode 156,GridPlus.atNode 157,NodePlus02.w28,CompactPlus0144.checked156,CompactPlus0144.small156,CompactPlus0144.nodes156,NodePlus02.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p157,GridPlus.atNode 157,GridPlus.atNode 158,NodePlus02.w29,CompactPlus0144.checked157,CompactPlus0144.small157,CompactPlus0144.nodes157,NodePlus02.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p158,GridPlus.atNode 158,GridPlus.atNode 159,NodePlus02.w30,CompactPlus0144.checked158,CompactPlus0144.small158,CompactPlus0144.nodes158,NodePlus02.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0144.p159,GridPlus.atNode 159,GridPlus.atNode 160,NodePlus02.w31,CompactPlus0144.checked159,CompactPlus0144.small159,CompactPlus0144.nodes159,NodePlus02.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p160,GridPlus.atNode 160,GridPlus.atNode 161,NodePlus02.w32,CompactPlus0160.checked160,CompactPlus0160.small160,CompactPlus0160.nodes160,NodePlus02.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p161,GridPlus.atNode 161,GridPlus.atNode 162,NodePlus02.w33,CompactPlus0160.checked161,CompactPlus0160.small161,CompactPlus0160.nodes161,NodePlus02.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p162,GridPlus.atNode 162,GridPlus.atNode 163,NodePlus02.w34,CompactPlus0160.checked162,CompactPlus0160.small162,CompactPlus0160.nodes162,NodePlus02.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p163,GridPlus.atNode 163,GridPlus.atNode 164,NodePlus02.w35,CompactPlus0160.checked163,CompactPlus0160.small163,CompactPlus0160.nodes163,NodePlus02.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p164,GridPlus.atNode 164,GridPlus.atNode 165,NodePlus02.w36,CompactPlus0160.checked164,CompactPlus0160.small164,CompactPlus0160.nodes164,NodePlus02.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p165,GridPlus.atNode 165,GridPlus.atNode 166,NodePlus02.w37,CompactPlus0160.checked165,CompactPlus0160.small165,CompactPlus0160.nodes165,NodePlus02.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p166,GridPlus.atNode 166,GridPlus.atNode 167,NodePlus02.w38,CompactPlus0160.checked166,CompactPlus0160.small166,CompactPlus0160.nodes166,NodePlus02.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p167,GridPlus.atNode 167,GridPlus.atNode 168,NodePlus02.w39,CompactPlus0160.checked167,CompactPlus0160.small167,CompactPlus0160.nodes167,NodePlus02.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p168,GridPlus.atNode 168,GridPlus.atNode 169,NodePlus02.w40,CompactPlus0160.checked168,CompactPlus0160.small168,CompactPlus0160.nodes168,NodePlus02.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p169,GridPlus.atNode 169,GridPlus.atNode 170,NodePlus02.w41,CompactPlus0160.checked169,CompactPlus0160.small169,CompactPlus0160.nodes169,NodePlus02.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p170,GridPlus.atNode 170,GridPlus.atNode 171,NodePlus02.w42,CompactPlus0160.checked170,CompactPlus0160.small170,CompactPlus0160.nodes170,NodePlus02.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p171,GridPlus.atNode 171,GridPlus.atNode 172,NodePlus02.w43,CompactPlus0160.checked171,CompactPlus0160.small171,CompactPlus0160.nodes171,NodePlus02.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p172,GridPlus.atNode 172,GridPlus.atNode 173,NodePlus02.w44,CompactPlus0160.checked172,CompactPlus0160.small172,CompactPlus0160.nodes172,NodePlus02.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p173,GridPlus.atNode 173,GridPlus.atNode 174,NodePlus02.w45,CompactPlus0160.checked173,CompactPlus0160.small173,CompactPlus0160.nodes173,NodePlus02.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p174,GridPlus.atNode 174,GridPlus.atNode 175,NodePlus02.w46,CompactPlus0160.checked174,CompactPlus0160.small174,CompactPlus0160.nodes174,NodePlus02.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0160.p175,GridPlus.atNode 175,GridPlus.atNode 176,NodePlus02.w47,CompactPlus0160.checked175,CompactPlus0160.small175,CompactPlus0160.nodes175,NodePlus02.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p176,GridPlus.atNode 176,GridPlus.atNode 177,NodePlus02.w48,CompactPlus0176.checked176,CompactPlus0176.small176,CompactPlus0176.nodes176,NodePlus02.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p177,GridPlus.atNode 177,GridPlus.atNode 178,NodePlus02.w49,CompactPlus0176.checked177,CompactPlus0176.small177,CompactPlus0176.nodes177,NodePlus02.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p178,GridPlus.atNode 178,GridPlus.atNode 179,NodePlus02.w50,CompactPlus0176.checked178,CompactPlus0176.small178,CompactPlus0176.nodes178,NodePlus02.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p179,GridPlus.atNode 179,GridPlus.atNode 180,NodePlus02.w51,CompactPlus0176.checked179,CompactPlus0176.small179,CompactPlus0176.nodes179,NodePlus02.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p180,GridPlus.atNode 180,GridPlus.atNode 181,NodePlus02.w52,CompactPlus0176.checked180,CompactPlus0176.small180,CompactPlus0176.nodes180,NodePlus02.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p181,GridPlus.atNode 181,GridPlus.atNode 182,NodePlus02.w53,CompactPlus0176.checked181,CompactPlus0176.small181,CompactPlus0176.nodes181,NodePlus02.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p182,GridPlus.atNode 182,GridPlus.atNode 183,NodePlus02.w54,CompactPlus0176.checked182,CompactPlus0176.small182,CompactPlus0176.nodes182,NodePlus02.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p183,GridPlus.atNode 183,GridPlus.atNode 184,NodePlus02.w55,CompactPlus0176.checked183,CompactPlus0176.small183,CompactPlus0176.nodes183,NodePlus02.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p184,GridPlus.atNode 184,GridPlus.atNode 185,NodePlus02.w56,CompactPlus0176.checked184,CompactPlus0176.small184,CompactPlus0176.nodes184,NodePlus02.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p185,GridPlus.atNode 185,GridPlus.atNode 186,NodePlus02.w57,CompactPlus0176.checked185,CompactPlus0176.small185,CompactPlus0176.nodes185,NodePlus02.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p186,GridPlus.atNode 186,GridPlus.atNode 187,NodePlus02.w58,CompactPlus0176.checked186,CompactPlus0176.small186,CompactPlus0176.nodes186,NodePlus02.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p187,GridPlus.atNode 187,GridPlus.atNode 188,NodePlus02.w59,CompactPlus0176.checked187,CompactPlus0176.small187,CompactPlus0176.nodes187,NodePlus02.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p188,GridPlus.atNode 188,GridPlus.atNode 189,NodePlus02.w60,CompactPlus0176.checked188,CompactPlus0176.small188,CompactPlus0176.nodes188,NodePlus02.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p189,GridPlus.atNode 189,GridPlus.atNode 190,NodePlus02.w61,CompactPlus0176.checked189,CompactPlus0176.small189,CompactPlus0176.nodes189,NodePlus02.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p190,GridPlus.atNode 190,GridPlus.atNode 191,NodePlus02.w62,CompactPlus0176.checked190,CompactPlus0176.small190,CompactPlus0176.nodes190,NodePlus02.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0176.p191,GridPlus.atNode 191,GridPlus.atNode 192,NodePlus02.w63,CompactPlus0176.checked191,CompactPlus0176.small191,CompactPlus0176.nodes191,NodePlus02.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (128+j) ∧
    (atRow j).right=GridPlus.atNode (128+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus02
