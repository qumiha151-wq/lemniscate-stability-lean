import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0128
import SolitonClassification.Rotating.ResetPackedMinus0144
import SolitonClassification.Rotating.ResetPackedMinus0160
import SolitonClassification.Rotating.ResetPackedMinus0176
namespace SolitonClassification.Rotating.DyadicReset.TileMinus02
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p128,GridMinus.atNode 128,GridMinus.atNode 129,NodeMinus02.w0,CompactMinus0128.checked128,CompactMinus0128.small128,CompactMinus0128.nodes128,NodeMinus02.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p129,GridMinus.atNode 129,GridMinus.atNode 130,NodeMinus02.w1,CompactMinus0128.checked129,CompactMinus0128.small129,CompactMinus0128.nodes129,NodeMinus02.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p130,GridMinus.atNode 130,GridMinus.atNode 131,NodeMinus02.w2,CompactMinus0128.checked130,CompactMinus0128.small130,CompactMinus0128.nodes130,NodeMinus02.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p131,GridMinus.atNode 131,GridMinus.atNode 132,NodeMinus02.w3,CompactMinus0128.checked131,CompactMinus0128.small131,CompactMinus0128.nodes131,NodeMinus02.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p132,GridMinus.atNode 132,GridMinus.atNode 133,NodeMinus02.w4,CompactMinus0128.checked132,CompactMinus0128.small132,CompactMinus0128.nodes132,NodeMinus02.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p133,GridMinus.atNode 133,GridMinus.atNode 134,NodeMinus02.w5,CompactMinus0128.checked133,CompactMinus0128.small133,CompactMinus0128.nodes133,NodeMinus02.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p134,GridMinus.atNode 134,GridMinus.atNode 135,NodeMinus02.w6,CompactMinus0128.checked134,CompactMinus0128.small134,CompactMinus0128.nodes134,NodeMinus02.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p135,GridMinus.atNode 135,GridMinus.atNode 136,NodeMinus02.w7,CompactMinus0128.checked135,CompactMinus0128.small135,CompactMinus0128.nodes135,NodeMinus02.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p136,GridMinus.atNode 136,GridMinus.atNode 137,NodeMinus02.w8,CompactMinus0128.checked136,CompactMinus0128.small136,CompactMinus0128.nodes136,NodeMinus02.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p137,GridMinus.atNode 137,GridMinus.atNode 138,NodeMinus02.w9,CompactMinus0128.checked137,CompactMinus0128.small137,CompactMinus0128.nodes137,NodeMinus02.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p138,GridMinus.atNode 138,GridMinus.atNode 139,NodeMinus02.w10,CompactMinus0128.checked138,CompactMinus0128.small138,CompactMinus0128.nodes138,NodeMinus02.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p139,GridMinus.atNode 139,GridMinus.atNode 140,NodeMinus02.w11,CompactMinus0128.checked139,CompactMinus0128.small139,CompactMinus0128.nodes139,NodeMinus02.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p140,GridMinus.atNode 140,GridMinus.atNode 141,NodeMinus02.w12,CompactMinus0128.checked140,CompactMinus0128.small140,CompactMinus0128.nodes140,NodeMinus02.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p141,GridMinus.atNode 141,GridMinus.atNode 142,NodeMinus02.w13,CompactMinus0128.checked141,CompactMinus0128.small141,CompactMinus0128.nodes141,NodeMinus02.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p142,GridMinus.atNode 142,GridMinus.atNode 143,NodeMinus02.w14,CompactMinus0128.checked142,CompactMinus0128.small142,CompactMinus0128.nodes142,NodeMinus02.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0128.p143,GridMinus.atNode 143,GridMinus.atNode 144,NodeMinus02.w15,CompactMinus0128.checked143,CompactMinus0128.small143,CompactMinus0128.nodes143,NodeMinus02.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p144,GridMinus.atNode 144,GridMinus.atNode 145,NodeMinus02.w16,CompactMinus0144.checked144,CompactMinus0144.small144,CompactMinus0144.nodes144,NodeMinus02.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p145,GridMinus.atNode 145,GridMinus.atNode 146,NodeMinus02.w17,CompactMinus0144.checked145,CompactMinus0144.small145,CompactMinus0144.nodes145,NodeMinus02.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p146,GridMinus.atNode 146,GridMinus.atNode 147,NodeMinus02.w18,CompactMinus0144.checked146,CompactMinus0144.small146,CompactMinus0144.nodes146,NodeMinus02.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p147,GridMinus.atNode 147,GridMinus.atNode 148,NodeMinus02.w19,CompactMinus0144.checked147,CompactMinus0144.small147,CompactMinus0144.nodes147,NodeMinus02.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p148,GridMinus.atNode 148,GridMinus.atNode 149,NodeMinus02.w20,CompactMinus0144.checked148,CompactMinus0144.small148,CompactMinus0144.nodes148,NodeMinus02.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p149,GridMinus.atNode 149,GridMinus.atNode 150,NodeMinus02.w21,CompactMinus0144.checked149,CompactMinus0144.small149,CompactMinus0144.nodes149,NodeMinus02.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p150,GridMinus.atNode 150,GridMinus.atNode 151,NodeMinus02.w22,CompactMinus0144.checked150,CompactMinus0144.small150,CompactMinus0144.nodes150,NodeMinus02.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p151,GridMinus.atNode 151,GridMinus.atNode 152,NodeMinus02.w23,CompactMinus0144.checked151,CompactMinus0144.small151,CompactMinus0144.nodes151,NodeMinus02.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p152,GridMinus.atNode 152,GridMinus.atNode 153,NodeMinus02.w24,CompactMinus0144.checked152,CompactMinus0144.small152,CompactMinus0144.nodes152,NodeMinus02.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p153,GridMinus.atNode 153,GridMinus.atNode 154,NodeMinus02.w25,CompactMinus0144.checked153,CompactMinus0144.small153,CompactMinus0144.nodes153,NodeMinus02.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p154,GridMinus.atNode 154,GridMinus.atNode 155,NodeMinus02.w26,CompactMinus0144.checked154,CompactMinus0144.small154,CompactMinus0144.nodes154,NodeMinus02.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p155,GridMinus.atNode 155,GridMinus.atNode 156,NodeMinus02.w27,CompactMinus0144.checked155,CompactMinus0144.small155,CompactMinus0144.nodes155,NodeMinus02.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p156,GridMinus.atNode 156,GridMinus.atNode 157,NodeMinus02.w28,CompactMinus0144.checked156,CompactMinus0144.small156,CompactMinus0144.nodes156,NodeMinus02.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p157,GridMinus.atNode 157,GridMinus.atNode 158,NodeMinus02.w29,CompactMinus0144.checked157,CompactMinus0144.small157,CompactMinus0144.nodes157,NodeMinus02.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p158,GridMinus.atNode 158,GridMinus.atNode 159,NodeMinus02.w30,CompactMinus0144.checked158,CompactMinus0144.small158,CompactMinus0144.nodes158,NodeMinus02.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0144.p159,GridMinus.atNode 159,GridMinus.atNode 160,NodeMinus02.w31,CompactMinus0144.checked159,CompactMinus0144.small159,CompactMinus0144.nodes159,NodeMinus02.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p160,GridMinus.atNode 160,GridMinus.atNode 161,NodeMinus02.w32,CompactMinus0160.checked160,CompactMinus0160.small160,CompactMinus0160.nodes160,NodeMinus02.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p161,GridMinus.atNode 161,GridMinus.atNode 162,NodeMinus02.w33,CompactMinus0160.checked161,CompactMinus0160.small161,CompactMinus0160.nodes161,NodeMinus02.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p162,GridMinus.atNode 162,GridMinus.atNode 163,NodeMinus02.w34,CompactMinus0160.checked162,CompactMinus0160.small162,CompactMinus0160.nodes162,NodeMinus02.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p163,GridMinus.atNode 163,GridMinus.atNode 164,NodeMinus02.w35,CompactMinus0160.checked163,CompactMinus0160.small163,CompactMinus0160.nodes163,NodeMinus02.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p164,GridMinus.atNode 164,GridMinus.atNode 165,NodeMinus02.w36,CompactMinus0160.checked164,CompactMinus0160.small164,CompactMinus0160.nodes164,NodeMinus02.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p165,GridMinus.atNode 165,GridMinus.atNode 166,NodeMinus02.w37,CompactMinus0160.checked165,CompactMinus0160.small165,CompactMinus0160.nodes165,NodeMinus02.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p166,GridMinus.atNode 166,GridMinus.atNode 167,NodeMinus02.w38,CompactMinus0160.checked166,CompactMinus0160.small166,CompactMinus0160.nodes166,NodeMinus02.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p167,GridMinus.atNode 167,GridMinus.atNode 168,NodeMinus02.w39,CompactMinus0160.checked167,CompactMinus0160.small167,CompactMinus0160.nodes167,NodeMinus02.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p168,GridMinus.atNode 168,GridMinus.atNode 169,NodeMinus02.w40,CompactMinus0160.checked168,CompactMinus0160.small168,CompactMinus0160.nodes168,NodeMinus02.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p169,GridMinus.atNode 169,GridMinus.atNode 170,NodeMinus02.w41,CompactMinus0160.checked169,CompactMinus0160.small169,CompactMinus0160.nodes169,NodeMinus02.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p170,GridMinus.atNode 170,GridMinus.atNode 171,NodeMinus02.w42,CompactMinus0160.checked170,CompactMinus0160.small170,CompactMinus0160.nodes170,NodeMinus02.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p171,GridMinus.atNode 171,GridMinus.atNode 172,NodeMinus02.w43,CompactMinus0160.checked171,CompactMinus0160.small171,CompactMinus0160.nodes171,NodeMinus02.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p172,GridMinus.atNode 172,GridMinus.atNode 173,NodeMinus02.w44,CompactMinus0160.checked172,CompactMinus0160.small172,CompactMinus0160.nodes172,NodeMinus02.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p173,GridMinus.atNode 173,GridMinus.atNode 174,NodeMinus02.w45,CompactMinus0160.checked173,CompactMinus0160.small173,CompactMinus0160.nodes173,NodeMinus02.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p174,GridMinus.atNode 174,GridMinus.atNode 175,NodeMinus02.w46,CompactMinus0160.checked174,CompactMinus0160.small174,CompactMinus0160.nodes174,NodeMinus02.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0160.p175,GridMinus.atNode 175,GridMinus.atNode 176,NodeMinus02.w47,CompactMinus0160.checked175,CompactMinus0160.small175,CompactMinus0160.nodes175,NodeMinus02.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p176,GridMinus.atNode 176,GridMinus.atNode 177,NodeMinus02.w48,CompactMinus0176.checked176,CompactMinus0176.small176,CompactMinus0176.nodes176,NodeMinus02.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p177,GridMinus.atNode 177,GridMinus.atNode 178,NodeMinus02.w49,CompactMinus0176.checked177,CompactMinus0176.small177,CompactMinus0176.nodes177,NodeMinus02.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p178,GridMinus.atNode 178,GridMinus.atNode 179,NodeMinus02.w50,CompactMinus0176.checked178,CompactMinus0176.small178,CompactMinus0176.nodes178,NodeMinus02.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p179,GridMinus.atNode 179,GridMinus.atNode 180,NodeMinus02.w51,CompactMinus0176.checked179,CompactMinus0176.small179,CompactMinus0176.nodes179,NodeMinus02.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p180,GridMinus.atNode 180,GridMinus.atNode 181,NodeMinus02.w52,CompactMinus0176.checked180,CompactMinus0176.small180,CompactMinus0176.nodes180,NodeMinus02.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p181,GridMinus.atNode 181,GridMinus.atNode 182,NodeMinus02.w53,CompactMinus0176.checked181,CompactMinus0176.small181,CompactMinus0176.nodes181,NodeMinus02.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p182,GridMinus.atNode 182,GridMinus.atNode 183,NodeMinus02.w54,CompactMinus0176.checked182,CompactMinus0176.small182,CompactMinus0176.nodes182,NodeMinus02.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p183,GridMinus.atNode 183,GridMinus.atNode 184,NodeMinus02.w55,CompactMinus0176.checked183,CompactMinus0176.small183,CompactMinus0176.nodes183,NodeMinus02.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p184,GridMinus.atNode 184,GridMinus.atNode 185,NodeMinus02.w56,CompactMinus0176.checked184,CompactMinus0176.small184,CompactMinus0176.nodes184,NodeMinus02.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p185,GridMinus.atNode 185,GridMinus.atNode 186,NodeMinus02.w57,CompactMinus0176.checked185,CompactMinus0176.small185,CompactMinus0176.nodes185,NodeMinus02.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p186,GridMinus.atNode 186,GridMinus.atNode 187,NodeMinus02.w58,CompactMinus0176.checked186,CompactMinus0176.small186,CompactMinus0176.nodes186,NodeMinus02.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p187,GridMinus.atNode 187,GridMinus.atNode 188,NodeMinus02.w59,CompactMinus0176.checked187,CompactMinus0176.small187,CompactMinus0176.nodes187,NodeMinus02.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p188,GridMinus.atNode 188,GridMinus.atNode 189,NodeMinus02.w60,CompactMinus0176.checked188,CompactMinus0176.small188,CompactMinus0176.nodes188,NodeMinus02.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p189,GridMinus.atNode 189,GridMinus.atNode 190,NodeMinus02.w61,CompactMinus0176.checked189,CompactMinus0176.small189,CompactMinus0176.nodes189,NodeMinus02.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p190,GridMinus.atNode 190,GridMinus.atNode 191,NodeMinus02.w62,CompactMinus0176.checked190,CompactMinus0176.small190,CompactMinus0176.nodes190,NodeMinus02.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0176.p191,GridMinus.atNode 191,GridMinus.atNode 192,NodeMinus02.w63,CompactMinus0176.checked191,CompactMinus0176.small191,CompactMinus0176.nodes191,NodeMinus02.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (128+j) ∧
    (atRow j).right=GridMinus.atNode (128+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus02
