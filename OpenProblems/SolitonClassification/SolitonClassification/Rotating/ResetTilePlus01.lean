import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0064
import SolitonClassification.Rotating.ResetPackedPlus0080
import SolitonClassification.Rotating.ResetPackedPlus0096
import SolitonClassification.Rotating.ResetPackedPlus0112
namespace SolitonClassification.Rotating.DyadicReset.TilePlus01
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p64,GridPlus.atNode 64,GridPlus.atNode 65,NodePlus01.w0,CompactPlus0064.checked64,CompactPlus0064.small64,CompactPlus0064.nodes64,NodePlus01.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p65,GridPlus.atNode 65,GridPlus.atNode 66,NodePlus01.w1,CompactPlus0064.checked65,CompactPlus0064.small65,CompactPlus0064.nodes65,NodePlus01.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p66,GridPlus.atNode 66,GridPlus.atNode 67,NodePlus01.w2,CompactPlus0064.checked66,CompactPlus0064.small66,CompactPlus0064.nodes66,NodePlus01.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p67,GridPlus.atNode 67,GridPlus.atNode 68,NodePlus01.w3,CompactPlus0064.checked67,CompactPlus0064.small67,CompactPlus0064.nodes67,NodePlus01.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p68,GridPlus.atNode 68,GridPlus.atNode 69,NodePlus01.w4,CompactPlus0064.checked68,CompactPlus0064.small68,CompactPlus0064.nodes68,NodePlus01.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p69,GridPlus.atNode 69,GridPlus.atNode 70,NodePlus01.w5,CompactPlus0064.checked69,CompactPlus0064.small69,CompactPlus0064.nodes69,NodePlus01.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p70,GridPlus.atNode 70,GridPlus.atNode 71,NodePlus01.w6,CompactPlus0064.checked70,CompactPlus0064.small70,CompactPlus0064.nodes70,NodePlus01.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p71,GridPlus.atNode 71,GridPlus.atNode 72,NodePlus01.w7,CompactPlus0064.checked71,CompactPlus0064.small71,CompactPlus0064.nodes71,NodePlus01.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p72,GridPlus.atNode 72,GridPlus.atNode 73,NodePlus01.w8,CompactPlus0064.checked72,CompactPlus0064.small72,CompactPlus0064.nodes72,NodePlus01.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p73,GridPlus.atNode 73,GridPlus.atNode 74,NodePlus01.w9,CompactPlus0064.checked73,CompactPlus0064.small73,CompactPlus0064.nodes73,NodePlus01.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p74,GridPlus.atNode 74,GridPlus.atNode 75,NodePlus01.w10,CompactPlus0064.checked74,CompactPlus0064.small74,CompactPlus0064.nodes74,NodePlus01.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p75,GridPlus.atNode 75,GridPlus.atNode 76,NodePlus01.w11,CompactPlus0064.checked75,CompactPlus0064.small75,CompactPlus0064.nodes75,NodePlus01.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p76,GridPlus.atNode 76,GridPlus.atNode 77,NodePlus01.w12,CompactPlus0064.checked76,CompactPlus0064.small76,CompactPlus0064.nodes76,NodePlus01.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p77,GridPlus.atNode 77,GridPlus.atNode 78,NodePlus01.w13,CompactPlus0064.checked77,CompactPlus0064.small77,CompactPlus0064.nodes77,NodePlus01.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p78,GridPlus.atNode 78,GridPlus.atNode 79,NodePlus01.w14,CompactPlus0064.checked78,CompactPlus0064.small78,CompactPlus0064.nodes78,NodePlus01.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0064.p79,GridPlus.atNode 79,GridPlus.atNode 80,NodePlus01.w15,CompactPlus0064.checked79,CompactPlus0064.small79,CompactPlus0064.nodes79,NodePlus01.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p80,GridPlus.atNode 80,GridPlus.atNode 81,NodePlus01.w16,CompactPlus0080.checked80,CompactPlus0080.small80,CompactPlus0080.nodes80,NodePlus01.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p81,GridPlus.atNode 81,GridPlus.atNode 82,NodePlus01.w17,CompactPlus0080.checked81,CompactPlus0080.small81,CompactPlus0080.nodes81,NodePlus01.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p82,GridPlus.atNode 82,GridPlus.atNode 83,NodePlus01.w18,CompactPlus0080.checked82,CompactPlus0080.small82,CompactPlus0080.nodes82,NodePlus01.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p83,GridPlus.atNode 83,GridPlus.atNode 84,NodePlus01.w19,CompactPlus0080.checked83,CompactPlus0080.small83,CompactPlus0080.nodes83,NodePlus01.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p84,GridPlus.atNode 84,GridPlus.atNode 85,NodePlus01.w20,CompactPlus0080.checked84,CompactPlus0080.small84,CompactPlus0080.nodes84,NodePlus01.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p85,GridPlus.atNode 85,GridPlus.atNode 86,NodePlus01.w21,CompactPlus0080.checked85,CompactPlus0080.small85,CompactPlus0080.nodes85,NodePlus01.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p86,GridPlus.atNode 86,GridPlus.atNode 87,NodePlus01.w22,CompactPlus0080.checked86,CompactPlus0080.small86,CompactPlus0080.nodes86,NodePlus01.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p87,GridPlus.atNode 87,GridPlus.atNode 88,NodePlus01.w23,CompactPlus0080.checked87,CompactPlus0080.small87,CompactPlus0080.nodes87,NodePlus01.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p88,GridPlus.atNode 88,GridPlus.atNode 89,NodePlus01.w24,CompactPlus0080.checked88,CompactPlus0080.small88,CompactPlus0080.nodes88,NodePlus01.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p89,GridPlus.atNode 89,GridPlus.atNode 90,NodePlus01.w25,CompactPlus0080.checked89,CompactPlus0080.small89,CompactPlus0080.nodes89,NodePlus01.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p90,GridPlus.atNode 90,GridPlus.atNode 91,NodePlus01.w26,CompactPlus0080.checked90,CompactPlus0080.small90,CompactPlus0080.nodes90,NodePlus01.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p91,GridPlus.atNode 91,GridPlus.atNode 92,NodePlus01.w27,CompactPlus0080.checked91,CompactPlus0080.small91,CompactPlus0080.nodes91,NodePlus01.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p92,GridPlus.atNode 92,GridPlus.atNode 93,NodePlus01.w28,CompactPlus0080.checked92,CompactPlus0080.small92,CompactPlus0080.nodes92,NodePlus01.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p93,GridPlus.atNode 93,GridPlus.atNode 94,NodePlus01.w29,CompactPlus0080.checked93,CompactPlus0080.small93,CompactPlus0080.nodes93,NodePlus01.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p94,GridPlus.atNode 94,GridPlus.atNode 95,NodePlus01.w30,CompactPlus0080.checked94,CompactPlus0080.small94,CompactPlus0080.nodes94,NodePlus01.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0080.p95,GridPlus.atNode 95,GridPlus.atNode 96,NodePlus01.w31,CompactPlus0080.checked95,CompactPlus0080.small95,CompactPlus0080.nodes95,NodePlus01.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p96,GridPlus.atNode 96,GridPlus.atNode 97,NodePlus01.w32,CompactPlus0096.checked96,CompactPlus0096.small96,CompactPlus0096.nodes96,NodePlus01.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p97,GridPlus.atNode 97,GridPlus.atNode 98,NodePlus01.w33,CompactPlus0096.checked97,CompactPlus0096.small97,CompactPlus0096.nodes97,NodePlus01.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p98,GridPlus.atNode 98,GridPlus.atNode 99,NodePlus01.w34,CompactPlus0096.checked98,CompactPlus0096.small98,CompactPlus0096.nodes98,NodePlus01.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p99,GridPlus.atNode 99,GridPlus.atNode 100,NodePlus01.w35,CompactPlus0096.checked99,CompactPlus0096.small99,CompactPlus0096.nodes99,NodePlus01.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p100,GridPlus.atNode 100,GridPlus.atNode 101,NodePlus01.w36,CompactPlus0096.checked100,CompactPlus0096.small100,CompactPlus0096.nodes100,NodePlus01.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p101,GridPlus.atNode 101,GridPlus.atNode 102,NodePlus01.w37,CompactPlus0096.checked101,CompactPlus0096.small101,CompactPlus0096.nodes101,NodePlus01.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p102,GridPlus.atNode 102,GridPlus.atNode 103,NodePlus01.w38,CompactPlus0096.checked102,CompactPlus0096.small102,CompactPlus0096.nodes102,NodePlus01.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p103,GridPlus.atNode 103,GridPlus.atNode 104,NodePlus01.w39,CompactPlus0096.checked103,CompactPlus0096.small103,CompactPlus0096.nodes103,NodePlus01.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p104,GridPlus.atNode 104,GridPlus.atNode 105,NodePlus01.w40,CompactPlus0096.checked104,CompactPlus0096.small104,CompactPlus0096.nodes104,NodePlus01.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p105,GridPlus.atNode 105,GridPlus.atNode 106,NodePlus01.w41,CompactPlus0096.checked105,CompactPlus0096.small105,CompactPlus0096.nodes105,NodePlus01.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p106,GridPlus.atNode 106,GridPlus.atNode 107,NodePlus01.w42,CompactPlus0096.checked106,CompactPlus0096.small106,CompactPlus0096.nodes106,NodePlus01.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p107,GridPlus.atNode 107,GridPlus.atNode 108,NodePlus01.w43,CompactPlus0096.checked107,CompactPlus0096.small107,CompactPlus0096.nodes107,NodePlus01.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p108,GridPlus.atNode 108,GridPlus.atNode 109,NodePlus01.w44,CompactPlus0096.checked108,CompactPlus0096.small108,CompactPlus0096.nodes108,NodePlus01.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p109,GridPlus.atNode 109,GridPlus.atNode 110,NodePlus01.w45,CompactPlus0096.checked109,CompactPlus0096.small109,CompactPlus0096.nodes109,NodePlus01.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p110,GridPlus.atNode 110,GridPlus.atNode 111,NodePlus01.w46,CompactPlus0096.checked110,CompactPlus0096.small110,CompactPlus0096.nodes110,NodePlus01.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0096.p111,GridPlus.atNode 111,GridPlus.atNode 112,NodePlus01.w47,CompactPlus0096.checked111,CompactPlus0096.small111,CompactPlus0096.nodes111,NodePlus01.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p112,GridPlus.atNode 112,GridPlus.atNode 113,NodePlus01.w48,CompactPlus0112.checked112,CompactPlus0112.small112,CompactPlus0112.nodes112,NodePlus01.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p113,GridPlus.atNode 113,GridPlus.atNode 114,NodePlus01.w49,CompactPlus0112.checked113,CompactPlus0112.small113,CompactPlus0112.nodes113,NodePlus01.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p114,GridPlus.atNode 114,GridPlus.atNode 115,NodePlus01.w50,CompactPlus0112.checked114,CompactPlus0112.small114,CompactPlus0112.nodes114,NodePlus01.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p115,GridPlus.atNode 115,GridPlus.atNode 116,NodePlus01.w51,CompactPlus0112.checked115,CompactPlus0112.small115,CompactPlus0112.nodes115,NodePlus01.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p116,GridPlus.atNode 116,GridPlus.atNode 117,NodePlus01.w52,CompactPlus0112.checked116,CompactPlus0112.small116,CompactPlus0112.nodes116,NodePlus01.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p117,GridPlus.atNode 117,GridPlus.atNode 118,NodePlus01.w53,CompactPlus0112.checked117,CompactPlus0112.small117,CompactPlus0112.nodes117,NodePlus01.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p118,GridPlus.atNode 118,GridPlus.atNode 119,NodePlus01.w54,CompactPlus0112.checked118,CompactPlus0112.small118,CompactPlus0112.nodes118,NodePlus01.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p119,GridPlus.atNode 119,GridPlus.atNode 120,NodePlus01.w55,CompactPlus0112.checked119,CompactPlus0112.small119,CompactPlus0112.nodes119,NodePlus01.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p120,GridPlus.atNode 120,GridPlus.atNode 121,NodePlus01.w56,CompactPlus0112.checked120,CompactPlus0112.small120,CompactPlus0112.nodes120,NodePlus01.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p121,GridPlus.atNode 121,GridPlus.atNode 122,NodePlus01.w57,CompactPlus0112.checked121,CompactPlus0112.small121,CompactPlus0112.nodes121,NodePlus01.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p122,GridPlus.atNode 122,GridPlus.atNode 123,NodePlus01.w58,CompactPlus0112.checked122,CompactPlus0112.small122,CompactPlus0112.nodes122,NodePlus01.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p123,GridPlus.atNode 123,GridPlus.atNode 124,NodePlus01.w59,CompactPlus0112.checked123,CompactPlus0112.small123,CompactPlus0112.nodes123,NodePlus01.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p124,GridPlus.atNode 124,GridPlus.atNode 125,NodePlus01.w60,CompactPlus0112.checked124,CompactPlus0112.small124,CompactPlus0112.nodes124,NodePlus01.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p125,GridPlus.atNode 125,GridPlus.atNode 126,NodePlus01.w61,CompactPlus0112.checked125,CompactPlus0112.small125,CompactPlus0112.nodes125,NodePlus01.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p126,GridPlus.atNode 126,GridPlus.atNode 127,NodePlus01.w62,CompactPlus0112.checked126,CompactPlus0112.small126,CompactPlus0112.nodes126,NodePlus01.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0112.p127,GridPlus.atNode 127,GridPlus.atNode 128,NodePlus01.w63,CompactPlus0112.checked127,CompactPlus0112.small127,CompactPlus0112.nodes127,NodePlus01.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (64+j) ∧
    (atRow j).right=GridPlus.atNode (64+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus01
