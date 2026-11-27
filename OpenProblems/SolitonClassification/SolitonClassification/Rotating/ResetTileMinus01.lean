import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0064
import SolitonClassification.Rotating.ResetPackedMinus0080
import SolitonClassification.Rotating.ResetPackedMinus0096
import SolitonClassification.Rotating.ResetPackedMinus0112
namespace SolitonClassification.Rotating.DyadicReset.TileMinus01
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p64,GridMinus.atNode 64,GridMinus.atNode 65,NodeMinus01.w0,CompactMinus0064.checked64,CompactMinus0064.small64,CompactMinus0064.nodes64,NodeMinus01.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p65,GridMinus.atNode 65,GridMinus.atNode 66,NodeMinus01.w1,CompactMinus0064.checked65,CompactMinus0064.small65,CompactMinus0064.nodes65,NodeMinus01.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p66,GridMinus.atNode 66,GridMinus.atNode 67,NodeMinus01.w2,CompactMinus0064.checked66,CompactMinus0064.small66,CompactMinus0064.nodes66,NodeMinus01.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p67,GridMinus.atNode 67,GridMinus.atNode 68,NodeMinus01.w3,CompactMinus0064.checked67,CompactMinus0064.small67,CompactMinus0064.nodes67,NodeMinus01.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p68,GridMinus.atNode 68,GridMinus.atNode 69,NodeMinus01.w4,CompactMinus0064.checked68,CompactMinus0064.small68,CompactMinus0064.nodes68,NodeMinus01.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p69,GridMinus.atNode 69,GridMinus.atNode 70,NodeMinus01.w5,CompactMinus0064.checked69,CompactMinus0064.small69,CompactMinus0064.nodes69,NodeMinus01.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p70,GridMinus.atNode 70,GridMinus.atNode 71,NodeMinus01.w6,CompactMinus0064.checked70,CompactMinus0064.small70,CompactMinus0064.nodes70,NodeMinus01.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p71,GridMinus.atNode 71,GridMinus.atNode 72,NodeMinus01.w7,CompactMinus0064.checked71,CompactMinus0064.small71,CompactMinus0064.nodes71,NodeMinus01.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p72,GridMinus.atNode 72,GridMinus.atNode 73,NodeMinus01.w8,CompactMinus0064.checked72,CompactMinus0064.small72,CompactMinus0064.nodes72,NodeMinus01.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p73,GridMinus.atNode 73,GridMinus.atNode 74,NodeMinus01.w9,CompactMinus0064.checked73,CompactMinus0064.small73,CompactMinus0064.nodes73,NodeMinus01.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p74,GridMinus.atNode 74,GridMinus.atNode 75,NodeMinus01.w10,CompactMinus0064.checked74,CompactMinus0064.small74,CompactMinus0064.nodes74,NodeMinus01.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p75,GridMinus.atNode 75,GridMinus.atNode 76,NodeMinus01.w11,CompactMinus0064.checked75,CompactMinus0064.small75,CompactMinus0064.nodes75,NodeMinus01.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p76,GridMinus.atNode 76,GridMinus.atNode 77,NodeMinus01.w12,CompactMinus0064.checked76,CompactMinus0064.small76,CompactMinus0064.nodes76,NodeMinus01.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p77,GridMinus.atNode 77,GridMinus.atNode 78,NodeMinus01.w13,CompactMinus0064.checked77,CompactMinus0064.small77,CompactMinus0064.nodes77,NodeMinus01.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p78,GridMinus.atNode 78,GridMinus.atNode 79,NodeMinus01.w14,CompactMinus0064.checked78,CompactMinus0064.small78,CompactMinus0064.nodes78,NodeMinus01.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0064.p79,GridMinus.atNode 79,GridMinus.atNode 80,NodeMinus01.w15,CompactMinus0064.checked79,CompactMinus0064.small79,CompactMinus0064.nodes79,NodeMinus01.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p80,GridMinus.atNode 80,GridMinus.atNode 81,NodeMinus01.w16,CompactMinus0080.checked80,CompactMinus0080.small80,CompactMinus0080.nodes80,NodeMinus01.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p81,GridMinus.atNode 81,GridMinus.atNode 82,NodeMinus01.w17,CompactMinus0080.checked81,CompactMinus0080.small81,CompactMinus0080.nodes81,NodeMinus01.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p82,GridMinus.atNode 82,GridMinus.atNode 83,NodeMinus01.w18,CompactMinus0080.checked82,CompactMinus0080.small82,CompactMinus0080.nodes82,NodeMinus01.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p83,GridMinus.atNode 83,GridMinus.atNode 84,NodeMinus01.w19,CompactMinus0080.checked83,CompactMinus0080.small83,CompactMinus0080.nodes83,NodeMinus01.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p84,GridMinus.atNode 84,GridMinus.atNode 85,NodeMinus01.w20,CompactMinus0080.checked84,CompactMinus0080.small84,CompactMinus0080.nodes84,NodeMinus01.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p85,GridMinus.atNode 85,GridMinus.atNode 86,NodeMinus01.w21,CompactMinus0080.checked85,CompactMinus0080.small85,CompactMinus0080.nodes85,NodeMinus01.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p86,GridMinus.atNode 86,GridMinus.atNode 87,NodeMinus01.w22,CompactMinus0080.checked86,CompactMinus0080.small86,CompactMinus0080.nodes86,NodeMinus01.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p87,GridMinus.atNode 87,GridMinus.atNode 88,NodeMinus01.w23,CompactMinus0080.checked87,CompactMinus0080.small87,CompactMinus0080.nodes87,NodeMinus01.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p88,GridMinus.atNode 88,GridMinus.atNode 89,NodeMinus01.w24,CompactMinus0080.checked88,CompactMinus0080.small88,CompactMinus0080.nodes88,NodeMinus01.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p89,GridMinus.atNode 89,GridMinus.atNode 90,NodeMinus01.w25,CompactMinus0080.checked89,CompactMinus0080.small89,CompactMinus0080.nodes89,NodeMinus01.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p90,GridMinus.atNode 90,GridMinus.atNode 91,NodeMinus01.w26,CompactMinus0080.checked90,CompactMinus0080.small90,CompactMinus0080.nodes90,NodeMinus01.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p91,GridMinus.atNode 91,GridMinus.atNode 92,NodeMinus01.w27,CompactMinus0080.checked91,CompactMinus0080.small91,CompactMinus0080.nodes91,NodeMinus01.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p92,GridMinus.atNode 92,GridMinus.atNode 93,NodeMinus01.w28,CompactMinus0080.checked92,CompactMinus0080.small92,CompactMinus0080.nodes92,NodeMinus01.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p93,GridMinus.atNode 93,GridMinus.atNode 94,NodeMinus01.w29,CompactMinus0080.checked93,CompactMinus0080.small93,CompactMinus0080.nodes93,NodeMinus01.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p94,GridMinus.atNode 94,GridMinus.atNode 95,NodeMinus01.w30,CompactMinus0080.checked94,CompactMinus0080.small94,CompactMinus0080.nodes94,NodeMinus01.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0080.p95,GridMinus.atNode 95,GridMinus.atNode 96,NodeMinus01.w31,CompactMinus0080.checked95,CompactMinus0080.small95,CompactMinus0080.nodes95,NodeMinus01.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p96,GridMinus.atNode 96,GridMinus.atNode 97,NodeMinus01.w32,CompactMinus0096.checked96,CompactMinus0096.small96,CompactMinus0096.nodes96,NodeMinus01.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p97,GridMinus.atNode 97,GridMinus.atNode 98,NodeMinus01.w33,CompactMinus0096.checked97,CompactMinus0096.small97,CompactMinus0096.nodes97,NodeMinus01.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p98,GridMinus.atNode 98,GridMinus.atNode 99,NodeMinus01.w34,CompactMinus0096.checked98,CompactMinus0096.small98,CompactMinus0096.nodes98,NodeMinus01.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p99,GridMinus.atNode 99,GridMinus.atNode 100,NodeMinus01.w35,CompactMinus0096.checked99,CompactMinus0096.small99,CompactMinus0096.nodes99,NodeMinus01.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p100,GridMinus.atNode 100,GridMinus.atNode 101,NodeMinus01.w36,CompactMinus0096.checked100,CompactMinus0096.small100,CompactMinus0096.nodes100,NodeMinus01.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p101,GridMinus.atNode 101,GridMinus.atNode 102,NodeMinus01.w37,CompactMinus0096.checked101,CompactMinus0096.small101,CompactMinus0096.nodes101,NodeMinus01.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p102,GridMinus.atNode 102,GridMinus.atNode 103,NodeMinus01.w38,CompactMinus0096.checked102,CompactMinus0096.small102,CompactMinus0096.nodes102,NodeMinus01.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p103,GridMinus.atNode 103,GridMinus.atNode 104,NodeMinus01.w39,CompactMinus0096.checked103,CompactMinus0096.small103,CompactMinus0096.nodes103,NodeMinus01.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p104,GridMinus.atNode 104,GridMinus.atNode 105,NodeMinus01.w40,CompactMinus0096.checked104,CompactMinus0096.small104,CompactMinus0096.nodes104,NodeMinus01.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p105,GridMinus.atNode 105,GridMinus.atNode 106,NodeMinus01.w41,CompactMinus0096.checked105,CompactMinus0096.small105,CompactMinus0096.nodes105,NodeMinus01.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p106,GridMinus.atNode 106,GridMinus.atNode 107,NodeMinus01.w42,CompactMinus0096.checked106,CompactMinus0096.small106,CompactMinus0096.nodes106,NodeMinus01.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p107,GridMinus.atNode 107,GridMinus.atNode 108,NodeMinus01.w43,CompactMinus0096.checked107,CompactMinus0096.small107,CompactMinus0096.nodes107,NodeMinus01.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p108,GridMinus.atNode 108,GridMinus.atNode 109,NodeMinus01.w44,CompactMinus0096.checked108,CompactMinus0096.small108,CompactMinus0096.nodes108,NodeMinus01.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p109,GridMinus.atNode 109,GridMinus.atNode 110,NodeMinus01.w45,CompactMinus0096.checked109,CompactMinus0096.small109,CompactMinus0096.nodes109,NodeMinus01.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p110,GridMinus.atNode 110,GridMinus.atNode 111,NodeMinus01.w46,CompactMinus0096.checked110,CompactMinus0096.small110,CompactMinus0096.nodes110,NodeMinus01.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0096.p111,GridMinus.atNode 111,GridMinus.atNode 112,NodeMinus01.w47,CompactMinus0096.checked111,CompactMinus0096.small111,CompactMinus0096.nodes111,NodeMinus01.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p112,GridMinus.atNode 112,GridMinus.atNode 113,NodeMinus01.w48,CompactMinus0112.checked112,CompactMinus0112.small112,CompactMinus0112.nodes112,NodeMinus01.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p113,GridMinus.atNode 113,GridMinus.atNode 114,NodeMinus01.w49,CompactMinus0112.checked113,CompactMinus0112.small113,CompactMinus0112.nodes113,NodeMinus01.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p114,GridMinus.atNode 114,GridMinus.atNode 115,NodeMinus01.w50,CompactMinus0112.checked114,CompactMinus0112.small114,CompactMinus0112.nodes114,NodeMinus01.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p115,GridMinus.atNode 115,GridMinus.atNode 116,NodeMinus01.w51,CompactMinus0112.checked115,CompactMinus0112.small115,CompactMinus0112.nodes115,NodeMinus01.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p116,GridMinus.atNode 116,GridMinus.atNode 117,NodeMinus01.w52,CompactMinus0112.checked116,CompactMinus0112.small116,CompactMinus0112.nodes116,NodeMinus01.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p117,GridMinus.atNode 117,GridMinus.atNode 118,NodeMinus01.w53,CompactMinus0112.checked117,CompactMinus0112.small117,CompactMinus0112.nodes117,NodeMinus01.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p118,GridMinus.atNode 118,GridMinus.atNode 119,NodeMinus01.w54,CompactMinus0112.checked118,CompactMinus0112.small118,CompactMinus0112.nodes118,NodeMinus01.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p119,GridMinus.atNode 119,GridMinus.atNode 120,NodeMinus01.w55,CompactMinus0112.checked119,CompactMinus0112.small119,CompactMinus0112.nodes119,NodeMinus01.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p120,GridMinus.atNode 120,GridMinus.atNode 121,NodeMinus01.w56,CompactMinus0112.checked120,CompactMinus0112.small120,CompactMinus0112.nodes120,NodeMinus01.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p121,GridMinus.atNode 121,GridMinus.atNode 122,NodeMinus01.w57,CompactMinus0112.checked121,CompactMinus0112.small121,CompactMinus0112.nodes121,NodeMinus01.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p122,GridMinus.atNode 122,GridMinus.atNode 123,NodeMinus01.w58,CompactMinus0112.checked122,CompactMinus0112.small122,CompactMinus0112.nodes122,NodeMinus01.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p123,GridMinus.atNode 123,GridMinus.atNode 124,NodeMinus01.w59,CompactMinus0112.checked123,CompactMinus0112.small123,CompactMinus0112.nodes123,NodeMinus01.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p124,GridMinus.atNode 124,GridMinus.atNode 125,NodeMinus01.w60,CompactMinus0112.checked124,CompactMinus0112.small124,CompactMinus0112.nodes124,NodeMinus01.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p125,GridMinus.atNode 125,GridMinus.atNode 126,NodeMinus01.w61,CompactMinus0112.checked125,CompactMinus0112.small125,CompactMinus0112.nodes125,NodeMinus01.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p126,GridMinus.atNode 126,GridMinus.atNode 127,NodeMinus01.w62,CompactMinus0112.checked126,CompactMinus0112.small126,CompactMinus0112.nodes126,NodeMinus01.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0112.p127,GridMinus.atNode 127,GridMinus.atNode 128,NodeMinus01.w63,CompactMinus0112.checked127,CompactMinus0112.small127,CompactMinus0112.nodes127,NodeMinus01.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (64+j) ∧
    (atRow j).right=GridMinus.atNode (64+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus01
