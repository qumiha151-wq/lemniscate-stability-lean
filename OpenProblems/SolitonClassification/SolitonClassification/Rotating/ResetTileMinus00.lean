import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0000
import SolitonClassification.Rotating.ResetPackedMinus0016
import SolitonClassification.Rotating.ResetPackedMinus0032
import SolitonClassification.Rotating.ResetPackedMinus0048
namespace SolitonClassification.Rotating.DyadicReset.TileMinus00
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p0,GridMinus.atNode 0,GridMinus.atNode 1,NodeMinus00.w0,CompactMinus0000.checked0,CompactMinus0000.small0,CompactMinus0000.nodes0,NodeMinus00.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p1,GridMinus.atNode 1,GridMinus.atNode 2,NodeMinus00.w1,CompactMinus0000.checked1,CompactMinus0000.small1,CompactMinus0000.nodes1,NodeMinus00.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p2,GridMinus.atNode 2,GridMinus.atNode 3,NodeMinus00.w2,CompactMinus0000.checked2,CompactMinus0000.small2,CompactMinus0000.nodes2,NodeMinus00.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p3,GridMinus.atNode 3,GridMinus.atNode 4,NodeMinus00.w3,CompactMinus0000.checked3,CompactMinus0000.small3,CompactMinus0000.nodes3,NodeMinus00.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p4,GridMinus.atNode 4,GridMinus.atNode 5,NodeMinus00.w4,CompactMinus0000.checked4,CompactMinus0000.small4,CompactMinus0000.nodes4,NodeMinus00.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p5,GridMinus.atNode 5,GridMinus.atNode 6,NodeMinus00.w5,CompactMinus0000.checked5,CompactMinus0000.small5,CompactMinus0000.nodes5,NodeMinus00.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p6,GridMinus.atNode 6,GridMinus.atNode 7,NodeMinus00.w6,CompactMinus0000.checked6,CompactMinus0000.small6,CompactMinus0000.nodes6,NodeMinus00.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p7,GridMinus.atNode 7,GridMinus.atNode 8,NodeMinus00.w7,CompactMinus0000.checked7,CompactMinus0000.small7,CompactMinus0000.nodes7,NodeMinus00.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p8,GridMinus.atNode 8,GridMinus.atNode 9,NodeMinus00.w8,CompactMinus0000.checked8,CompactMinus0000.small8,CompactMinus0000.nodes8,NodeMinus00.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p9,GridMinus.atNode 9,GridMinus.atNode 10,NodeMinus00.w9,CompactMinus0000.checked9,CompactMinus0000.small9,CompactMinus0000.nodes9,NodeMinus00.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p10,GridMinus.atNode 10,GridMinus.atNode 11,NodeMinus00.w10,CompactMinus0000.checked10,CompactMinus0000.small10,CompactMinus0000.nodes10,NodeMinus00.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p11,GridMinus.atNode 11,GridMinus.atNode 12,NodeMinus00.w11,CompactMinus0000.checked11,CompactMinus0000.small11,CompactMinus0000.nodes11,NodeMinus00.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p12,GridMinus.atNode 12,GridMinus.atNode 13,NodeMinus00.w12,CompactMinus0000.checked12,CompactMinus0000.small12,CompactMinus0000.nodes12,NodeMinus00.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p13,GridMinus.atNode 13,GridMinus.atNode 14,NodeMinus00.w13,CompactMinus0000.checked13,CompactMinus0000.small13,CompactMinus0000.nodes13,NodeMinus00.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p14,GridMinus.atNode 14,GridMinus.atNode 15,NodeMinus00.w14,CompactMinus0000.checked14,CompactMinus0000.small14,CompactMinus0000.nodes14,NodeMinus00.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p15,GridMinus.atNode 15,GridMinus.atNode 16,NodeMinus00.w15,CompactMinus0000.checked15,CompactMinus0000.small15,CompactMinus0000.nodes15,NodeMinus00.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p16,GridMinus.atNode 16,GridMinus.atNode 17,NodeMinus00.w16,CompactMinus0016.checked16,CompactMinus0016.small16,CompactMinus0016.nodes16,NodeMinus00.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p17,GridMinus.atNode 17,GridMinus.atNode 18,NodeMinus00.w17,CompactMinus0016.checked17,CompactMinus0016.small17,CompactMinus0016.nodes17,NodeMinus00.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p18,GridMinus.atNode 18,GridMinus.atNode 19,NodeMinus00.w18,CompactMinus0016.checked18,CompactMinus0016.small18,CompactMinus0016.nodes18,NodeMinus00.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p19,GridMinus.atNode 19,GridMinus.atNode 20,NodeMinus00.w19,CompactMinus0016.checked19,CompactMinus0016.small19,CompactMinus0016.nodes19,NodeMinus00.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p20,GridMinus.atNode 20,GridMinus.atNode 21,NodeMinus00.w20,CompactMinus0016.checked20,CompactMinus0016.small20,CompactMinus0016.nodes20,NodeMinus00.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p21,GridMinus.atNode 21,GridMinus.atNode 22,NodeMinus00.w21,CompactMinus0016.checked21,CompactMinus0016.small21,CompactMinus0016.nodes21,NodeMinus00.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p22,GridMinus.atNode 22,GridMinus.atNode 23,NodeMinus00.w22,CompactMinus0016.checked22,CompactMinus0016.small22,CompactMinus0016.nodes22,NodeMinus00.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p23,GridMinus.atNode 23,GridMinus.atNode 24,NodeMinus00.w23,CompactMinus0016.checked23,CompactMinus0016.small23,CompactMinus0016.nodes23,NodeMinus00.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p24,GridMinus.atNode 24,GridMinus.atNode 25,NodeMinus00.w24,CompactMinus0016.checked24,CompactMinus0016.small24,CompactMinus0016.nodes24,NodeMinus00.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p25,GridMinus.atNode 25,GridMinus.atNode 26,NodeMinus00.w25,CompactMinus0016.checked25,CompactMinus0016.small25,CompactMinus0016.nodes25,NodeMinus00.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p26,GridMinus.atNode 26,GridMinus.atNode 27,NodeMinus00.w26,CompactMinus0016.checked26,CompactMinus0016.small26,CompactMinus0016.nodes26,NodeMinus00.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p27,GridMinus.atNode 27,GridMinus.atNode 28,NodeMinus00.w27,CompactMinus0016.checked27,CompactMinus0016.small27,CompactMinus0016.nodes27,NodeMinus00.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p28,GridMinus.atNode 28,GridMinus.atNode 29,NodeMinus00.w28,CompactMinus0016.checked28,CompactMinus0016.small28,CompactMinus0016.nodes28,NodeMinus00.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p29,GridMinus.atNode 29,GridMinus.atNode 30,NodeMinus00.w29,CompactMinus0016.checked29,CompactMinus0016.small29,CompactMinus0016.nodes29,NodeMinus00.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p30,GridMinus.atNode 30,GridMinus.atNode 31,NodeMinus00.w30,CompactMinus0016.checked30,CompactMinus0016.small30,CompactMinus0016.nodes30,NodeMinus00.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0016.p31,GridMinus.atNode 31,GridMinus.atNode 32,NodeMinus00.w31,CompactMinus0016.checked31,CompactMinus0016.small31,CompactMinus0016.nodes31,NodeMinus00.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p32,GridMinus.atNode 32,GridMinus.atNode 33,NodeMinus00.w32,CompactMinus0032.checked32,CompactMinus0032.small32,CompactMinus0032.nodes32,NodeMinus00.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p33,GridMinus.atNode 33,GridMinus.atNode 34,NodeMinus00.w33,CompactMinus0032.checked33,CompactMinus0032.small33,CompactMinus0032.nodes33,NodeMinus00.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p34,GridMinus.atNode 34,GridMinus.atNode 35,NodeMinus00.w34,CompactMinus0032.checked34,CompactMinus0032.small34,CompactMinus0032.nodes34,NodeMinus00.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p35,GridMinus.atNode 35,GridMinus.atNode 36,NodeMinus00.w35,CompactMinus0032.checked35,CompactMinus0032.small35,CompactMinus0032.nodes35,NodeMinus00.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p36,GridMinus.atNode 36,GridMinus.atNode 37,NodeMinus00.w36,CompactMinus0032.checked36,CompactMinus0032.small36,CompactMinus0032.nodes36,NodeMinus00.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p37,GridMinus.atNode 37,GridMinus.atNode 38,NodeMinus00.w37,CompactMinus0032.checked37,CompactMinus0032.small37,CompactMinus0032.nodes37,NodeMinus00.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p38,GridMinus.atNode 38,GridMinus.atNode 39,NodeMinus00.w38,CompactMinus0032.checked38,CompactMinus0032.small38,CompactMinus0032.nodes38,NodeMinus00.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p39,GridMinus.atNode 39,GridMinus.atNode 40,NodeMinus00.w39,CompactMinus0032.checked39,CompactMinus0032.small39,CompactMinus0032.nodes39,NodeMinus00.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p40,GridMinus.atNode 40,GridMinus.atNode 41,NodeMinus00.w40,CompactMinus0032.checked40,CompactMinus0032.small40,CompactMinus0032.nodes40,NodeMinus00.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p41,GridMinus.atNode 41,GridMinus.atNode 42,NodeMinus00.w41,CompactMinus0032.checked41,CompactMinus0032.small41,CompactMinus0032.nodes41,NodeMinus00.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p42,GridMinus.atNode 42,GridMinus.atNode 43,NodeMinus00.w42,CompactMinus0032.checked42,CompactMinus0032.small42,CompactMinus0032.nodes42,NodeMinus00.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p43,GridMinus.atNode 43,GridMinus.atNode 44,NodeMinus00.w43,CompactMinus0032.checked43,CompactMinus0032.small43,CompactMinus0032.nodes43,NodeMinus00.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p44,GridMinus.atNode 44,GridMinus.atNode 45,NodeMinus00.w44,CompactMinus0032.checked44,CompactMinus0032.small44,CompactMinus0032.nodes44,NodeMinus00.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p45,GridMinus.atNode 45,GridMinus.atNode 46,NodeMinus00.w45,CompactMinus0032.checked45,CompactMinus0032.small45,CompactMinus0032.nodes45,NodeMinus00.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p46,GridMinus.atNode 46,GridMinus.atNode 47,NodeMinus00.w46,CompactMinus0032.checked46,CompactMinus0032.small46,CompactMinus0032.nodes46,NodeMinus00.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0032.p47,GridMinus.atNode 47,GridMinus.atNode 48,NodeMinus00.w47,CompactMinus0032.checked47,CompactMinus0032.small47,CompactMinus0032.nodes47,NodeMinus00.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p48,GridMinus.atNode 48,GridMinus.atNode 49,NodeMinus00.w48,CompactMinus0048.checked48,CompactMinus0048.small48,CompactMinus0048.nodes48,NodeMinus00.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p49,GridMinus.atNode 49,GridMinus.atNode 50,NodeMinus00.w49,CompactMinus0048.checked49,CompactMinus0048.small49,CompactMinus0048.nodes49,NodeMinus00.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p50,GridMinus.atNode 50,GridMinus.atNode 51,NodeMinus00.w50,CompactMinus0048.checked50,CompactMinus0048.small50,CompactMinus0048.nodes50,NodeMinus00.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p51,GridMinus.atNode 51,GridMinus.atNode 52,NodeMinus00.w51,CompactMinus0048.checked51,CompactMinus0048.small51,CompactMinus0048.nodes51,NodeMinus00.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p52,GridMinus.atNode 52,GridMinus.atNode 53,NodeMinus00.w52,CompactMinus0048.checked52,CompactMinus0048.small52,CompactMinus0048.nodes52,NodeMinus00.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p53,GridMinus.atNode 53,GridMinus.atNode 54,NodeMinus00.w53,CompactMinus0048.checked53,CompactMinus0048.small53,CompactMinus0048.nodes53,NodeMinus00.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p54,GridMinus.atNode 54,GridMinus.atNode 55,NodeMinus00.w54,CompactMinus0048.checked54,CompactMinus0048.small54,CompactMinus0048.nodes54,NodeMinus00.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p55,GridMinus.atNode 55,GridMinus.atNode 56,NodeMinus00.w55,CompactMinus0048.checked55,CompactMinus0048.small55,CompactMinus0048.nodes55,NodeMinus00.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p56,GridMinus.atNode 56,GridMinus.atNode 57,NodeMinus00.w56,CompactMinus0048.checked56,CompactMinus0048.small56,CompactMinus0048.nodes56,NodeMinus00.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p57,GridMinus.atNode 57,GridMinus.atNode 58,NodeMinus00.w57,CompactMinus0048.checked57,CompactMinus0048.small57,CompactMinus0048.nodes57,NodeMinus00.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p58,GridMinus.atNode 58,GridMinus.atNode 59,NodeMinus00.w58,CompactMinus0048.checked58,CompactMinus0048.small58,CompactMinus0048.nodes58,NodeMinus00.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p59,GridMinus.atNode 59,GridMinus.atNode 60,NodeMinus00.w59,CompactMinus0048.checked59,CompactMinus0048.small59,CompactMinus0048.nodes59,NodeMinus00.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p60,GridMinus.atNode 60,GridMinus.atNode 61,NodeMinus00.w60,CompactMinus0048.checked60,CompactMinus0048.small60,CompactMinus0048.nodes60,NodeMinus00.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p61,GridMinus.atNode 61,GridMinus.atNode 62,NodeMinus00.w61,CompactMinus0048.checked61,CompactMinus0048.small61,CompactMinus0048.nodes61,NodeMinus00.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p62,GridMinus.atNode 62,GridMinus.atNode 63,NodeMinus00.w62,CompactMinus0048.checked62,CompactMinus0048.small62,CompactMinus0048.nodes62,NodeMinus00.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0048.p63,GridMinus.atNode 63,GridMinus.atNode 64,NodeMinus00.w63,CompactMinus0048.checked63,CompactMinus0048.small63,CompactMinus0048.nodes63,NodeMinus00.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (0+j) ∧
    (atRow j).right=GridMinus.atNode (0+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus00
