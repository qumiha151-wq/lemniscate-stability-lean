import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0000
import SolitonClassification.Rotating.ResetPackedPlus0016
import SolitonClassification.Rotating.ResetPackedPlus0032
import SolitonClassification.Rotating.ResetPackedPlus0048
namespace SolitonClassification.Rotating.DyadicReset.TilePlus00
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p0,GridPlus.atNode 0,GridPlus.atNode 1,NodePlus00.w0,CompactPlus0000.checked0,CompactPlus0000.small0,CompactPlus0000.nodes0,NodePlus00.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p1,GridPlus.atNode 1,GridPlus.atNode 2,NodePlus00.w1,CompactPlus0000.checked1,CompactPlus0000.small1,CompactPlus0000.nodes1,NodePlus00.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p2,GridPlus.atNode 2,GridPlus.atNode 3,NodePlus00.w2,CompactPlus0000.checked2,CompactPlus0000.small2,CompactPlus0000.nodes2,NodePlus00.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p3,GridPlus.atNode 3,GridPlus.atNode 4,NodePlus00.w3,CompactPlus0000.checked3,CompactPlus0000.small3,CompactPlus0000.nodes3,NodePlus00.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p4,GridPlus.atNode 4,GridPlus.atNode 5,NodePlus00.w4,CompactPlus0000.checked4,CompactPlus0000.small4,CompactPlus0000.nodes4,NodePlus00.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p5,GridPlus.atNode 5,GridPlus.atNode 6,NodePlus00.w5,CompactPlus0000.checked5,CompactPlus0000.small5,CompactPlus0000.nodes5,NodePlus00.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p6,GridPlus.atNode 6,GridPlus.atNode 7,NodePlus00.w6,CompactPlus0000.checked6,CompactPlus0000.small6,CompactPlus0000.nodes6,NodePlus00.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p7,GridPlus.atNode 7,GridPlus.atNode 8,NodePlus00.w7,CompactPlus0000.checked7,CompactPlus0000.small7,CompactPlus0000.nodes7,NodePlus00.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p8,GridPlus.atNode 8,GridPlus.atNode 9,NodePlus00.w8,CompactPlus0000.checked8,CompactPlus0000.small8,CompactPlus0000.nodes8,NodePlus00.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p9,GridPlus.atNode 9,GridPlus.atNode 10,NodePlus00.w9,CompactPlus0000.checked9,CompactPlus0000.small9,CompactPlus0000.nodes9,NodePlus00.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p10,GridPlus.atNode 10,GridPlus.atNode 11,NodePlus00.w10,CompactPlus0000.checked10,CompactPlus0000.small10,CompactPlus0000.nodes10,NodePlus00.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p11,GridPlus.atNode 11,GridPlus.atNode 12,NodePlus00.w11,CompactPlus0000.checked11,CompactPlus0000.small11,CompactPlus0000.nodes11,NodePlus00.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p12,GridPlus.atNode 12,GridPlus.atNode 13,NodePlus00.w12,CompactPlus0000.checked12,CompactPlus0000.small12,CompactPlus0000.nodes12,NodePlus00.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p13,GridPlus.atNode 13,GridPlus.atNode 14,NodePlus00.w13,CompactPlus0000.checked13,CompactPlus0000.small13,CompactPlus0000.nodes13,NodePlus00.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p14,GridPlus.atNode 14,GridPlus.atNode 15,NodePlus00.w14,CompactPlus0000.checked14,CompactPlus0000.small14,CompactPlus0000.nodes14,NodePlus00.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p15,GridPlus.atNode 15,GridPlus.atNode 16,NodePlus00.w15,CompactPlus0000.checked15,CompactPlus0000.small15,CompactPlus0000.nodes15,NodePlus00.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p16,GridPlus.atNode 16,GridPlus.atNode 17,NodePlus00.w16,CompactPlus0016.checked16,CompactPlus0016.small16,CompactPlus0016.nodes16,NodePlus00.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p17,GridPlus.atNode 17,GridPlus.atNode 18,NodePlus00.w17,CompactPlus0016.checked17,CompactPlus0016.small17,CompactPlus0016.nodes17,NodePlus00.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p18,GridPlus.atNode 18,GridPlus.atNode 19,NodePlus00.w18,CompactPlus0016.checked18,CompactPlus0016.small18,CompactPlus0016.nodes18,NodePlus00.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p19,GridPlus.atNode 19,GridPlus.atNode 20,NodePlus00.w19,CompactPlus0016.checked19,CompactPlus0016.small19,CompactPlus0016.nodes19,NodePlus00.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p20,GridPlus.atNode 20,GridPlus.atNode 21,NodePlus00.w20,CompactPlus0016.checked20,CompactPlus0016.small20,CompactPlus0016.nodes20,NodePlus00.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p21,GridPlus.atNode 21,GridPlus.atNode 22,NodePlus00.w21,CompactPlus0016.checked21,CompactPlus0016.small21,CompactPlus0016.nodes21,NodePlus00.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p22,GridPlus.atNode 22,GridPlus.atNode 23,NodePlus00.w22,CompactPlus0016.checked22,CompactPlus0016.small22,CompactPlus0016.nodes22,NodePlus00.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p23,GridPlus.atNode 23,GridPlus.atNode 24,NodePlus00.w23,CompactPlus0016.checked23,CompactPlus0016.small23,CompactPlus0016.nodes23,NodePlus00.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p24,GridPlus.atNode 24,GridPlus.atNode 25,NodePlus00.w24,CompactPlus0016.checked24,CompactPlus0016.small24,CompactPlus0016.nodes24,NodePlus00.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p25,GridPlus.atNode 25,GridPlus.atNode 26,NodePlus00.w25,CompactPlus0016.checked25,CompactPlus0016.small25,CompactPlus0016.nodes25,NodePlus00.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p26,GridPlus.atNode 26,GridPlus.atNode 27,NodePlus00.w26,CompactPlus0016.checked26,CompactPlus0016.small26,CompactPlus0016.nodes26,NodePlus00.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p27,GridPlus.atNode 27,GridPlus.atNode 28,NodePlus00.w27,CompactPlus0016.checked27,CompactPlus0016.small27,CompactPlus0016.nodes27,NodePlus00.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p28,GridPlus.atNode 28,GridPlus.atNode 29,NodePlus00.w28,CompactPlus0016.checked28,CompactPlus0016.small28,CompactPlus0016.nodes28,NodePlus00.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p29,GridPlus.atNode 29,GridPlus.atNode 30,NodePlus00.w29,CompactPlus0016.checked29,CompactPlus0016.small29,CompactPlus0016.nodes29,NodePlus00.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p30,GridPlus.atNode 30,GridPlus.atNode 31,NodePlus00.w30,CompactPlus0016.checked30,CompactPlus0016.small30,CompactPlus0016.nodes30,NodePlus00.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0016.p31,GridPlus.atNode 31,GridPlus.atNode 32,NodePlus00.w31,CompactPlus0016.checked31,CompactPlus0016.small31,CompactPlus0016.nodes31,NodePlus00.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p32,GridPlus.atNode 32,GridPlus.atNode 33,NodePlus00.w32,CompactPlus0032.checked32,CompactPlus0032.small32,CompactPlus0032.nodes32,NodePlus00.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p33,GridPlus.atNode 33,GridPlus.atNode 34,NodePlus00.w33,CompactPlus0032.checked33,CompactPlus0032.small33,CompactPlus0032.nodes33,NodePlus00.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p34,GridPlus.atNode 34,GridPlus.atNode 35,NodePlus00.w34,CompactPlus0032.checked34,CompactPlus0032.small34,CompactPlus0032.nodes34,NodePlus00.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p35,GridPlus.atNode 35,GridPlus.atNode 36,NodePlus00.w35,CompactPlus0032.checked35,CompactPlus0032.small35,CompactPlus0032.nodes35,NodePlus00.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p36,GridPlus.atNode 36,GridPlus.atNode 37,NodePlus00.w36,CompactPlus0032.checked36,CompactPlus0032.small36,CompactPlus0032.nodes36,NodePlus00.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p37,GridPlus.atNode 37,GridPlus.atNode 38,NodePlus00.w37,CompactPlus0032.checked37,CompactPlus0032.small37,CompactPlus0032.nodes37,NodePlus00.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p38,GridPlus.atNode 38,GridPlus.atNode 39,NodePlus00.w38,CompactPlus0032.checked38,CompactPlus0032.small38,CompactPlus0032.nodes38,NodePlus00.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p39,GridPlus.atNode 39,GridPlus.atNode 40,NodePlus00.w39,CompactPlus0032.checked39,CompactPlus0032.small39,CompactPlus0032.nodes39,NodePlus00.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p40,GridPlus.atNode 40,GridPlus.atNode 41,NodePlus00.w40,CompactPlus0032.checked40,CompactPlus0032.small40,CompactPlus0032.nodes40,NodePlus00.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p41,GridPlus.atNode 41,GridPlus.atNode 42,NodePlus00.w41,CompactPlus0032.checked41,CompactPlus0032.small41,CompactPlus0032.nodes41,NodePlus00.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p42,GridPlus.atNode 42,GridPlus.atNode 43,NodePlus00.w42,CompactPlus0032.checked42,CompactPlus0032.small42,CompactPlus0032.nodes42,NodePlus00.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p43,GridPlus.atNode 43,GridPlus.atNode 44,NodePlus00.w43,CompactPlus0032.checked43,CompactPlus0032.small43,CompactPlus0032.nodes43,NodePlus00.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p44,GridPlus.atNode 44,GridPlus.atNode 45,NodePlus00.w44,CompactPlus0032.checked44,CompactPlus0032.small44,CompactPlus0032.nodes44,NodePlus00.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p45,GridPlus.atNode 45,GridPlus.atNode 46,NodePlus00.w45,CompactPlus0032.checked45,CompactPlus0032.small45,CompactPlus0032.nodes45,NodePlus00.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p46,GridPlus.atNode 46,GridPlus.atNode 47,NodePlus00.w46,CompactPlus0032.checked46,CompactPlus0032.small46,CompactPlus0032.nodes46,NodePlus00.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0032.p47,GridPlus.atNode 47,GridPlus.atNode 48,NodePlus00.w47,CompactPlus0032.checked47,CompactPlus0032.small47,CompactPlus0032.nodes47,NodePlus00.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p48,GridPlus.atNode 48,GridPlus.atNode 49,NodePlus00.w48,CompactPlus0048.checked48,CompactPlus0048.small48,CompactPlus0048.nodes48,NodePlus00.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p49,GridPlus.atNode 49,GridPlus.atNode 50,NodePlus00.w49,CompactPlus0048.checked49,CompactPlus0048.small49,CompactPlus0048.nodes49,NodePlus00.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p50,GridPlus.atNode 50,GridPlus.atNode 51,NodePlus00.w50,CompactPlus0048.checked50,CompactPlus0048.small50,CompactPlus0048.nodes50,NodePlus00.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p51,GridPlus.atNode 51,GridPlus.atNode 52,NodePlus00.w51,CompactPlus0048.checked51,CompactPlus0048.small51,CompactPlus0048.nodes51,NodePlus00.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p52,GridPlus.atNode 52,GridPlus.atNode 53,NodePlus00.w52,CompactPlus0048.checked52,CompactPlus0048.small52,CompactPlus0048.nodes52,NodePlus00.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p53,GridPlus.atNode 53,GridPlus.atNode 54,NodePlus00.w53,CompactPlus0048.checked53,CompactPlus0048.small53,CompactPlus0048.nodes53,NodePlus00.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p54,GridPlus.atNode 54,GridPlus.atNode 55,NodePlus00.w54,CompactPlus0048.checked54,CompactPlus0048.small54,CompactPlus0048.nodes54,NodePlus00.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p55,GridPlus.atNode 55,GridPlus.atNode 56,NodePlus00.w55,CompactPlus0048.checked55,CompactPlus0048.small55,CompactPlus0048.nodes55,NodePlus00.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p56,GridPlus.atNode 56,GridPlus.atNode 57,NodePlus00.w56,CompactPlus0048.checked56,CompactPlus0048.small56,CompactPlus0048.nodes56,NodePlus00.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p57,GridPlus.atNode 57,GridPlus.atNode 58,NodePlus00.w57,CompactPlus0048.checked57,CompactPlus0048.small57,CompactPlus0048.nodes57,NodePlus00.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p58,GridPlus.atNode 58,GridPlus.atNode 59,NodePlus00.w58,CompactPlus0048.checked58,CompactPlus0048.small58,CompactPlus0048.nodes58,NodePlus00.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p59,GridPlus.atNode 59,GridPlus.atNode 60,NodePlus00.w59,CompactPlus0048.checked59,CompactPlus0048.small59,CompactPlus0048.nodes59,NodePlus00.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p60,GridPlus.atNode 60,GridPlus.atNode 61,NodePlus00.w60,CompactPlus0048.checked60,CompactPlus0048.small60,CompactPlus0048.nodes60,NodePlus00.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p61,GridPlus.atNode 61,GridPlus.atNode 62,NodePlus00.w61,CompactPlus0048.checked61,CompactPlus0048.small61,CompactPlus0048.nodes61,NodePlus00.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p62,GridPlus.atNode 62,GridPlus.atNode 63,NodePlus00.w62,CompactPlus0048.checked62,CompactPlus0048.small62,CompactPlus0048.nodes62,NodePlus00.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0048.p63,GridPlus.atNode 63,GridPlus.atNode 64,NodePlus00.w63,CompactPlus0048.checked63,CompactPlus0048.small63,CompactPlus0048.nodes63,NodePlus00.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (0+j) ∧
    (atRow j).right=GridPlus.atNode (0+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus00
