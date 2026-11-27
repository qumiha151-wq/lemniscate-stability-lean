import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0512
import SolitonClassification.Rotating.ResetPackedMinus0528
import SolitonClassification.Rotating.ResetPackedMinus0544
import SolitonClassification.Rotating.ResetPackedMinus0560
namespace SolitonClassification.Rotating.DyadicReset.TileMinus08
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p512,GridMinus.atNode 512,GridMinus.atNode 513,NodeMinus08.w0,CompactMinus0512.checked512,CompactMinus0512.small512,CompactMinus0512.nodes512,NodeMinus08.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p513,GridMinus.atNode 513,GridMinus.atNode 514,NodeMinus08.w1,CompactMinus0512.checked513,CompactMinus0512.small513,CompactMinus0512.nodes513,NodeMinus08.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p514,GridMinus.atNode 514,GridMinus.atNode 515,NodeMinus08.w2,CompactMinus0512.checked514,CompactMinus0512.small514,CompactMinus0512.nodes514,NodeMinus08.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p515,GridMinus.atNode 515,GridMinus.atNode 516,NodeMinus08.w3,CompactMinus0512.checked515,CompactMinus0512.small515,CompactMinus0512.nodes515,NodeMinus08.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p516,GridMinus.atNode 516,GridMinus.atNode 517,NodeMinus08.w4,CompactMinus0512.checked516,CompactMinus0512.small516,CompactMinus0512.nodes516,NodeMinus08.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p517,GridMinus.atNode 517,GridMinus.atNode 518,NodeMinus08.w5,CompactMinus0512.checked517,CompactMinus0512.small517,CompactMinus0512.nodes517,NodeMinus08.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p518,GridMinus.atNode 518,GridMinus.atNode 519,NodeMinus08.w6,CompactMinus0512.checked518,CompactMinus0512.small518,CompactMinus0512.nodes518,NodeMinus08.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p519,GridMinus.atNode 519,GridMinus.atNode 520,NodeMinus08.w7,CompactMinus0512.checked519,CompactMinus0512.small519,CompactMinus0512.nodes519,NodeMinus08.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p520,GridMinus.atNode 520,GridMinus.atNode 521,NodeMinus08.w8,CompactMinus0512.checked520,CompactMinus0512.small520,CompactMinus0512.nodes520,NodeMinus08.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p521,GridMinus.atNode 521,GridMinus.atNode 522,NodeMinus08.w9,CompactMinus0512.checked521,CompactMinus0512.small521,CompactMinus0512.nodes521,NodeMinus08.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p522,GridMinus.atNode 522,GridMinus.atNode 523,NodeMinus08.w10,CompactMinus0512.checked522,CompactMinus0512.small522,CompactMinus0512.nodes522,NodeMinus08.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p523,GridMinus.atNode 523,GridMinus.atNode 524,NodeMinus08.w11,CompactMinus0512.checked523,CompactMinus0512.small523,CompactMinus0512.nodes523,NodeMinus08.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p524,GridMinus.atNode 524,GridMinus.atNode 525,NodeMinus08.w12,CompactMinus0512.checked524,CompactMinus0512.small524,CompactMinus0512.nodes524,NodeMinus08.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p525,GridMinus.atNode 525,GridMinus.atNode 526,NodeMinus08.w13,CompactMinus0512.checked525,CompactMinus0512.small525,CompactMinus0512.nodes525,NodeMinus08.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p526,GridMinus.atNode 526,GridMinus.atNode 527,NodeMinus08.w14,CompactMinus0512.checked526,CompactMinus0512.small526,CompactMinus0512.nodes526,NodeMinus08.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0512.p527,GridMinus.atNode 527,GridMinus.atNode 528,NodeMinus08.w15,CompactMinus0512.checked527,CompactMinus0512.small527,CompactMinus0512.nodes527,NodeMinus08.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p528,GridMinus.atNode 528,GridMinus.atNode 529,NodeMinus08.w16,CompactMinus0528.checked528,CompactMinus0528.small528,CompactMinus0528.nodes528,NodeMinus08.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p529,GridMinus.atNode 529,GridMinus.atNode 530,NodeMinus08.w17,CompactMinus0528.checked529,CompactMinus0528.small529,CompactMinus0528.nodes529,NodeMinus08.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p530,GridMinus.atNode 530,GridMinus.atNode 531,NodeMinus08.w18,CompactMinus0528.checked530,CompactMinus0528.small530,CompactMinus0528.nodes530,NodeMinus08.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p531,GridMinus.atNode 531,GridMinus.atNode 532,NodeMinus08.w19,CompactMinus0528.checked531,CompactMinus0528.small531,CompactMinus0528.nodes531,NodeMinus08.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p532,GridMinus.atNode 532,GridMinus.atNode 533,NodeMinus08.w20,CompactMinus0528.checked532,CompactMinus0528.small532,CompactMinus0528.nodes532,NodeMinus08.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p533,GridMinus.atNode 533,GridMinus.atNode 534,NodeMinus08.w21,CompactMinus0528.checked533,CompactMinus0528.small533,CompactMinus0528.nodes533,NodeMinus08.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p534,GridMinus.atNode 534,GridMinus.atNode 535,NodeMinus08.w22,CompactMinus0528.checked534,CompactMinus0528.small534,CompactMinus0528.nodes534,NodeMinus08.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p535,GridMinus.atNode 535,GridMinus.atNode 536,NodeMinus08.w23,CompactMinus0528.checked535,CompactMinus0528.small535,CompactMinus0528.nodes535,NodeMinus08.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p536,GridMinus.atNode 536,GridMinus.atNode 537,NodeMinus08.w24,CompactMinus0528.checked536,CompactMinus0528.small536,CompactMinus0528.nodes536,NodeMinus08.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p537,GridMinus.atNode 537,GridMinus.atNode 538,NodeMinus08.w25,CompactMinus0528.checked537,CompactMinus0528.small537,CompactMinus0528.nodes537,NodeMinus08.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p538,GridMinus.atNode 538,GridMinus.atNode 539,NodeMinus08.w26,CompactMinus0528.checked538,CompactMinus0528.small538,CompactMinus0528.nodes538,NodeMinus08.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p539,GridMinus.atNode 539,GridMinus.atNode 540,NodeMinus08.w27,CompactMinus0528.checked539,CompactMinus0528.small539,CompactMinus0528.nodes539,NodeMinus08.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p540,GridMinus.atNode 540,GridMinus.atNode 541,NodeMinus08.w28,CompactMinus0528.checked540,CompactMinus0528.small540,CompactMinus0528.nodes540,NodeMinus08.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p541,GridMinus.atNode 541,GridMinus.atNode 542,NodeMinus08.w29,CompactMinus0528.checked541,CompactMinus0528.small541,CompactMinus0528.nodes541,NodeMinus08.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p542,GridMinus.atNode 542,GridMinus.atNode 543,NodeMinus08.w30,CompactMinus0528.checked542,CompactMinus0528.small542,CompactMinus0528.nodes542,NodeMinus08.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0528.p543,GridMinus.atNode 543,GridMinus.atNode 544,NodeMinus08.w31,CompactMinus0528.checked543,CompactMinus0528.small543,CompactMinus0528.nodes543,NodeMinus08.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p544,GridMinus.atNode 544,GridMinus.atNode 545,NodeMinus08.w32,CompactMinus0544.checked544,CompactMinus0544.small544,CompactMinus0544.nodes544,NodeMinus08.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p545,GridMinus.atNode 545,GridMinus.atNode 546,NodeMinus08.w33,CompactMinus0544.checked545,CompactMinus0544.small545,CompactMinus0544.nodes545,NodeMinus08.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p546,GridMinus.atNode 546,GridMinus.atNode 547,NodeMinus08.w34,CompactMinus0544.checked546,CompactMinus0544.small546,CompactMinus0544.nodes546,NodeMinus08.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p547,GridMinus.atNode 547,GridMinus.atNode 548,NodeMinus08.w35,CompactMinus0544.checked547,CompactMinus0544.small547,CompactMinus0544.nodes547,NodeMinus08.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p548,GridMinus.atNode 548,GridMinus.atNode 549,NodeMinus08.w36,CompactMinus0544.checked548,CompactMinus0544.small548,CompactMinus0544.nodes548,NodeMinus08.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p549,GridMinus.atNode 549,GridMinus.atNode 550,NodeMinus08.w37,CompactMinus0544.checked549,CompactMinus0544.small549,CompactMinus0544.nodes549,NodeMinus08.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p550,GridMinus.atNode 550,GridMinus.atNode 551,NodeMinus08.w38,CompactMinus0544.checked550,CompactMinus0544.small550,CompactMinus0544.nodes550,NodeMinus08.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p551,GridMinus.atNode 551,GridMinus.atNode 552,NodeMinus08.w39,CompactMinus0544.checked551,CompactMinus0544.small551,CompactMinus0544.nodes551,NodeMinus08.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p552,GridMinus.atNode 552,GridMinus.atNode 553,NodeMinus08.w40,CompactMinus0544.checked552,CompactMinus0544.small552,CompactMinus0544.nodes552,NodeMinus08.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p553,GridMinus.atNode 553,GridMinus.atNode 554,NodeMinus08.w41,CompactMinus0544.checked553,CompactMinus0544.small553,CompactMinus0544.nodes553,NodeMinus08.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p554,GridMinus.atNode 554,GridMinus.atNode 555,NodeMinus08.w42,CompactMinus0544.checked554,CompactMinus0544.small554,CompactMinus0544.nodes554,NodeMinus08.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p555,GridMinus.atNode 555,GridMinus.atNode 556,NodeMinus08.w43,CompactMinus0544.checked555,CompactMinus0544.small555,CompactMinus0544.nodes555,NodeMinus08.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p556,GridMinus.atNode 556,GridMinus.atNode 557,NodeMinus08.w44,CompactMinus0544.checked556,CompactMinus0544.small556,CompactMinus0544.nodes556,NodeMinus08.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p557,GridMinus.atNode 557,GridMinus.atNode 558,NodeMinus08.w45,CompactMinus0544.checked557,CompactMinus0544.small557,CompactMinus0544.nodes557,NodeMinus08.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p558,GridMinus.atNode 558,GridMinus.atNode 559,NodeMinus08.w46,CompactMinus0544.checked558,CompactMinus0544.small558,CompactMinus0544.nodes558,NodeMinus08.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0544.p559,GridMinus.atNode 559,GridMinus.atNode 560,NodeMinus08.w47,CompactMinus0544.checked559,CompactMinus0544.small559,CompactMinus0544.nodes559,NodeMinus08.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p560,GridMinus.atNode 560,GridMinus.atNode 561,NodeMinus08.w48,CompactMinus0560.checked560,CompactMinus0560.small560,CompactMinus0560.nodes560,NodeMinus08.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p561,GridMinus.atNode 561,GridMinus.atNode 562,NodeMinus08.w49,CompactMinus0560.checked561,CompactMinus0560.small561,CompactMinus0560.nodes561,NodeMinus08.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p562,GridMinus.atNode 562,GridMinus.atNode 563,NodeMinus08.w50,CompactMinus0560.checked562,CompactMinus0560.small562,CompactMinus0560.nodes562,NodeMinus08.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p563,GridMinus.atNode 563,GridMinus.atNode 564,NodeMinus08.w51,CompactMinus0560.checked563,CompactMinus0560.small563,CompactMinus0560.nodes563,NodeMinus08.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p564,GridMinus.atNode 564,GridMinus.atNode 565,NodeMinus08.w52,CompactMinus0560.checked564,CompactMinus0560.small564,CompactMinus0560.nodes564,NodeMinus08.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p565,GridMinus.atNode 565,GridMinus.atNode 566,NodeMinus08.w53,CompactMinus0560.checked565,CompactMinus0560.small565,CompactMinus0560.nodes565,NodeMinus08.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p566,GridMinus.atNode 566,GridMinus.atNode 567,NodeMinus08.w54,CompactMinus0560.checked566,CompactMinus0560.small566,CompactMinus0560.nodes566,NodeMinus08.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p567,GridMinus.atNode 567,GridMinus.atNode 568,NodeMinus08.w55,CompactMinus0560.checked567,CompactMinus0560.small567,CompactMinus0560.nodes567,NodeMinus08.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p568,GridMinus.atNode 568,GridMinus.atNode 569,NodeMinus08.w56,CompactMinus0560.checked568,CompactMinus0560.small568,CompactMinus0560.nodes568,NodeMinus08.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p569,GridMinus.atNode 569,GridMinus.atNode 570,NodeMinus08.w57,CompactMinus0560.checked569,CompactMinus0560.small569,CompactMinus0560.nodes569,NodeMinus08.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p570,GridMinus.atNode 570,GridMinus.atNode 571,NodeMinus08.w58,CompactMinus0560.checked570,CompactMinus0560.small570,CompactMinus0560.nodes570,NodeMinus08.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p571,GridMinus.atNode 571,GridMinus.atNode 572,NodeMinus08.w59,CompactMinus0560.checked571,CompactMinus0560.small571,CompactMinus0560.nodes571,NodeMinus08.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p572,GridMinus.atNode 572,GridMinus.atNode 573,NodeMinus08.w60,CompactMinus0560.checked572,CompactMinus0560.small572,CompactMinus0560.nodes572,NodeMinus08.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p573,GridMinus.atNode 573,GridMinus.atNode 574,NodeMinus08.w61,CompactMinus0560.checked573,CompactMinus0560.small573,CompactMinus0560.nodes573,NodeMinus08.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p574,GridMinus.atNode 574,GridMinus.atNode 575,NodeMinus08.w62,CompactMinus0560.checked574,CompactMinus0560.small574,CompactMinus0560.nodes574,NodeMinus08.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0560.p575,GridMinus.atNode 575,GridMinus.atNode 576,NodeMinus08.w63,CompactMinus0560.checked575,CompactMinus0560.small575,CompactMinus0560.nodes575,NodeMinus08.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (512+j) ∧
    (atRow j).right=GridMinus.atNode (512+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus08
