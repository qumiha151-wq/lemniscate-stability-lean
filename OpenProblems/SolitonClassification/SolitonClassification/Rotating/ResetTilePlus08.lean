import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0512
import SolitonClassification.Rotating.ResetPackedPlus0528
import SolitonClassification.Rotating.ResetPackedPlus0544
import SolitonClassification.Rotating.ResetPackedPlus0560
namespace SolitonClassification.Rotating.DyadicReset.TilePlus08
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p512,GridPlus.atNode 512,GridPlus.atNode 513,NodePlus08.w0,CompactPlus0512.checked512,CompactPlus0512.small512,CompactPlus0512.nodes512,NodePlus08.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p513,GridPlus.atNode 513,GridPlus.atNode 514,NodePlus08.w1,CompactPlus0512.checked513,CompactPlus0512.small513,CompactPlus0512.nodes513,NodePlus08.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p514,GridPlus.atNode 514,GridPlus.atNode 515,NodePlus08.w2,CompactPlus0512.checked514,CompactPlus0512.small514,CompactPlus0512.nodes514,NodePlus08.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p515,GridPlus.atNode 515,GridPlus.atNode 516,NodePlus08.w3,CompactPlus0512.checked515,CompactPlus0512.small515,CompactPlus0512.nodes515,NodePlus08.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p516,GridPlus.atNode 516,GridPlus.atNode 517,NodePlus08.w4,CompactPlus0512.checked516,CompactPlus0512.small516,CompactPlus0512.nodes516,NodePlus08.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p517,GridPlus.atNode 517,GridPlus.atNode 518,NodePlus08.w5,CompactPlus0512.checked517,CompactPlus0512.small517,CompactPlus0512.nodes517,NodePlus08.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p518,GridPlus.atNode 518,GridPlus.atNode 519,NodePlus08.w6,CompactPlus0512.checked518,CompactPlus0512.small518,CompactPlus0512.nodes518,NodePlus08.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p519,GridPlus.atNode 519,GridPlus.atNode 520,NodePlus08.w7,CompactPlus0512.checked519,CompactPlus0512.small519,CompactPlus0512.nodes519,NodePlus08.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p520,GridPlus.atNode 520,GridPlus.atNode 521,NodePlus08.w8,CompactPlus0512.checked520,CompactPlus0512.small520,CompactPlus0512.nodes520,NodePlus08.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p521,GridPlus.atNode 521,GridPlus.atNode 522,NodePlus08.w9,CompactPlus0512.checked521,CompactPlus0512.small521,CompactPlus0512.nodes521,NodePlus08.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p522,GridPlus.atNode 522,GridPlus.atNode 523,NodePlus08.w10,CompactPlus0512.checked522,CompactPlus0512.small522,CompactPlus0512.nodes522,NodePlus08.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p523,GridPlus.atNode 523,GridPlus.atNode 524,NodePlus08.w11,CompactPlus0512.checked523,CompactPlus0512.small523,CompactPlus0512.nodes523,NodePlus08.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p524,GridPlus.atNode 524,GridPlus.atNode 525,NodePlus08.w12,CompactPlus0512.checked524,CompactPlus0512.small524,CompactPlus0512.nodes524,NodePlus08.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p525,GridPlus.atNode 525,GridPlus.atNode 526,NodePlus08.w13,CompactPlus0512.checked525,CompactPlus0512.small525,CompactPlus0512.nodes525,NodePlus08.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p526,GridPlus.atNode 526,GridPlus.atNode 527,NodePlus08.w14,CompactPlus0512.checked526,CompactPlus0512.small526,CompactPlus0512.nodes526,NodePlus08.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0512.p527,GridPlus.atNode 527,GridPlus.atNode 528,NodePlus08.w15,CompactPlus0512.checked527,CompactPlus0512.small527,CompactPlus0512.nodes527,NodePlus08.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p528,GridPlus.atNode 528,GridPlus.atNode 529,NodePlus08.w16,CompactPlus0528.checked528,CompactPlus0528.small528,CompactPlus0528.nodes528,NodePlus08.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p529,GridPlus.atNode 529,GridPlus.atNode 530,NodePlus08.w17,CompactPlus0528.checked529,CompactPlus0528.small529,CompactPlus0528.nodes529,NodePlus08.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p530,GridPlus.atNode 530,GridPlus.atNode 531,NodePlus08.w18,CompactPlus0528.checked530,CompactPlus0528.small530,CompactPlus0528.nodes530,NodePlus08.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p531,GridPlus.atNode 531,GridPlus.atNode 532,NodePlus08.w19,CompactPlus0528.checked531,CompactPlus0528.small531,CompactPlus0528.nodes531,NodePlus08.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p532,GridPlus.atNode 532,GridPlus.atNode 533,NodePlus08.w20,CompactPlus0528.checked532,CompactPlus0528.small532,CompactPlus0528.nodes532,NodePlus08.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p533,GridPlus.atNode 533,GridPlus.atNode 534,NodePlus08.w21,CompactPlus0528.checked533,CompactPlus0528.small533,CompactPlus0528.nodes533,NodePlus08.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p534,GridPlus.atNode 534,GridPlus.atNode 535,NodePlus08.w22,CompactPlus0528.checked534,CompactPlus0528.small534,CompactPlus0528.nodes534,NodePlus08.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p535,GridPlus.atNode 535,GridPlus.atNode 536,NodePlus08.w23,CompactPlus0528.checked535,CompactPlus0528.small535,CompactPlus0528.nodes535,NodePlus08.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p536,GridPlus.atNode 536,GridPlus.atNode 537,NodePlus08.w24,CompactPlus0528.checked536,CompactPlus0528.small536,CompactPlus0528.nodes536,NodePlus08.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p537,GridPlus.atNode 537,GridPlus.atNode 538,NodePlus08.w25,CompactPlus0528.checked537,CompactPlus0528.small537,CompactPlus0528.nodes537,NodePlus08.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p538,GridPlus.atNode 538,GridPlus.atNode 539,NodePlus08.w26,CompactPlus0528.checked538,CompactPlus0528.small538,CompactPlus0528.nodes538,NodePlus08.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p539,GridPlus.atNode 539,GridPlus.atNode 540,NodePlus08.w27,CompactPlus0528.checked539,CompactPlus0528.small539,CompactPlus0528.nodes539,NodePlus08.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p540,GridPlus.atNode 540,GridPlus.atNode 541,NodePlus08.w28,CompactPlus0528.checked540,CompactPlus0528.small540,CompactPlus0528.nodes540,NodePlus08.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p541,GridPlus.atNode 541,GridPlus.atNode 542,NodePlus08.w29,CompactPlus0528.checked541,CompactPlus0528.small541,CompactPlus0528.nodes541,NodePlus08.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p542,GridPlus.atNode 542,GridPlus.atNode 543,NodePlus08.w30,CompactPlus0528.checked542,CompactPlus0528.small542,CompactPlus0528.nodes542,NodePlus08.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0528.p543,GridPlus.atNode 543,GridPlus.atNode 544,NodePlus08.w31,CompactPlus0528.checked543,CompactPlus0528.small543,CompactPlus0528.nodes543,NodePlus08.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p544,GridPlus.atNode 544,GridPlus.atNode 545,NodePlus08.w32,CompactPlus0544.checked544,CompactPlus0544.small544,CompactPlus0544.nodes544,NodePlus08.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p545,GridPlus.atNode 545,GridPlus.atNode 546,NodePlus08.w33,CompactPlus0544.checked545,CompactPlus0544.small545,CompactPlus0544.nodes545,NodePlus08.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p546,GridPlus.atNode 546,GridPlus.atNode 547,NodePlus08.w34,CompactPlus0544.checked546,CompactPlus0544.small546,CompactPlus0544.nodes546,NodePlus08.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p547,GridPlus.atNode 547,GridPlus.atNode 548,NodePlus08.w35,CompactPlus0544.checked547,CompactPlus0544.small547,CompactPlus0544.nodes547,NodePlus08.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p548,GridPlus.atNode 548,GridPlus.atNode 549,NodePlus08.w36,CompactPlus0544.checked548,CompactPlus0544.small548,CompactPlus0544.nodes548,NodePlus08.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p549,GridPlus.atNode 549,GridPlus.atNode 550,NodePlus08.w37,CompactPlus0544.checked549,CompactPlus0544.small549,CompactPlus0544.nodes549,NodePlus08.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p550,GridPlus.atNode 550,GridPlus.atNode 551,NodePlus08.w38,CompactPlus0544.checked550,CompactPlus0544.small550,CompactPlus0544.nodes550,NodePlus08.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p551,GridPlus.atNode 551,GridPlus.atNode 552,NodePlus08.w39,CompactPlus0544.checked551,CompactPlus0544.small551,CompactPlus0544.nodes551,NodePlus08.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p552,GridPlus.atNode 552,GridPlus.atNode 553,NodePlus08.w40,CompactPlus0544.checked552,CompactPlus0544.small552,CompactPlus0544.nodes552,NodePlus08.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p553,GridPlus.atNode 553,GridPlus.atNode 554,NodePlus08.w41,CompactPlus0544.checked553,CompactPlus0544.small553,CompactPlus0544.nodes553,NodePlus08.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p554,GridPlus.atNode 554,GridPlus.atNode 555,NodePlus08.w42,CompactPlus0544.checked554,CompactPlus0544.small554,CompactPlus0544.nodes554,NodePlus08.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p555,GridPlus.atNode 555,GridPlus.atNode 556,NodePlus08.w43,CompactPlus0544.checked555,CompactPlus0544.small555,CompactPlus0544.nodes555,NodePlus08.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p556,GridPlus.atNode 556,GridPlus.atNode 557,NodePlus08.w44,CompactPlus0544.checked556,CompactPlus0544.small556,CompactPlus0544.nodes556,NodePlus08.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p557,GridPlus.atNode 557,GridPlus.atNode 558,NodePlus08.w45,CompactPlus0544.checked557,CompactPlus0544.small557,CompactPlus0544.nodes557,NodePlus08.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p558,GridPlus.atNode 558,GridPlus.atNode 559,NodePlus08.w46,CompactPlus0544.checked558,CompactPlus0544.small558,CompactPlus0544.nodes558,NodePlus08.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0544.p559,GridPlus.atNode 559,GridPlus.atNode 560,NodePlus08.w47,CompactPlus0544.checked559,CompactPlus0544.small559,CompactPlus0544.nodes559,NodePlus08.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p560,GridPlus.atNode 560,GridPlus.atNode 561,NodePlus08.w48,CompactPlus0560.checked560,CompactPlus0560.small560,CompactPlus0560.nodes560,NodePlus08.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p561,GridPlus.atNode 561,GridPlus.atNode 562,NodePlus08.w49,CompactPlus0560.checked561,CompactPlus0560.small561,CompactPlus0560.nodes561,NodePlus08.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p562,GridPlus.atNode 562,GridPlus.atNode 563,NodePlus08.w50,CompactPlus0560.checked562,CompactPlus0560.small562,CompactPlus0560.nodes562,NodePlus08.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p563,GridPlus.atNode 563,GridPlus.atNode 564,NodePlus08.w51,CompactPlus0560.checked563,CompactPlus0560.small563,CompactPlus0560.nodes563,NodePlus08.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p564,GridPlus.atNode 564,GridPlus.atNode 565,NodePlus08.w52,CompactPlus0560.checked564,CompactPlus0560.small564,CompactPlus0560.nodes564,NodePlus08.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p565,GridPlus.atNode 565,GridPlus.atNode 566,NodePlus08.w53,CompactPlus0560.checked565,CompactPlus0560.small565,CompactPlus0560.nodes565,NodePlus08.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p566,GridPlus.atNode 566,GridPlus.atNode 567,NodePlus08.w54,CompactPlus0560.checked566,CompactPlus0560.small566,CompactPlus0560.nodes566,NodePlus08.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p567,GridPlus.atNode 567,GridPlus.atNode 568,NodePlus08.w55,CompactPlus0560.checked567,CompactPlus0560.small567,CompactPlus0560.nodes567,NodePlus08.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p568,GridPlus.atNode 568,GridPlus.atNode 569,NodePlus08.w56,CompactPlus0560.checked568,CompactPlus0560.small568,CompactPlus0560.nodes568,NodePlus08.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p569,GridPlus.atNode 569,GridPlus.atNode 570,NodePlus08.w57,CompactPlus0560.checked569,CompactPlus0560.small569,CompactPlus0560.nodes569,NodePlus08.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p570,GridPlus.atNode 570,GridPlus.atNode 571,NodePlus08.w58,CompactPlus0560.checked570,CompactPlus0560.small570,CompactPlus0560.nodes570,NodePlus08.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p571,GridPlus.atNode 571,GridPlus.atNode 572,NodePlus08.w59,CompactPlus0560.checked571,CompactPlus0560.small571,CompactPlus0560.nodes571,NodePlus08.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p572,GridPlus.atNode 572,GridPlus.atNode 573,NodePlus08.w60,CompactPlus0560.checked572,CompactPlus0560.small572,CompactPlus0560.nodes572,NodePlus08.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p573,GridPlus.atNode 573,GridPlus.atNode 574,NodePlus08.w61,CompactPlus0560.checked573,CompactPlus0560.small573,CompactPlus0560.nodes573,NodePlus08.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p574,GridPlus.atNode 574,GridPlus.atNode 575,NodePlus08.w62,CompactPlus0560.checked574,CompactPlus0560.small574,CompactPlus0560.nodes574,NodePlus08.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0560.p575,GridPlus.atNode 575,GridPlus.atNode 576,NodePlus08.w63,CompactPlus0560.checked575,CompactPlus0560.small575,CompactPlus0560.nodes575,NodePlus08.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (512+j) ∧
    (atRow j).right=GridPlus.atNode (512+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus08
