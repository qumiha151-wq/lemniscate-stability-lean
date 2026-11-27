import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0448
import SolitonClassification.Rotating.ResetPackedPlus0464
import SolitonClassification.Rotating.ResetPackedPlus0480
import SolitonClassification.Rotating.ResetPackedPlus0496
namespace SolitonClassification.Rotating.DyadicReset.TilePlus07
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p448,GridPlus.atNode 448,GridPlus.atNode 449,NodePlus07.w0,CompactPlus0448.checked448,CompactPlus0448.small448,CompactPlus0448.nodes448,NodePlus07.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p449,GridPlus.atNode 449,GridPlus.atNode 450,NodePlus07.w1,CompactPlus0448.checked449,CompactPlus0448.small449,CompactPlus0448.nodes449,NodePlus07.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p450,GridPlus.atNode 450,GridPlus.atNode 451,NodePlus07.w2,CompactPlus0448.checked450,CompactPlus0448.small450,CompactPlus0448.nodes450,NodePlus07.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p451,GridPlus.atNode 451,GridPlus.atNode 452,NodePlus07.w3,CompactPlus0448.checked451,CompactPlus0448.small451,CompactPlus0448.nodes451,NodePlus07.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p452,GridPlus.atNode 452,GridPlus.atNode 453,NodePlus07.w4,CompactPlus0448.checked452,CompactPlus0448.small452,CompactPlus0448.nodes452,NodePlus07.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p453,GridPlus.atNode 453,GridPlus.atNode 454,NodePlus07.w5,CompactPlus0448.checked453,CompactPlus0448.small453,CompactPlus0448.nodes453,NodePlus07.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p454,GridPlus.atNode 454,GridPlus.atNode 455,NodePlus07.w6,CompactPlus0448.checked454,CompactPlus0448.small454,CompactPlus0448.nodes454,NodePlus07.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p455,GridPlus.atNode 455,GridPlus.atNode 456,NodePlus07.w7,CompactPlus0448.checked455,CompactPlus0448.small455,CompactPlus0448.nodes455,NodePlus07.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p456,GridPlus.atNode 456,GridPlus.atNode 457,NodePlus07.w8,CompactPlus0448.checked456,CompactPlus0448.small456,CompactPlus0448.nodes456,NodePlus07.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p457,GridPlus.atNode 457,GridPlus.atNode 458,NodePlus07.w9,CompactPlus0448.checked457,CompactPlus0448.small457,CompactPlus0448.nodes457,NodePlus07.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p458,GridPlus.atNode 458,GridPlus.atNode 459,NodePlus07.w10,CompactPlus0448.checked458,CompactPlus0448.small458,CompactPlus0448.nodes458,NodePlus07.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p459,GridPlus.atNode 459,GridPlus.atNode 460,NodePlus07.w11,CompactPlus0448.checked459,CompactPlus0448.small459,CompactPlus0448.nodes459,NodePlus07.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p460,GridPlus.atNode 460,GridPlus.atNode 461,NodePlus07.w12,CompactPlus0448.checked460,CompactPlus0448.small460,CompactPlus0448.nodes460,NodePlus07.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p461,GridPlus.atNode 461,GridPlus.atNode 462,NodePlus07.w13,CompactPlus0448.checked461,CompactPlus0448.small461,CompactPlus0448.nodes461,NodePlus07.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p462,GridPlus.atNode 462,GridPlus.atNode 463,NodePlus07.w14,CompactPlus0448.checked462,CompactPlus0448.small462,CompactPlus0448.nodes462,NodePlus07.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0448.p463,GridPlus.atNode 463,GridPlus.atNode 464,NodePlus07.w15,CompactPlus0448.checked463,CompactPlus0448.small463,CompactPlus0448.nodes463,NodePlus07.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p464,GridPlus.atNode 464,GridPlus.atNode 465,NodePlus07.w16,CompactPlus0464.checked464,CompactPlus0464.small464,CompactPlus0464.nodes464,NodePlus07.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p465,GridPlus.atNode 465,GridPlus.atNode 466,NodePlus07.w17,CompactPlus0464.checked465,CompactPlus0464.small465,CompactPlus0464.nodes465,NodePlus07.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p466,GridPlus.atNode 466,GridPlus.atNode 467,NodePlus07.w18,CompactPlus0464.checked466,CompactPlus0464.small466,CompactPlus0464.nodes466,NodePlus07.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p467,GridPlus.atNode 467,GridPlus.atNode 468,NodePlus07.w19,CompactPlus0464.checked467,CompactPlus0464.small467,CompactPlus0464.nodes467,NodePlus07.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p468,GridPlus.atNode 468,GridPlus.atNode 469,NodePlus07.w20,CompactPlus0464.checked468,CompactPlus0464.small468,CompactPlus0464.nodes468,NodePlus07.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p469,GridPlus.atNode 469,GridPlus.atNode 470,NodePlus07.w21,CompactPlus0464.checked469,CompactPlus0464.small469,CompactPlus0464.nodes469,NodePlus07.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p470,GridPlus.atNode 470,GridPlus.atNode 471,NodePlus07.w22,CompactPlus0464.checked470,CompactPlus0464.small470,CompactPlus0464.nodes470,NodePlus07.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p471,GridPlus.atNode 471,GridPlus.atNode 472,NodePlus07.w23,CompactPlus0464.checked471,CompactPlus0464.small471,CompactPlus0464.nodes471,NodePlus07.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p472,GridPlus.atNode 472,GridPlus.atNode 473,NodePlus07.w24,CompactPlus0464.checked472,CompactPlus0464.small472,CompactPlus0464.nodes472,NodePlus07.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p473,GridPlus.atNode 473,GridPlus.atNode 474,NodePlus07.w25,CompactPlus0464.checked473,CompactPlus0464.small473,CompactPlus0464.nodes473,NodePlus07.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p474,GridPlus.atNode 474,GridPlus.atNode 475,NodePlus07.w26,CompactPlus0464.checked474,CompactPlus0464.small474,CompactPlus0464.nodes474,NodePlus07.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p475,GridPlus.atNode 475,GridPlus.atNode 476,NodePlus07.w27,CompactPlus0464.checked475,CompactPlus0464.small475,CompactPlus0464.nodes475,NodePlus07.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p476,GridPlus.atNode 476,GridPlus.atNode 477,NodePlus07.w28,CompactPlus0464.checked476,CompactPlus0464.small476,CompactPlus0464.nodes476,NodePlus07.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p477,GridPlus.atNode 477,GridPlus.atNode 478,NodePlus07.w29,CompactPlus0464.checked477,CompactPlus0464.small477,CompactPlus0464.nodes477,NodePlus07.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p478,GridPlus.atNode 478,GridPlus.atNode 479,NodePlus07.w30,CompactPlus0464.checked478,CompactPlus0464.small478,CompactPlus0464.nodes478,NodePlus07.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0464.p479,GridPlus.atNode 479,GridPlus.atNode 480,NodePlus07.w31,CompactPlus0464.checked479,CompactPlus0464.small479,CompactPlus0464.nodes479,NodePlus07.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p480,GridPlus.atNode 480,GridPlus.atNode 481,NodePlus07.w32,CompactPlus0480.checked480,CompactPlus0480.small480,CompactPlus0480.nodes480,NodePlus07.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p481,GridPlus.atNode 481,GridPlus.atNode 482,NodePlus07.w33,CompactPlus0480.checked481,CompactPlus0480.small481,CompactPlus0480.nodes481,NodePlus07.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p482,GridPlus.atNode 482,GridPlus.atNode 483,NodePlus07.w34,CompactPlus0480.checked482,CompactPlus0480.small482,CompactPlus0480.nodes482,NodePlus07.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p483,GridPlus.atNode 483,GridPlus.atNode 484,NodePlus07.w35,CompactPlus0480.checked483,CompactPlus0480.small483,CompactPlus0480.nodes483,NodePlus07.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p484,GridPlus.atNode 484,GridPlus.atNode 485,NodePlus07.w36,CompactPlus0480.checked484,CompactPlus0480.small484,CompactPlus0480.nodes484,NodePlus07.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p485,GridPlus.atNode 485,GridPlus.atNode 486,NodePlus07.w37,CompactPlus0480.checked485,CompactPlus0480.small485,CompactPlus0480.nodes485,NodePlus07.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p486,GridPlus.atNode 486,GridPlus.atNode 487,NodePlus07.w38,CompactPlus0480.checked486,CompactPlus0480.small486,CompactPlus0480.nodes486,NodePlus07.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p487,GridPlus.atNode 487,GridPlus.atNode 488,NodePlus07.w39,CompactPlus0480.checked487,CompactPlus0480.small487,CompactPlus0480.nodes487,NodePlus07.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p488,GridPlus.atNode 488,GridPlus.atNode 489,NodePlus07.w40,CompactPlus0480.checked488,CompactPlus0480.small488,CompactPlus0480.nodes488,NodePlus07.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p489,GridPlus.atNode 489,GridPlus.atNode 490,NodePlus07.w41,CompactPlus0480.checked489,CompactPlus0480.small489,CompactPlus0480.nodes489,NodePlus07.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p490,GridPlus.atNode 490,GridPlus.atNode 491,NodePlus07.w42,CompactPlus0480.checked490,CompactPlus0480.small490,CompactPlus0480.nodes490,NodePlus07.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p491,GridPlus.atNode 491,GridPlus.atNode 492,NodePlus07.w43,CompactPlus0480.checked491,CompactPlus0480.small491,CompactPlus0480.nodes491,NodePlus07.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p492,GridPlus.atNode 492,GridPlus.atNode 493,NodePlus07.w44,CompactPlus0480.checked492,CompactPlus0480.small492,CompactPlus0480.nodes492,NodePlus07.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p493,GridPlus.atNode 493,GridPlus.atNode 494,NodePlus07.w45,CompactPlus0480.checked493,CompactPlus0480.small493,CompactPlus0480.nodes493,NodePlus07.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p494,GridPlus.atNode 494,GridPlus.atNode 495,NodePlus07.w46,CompactPlus0480.checked494,CompactPlus0480.small494,CompactPlus0480.nodes494,NodePlus07.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0480.p495,GridPlus.atNode 495,GridPlus.atNode 496,NodePlus07.w47,CompactPlus0480.checked495,CompactPlus0480.small495,CompactPlus0480.nodes495,NodePlus07.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p496,GridPlus.atNode 496,GridPlus.atNode 497,NodePlus07.w48,CompactPlus0496.checked496,CompactPlus0496.small496,CompactPlus0496.nodes496,NodePlus07.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p497,GridPlus.atNode 497,GridPlus.atNode 498,NodePlus07.w49,CompactPlus0496.checked497,CompactPlus0496.small497,CompactPlus0496.nodes497,NodePlus07.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p498,GridPlus.atNode 498,GridPlus.atNode 499,NodePlus07.w50,CompactPlus0496.checked498,CompactPlus0496.small498,CompactPlus0496.nodes498,NodePlus07.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p499,GridPlus.atNode 499,GridPlus.atNode 500,NodePlus07.w51,CompactPlus0496.checked499,CompactPlus0496.small499,CompactPlus0496.nodes499,NodePlus07.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p500,GridPlus.atNode 500,GridPlus.atNode 501,NodePlus07.w52,CompactPlus0496.checked500,CompactPlus0496.small500,CompactPlus0496.nodes500,NodePlus07.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p501,GridPlus.atNode 501,GridPlus.atNode 502,NodePlus07.w53,CompactPlus0496.checked501,CompactPlus0496.small501,CompactPlus0496.nodes501,NodePlus07.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p502,GridPlus.atNode 502,GridPlus.atNode 503,NodePlus07.w54,CompactPlus0496.checked502,CompactPlus0496.small502,CompactPlus0496.nodes502,NodePlus07.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p503,GridPlus.atNode 503,GridPlus.atNode 504,NodePlus07.w55,CompactPlus0496.checked503,CompactPlus0496.small503,CompactPlus0496.nodes503,NodePlus07.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p504,GridPlus.atNode 504,GridPlus.atNode 505,NodePlus07.w56,CompactPlus0496.checked504,CompactPlus0496.small504,CompactPlus0496.nodes504,NodePlus07.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p505,GridPlus.atNode 505,GridPlus.atNode 506,NodePlus07.w57,CompactPlus0496.checked505,CompactPlus0496.small505,CompactPlus0496.nodes505,NodePlus07.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p506,GridPlus.atNode 506,GridPlus.atNode 507,NodePlus07.w58,CompactPlus0496.checked506,CompactPlus0496.small506,CompactPlus0496.nodes506,NodePlus07.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p507,GridPlus.atNode 507,GridPlus.atNode 508,NodePlus07.w59,CompactPlus0496.checked507,CompactPlus0496.small507,CompactPlus0496.nodes507,NodePlus07.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p508,GridPlus.atNode 508,GridPlus.atNode 509,NodePlus07.w60,CompactPlus0496.checked508,CompactPlus0496.small508,CompactPlus0496.nodes508,NodePlus07.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p509,GridPlus.atNode 509,GridPlus.atNode 510,NodePlus07.w61,CompactPlus0496.checked509,CompactPlus0496.small509,CompactPlus0496.nodes509,NodePlus07.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p510,GridPlus.atNode 510,GridPlus.atNode 511,NodePlus07.w62,CompactPlus0496.checked510,CompactPlus0496.small510,CompactPlus0496.nodes510,NodePlus07.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0496.p511,GridPlus.atNode 511,GridPlus.atNode 512,NodePlus07.w63,CompactPlus0496.checked511,CompactPlus0496.small511,CompactPlus0496.nodes511,NodePlus07.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (448+j) ∧
    (atRow j).right=GridPlus.atNode (448+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus07
