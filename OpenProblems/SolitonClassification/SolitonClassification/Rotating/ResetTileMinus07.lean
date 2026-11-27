import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0448
import SolitonClassification.Rotating.ResetPackedMinus0464
import SolitonClassification.Rotating.ResetPackedMinus0480
import SolitonClassification.Rotating.ResetPackedMinus0496
namespace SolitonClassification.Rotating.DyadicReset.TileMinus07
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p448,GridMinus.atNode 448,GridMinus.atNode 449,NodeMinus07.w0,CompactMinus0448.checked448,CompactMinus0448.small448,CompactMinus0448.nodes448,NodeMinus07.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p449,GridMinus.atNode 449,GridMinus.atNode 450,NodeMinus07.w1,CompactMinus0448.checked449,CompactMinus0448.small449,CompactMinus0448.nodes449,NodeMinus07.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p450,GridMinus.atNode 450,GridMinus.atNode 451,NodeMinus07.w2,CompactMinus0448.checked450,CompactMinus0448.small450,CompactMinus0448.nodes450,NodeMinus07.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p451,GridMinus.atNode 451,GridMinus.atNode 452,NodeMinus07.w3,CompactMinus0448.checked451,CompactMinus0448.small451,CompactMinus0448.nodes451,NodeMinus07.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p452,GridMinus.atNode 452,GridMinus.atNode 453,NodeMinus07.w4,CompactMinus0448.checked452,CompactMinus0448.small452,CompactMinus0448.nodes452,NodeMinus07.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p453,GridMinus.atNode 453,GridMinus.atNode 454,NodeMinus07.w5,CompactMinus0448.checked453,CompactMinus0448.small453,CompactMinus0448.nodes453,NodeMinus07.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p454,GridMinus.atNode 454,GridMinus.atNode 455,NodeMinus07.w6,CompactMinus0448.checked454,CompactMinus0448.small454,CompactMinus0448.nodes454,NodeMinus07.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p455,GridMinus.atNode 455,GridMinus.atNode 456,NodeMinus07.w7,CompactMinus0448.checked455,CompactMinus0448.small455,CompactMinus0448.nodes455,NodeMinus07.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p456,GridMinus.atNode 456,GridMinus.atNode 457,NodeMinus07.w8,CompactMinus0448.checked456,CompactMinus0448.small456,CompactMinus0448.nodes456,NodeMinus07.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p457,GridMinus.atNode 457,GridMinus.atNode 458,NodeMinus07.w9,CompactMinus0448.checked457,CompactMinus0448.small457,CompactMinus0448.nodes457,NodeMinus07.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p458,GridMinus.atNode 458,GridMinus.atNode 459,NodeMinus07.w10,CompactMinus0448.checked458,CompactMinus0448.small458,CompactMinus0448.nodes458,NodeMinus07.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p459,GridMinus.atNode 459,GridMinus.atNode 460,NodeMinus07.w11,CompactMinus0448.checked459,CompactMinus0448.small459,CompactMinus0448.nodes459,NodeMinus07.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p460,GridMinus.atNode 460,GridMinus.atNode 461,NodeMinus07.w12,CompactMinus0448.checked460,CompactMinus0448.small460,CompactMinus0448.nodes460,NodeMinus07.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p461,GridMinus.atNode 461,GridMinus.atNode 462,NodeMinus07.w13,CompactMinus0448.checked461,CompactMinus0448.small461,CompactMinus0448.nodes461,NodeMinus07.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p462,GridMinus.atNode 462,GridMinus.atNode 463,NodeMinus07.w14,CompactMinus0448.checked462,CompactMinus0448.small462,CompactMinus0448.nodes462,NodeMinus07.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0448.p463,GridMinus.atNode 463,GridMinus.atNode 464,NodeMinus07.w15,CompactMinus0448.checked463,CompactMinus0448.small463,CompactMinus0448.nodes463,NodeMinus07.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p464,GridMinus.atNode 464,GridMinus.atNode 465,NodeMinus07.w16,CompactMinus0464.checked464,CompactMinus0464.small464,CompactMinus0464.nodes464,NodeMinus07.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p465,GridMinus.atNode 465,GridMinus.atNode 466,NodeMinus07.w17,CompactMinus0464.checked465,CompactMinus0464.small465,CompactMinus0464.nodes465,NodeMinus07.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p466,GridMinus.atNode 466,GridMinus.atNode 467,NodeMinus07.w18,CompactMinus0464.checked466,CompactMinus0464.small466,CompactMinus0464.nodes466,NodeMinus07.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p467,GridMinus.atNode 467,GridMinus.atNode 468,NodeMinus07.w19,CompactMinus0464.checked467,CompactMinus0464.small467,CompactMinus0464.nodes467,NodeMinus07.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p468,GridMinus.atNode 468,GridMinus.atNode 469,NodeMinus07.w20,CompactMinus0464.checked468,CompactMinus0464.small468,CompactMinus0464.nodes468,NodeMinus07.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p469,GridMinus.atNode 469,GridMinus.atNode 470,NodeMinus07.w21,CompactMinus0464.checked469,CompactMinus0464.small469,CompactMinus0464.nodes469,NodeMinus07.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p470,GridMinus.atNode 470,GridMinus.atNode 471,NodeMinus07.w22,CompactMinus0464.checked470,CompactMinus0464.small470,CompactMinus0464.nodes470,NodeMinus07.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p471,GridMinus.atNode 471,GridMinus.atNode 472,NodeMinus07.w23,CompactMinus0464.checked471,CompactMinus0464.small471,CompactMinus0464.nodes471,NodeMinus07.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p472,GridMinus.atNode 472,GridMinus.atNode 473,NodeMinus07.w24,CompactMinus0464.checked472,CompactMinus0464.small472,CompactMinus0464.nodes472,NodeMinus07.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p473,GridMinus.atNode 473,GridMinus.atNode 474,NodeMinus07.w25,CompactMinus0464.checked473,CompactMinus0464.small473,CompactMinus0464.nodes473,NodeMinus07.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p474,GridMinus.atNode 474,GridMinus.atNode 475,NodeMinus07.w26,CompactMinus0464.checked474,CompactMinus0464.small474,CompactMinus0464.nodes474,NodeMinus07.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p475,GridMinus.atNode 475,GridMinus.atNode 476,NodeMinus07.w27,CompactMinus0464.checked475,CompactMinus0464.small475,CompactMinus0464.nodes475,NodeMinus07.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p476,GridMinus.atNode 476,GridMinus.atNode 477,NodeMinus07.w28,CompactMinus0464.checked476,CompactMinus0464.small476,CompactMinus0464.nodes476,NodeMinus07.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p477,GridMinus.atNode 477,GridMinus.atNode 478,NodeMinus07.w29,CompactMinus0464.checked477,CompactMinus0464.small477,CompactMinus0464.nodes477,NodeMinus07.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p478,GridMinus.atNode 478,GridMinus.atNode 479,NodeMinus07.w30,CompactMinus0464.checked478,CompactMinus0464.small478,CompactMinus0464.nodes478,NodeMinus07.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0464.p479,GridMinus.atNode 479,GridMinus.atNode 480,NodeMinus07.w31,CompactMinus0464.checked479,CompactMinus0464.small479,CompactMinus0464.nodes479,NodeMinus07.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p480,GridMinus.atNode 480,GridMinus.atNode 481,NodeMinus07.w32,CompactMinus0480.checked480,CompactMinus0480.small480,CompactMinus0480.nodes480,NodeMinus07.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p481,GridMinus.atNode 481,GridMinus.atNode 482,NodeMinus07.w33,CompactMinus0480.checked481,CompactMinus0480.small481,CompactMinus0480.nodes481,NodeMinus07.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p482,GridMinus.atNode 482,GridMinus.atNode 483,NodeMinus07.w34,CompactMinus0480.checked482,CompactMinus0480.small482,CompactMinus0480.nodes482,NodeMinus07.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p483,GridMinus.atNode 483,GridMinus.atNode 484,NodeMinus07.w35,CompactMinus0480.checked483,CompactMinus0480.small483,CompactMinus0480.nodes483,NodeMinus07.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p484,GridMinus.atNode 484,GridMinus.atNode 485,NodeMinus07.w36,CompactMinus0480.checked484,CompactMinus0480.small484,CompactMinus0480.nodes484,NodeMinus07.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p485,GridMinus.atNode 485,GridMinus.atNode 486,NodeMinus07.w37,CompactMinus0480.checked485,CompactMinus0480.small485,CompactMinus0480.nodes485,NodeMinus07.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p486,GridMinus.atNode 486,GridMinus.atNode 487,NodeMinus07.w38,CompactMinus0480.checked486,CompactMinus0480.small486,CompactMinus0480.nodes486,NodeMinus07.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p487,GridMinus.atNode 487,GridMinus.atNode 488,NodeMinus07.w39,CompactMinus0480.checked487,CompactMinus0480.small487,CompactMinus0480.nodes487,NodeMinus07.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p488,GridMinus.atNode 488,GridMinus.atNode 489,NodeMinus07.w40,CompactMinus0480.checked488,CompactMinus0480.small488,CompactMinus0480.nodes488,NodeMinus07.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p489,GridMinus.atNode 489,GridMinus.atNode 490,NodeMinus07.w41,CompactMinus0480.checked489,CompactMinus0480.small489,CompactMinus0480.nodes489,NodeMinus07.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p490,GridMinus.atNode 490,GridMinus.atNode 491,NodeMinus07.w42,CompactMinus0480.checked490,CompactMinus0480.small490,CompactMinus0480.nodes490,NodeMinus07.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p491,GridMinus.atNode 491,GridMinus.atNode 492,NodeMinus07.w43,CompactMinus0480.checked491,CompactMinus0480.small491,CompactMinus0480.nodes491,NodeMinus07.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p492,GridMinus.atNode 492,GridMinus.atNode 493,NodeMinus07.w44,CompactMinus0480.checked492,CompactMinus0480.small492,CompactMinus0480.nodes492,NodeMinus07.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p493,GridMinus.atNode 493,GridMinus.atNode 494,NodeMinus07.w45,CompactMinus0480.checked493,CompactMinus0480.small493,CompactMinus0480.nodes493,NodeMinus07.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p494,GridMinus.atNode 494,GridMinus.atNode 495,NodeMinus07.w46,CompactMinus0480.checked494,CompactMinus0480.small494,CompactMinus0480.nodes494,NodeMinus07.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0480.p495,GridMinus.atNode 495,GridMinus.atNode 496,NodeMinus07.w47,CompactMinus0480.checked495,CompactMinus0480.small495,CompactMinus0480.nodes495,NodeMinus07.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p496,GridMinus.atNode 496,GridMinus.atNode 497,NodeMinus07.w48,CompactMinus0496.checked496,CompactMinus0496.small496,CompactMinus0496.nodes496,NodeMinus07.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p497,GridMinus.atNode 497,GridMinus.atNode 498,NodeMinus07.w49,CompactMinus0496.checked497,CompactMinus0496.small497,CompactMinus0496.nodes497,NodeMinus07.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p498,GridMinus.atNode 498,GridMinus.atNode 499,NodeMinus07.w50,CompactMinus0496.checked498,CompactMinus0496.small498,CompactMinus0496.nodes498,NodeMinus07.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p499,GridMinus.atNode 499,GridMinus.atNode 500,NodeMinus07.w51,CompactMinus0496.checked499,CompactMinus0496.small499,CompactMinus0496.nodes499,NodeMinus07.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p500,GridMinus.atNode 500,GridMinus.atNode 501,NodeMinus07.w52,CompactMinus0496.checked500,CompactMinus0496.small500,CompactMinus0496.nodes500,NodeMinus07.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p501,GridMinus.atNode 501,GridMinus.atNode 502,NodeMinus07.w53,CompactMinus0496.checked501,CompactMinus0496.small501,CompactMinus0496.nodes501,NodeMinus07.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p502,GridMinus.atNode 502,GridMinus.atNode 503,NodeMinus07.w54,CompactMinus0496.checked502,CompactMinus0496.small502,CompactMinus0496.nodes502,NodeMinus07.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p503,GridMinus.atNode 503,GridMinus.atNode 504,NodeMinus07.w55,CompactMinus0496.checked503,CompactMinus0496.small503,CompactMinus0496.nodes503,NodeMinus07.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p504,GridMinus.atNode 504,GridMinus.atNode 505,NodeMinus07.w56,CompactMinus0496.checked504,CompactMinus0496.small504,CompactMinus0496.nodes504,NodeMinus07.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p505,GridMinus.atNode 505,GridMinus.atNode 506,NodeMinus07.w57,CompactMinus0496.checked505,CompactMinus0496.small505,CompactMinus0496.nodes505,NodeMinus07.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p506,GridMinus.atNode 506,GridMinus.atNode 507,NodeMinus07.w58,CompactMinus0496.checked506,CompactMinus0496.small506,CompactMinus0496.nodes506,NodeMinus07.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p507,GridMinus.atNode 507,GridMinus.atNode 508,NodeMinus07.w59,CompactMinus0496.checked507,CompactMinus0496.small507,CompactMinus0496.nodes507,NodeMinus07.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p508,GridMinus.atNode 508,GridMinus.atNode 509,NodeMinus07.w60,CompactMinus0496.checked508,CompactMinus0496.small508,CompactMinus0496.nodes508,NodeMinus07.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p509,GridMinus.atNode 509,GridMinus.atNode 510,NodeMinus07.w61,CompactMinus0496.checked509,CompactMinus0496.small509,CompactMinus0496.nodes509,NodeMinus07.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p510,GridMinus.atNode 510,GridMinus.atNode 511,NodeMinus07.w62,CompactMinus0496.checked510,CompactMinus0496.small510,CompactMinus0496.nodes510,NodeMinus07.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0496.p511,GridMinus.atNode 511,GridMinus.atNode 512,NodeMinus07.w63,CompactMinus0496.checked511,CompactMinus0496.small511,CompactMinus0496.nodes511,NodeMinus07.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (448+j) ∧
    (atRow j).right=GridMinus.atNode (448+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus07
