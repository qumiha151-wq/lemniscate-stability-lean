import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0384
import SolitonClassification.Rotating.ResetPackedPlus0400
import SolitonClassification.Rotating.ResetPackedPlus0416
import SolitonClassification.Rotating.ResetPackedPlus0432
namespace SolitonClassification.Rotating.DyadicReset.TilePlus06
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p384,GridPlus.atNode 384,GridPlus.atNode 385,NodePlus06.w0,CompactPlus0384.checked384,CompactPlus0384.small384,CompactPlus0384.nodes384,NodePlus06.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p385,GridPlus.atNode 385,GridPlus.atNode 386,NodePlus06.w1,CompactPlus0384.checked385,CompactPlus0384.small385,CompactPlus0384.nodes385,NodePlus06.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p386,GridPlus.atNode 386,GridPlus.atNode 387,NodePlus06.w2,CompactPlus0384.checked386,CompactPlus0384.small386,CompactPlus0384.nodes386,NodePlus06.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p387,GridPlus.atNode 387,GridPlus.atNode 388,NodePlus06.w3,CompactPlus0384.checked387,CompactPlus0384.small387,CompactPlus0384.nodes387,NodePlus06.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p388,GridPlus.atNode 388,GridPlus.atNode 389,NodePlus06.w4,CompactPlus0384.checked388,CompactPlus0384.small388,CompactPlus0384.nodes388,NodePlus06.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p389,GridPlus.atNode 389,GridPlus.atNode 390,NodePlus06.w5,CompactPlus0384.checked389,CompactPlus0384.small389,CompactPlus0384.nodes389,NodePlus06.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p390,GridPlus.atNode 390,GridPlus.atNode 391,NodePlus06.w6,CompactPlus0384.checked390,CompactPlus0384.small390,CompactPlus0384.nodes390,NodePlus06.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p391,GridPlus.atNode 391,GridPlus.atNode 392,NodePlus06.w7,CompactPlus0384.checked391,CompactPlus0384.small391,CompactPlus0384.nodes391,NodePlus06.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p392,GridPlus.atNode 392,GridPlus.atNode 393,NodePlus06.w8,CompactPlus0384.checked392,CompactPlus0384.small392,CompactPlus0384.nodes392,NodePlus06.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p393,GridPlus.atNode 393,GridPlus.atNode 394,NodePlus06.w9,CompactPlus0384.checked393,CompactPlus0384.small393,CompactPlus0384.nodes393,NodePlus06.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p394,GridPlus.atNode 394,GridPlus.atNode 395,NodePlus06.w10,CompactPlus0384.checked394,CompactPlus0384.small394,CompactPlus0384.nodes394,NodePlus06.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p395,GridPlus.atNode 395,GridPlus.atNode 396,NodePlus06.w11,CompactPlus0384.checked395,CompactPlus0384.small395,CompactPlus0384.nodes395,NodePlus06.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p396,GridPlus.atNode 396,GridPlus.atNode 397,NodePlus06.w12,CompactPlus0384.checked396,CompactPlus0384.small396,CompactPlus0384.nodes396,NodePlus06.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p397,GridPlus.atNode 397,GridPlus.atNode 398,NodePlus06.w13,CompactPlus0384.checked397,CompactPlus0384.small397,CompactPlus0384.nodes397,NodePlus06.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p398,GridPlus.atNode 398,GridPlus.atNode 399,NodePlus06.w14,CompactPlus0384.checked398,CompactPlus0384.small398,CompactPlus0384.nodes398,NodePlus06.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0384.p399,GridPlus.atNode 399,GridPlus.atNode 400,NodePlus06.w15,CompactPlus0384.checked399,CompactPlus0384.small399,CompactPlus0384.nodes399,NodePlus06.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p400,GridPlus.atNode 400,GridPlus.atNode 401,NodePlus06.w16,CompactPlus0400.checked400,CompactPlus0400.small400,CompactPlus0400.nodes400,NodePlus06.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p401,GridPlus.atNode 401,GridPlus.atNode 402,NodePlus06.w17,CompactPlus0400.checked401,CompactPlus0400.small401,CompactPlus0400.nodes401,NodePlus06.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p402,GridPlus.atNode 402,GridPlus.atNode 403,NodePlus06.w18,CompactPlus0400.checked402,CompactPlus0400.small402,CompactPlus0400.nodes402,NodePlus06.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p403,GridPlus.atNode 403,GridPlus.atNode 404,NodePlus06.w19,CompactPlus0400.checked403,CompactPlus0400.small403,CompactPlus0400.nodes403,NodePlus06.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p404,GridPlus.atNode 404,GridPlus.atNode 405,NodePlus06.w20,CompactPlus0400.checked404,CompactPlus0400.small404,CompactPlus0400.nodes404,NodePlus06.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p405,GridPlus.atNode 405,GridPlus.atNode 406,NodePlus06.w21,CompactPlus0400.checked405,CompactPlus0400.small405,CompactPlus0400.nodes405,NodePlus06.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p406,GridPlus.atNode 406,GridPlus.atNode 407,NodePlus06.w22,CompactPlus0400.checked406,CompactPlus0400.small406,CompactPlus0400.nodes406,NodePlus06.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p407,GridPlus.atNode 407,GridPlus.atNode 408,NodePlus06.w23,CompactPlus0400.checked407,CompactPlus0400.small407,CompactPlus0400.nodes407,NodePlus06.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p408,GridPlus.atNode 408,GridPlus.atNode 409,NodePlus06.w24,CompactPlus0400.checked408,CompactPlus0400.small408,CompactPlus0400.nodes408,NodePlus06.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p409,GridPlus.atNode 409,GridPlus.atNode 410,NodePlus06.w25,CompactPlus0400.checked409,CompactPlus0400.small409,CompactPlus0400.nodes409,NodePlus06.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p410,GridPlus.atNode 410,GridPlus.atNode 411,NodePlus06.w26,CompactPlus0400.checked410,CompactPlus0400.small410,CompactPlus0400.nodes410,NodePlus06.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p411,GridPlus.atNode 411,GridPlus.atNode 412,NodePlus06.w27,CompactPlus0400.checked411,CompactPlus0400.small411,CompactPlus0400.nodes411,NodePlus06.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p412,GridPlus.atNode 412,GridPlus.atNode 413,NodePlus06.w28,CompactPlus0400.checked412,CompactPlus0400.small412,CompactPlus0400.nodes412,NodePlus06.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p413,GridPlus.atNode 413,GridPlus.atNode 414,NodePlus06.w29,CompactPlus0400.checked413,CompactPlus0400.small413,CompactPlus0400.nodes413,NodePlus06.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p414,GridPlus.atNode 414,GridPlus.atNode 415,NodePlus06.w30,CompactPlus0400.checked414,CompactPlus0400.small414,CompactPlus0400.nodes414,NodePlus06.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0400.p415,GridPlus.atNode 415,GridPlus.atNode 416,NodePlus06.w31,CompactPlus0400.checked415,CompactPlus0400.small415,CompactPlus0400.nodes415,NodePlus06.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p416,GridPlus.atNode 416,GridPlus.atNode 417,NodePlus06.w32,CompactPlus0416.checked416,CompactPlus0416.small416,CompactPlus0416.nodes416,NodePlus06.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p417,GridPlus.atNode 417,GridPlus.atNode 418,NodePlus06.w33,CompactPlus0416.checked417,CompactPlus0416.small417,CompactPlus0416.nodes417,NodePlus06.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p418,GridPlus.atNode 418,GridPlus.atNode 419,NodePlus06.w34,CompactPlus0416.checked418,CompactPlus0416.small418,CompactPlus0416.nodes418,NodePlus06.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p419,GridPlus.atNode 419,GridPlus.atNode 420,NodePlus06.w35,CompactPlus0416.checked419,CompactPlus0416.small419,CompactPlus0416.nodes419,NodePlus06.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p420,GridPlus.atNode 420,GridPlus.atNode 421,NodePlus06.w36,CompactPlus0416.checked420,CompactPlus0416.small420,CompactPlus0416.nodes420,NodePlus06.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p421,GridPlus.atNode 421,GridPlus.atNode 422,NodePlus06.w37,CompactPlus0416.checked421,CompactPlus0416.small421,CompactPlus0416.nodes421,NodePlus06.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p422,GridPlus.atNode 422,GridPlus.atNode 423,NodePlus06.w38,CompactPlus0416.checked422,CompactPlus0416.small422,CompactPlus0416.nodes422,NodePlus06.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p423,GridPlus.atNode 423,GridPlus.atNode 424,NodePlus06.w39,CompactPlus0416.checked423,CompactPlus0416.small423,CompactPlus0416.nodes423,NodePlus06.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p424,GridPlus.atNode 424,GridPlus.atNode 425,NodePlus06.w40,CompactPlus0416.checked424,CompactPlus0416.small424,CompactPlus0416.nodes424,NodePlus06.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p425,GridPlus.atNode 425,GridPlus.atNode 426,NodePlus06.w41,CompactPlus0416.checked425,CompactPlus0416.small425,CompactPlus0416.nodes425,NodePlus06.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p426,GridPlus.atNode 426,GridPlus.atNode 427,NodePlus06.w42,CompactPlus0416.checked426,CompactPlus0416.small426,CompactPlus0416.nodes426,NodePlus06.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p427,GridPlus.atNode 427,GridPlus.atNode 428,NodePlus06.w43,CompactPlus0416.checked427,CompactPlus0416.small427,CompactPlus0416.nodes427,NodePlus06.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p428,GridPlus.atNode 428,GridPlus.atNode 429,NodePlus06.w44,CompactPlus0416.checked428,CompactPlus0416.small428,CompactPlus0416.nodes428,NodePlus06.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p429,GridPlus.atNode 429,GridPlus.atNode 430,NodePlus06.w45,CompactPlus0416.checked429,CompactPlus0416.small429,CompactPlus0416.nodes429,NodePlus06.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p430,GridPlus.atNode 430,GridPlus.atNode 431,NodePlus06.w46,CompactPlus0416.checked430,CompactPlus0416.small430,CompactPlus0416.nodes430,NodePlus06.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0416.p431,GridPlus.atNode 431,GridPlus.atNode 432,NodePlus06.w47,CompactPlus0416.checked431,CompactPlus0416.small431,CompactPlus0416.nodes431,NodePlus06.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p432,GridPlus.atNode 432,GridPlus.atNode 433,NodePlus06.w48,CompactPlus0432.checked432,CompactPlus0432.small432,CompactPlus0432.nodes432,NodePlus06.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p433,GridPlus.atNode 433,GridPlus.atNode 434,NodePlus06.w49,CompactPlus0432.checked433,CompactPlus0432.small433,CompactPlus0432.nodes433,NodePlus06.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p434,GridPlus.atNode 434,GridPlus.atNode 435,NodePlus06.w50,CompactPlus0432.checked434,CompactPlus0432.small434,CompactPlus0432.nodes434,NodePlus06.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p435,GridPlus.atNode 435,GridPlus.atNode 436,NodePlus06.w51,CompactPlus0432.checked435,CompactPlus0432.small435,CompactPlus0432.nodes435,NodePlus06.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p436,GridPlus.atNode 436,GridPlus.atNode 437,NodePlus06.w52,CompactPlus0432.checked436,CompactPlus0432.small436,CompactPlus0432.nodes436,NodePlus06.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p437,GridPlus.atNode 437,GridPlus.atNode 438,NodePlus06.w53,CompactPlus0432.checked437,CompactPlus0432.small437,CompactPlus0432.nodes437,NodePlus06.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p438,GridPlus.atNode 438,GridPlus.atNode 439,NodePlus06.w54,CompactPlus0432.checked438,CompactPlus0432.small438,CompactPlus0432.nodes438,NodePlus06.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p439,GridPlus.atNode 439,GridPlus.atNode 440,NodePlus06.w55,CompactPlus0432.checked439,CompactPlus0432.small439,CompactPlus0432.nodes439,NodePlus06.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p440,GridPlus.atNode 440,GridPlus.atNode 441,NodePlus06.w56,CompactPlus0432.checked440,CompactPlus0432.small440,CompactPlus0432.nodes440,NodePlus06.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p441,GridPlus.atNode 441,GridPlus.atNode 442,NodePlus06.w57,CompactPlus0432.checked441,CompactPlus0432.small441,CompactPlus0432.nodes441,NodePlus06.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p442,GridPlus.atNode 442,GridPlus.atNode 443,NodePlus06.w58,CompactPlus0432.checked442,CompactPlus0432.small442,CompactPlus0432.nodes442,NodePlus06.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p443,GridPlus.atNode 443,GridPlus.atNode 444,NodePlus06.w59,CompactPlus0432.checked443,CompactPlus0432.small443,CompactPlus0432.nodes443,NodePlus06.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p444,GridPlus.atNode 444,GridPlus.atNode 445,NodePlus06.w60,CompactPlus0432.checked444,CompactPlus0432.small444,CompactPlus0432.nodes444,NodePlus06.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p445,GridPlus.atNode 445,GridPlus.atNode 446,NodePlus06.w61,CompactPlus0432.checked445,CompactPlus0432.small445,CompactPlus0432.nodes445,NodePlus06.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p446,GridPlus.atNode 446,GridPlus.atNode 447,NodePlus06.w62,CompactPlus0432.checked446,CompactPlus0432.small446,CompactPlus0432.nodes446,NodePlus06.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0432.p447,GridPlus.atNode 447,GridPlus.atNode 448,NodePlus06.w63,CompactPlus0432.checked447,CompactPlus0432.small447,CompactPlus0432.nodes447,NodePlus06.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (384+j) ∧
    (atRow j).right=GridPlus.atNode (384+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus06
