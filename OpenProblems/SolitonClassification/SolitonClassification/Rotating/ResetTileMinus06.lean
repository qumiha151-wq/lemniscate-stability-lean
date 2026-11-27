import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0384
import SolitonClassification.Rotating.ResetPackedMinus0400
import SolitonClassification.Rotating.ResetPackedMinus0416
import SolitonClassification.Rotating.ResetPackedMinus0432
namespace SolitonClassification.Rotating.DyadicReset.TileMinus06
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p384,GridMinus.atNode 384,GridMinus.atNode 385,NodeMinus06.w0,CompactMinus0384.checked384,CompactMinus0384.small384,CompactMinus0384.nodes384,NodeMinus06.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p385,GridMinus.atNode 385,GridMinus.atNode 386,NodeMinus06.w1,CompactMinus0384.checked385,CompactMinus0384.small385,CompactMinus0384.nodes385,NodeMinus06.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p386,GridMinus.atNode 386,GridMinus.atNode 387,NodeMinus06.w2,CompactMinus0384.checked386,CompactMinus0384.small386,CompactMinus0384.nodes386,NodeMinus06.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p387,GridMinus.atNode 387,GridMinus.atNode 388,NodeMinus06.w3,CompactMinus0384.checked387,CompactMinus0384.small387,CompactMinus0384.nodes387,NodeMinus06.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p388,GridMinus.atNode 388,GridMinus.atNode 389,NodeMinus06.w4,CompactMinus0384.checked388,CompactMinus0384.small388,CompactMinus0384.nodes388,NodeMinus06.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p389,GridMinus.atNode 389,GridMinus.atNode 390,NodeMinus06.w5,CompactMinus0384.checked389,CompactMinus0384.small389,CompactMinus0384.nodes389,NodeMinus06.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p390,GridMinus.atNode 390,GridMinus.atNode 391,NodeMinus06.w6,CompactMinus0384.checked390,CompactMinus0384.small390,CompactMinus0384.nodes390,NodeMinus06.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p391,GridMinus.atNode 391,GridMinus.atNode 392,NodeMinus06.w7,CompactMinus0384.checked391,CompactMinus0384.small391,CompactMinus0384.nodes391,NodeMinus06.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p392,GridMinus.atNode 392,GridMinus.atNode 393,NodeMinus06.w8,CompactMinus0384.checked392,CompactMinus0384.small392,CompactMinus0384.nodes392,NodeMinus06.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p393,GridMinus.atNode 393,GridMinus.atNode 394,NodeMinus06.w9,CompactMinus0384.checked393,CompactMinus0384.small393,CompactMinus0384.nodes393,NodeMinus06.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p394,GridMinus.atNode 394,GridMinus.atNode 395,NodeMinus06.w10,CompactMinus0384.checked394,CompactMinus0384.small394,CompactMinus0384.nodes394,NodeMinus06.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p395,GridMinus.atNode 395,GridMinus.atNode 396,NodeMinus06.w11,CompactMinus0384.checked395,CompactMinus0384.small395,CompactMinus0384.nodes395,NodeMinus06.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p396,GridMinus.atNode 396,GridMinus.atNode 397,NodeMinus06.w12,CompactMinus0384.checked396,CompactMinus0384.small396,CompactMinus0384.nodes396,NodeMinus06.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p397,GridMinus.atNode 397,GridMinus.atNode 398,NodeMinus06.w13,CompactMinus0384.checked397,CompactMinus0384.small397,CompactMinus0384.nodes397,NodeMinus06.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p398,GridMinus.atNode 398,GridMinus.atNode 399,NodeMinus06.w14,CompactMinus0384.checked398,CompactMinus0384.small398,CompactMinus0384.nodes398,NodeMinus06.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0384.p399,GridMinus.atNode 399,GridMinus.atNode 400,NodeMinus06.w15,CompactMinus0384.checked399,CompactMinus0384.small399,CompactMinus0384.nodes399,NodeMinus06.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p400,GridMinus.atNode 400,GridMinus.atNode 401,NodeMinus06.w16,CompactMinus0400.checked400,CompactMinus0400.small400,CompactMinus0400.nodes400,NodeMinus06.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p401,GridMinus.atNode 401,GridMinus.atNode 402,NodeMinus06.w17,CompactMinus0400.checked401,CompactMinus0400.small401,CompactMinus0400.nodes401,NodeMinus06.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p402,GridMinus.atNode 402,GridMinus.atNode 403,NodeMinus06.w18,CompactMinus0400.checked402,CompactMinus0400.small402,CompactMinus0400.nodes402,NodeMinus06.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p403,GridMinus.atNode 403,GridMinus.atNode 404,NodeMinus06.w19,CompactMinus0400.checked403,CompactMinus0400.small403,CompactMinus0400.nodes403,NodeMinus06.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p404,GridMinus.atNode 404,GridMinus.atNode 405,NodeMinus06.w20,CompactMinus0400.checked404,CompactMinus0400.small404,CompactMinus0400.nodes404,NodeMinus06.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p405,GridMinus.atNode 405,GridMinus.atNode 406,NodeMinus06.w21,CompactMinus0400.checked405,CompactMinus0400.small405,CompactMinus0400.nodes405,NodeMinus06.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p406,GridMinus.atNode 406,GridMinus.atNode 407,NodeMinus06.w22,CompactMinus0400.checked406,CompactMinus0400.small406,CompactMinus0400.nodes406,NodeMinus06.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p407,GridMinus.atNode 407,GridMinus.atNode 408,NodeMinus06.w23,CompactMinus0400.checked407,CompactMinus0400.small407,CompactMinus0400.nodes407,NodeMinus06.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p408,GridMinus.atNode 408,GridMinus.atNode 409,NodeMinus06.w24,CompactMinus0400.checked408,CompactMinus0400.small408,CompactMinus0400.nodes408,NodeMinus06.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p409,GridMinus.atNode 409,GridMinus.atNode 410,NodeMinus06.w25,CompactMinus0400.checked409,CompactMinus0400.small409,CompactMinus0400.nodes409,NodeMinus06.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p410,GridMinus.atNode 410,GridMinus.atNode 411,NodeMinus06.w26,CompactMinus0400.checked410,CompactMinus0400.small410,CompactMinus0400.nodes410,NodeMinus06.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p411,GridMinus.atNode 411,GridMinus.atNode 412,NodeMinus06.w27,CompactMinus0400.checked411,CompactMinus0400.small411,CompactMinus0400.nodes411,NodeMinus06.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p412,GridMinus.atNode 412,GridMinus.atNode 413,NodeMinus06.w28,CompactMinus0400.checked412,CompactMinus0400.small412,CompactMinus0400.nodes412,NodeMinus06.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p413,GridMinus.atNode 413,GridMinus.atNode 414,NodeMinus06.w29,CompactMinus0400.checked413,CompactMinus0400.small413,CompactMinus0400.nodes413,NodeMinus06.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p414,GridMinus.atNode 414,GridMinus.atNode 415,NodeMinus06.w30,CompactMinus0400.checked414,CompactMinus0400.small414,CompactMinus0400.nodes414,NodeMinus06.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0400.p415,GridMinus.atNode 415,GridMinus.atNode 416,NodeMinus06.w31,CompactMinus0400.checked415,CompactMinus0400.small415,CompactMinus0400.nodes415,NodeMinus06.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p416,GridMinus.atNode 416,GridMinus.atNode 417,NodeMinus06.w32,CompactMinus0416.checked416,CompactMinus0416.small416,CompactMinus0416.nodes416,NodeMinus06.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p417,GridMinus.atNode 417,GridMinus.atNode 418,NodeMinus06.w33,CompactMinus0416.checked417,CompactMinus0416.small417,CompactMinus0416.nodes417,NodeMinus06.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p418,GridMinus.atNode 418,GridMinus.atNode 419,NodeMinus06.w34,CompactMinus0416.checked418,CompactMinus0416.small418,CompactMinus0416.nodes418,NodeMinus06.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p419,GridMinus.atNode 419,GridMinus.atNode 420,NodeMinus06.w35,CompactMinus0416.checked419,CompactMinus0416.small419,CompactMinus0416.nodes419,NodeMinus06.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p420,GridMinus.atNode 420,GridMinus.atNode 421,NodeMinus06.w36,CompactMinus0416.checked420,CompactMinus0416.small420,CompactMinus0416.nodes420,NodeMinus06.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p421,GridMinus.atNode 421,GridMinus.atNode 422,NodeMinus06.w37,CompactMinus0416.checked421,CompactMinus0416.small421,CompactMinus0416.nodes421,NodeMinus06.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p422,GridMinus.atNode 422,GridMinus.atNode 423,NodeMinus06.w38,CompactMinus0416.checked422,CompactMinus0416.small422,CompactMinus0416.nodes422,NodeMinus06.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p423,GridMinus.atNode 423,GridMinus.atNode 424,NodeMinus06.w39,CompactMinus0416.checked423,CompactMinus0416.small423,CompactMinus0416.nodes423,NodeMinus06.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p424,GridMinus.atNode 424,GridMinus.atNode 425,NodeMinus06.w40,CompactMinus0416.checked424,CompactMinus0416.small424,CompactMinus0416.nodes424,NodeMinus06.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p425,GridMinus.atNode 425,GridMinus.atNode 426,NodeMinus06.w41,CompactMinus0416.checked425,CompactMinus0416.small425,CompactMinus0416.nodes425,NodeMinus06.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p426,GridMinus.atNode 426,GridMinus.atNode 427,NodeMinus06.w42,CompactMinus0416.checked426,CompactMinus0416.small426,CompactMinus0416.nodes426,NodeMinus06.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p427,GridMinus.atNode 427,GridMinus.atNode 428,NodeMinus06.w43,CompactMinus0416.checked427,CompactMinus0416.small427,CompactMinus0416.nodes427,NodeMinus06.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p428,GridMinus.atNode 428,GridMinus.atNode 429,NodeMinus06.w44,CompactMinus0416.checked428,CompactMinus0416.small428,CompactMinus0416.nodes428,NodeMinus06.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p429,GridMinus.atNode 429,GridMinus.atNode 430,NodeMinus06.w45,CompactMinus0416.checked429,CompactMinus0416.small429,CompactMinus0416.nodes429,NodeMinus06.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p430,GridMinus.atNode 430,GridMinus.atNode 431,NodeMinus06.w46,CompactMinus0416.checked430,CompactMinus0416.small430,CompactMinus0416.nodes430,NodeMinus06.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0416.p431,GridMinus.atNode 431,GridMinus.atNode 432,NodeMinus06.w47,CompactMinus0416.checked431,CompactMinus0416.small431,CompactMinus0416.nodes431,NodeMinus06.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p432,GridMinus.atNode 432,GridMinus.atNode 433,NodeMinus06.w48,CompactMinus0432.checked432,CompactMinus0432.small432,CompactMinus0432.nodes432,NodeMinus06.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p433,GridMinus.atNode 433,GridMinus.atNode 434,NodeMinus06.w49,CompactMinus0432.checked433,CompactMinus0432.small433,CompactMinus0432.nodes433,NodeMinus06.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p434,GridMinus.atNode 434,GridMinus.atNode 435,NodeMinus06.w50,CompactMinus0432.checked434,CompactMinus0432.small434,CompactMinus0432.nodes434,NodeMinus06.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p435,GridMinus.atNode 435,GridMinus.atNode 436,NodeMinus06.w51,CompactMinus0432.checked435,CompactMinus0432.small435,CompactMinus0432.nodes435,NodeMinus06.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p436,GridMinus.atNode 436,GridMinus.atNode 437,NodeMinus06.w52,CompactMinus0432.checked436,CompactMinus0432.small436,CompactMinus0432.nodes436,NodeMinus06.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p437,GridMinus.atNode 437,GridMinus.atNode 438,NodeMinus06.w53,CompactMinus0432.checked437,CompactMinus0432.small437,CompactMinus0432.nodes437,NodeMinus06.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p438,GridMinus.atNode 438,GridMinus.atNode 439,NodeMinus06.w54,CompactMinus0432.checked438,CompactMinus0432.small438,CompactMinus0432.nodes438,NodeMinus06.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p439,GridMinus.atNode 439,GridMinus.atNode 440,NodeMinus06.w55,CompactMinus0432.checked439,CompactMinus0432.small439,CompactMinus0432.nodes439,NodeMinus06.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p440,GridMinus.atNode 440,GridMinus.atNode 441,NodeMinus06.w56,CompactMinus0432.checked440,CompactMinus0432.small440,CompactMinus0432.nodes440,NodeMinus06.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p441,GridMinus.atNode 441,GridMinus.atNode 442,NodeMinus06.w57,CompactMinus0432.checked441,CompactMinus0432.small441,CompactMinus0432.nodes441,NodeMinus06.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p442,GridMinus.atNode 442,GridMinus.atNode 443,NodeMinus06.w58,CompactMinus0432.checked442,CompactMinus0432.small442,CompactMinus0432.nodes442,NodeMinus06.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p443,GridMinus.atNode 443,GridMinus.atNode 444,NodeMinus06.w59,CompactMinus0432.checked443,CompactMinus0432.small443,CompactMinus0432.nodes443,NodeMinus06.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p444,GridMinus.atNode 444,GridMinus.atNode 445,NodeMinus06.w60,CompactMinus0432.checked444,CompactMinus0432.small444,CompactMinus0432.nodes444,NodeMinus06.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p445,GridMinus.atNode 445,GridMinus.atNode 446,NodeMinus06.w61,CompactMinus0432.checked445,CompactMinus0432.small445,CompactMinus0432.nodes445,NodeMinus06.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p446,GridMinus.atNode 446,GridMinus.atNode 447,NodeMinus06.w62,CompactMinus0432.checked446,CompactMinus0432.small446,CompactMinus0432.nodes446,NodeMinus06.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0432.p447,GridMinus.atNode 447,GridMinus.atNode 448,NodeMinus06.w63,CompactMinus0432.checked447,CompactMinus0432.small447,CompactMinus0432.nodes447,NodeMinus06.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (384+j) ∧
    (atRow j).right=GridMinus.atNode (384+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus06
