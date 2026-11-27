import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3328
import SolitonClassification.Rotating.ResetPackedMinus3344
import SolitonClassification.Rotating.ResetPackedMinus3360
import SolitonClassification.Rotating.ResetPackedMinus3376
namespace SolitonClassification.Rotating.DyadicReset.TileMinus52
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3328,GridMinus.atNode 3328,GridMinus.atNode 3329,NodeMinus52.w0,CompactMinus3328.checked3328,CompactMinus3328.small3328,CompactMinus3328.nodes3328,NodeMinus52.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3329,GridMinus.atNode 3329,GridMinus.atNode 3330,NodeMinus52.w1,CompactMinus3328.checked3329,CompactMinus3328.small3329,CompactMinus3328.nodes3329,NodeMinus52.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3330,GridMinus.atNode 3330,GridMinus.atNode 3331,NodeMinus52.w2,CompactMinus3328.checked3330,CompactMinus3328.small3330,CompactMinus3328.nodes3330,NodeMinus52.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3331,GridMinus.atNode 3331,GridMinus.atNode 3332,NodeMinus52.w3,CompactMinus3328.checked3331,CompactMinus3328.small3331,CompactMinus3328.nodes3331,NodeMinus52.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3332,GridMinus.atNode 3332,GridMinus.atNode 3333,NodeMinus52.w4,CompactMinus3328.checked3332,CompactMinus3328.small3332,CompactMinus3328.nodes3332,NodeMinus52.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3333,GridMinus.atNode 3333,GridMinus.atNode 3334,NodeMinus52.w5,CompactMinus3328.checked3333,CompactMinus3328.small3333,CompactMinus3328.nodes3333,NodeMinus52.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3334,GridMinus.atNode 3334,GridMinus.atNode 3335,NodeMinus52.w6,CompactMinus3328.checked3334,CompactMinus3328.small3334,CompactMinus3328.nodes3334,NodeMinus52.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3335,GridMinus.atNode 3335,GridMinus.atNode 3336,NodeMinus52.w7,CompactMinus3328.checked3335,CompactMinus3328.small3335,CompactMinus3328.nodes3335,NodeMinus52.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3336,GridMinus.atNode 3336,GridMinus.atNode 3337,NodeMinus52.w8,CompactMinus3328.checked3336,CompactMinus3328.small3336,CompactMinus3328.nodes3336,NodeMinus52.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3337,GridMinus.atNode 3337,GridMinus.atNode 3338,NodeMinus52.w9,CompactMinus3328.checked3337,CompactMinus3328.small3337,CompactMinus3328.nodes3337,NodeMinus52.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3338,GridMinus.atNode 3338,GridMinus.atNode 3339,NodeMinus52.w10,CompactMinus3328.checked3338,CompactMinus3328.small3338,CompactMinus3328.nodes3338,NodeMinus52.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3339,GridMinus.atNode 3339,GridMinus.atNode 3340,NodeMinus52.w11,CompactMinus3328.checked3339,CompactMinus3328.small3339,CompactMinus3328.nodes3339,NodeMinus52.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3340,GridMinus.atNode 3340,GridMinus.atNode 3341,NodeMinus52.w12,CompactMinus3328.checked3340,CompactMinus3328.small3340,CompactMinus3328.nodes3340,NodeMinus52.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3341,GridMinus.atNode 3341,GridMinus.atNode 3342,NodeMinus52.w13,CompactMinus3328.checked3341,CompactMinus3328.small3341,CompactMinus3328.nodes3341,NodeMinus52.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3342,GridMinus.atNode 3342,GridMinus.atNode 3343,NodeMinus52.w14,CompactMinus3328.checked3342,CompactMinus3328.small3342,CompactMinus3328.nodes3342,NodeMinus52.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3328.p3343,GridMinus.atNode 3343,GridMinus.atNode 3344,NodeMinus52.w15,CompactMinus3328.checked3343,CompactMinus3328.small3343,CompactMinus3328.nodes3343,NodeMinus52.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3344,GridMinus.atNode 3344,GridMinus.atNode 3345,NodeMinus52.w16,CompactMinus3344.checked3344,CompactMinus3344.small3344,CompactMinus3344.nodes3344,NodeMinus52.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3345,GridMinus.atNode 3345,GridMinus.atNode 3346,NodeMinus52.w17,CompactMinus3344.checked3345,CompactMinus3344.small3345,CompactMinus3344.nodes3345,NodeMinus52.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3346,GridMinus.atNode 3346,GridMinus.atNode 3347,NodeMinus52.w18,CompactMinus3344.checked3346,CompactMinus3344.small3346,CompactMinus3344.nodes3346,NodeMinus52.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3347,GridMinus.atNode 3347,GridMinus.atNode 3348,NodeMinus52.w19,CompactMinus3344.checked3347,CompactMinus3344.small3347,CompactMinus3344.nodes3347,NodeMinus52.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3348,GridMinus.atNode 3348,GridMinus.atNode 3349,NodeMinus52.w20,CompactMinus3344.checked3348,CompactMinus3344.small3348,CompactMinus3344.nodes3348,NodeMinus52.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3349,GridMinus.atNode 3349,GridMinus.atNode 3350,NodeMinus52.w21,CompactMinus3344.checked3349,CompactMinus3344.small3349,CompactMinus3344.nodes3349,NodeMinus52.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3350,GridMinus.atNode 3350,GridMinus.atNode 3351,NodeMinus52.w22,CompactMinus3344.checked3350,CompactMinus3344.small3350,CompactMinus3344.nodes3350,NodeMinus52.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3351,GridMinus.atNode 3351,GridMinus.atNode 3352,NodeMinus52.w23,CompactMinus3344.checked3351,CompactMinus3344.small3351,CompactMinus3344.nodes3351,NodeMinus52.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3352,GridMinus.atNode 3352,GridMinus.atNode 3353,NodeMinus52.w24,CompactMinus3344.checked3352,CompactMinus3344.small3352,CompactMinus3344.nodes3352,NodeMinus52.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3353,GridMinus.atNode 3353,GridMinus.atNode 3354,NodeMinus52.w25,CompactMinus3344.checked3353,CompactMinus3344.small3353,CompactMinus3344.nodes3353,NodeMinus52.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3354,GridMinus.atNode 3354,GridMinus.atNode 3355,NodeMinus52.w26,CompactMinus3344.checked3354,CompactMinus3344.small3354,CompactMinus3344.nodes3354,NodeMinus52.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3355,GridMinus.atNode 3355,GridMinus.atNode 3356,NodeMinus52.w27,CompactMinus3344.checked3355,CompactMinus3344.small3355,CompactMinus3344.nodes3355,NodeMinus52.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3356,GridMinus.atNode 3356,GridMinus.atNode 3357,NodeMinus52.w28,CompactMinus3344.checked3356,CompactMinus3344.small3356,CompactMinus3344.nodes3356,NodeMinus52.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3357,GridMinus.atNode 3357,GridMinus.atNode 3358,NodeMinus52.w29,CompactMinus3344.checked3357,CompactMinus3344.small3357,CompactMinus3344.nodes3357,NodeMinus52.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3358,GridMinus.atNode 3358,GridMinus.atNode 3359,NodeMinus52.w30,CompactMinus3344.checked3358,CompactMinus3344.small3358,CompactMinus3344.nodes3358,NodeMinus52.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3344.p3359,GridMinus.atNode 3359,GridMinus.atNode 3360,NodeMinus52.w31,CompactMinus3344.checked3359,CompactMinus3344.small3359,CompactMinus3344.nodes3359,NodeMinus52.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3360,GridMinus.atNode 3360,GridMinus.atNode 3361,NodeMinus52.w32,CompactMinus3360.checked3360,CompactMinus3360.small3360,CompactMinus3360.nodes3360,NodeMinus52.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3361,GridMinus.atNode 3361,GridMinus.atNode 3362,NodeMinus52.w33,CompactMinus3360.checked3361,CompactMinus3360.small3361,CompactMinus3360.nodes3361,NodeMinus52.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3362,GridMinus.atNode 3362,GridMinus.atNode 3363,NodeMinus52.w34,CompactMinus3360.checked3362,CompactMinus3360.small3362,CompactMinus3360.nodes3362,NodeMinus52.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3363,GridMinus.atNode 3363,GridMinus.atNode 3364,NodeMinus52.w35,CompactMinus3360.checked3363,CompactMinus3360.small3363,CompactMinus3360.nodes3363,NodeMinus52.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3364,GridMinus.atNode 3364,GridMinus.atNode 3365,NodeMinus52.w36,CompactMinus3360.checked3364,CompactMinus3360.small3364,CompactMinus3360.nodes3364,NodeMinus52.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3365,GridMinus.atNode 3365,GridMinus.atNode 3366,NodeMinus52.w37,CompactMinus3360.checked3365,CompactMinus3360.small3365,CompactMinus3360.nodes3365,NodeMinus52.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3366,GridMinus.atNode 3366,GridMinus.atNode 3367,NodeMinus52.w38,CompactMinus3360.checked3366,CompactMinus3360.small3366,CompactMinus3360.nodes3366,NodeMinus52.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3367,GridMinus.atNode 3367,GridMinus.atNode 3368,NodeMinus52.w39,CompactMinus3360.checked3367,CompactMinus3360.small3367,CompactMinus3360.nodes3367,NodeMinus52.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3368,GridMinus.atNode 3368,GridMinus.atNode 3369,NodeMinus52.w40,CompactMinus3360.checked3368,CompactMinus3360.small3368,CompactMinus3360.nodes3368,NodeMinus52.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3369,GridMinus.atNode 3369,GridMinus.atNode 3370,NodeMinus52.w41,CompactMinus3360.checked3369,CompactMinus3360.small3369,CompactMinus3360.nodes3369,NodeMinus52.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3370,GridMinus.atNode 3370,GridMinus.atNode 3371,NodeMinus52.w42,CompactMinus3360.checked3370,CompactMinus3360.small3370,CompactMinus3360.nodes3370,NodeMinus52.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3371,GridMinus.atNode 3371,GridMinus.atNode 3372,NodeMinus52.w43,CompactMinus3360.checked3371,CompactMinus3360.small3371,CompactMinus3360.nodes3371,NodeMinus52.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3372,GridMinus.atNode 3372,GridMinus.atNode 3373,NodeMinus52.w44,CompactMinus3360.checked3372,CompactMinus3360.small3372,CompactMinus3360.nodes3372,NodeMinus52.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3373,GridMinus.atNode 3373,GridMinus.atNode 3374,NodeMinus52.w45,CompactMinus3360.checked3373,CompactMinus3360.small3373,CompactMinus3360.nodes3373,NodeMinus52.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3374,GridMinus.atNode 3374,GridMinus.atNode 3375,NodeMinus52.w46,CompactMinus3360.checked3374,CompactMinus3360.small3374,CompactMinus3360.nodes3374,NodeMinus52.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3360.p3375,GridMinus.atNode 3375,GridMinus.atNode 3376,NodeMinus52.w47,CompactMinus3360.checked3375,CompactMinus3360.small3375,CompactMinus3360.nodes3375,NodeMinus52.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3376,GridMinus.atNode 3376,GridMinus.atNode 3377,NodeMinus52.w48,CompactMinus3376.checked3376,CompactMinus3376.small3376,CompactMinus3376.nodes3376,NodeMinus52.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3377,GridMinus.atNode 3377,GridMinus.atNode 3378,NodeMinus52.w49,CompactMinus3376.checked3377,CompactMinus3376.small3377,CompactMinus3376.nodes3377,NodeMinus52.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3378,GridMinus.atNode 3378,GridMinus.atNode 3379,NodeMinus52.w50,CompactMinus3376.checked3378,CompactMinus3376.small3378,CompactMinus3376.nodes3378,NodeMinus52.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3379,GridMinus.atNode 3379,GridMinus.atNode 3380,NodeMinus52.w51,CompactMinus3376.checked3379,CompactMinus3376.small3379,CompactMinus3376.nodes3379,NodeMinus52.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3380,GridMinus.atNode 3380,GridMinus.atNode 3381,NodeMinus52.w52,CompactMinus3376.checked3380,CompactMinus3376.small3380,CompactMinus3376.nodes3380,NodeMinus52.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3381,GridMinus.atNode 3381,GridMinus.atNode 3382,NodeMinus52.w53,CompactMinus3376.checked3381,CompactMinus3376.small3381,CompactMinus3376.nodes3381,NodeMinus52.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3382,GridMinus.atNode 3382,GridMinus.atNode 3383,NodeMinus52.w54,CompactMinus3376.checked3382,CompactMinus3376.small3382,CompactMinus3376.nodes3382,NodeMinus52.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3383,GridMinus.atNode 3383,GridMinus.atNode 3384,NodeMinus52.w55,CompactMinus3376.checked3383,CompactMinus3376.small3383,CompactMinus3376.nodes3383,NodeMinus52.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3384,GridMinus.atNode 3384,GridMinus.atNode 3385,NodeMinus52.w56,CompactMinus3376.checked3384,CompactMinus3376.small3384,CompactMinus3376.nodes3384,NodeMinus52.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3385,GridMinus.atNode 3385,GridMinus.atNode 3386,NodeMinus52.w57,CompactMinus3376.checked3385,CompactMinus3376.small3385,CompactMinus3376.nodes3385,NodeMinus52.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3386,GridMinus.atNode 3386,GridMinus.atNode 3387,NodeMinus52.w58,CompactMinus3376.checked3386,CompactMinus3376.small3386,CompactMinus3376.nodes3386,NodeMinus52.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3387,GridMinus.atNode 3387,GridMinus.atNode 3388,NodeMinus52.w59,CompactMinus3376.checked3387,CompactMinus3376.small3387,CompactMinus3376.nodes3387,NodeMinus52.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3388,GridMinus.atNode 3388,GridMinus.atNode 3389,NodeMinus52.w60,CompactMinus3376.checked3388,CompactMinus3376.small3388,CompactMinus3376.nodes3388,NodeMinus52.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3389,GridMinus.atNode 3389,GridMinus.atNode 3390,NodeMinus52.w61,CompactMinus3376.checked3389,CompactMinus3376.small3389,CompactMinus3376.nodes3389,NodeMinus52.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3390,GridMinus.atNode 3390,GridMinus.atNode 3391,NodeMinus52.w62,CompactMinus3376.checked3390,CompactMinus3376.small3390,CompactMinus3376.nodes3390,NodeMinus52.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3376.p3391,GridMinus.atNode 3391,GridMinus.atNode 3392,NodeMinus52.w63,CompactMinus3376.checked3391,CompactMinus3376.small3391,CompactMinus3376.nodes3391,NodeMinus52.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3328+j) ∧
    (atRow j).right=GridMinus.atNode (3328+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus52
