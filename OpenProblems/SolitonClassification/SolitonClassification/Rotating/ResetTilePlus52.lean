import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3328
import SolitonClassification.Rotating.ResetPackedPlus3344
import SolitonClassification.Rotating.ResetPackedPlus3360
import SolitonClassification.Rotating.ResetPackedPlus3376
namespace SolitonClassification.Rotating.DyadicReset.TilePlus52
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3328,GridPlus.atNode 3328,GridPlus.atNode 3329,NodePlus52.w0,CompactPlus3328.checked3328,CompactPlus3328.small3328,CompactPlus3328.nodes3328,NodePlus52.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3329,GridPlus.atNode 3329,GridPlus.atNode 3330,NodePlus52.w1,CompactPlus3328.checked3329,CompactPlus3328.small3329,CompactPlus3328.nodes3329,NodePlus52.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3330,GridPlus.atNode 3330,GridPlus.atNode 3331,NodePlus52.w2,CompactPlus3328.checked3330,CompactPlus3328.small3330,CompactPlus3328.nodes3330,NodePlus52.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3331,GridPlus.atNode 3331,GridPlus.atNode 3332,NodePlus52.w3,CompactPlus3328.checked3331,CompactPlus3328.small3331,CompactPlus3328.nodes3331,NodePlus52.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3332,GridPlus.atNode 3332,GridPlus.atNode 3333,NodePlus52.w4,CompactPlus3328.checked3332,CompactPlus3328.small3332,CompactPlus3328.nodes3332,NodePlus52.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3333,GridPlus.atNode 3333,GridPlus.atNode 3334,NodePlus52.w5,CompactPlus3328.checked3333,CompactPlus3328.small3333,CompactPlus3328.nodes3333,NodePlus52.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3334,GridPlus.atNode 3334,GridPlus.atNode 3335,NodePlus52.w6,CompactPlus3328.checked3334,CompactPlus3328.small3334,CompactPlus3328.nodes3334,NodePlus52.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3335,GridPlus.atNode 3335,GridPlus.atNode 3336,NodePlus52.w7,CompactPlus3328.checked3335,CompactPlus3328.small3335,CompactPlus3328.nodes3335,NodePlus52.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3336,GridPlus.atNode 3336,GridPlus.atNode 3337,NodePlus52.w8,CompactPlus3328.checked3336,CompactPlus3328.small3336,CompactPlus3328.nodes3336,NodePlus52.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3337,GridPlus.atNode 3337,GridPlus.atNode 3338,NodePlus52.w9,CompactPlus3328.checked3337,CompactPlus3328.small3337,CompactPlus3328.nodes3337,NodePlus52.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3338,GridPlus.atNode 3338,GridPlus.atNode 3339,NodePlus52.w10,CompactPlus3328.checked3338,CompactPlus3328.small3338,CompactPlus3328.nodes3338,NodePlus52.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3339,GridPlus.atNode 3339,GridPlus.atNode 3340,NodePlus52.w11,CompactPlus3328.checked3339,CompactPlus3328.small3339,CompactPlus3328.nodes3339,NodePlus52.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3340,GridPlus.atNode 3340,GridPlus.atNode 3341,NodePlus52.w12,CompactPlus3328.checked3340,CompactPlus3328.small3340,CompactPlus3328.nodes3340,NodePlus52.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3341,GridPlus.atNode 3341,GridPlus.atNode 3342,NodePlus52.w13,CompactPlus3328.checked3341,CompactPlus3328.small3341,CompactPlus3328.nodes3341,NodePlus52.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3342,GridPlus.atNode 3342,GridPlus.atNode 3343,NodePlus52.w14,CompactPlus3328.checked3342,CompactPlus3328.small3342,CompactPlus3328.nodes3342,NodePlus52.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3328.p3343,GridPlus.atNode 3343,GridPlus.atNode 3344,NodePlus52.w15,CompactPlus3328.checked3343,CompactPlus3328.small3343,CompactPlus3328.nodes3343,NodePlus52.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3344,GridPlus.atNode 3344,GridPlus.atNode 3345,NodePlus52.w16,CompactPlus3344.checked3344,CompactPlus3344.small3344,CompactPlus3344.nodes3344,NodePlus52.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3345,GridPlus.atNode 3345,GridPlus.atNode 3346,NodePlus52.w17,CompactPlus3344.checked3345,CompactPlus3344.small3345,CompactPlus3344.nodes3345,NodePlus52.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3346,GridPlus.atNode 3346,GridPlus.atNode 3347,NodePlus52.w18,CompactPlus3344.checked3346,CompactPlus3344.small3346,CompactPlus3344.nodes3346,NodePlus52.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3347,GridPlus.atNode 3347,GridPlus.atNode 3348,NodePlus52.w19,CompactPlus3344.checked3347,CompactPlus3344.small3347,CompactPlus3344.nodes3347,NodePlus52.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3348,GridPlus.atNode 3348,GridPlus.atNode 3349,NodePlus52.w20,CompactPlus3344.checked3348,CompactPlus3344.small3348,CompactPlus3344.nodes3348,NodePlus52.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3349,GridPlus.atNode 3349,GridPlus.atNode 3350,NodePlus52.w21,CompactPlus3344.checked3349,CompactPlus3344.small3349,CompactPlus3344.nodes3349,NodePlus52.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3350,GridPlus.atNode 3350,GridPlus.atNode 3351,NodePlus52.w22,CompactPlus3344.checked3350,CompactPlus3344.small3350,CompactPlus3344.nodes3350,NodePlus52.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3351,GridPlus.atNode 3351,GridPlus.atNode 3352,NodePlus52.w23,CompactPlus3344.checked3351,CompactPlus3344.small3351,CompactPlus3344.nodes3351,NodePlus52.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3352,GridPlus.atNode 3352,GridPlus.atNode 3353,NodePlus52.w24,CompactPlus3344.checked3352,CompactPlus3344.small3352,CompactPlus3344.nodes3352,NodePlus52.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3353,GridPlus.atNode 3353,GridPlus.atNode 3354,NodePlus52.w25,CompactPlus3344.checked3353,CompactPlus3344.small3353,CompactPlus3344.nodes3353,NodePlus52.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3354,GridPlus.atNode 3354,GridPlus.atNode 3355,NodePlus52.w26,CompactPlus3344.checked3354,CompactPlus3344.small3354,CompactPlus3344.nodes3354,NodePlus52.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3355,GridPlus.atNode 3355,GridPlus.atNode 3356,NodePlus52.w27,CompactPlus3344.checked3355,CompactPlus3344.small3355,CompactPlus3344.nodes3355,NodePlus52.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3356,GridPlus.atNode 3356,GridPlus.atNode 3357,NodePlus52.w28,CompactPlus3344.checked3356,CompactPlus3344.small3356,CompactPlus3344.nodes3356,NodePlus52.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3357,GridPlus.atNode 3357,GridPlus.atNode 3358,NodePlus52.w29,CompactPlus3344.checked3357,CompactPlus3344.small3357,CompactPlus3344.nodes3357,NodePlus52.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3358,GridPlus.atNode 3358,GridPlus.atNode 3359,NodePlus52.w30,CompactPlus3344.checked3358,CompactPlus3344.small3358,CompactPlus3344.nodes3358,NodePlus52.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3344.p3359,GridPlus.atNode 3359,GridPlus.atNode 3360,NodePlus52.w31,CompactPlus3344.checked3359,CompactPlus3344.small3359,CompactPlus3344.nodes3359,NodePlus52.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3360,GridPlus.atNode 3360,GridPlus.atNode 3361,NodePlus52.w32,CompactPlus3360.checked3360,CompactPlus3360.small3360,CompactPlus3360.nodes3360,NodePlus52.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3361,GridPlus.atNode 3361,GridPlus.atNode 3362,NodePlus52.w33,CompactPlus3360.checked3361,CompactPlus3360.small3361,CompactPlus3360.nodes3361,NodePlus52.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3362,GridPlus.atNode 3362,GridPlus.atNode 3363,NodePlus52.w34,CompactPlus3360.checked3362,CompactPlus3360.small3362,CompactPlus3360.nodes3362,NodePlus52.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3363,GridPlus.atNode 3363,GridPlus.atNode 3364,NodePlus52.w35,CompactPlus3360.checked3363,CompactPlus3360.small3363,CompactPlus3360.nodes3363,NodePlus52.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3364,GridPlus.atNode 3364,GridPlus.atNode 3365,NodePlus52.w36,CompactPlus3360.checked3364,CompactPlus3360.small3364,CompactPlus3360.nodes3364,NodePlus52.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3365,GridPlus.atNode 3365,GridPlus.atNode 3366,NodePlus52.w37,CompactPlus3360.checked3365,CompactPlus3360.small3365,CompactPlus3360.nodes3365,NodePlus52.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3366,GridPlus.atNode 3366,GridPlus.atNode 3367,NodePlus52.w38,CompactPlus3360.checked3366,CompactPlus3360.small3366,CompactPlus3360.nodes3366,NodePlus52.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3367,GridPlus.atNode 3367,GridPlus.atNode 3368,NodePlus52.w39,CompactPlus3360.checked3367,CompactPlus3360.small3367,CompactPlus3360.nodes3367,NodePlus52.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3368,GridPlus.atNode 3368,GridPlus.atNode 3369,NodePlus52.w40,CompactPlus3360.checked3368,CompactPlus3360.small3368,CompactPlus3360.nodes3368,NodePlus52.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3369,GridPlus.atNode 3369,GridPlus.atNode 3370,NodePlus52.w41,CompactPlus3360.checked3369,CompactPlus3360.small3369,CompactPlus3360.nodes3369,NodePlus52.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3370,GridPlus.atNode 3370,GridPlus.atNode 3371,NodePlus52.w42,CompactPlus3360.checked3370,CompactPlus3360.small3370,CompactPlus3360.nodes3370,NodePlus52.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3371,GridPlus.atNode 3371,GridPlus.atNode 3372,NodePlus52.w43,CompactPlus3360.checked3371,CompactPlus3360.small3371,CompactPlus3360.nodes3371,NodePlus52.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3372,GridPlus.atNode 3372,GridPlus.atNode 3373,NodePlus52.w44,CompactPlus3360.checked3372,CompactPlus3360.small3372,CompactPlus3360.nodes3372,NodePlus52.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3373,GridPlus.atNode 3373,GridPlus.atNode 3374,NodePlus52.w45,CompactPlus3360.checked3373,CompactPlus3360.small3373,CompactPlus3360.nodes3373,NodePlus52.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3374,GridPlus.atNode 3374,GridPlus.atNode 3375,NodePlus52.w46,CompactPlus3360.checked3374,CompactPlus3360.small3374,CompactPlus3360.nodes3374,NodePlus52.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3360.p3375,GridPlus.atNode 3375,GridPlus.atNode 3376,NodePlus52.w47,CompactPlus3360.checked3375,CompactPlus3360.small3375,CompactPlus3360.nodes3375,NodePlus52.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3376,GridPlus.atNode 3376,GridPlus.atNode 3377,NodePlus52.w48,CompactPlus3376.checked3376,CompactPlus3376.small3376,CompactPlus3376.nodes3376,NodePlus52.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3377,GridPlus.atNode 3377,GridPlus.atNode 3378,NodePlus52.w49,CompactPlus3376.checked3377,CompactPlus3376.small3377,CompactPlus3376.nodes3377,NodePlus52.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3378,GridPlus.atNode 3378,GridPlus.atNode 3379,NodePlus52.w50,CompactPlus3376.checked3378,CompactPlus3376.small3378,CompactPlus3376.nodes3378,NodePlus52.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3379,GridPlus.atNode 3379,GridPlus.atNode 3380,NodePlus52.w51,CompactPlus3376.checked3379,CompactPlus3376.small3379,CompactPlus3376.nodes3379,NodePlus52.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3380,GridPlus.atNode 3380,GridPlus.atNode 3381,NodePlus52.w52,CompactPlus3376.checked3380,CompactPlus3376.small3380,CompactPlus3376.nodes3380,NodePlus52.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3381,GridPlus.atNode 3381,GridPlus.atNode 3382,NodePlus52.w53,CompactPlus3376.checked3381,CompactPlus3376.small3381,CompactPlus3376.nodes3381,NodePlus52.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3382,GridPlus.atNode 3382,GridPlus.atNode 3383,NodePlus52.w54,CompactPlus3376.checked3382,CompactPlus3376.small3382,CompactPlus3376.nodes3382,NodePlus52.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3383,GridPlus.atNode 3383,GridPlus.atNode 3384,NodePlus52.w55,CompactPlus3376.checked3383,CompactPlus3376.small3383,CompactPlus3376.nodes3383,NodePlus52.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3384,GridPlus.atNode 3384,GridPlus.atNode 3385,NodePlus52.w56,CompactPlus3376.checked3384,CompactPlus3376.small3384,CompactPlus3376.nodes3384,NodePlus52.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3385,GridPlus.atNode 3385,GridPlus.atNode 3386,NodePlus52.w57,CompactPlus3376.checked3385,CompactPlus3376.small3385,CompactPlus3376.nodes3385,NodePlus52.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3386,GridPlus.atNode 3386,GridPlus.atNode 3387,NodePlus52.w58,CompactPlus3376.checked3386,CompactPlus3376.small3386,CompactPlus3376.nodes3386,NodePlus52.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3387,GridPlus.atNode 3387,GridPlus.atNode 3388,NodePlus52.w59,CompactPlus3376.checked3387,CompactPlus3376.small3387,CompactPlus3376.nodes3387,NodePlus52.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3388,GridPlus.atNode 3388,GridPlus.atNode 3389,NodePlus52.w60,CompactPlus3376.checked3388,CompactPlus3376.small3388,CompactPlus3376.nodes3388,NodePlus52.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3389,GridPlus.atNode 3389,GridPlus.atNode 3390,NodePlus52.w61,CompactPlus3376.checked3389,CompactPlus3376.small3389,CompactPlus3376.nodes3389,NodePlus52.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3390,GridPlus.atNode 3390,GridPlus.atNode 3391,NodePlus52.w62,CompactPlus3376.checked3390,CompactPlus3376.small3390,CompactPlus3376.nodes3390,NodePlus52.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3376.p3391,GridPlus.atNode 3391,GridPlus.atNode 3392,NodePlus52.w63,CompactPlus3376.checked3391,CompactPlus3376.small3391,CompactPlus3376.nodes3391,NodePlus52.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3328+j) ∧
    (atRow j).right=GridPlus.atNode (3328+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus52
