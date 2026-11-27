import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3520
import SolitonClassification.Rotating.ResetPackedMinus3536
import SolitonClassification.Rotating.ResetPackedMinus3552
import SolitonClassification.Rotating.ResetPackedMinus3568
namespace SolitonClassification.Rotating.DyadicReset.TileMinus55
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3520,GridMinus.atNode 3520,GridMinus.atNode 3521,NodeMinus55.w0,CompactMinus3520.checked3520,CompactMinus3520.small3520,CompactMinus3520.nodes3520,NodeMinus55.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3521,GridMinus.atNode 3521,GridMinus.atNode 3522,NodeMinus55.w1,CompactMinus3520.checked3521,CompactMinus3520.small3521,CompactMinus3520.nodes3521,NodeMinus55.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3522,GridMinus.atNode 3522,GridMinus.atNode 3523,NodeMinus55.w2,CompactMinus3520.checked3522,CompactMinus3520.small3522,CompactMinus3520.nodes3522,NodeMinus55.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3523,GridMinus.atNode 3523,GridMinus.atNode 3524,NodeMinus55.w3,CompactMinus3520.checked3523,CompactMinus3520.small3523,CompactMinus3520.nodes3523,NodeMinus55.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3524,GridMinus.atNode 3524,GridMinus.atNode 3525,NodeMinus55.w4,CompactMinus3520.checked3524,CompactMinus3520.small3524,CompactMinus3520.nodes3524,NodeMinus55.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3525,GridMinus.atNode 3525,GridMinus.atNode 3526,NodeMinus55.w5,CompactMinus3520.checked3525,CompactMinus3520.small3525,CompactMinus3520.nodes3525,NodeMinus55.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3526,GridMinus.atNode 3526,GridMinus.atNode 3527,NodeMinus55.w6,CompactMinus3520.checked3526,CompactMinus3520.small3526,CompactMinus3520.nodes3526,NodeMinus55.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3527,GridMinus.atNode 3527,GridMinus.atNode 3528,NodeMinus55.w7,CompactMinus3520.checked3527,CompactMinus3520.small3527,CompactMinus3520.nodes3527,NodeMinus55.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3528,GridMinus.atNode 3528,GridMinus.atNode 3529,NodeMinus55.w8,CompactMinus3520.checked3528,CompactMinus3520.small3528,CompactMinus3520.nodes3528,NodeMinus55.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3529,GridMinus.atNode 3529,GridMinus.atNode 3530,NodeMinus55.w9,CompactMinus3520.checked3529,CompactMinus3520.small3529,CompactMinus3520.nodes3529,NodeMinus55.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3530,GridMinus.atNode 3530,GridMinus.atNode 3531,NodeMinus55.w10,CompactMinus3520.checked3530,CompactMinus3520.small3530,CompactMinus3520.nodes3530,NodeMinus55.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3531,GridMinus.atNode 3531,GridMinus.atNode 3532,NodeMinus55.w11,CompactMinus3520.checked3531,CompactMinus3520.small3531,CompactMinus3520.nodes3531,NodeMinus55.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3532,GridMinus.atNode 3532,GridMinus.atNode 3533,NodeMinus55.w12,CompactMinus3520.checked3532,CompactMinus3520.small3532,CompactMinus3520.nodes3532,NodeMinus55.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3533,GridMinus.atNode 3533,GridMinus.atNode 3534,NodeMinus55.w13,CompactMinus3520.checked3533,CompactMinus3520.small3533,CompactMinus3520.nodes3533,NodeMinus55.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3534,GridMinus.atNode 3534,GridMinus.atNode 3535,NodeMinus55.w14,CompactMinus3520.checked3534,CompactMinus3520.small3534,CompactMinus3520.nodes3534,NodeMinus55.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3520.p3535,GridMinus.atNode 3535,GridMinus.atNode 3536,NodeMinus55.w15,CompactMinus3520.checked3535,CompactMinus3520.small3535,CompactMinus3520.nodes3535,NodeMinus55.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3536,GridMinus.atNode 3536,GridMinus.atNode 3537,NodeMinus55.w16,CompactMinus3536.checked3536,CompactMinus3536.small3536,CompactMinus3536.nodes3536,NodeMinus55.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3537,GridMinus.atNode 3537,GridMinus.atNode 3538,NodeMinus55.w17,CompactMinus3536.checked3537,CompactMinus3536.small3537,CompactMinus3536.nodes3537,NodeMinus55.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3538,GridMinus.atNode 3538,GridMinus.atNode 3539,NodeMinus55.w18,CompactMinus3536.checked3538,CompactMinus3536.small3538,CompactMinus3536.nodes3538,NodeMinus55.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3539,GridMinus.atNode 3539,GridMinus.atNode 3540,NodeMinus55.w19,CompactMinus3536.checked3539,CompactMinus3536.small3539,CompactMinus3536.nodes3539,NodeMinus55.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3540,GridMinus.atNode 3540,GridMinus.atNode 3541,NodeMinus55.w20,CompactMinus3536.checked3540,CompactMinus3536.small3540,CompactMinus3536.nodes3540,NodeMinus55.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3541,GridMinus.atNode 3541,GridMinus.atNode 3542,NodeMinus55.w21,CompactMinus3536.checked3541,CompactMinus3536.small3541,CompactMinus3536.nodes3541,NodeMinus55.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3542,GridMinus.atNode 3542,GridMinus.atNode 3543,NodeMinus55.w22,CompactMinus3536.checked3542,CompactMinus3536.small3542,CompactMinus3536.nodes3542,NodeMinus55.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3543,GridMinus.atNode 3543,GridMinus.atNode 3544,NodeMinus55.w23,CompactMinus3536.checked3543,CompactMinus3536.small3543,CompactMinus3536.nodes3543,NodeMinus55.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3544,GridMinus.atNode 3544,GridMinus.atNode 3545,NodeMinus55.w24,CompactMinus3536.checked3544,CompactMinus3536.small3544,CompactMinus3536.nodes3544,NodeMinus55.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3545,GridMinus.atNode 3545,GridMinus.atNode 3546,NodeMinus55.w25,CompactMinus3536.checked3545,CompactMinus3536.small3545,CompactMinus3536.nodes3545,NodeMinus55.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3546,GridMinus.atNode 3546,GridMinus.atNode 3547,NodeMinus55.w26,CompactMinus3536.checked3546,CompactMinus3536.small3546,CompactMinus3536.nodes3546,NodeMinus55.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3547,GridMinus.atNode 3547,GridMinus.atNode 3548,NodeMinus55.w27,CompactMinus3536.checked3547,CompactMinus3536.small3547,CompactMinus3536.nodes3547,NodeMinus55.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3548,GridMinus.atNode 3548,GridMinus.atNode 3549,NodeMinus55.w28,CompactMinus3536.checked3548,CompactMinus3536.small3548,CompactMinus3536.nodes3548,NodeMinus55.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3549,GridMinus.atNode 3549,GridMinus.atNode 3550,NodeMinus55.w29,CompactMinus3536.checked3549,CompactMinus3536.small3549,CompactMinus3536.nodes3549,NodeMinus55.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3550,GridMinus.atNode 3550,GridMinus.atNode 3551,NodeMinus55.w30,CompactMinus3536.checked3550,CompactMinus3536.small3550,CompactMinus3536.nodes3550,NodeMinus55.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3536.p3551,GridMinus.atNode 3551,GridMinus.atNode 3552,NodeMinus55.w31,CompactMinus3536.checked3551,CompactMinus3536.small3551,CompactMinus3536.nodes3551,NodeMinus55.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3552,GridMinus.atNode 3552,GridMinus.atNode 3553,NodeMinus55.w32,CompactMinus3552.checked3552,CompactMinus3552.small3552,CompactMinus3552.nodes3552,NodeMinus55.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3553,GridMinus.atNode 3553,GridMinus.atNode 3554,NodeMinus55.w33,CompactMinus3552.checked3553,CompactMinus3552.small3553,CompactMinus3552.nodes3553,NodeMinus55.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3554,GridMinus.atNode 3554,GridMinus.atNode 3555,NodeMinus55.w34,CompactMinus3552.checked3554,CompactMinus3552.small3554,CompactMinus3552.nodes3554,NodeMinus55.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3555,GridMinus.atNode 3555,GridMinus.atNode 3556,NodeMinus55.w35,CompactMinus3552.checked3555,CompactMinus3552.small3555,CompactMinus3552.nodes3555,NodeMinus55.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3556,GridMinus.atNode 3556,GridMinus.atNode 3557,NodeMinus55.w36,CompactMinus3552.checked3556,CompactMinus3552.small3556,CompactMinus3552.nodes3556,NodeMinus55.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3557,GridMinus.atNode 3557,GridMinus.atNode 3558,NodeMinus55.w37,CompactMinus3552.checked3557,CompactMinus3552.small3557,CompactMinus3552.nodes3557,NodeMinus55.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3558,GridMinus.atNode 3558,GridMinus.atNode 3559,NodeMinus55.w38,CompactMinus3552.checked3558,CompactMinus3552.small3558,CompactMinus3552.nodes3558,NodeMinus55.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3559,GridMinus.atNode 3559,GridMinus.atNode 3560,NodeMinus55.w39,CompactMinus3552.checked3559,CompactMinus3552.small3559,CompactMinus3552.nodes3559,NodeMinus55.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3560,GridMinus.atNode 3560,GridMinus.atNode 3561,NodeMinus55.w40,CompactMinus3552.checked3560,CompactMinus3552.small3560,CompactMinus3552.nodes3560,NodeMinus55.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3561,GridMinus.atNode 3561,GridMinus.atNode 3562,NodeMinus55.w41,CompactMinus3552.checked3561,CompactMinus3552.small3561,CompactMinus3552.nodes3561,NodeMinus55.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3562,GridMinus.atNode 3562,GridMinus.atNode 3563,NodeMinus55.w42,CompactMinus3552.checked3562,CompactMinus3552.small3562,CompactMinus3552.nodes3562,NodeMinus55.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3563,GridMinus.atNode 3563,GridMinus.atNode 3564,NodeMinus55.w43,CompactMinus3552.checked3563,CompactMinus3552.small3563,CompactMinus3552.nodes3563,NodeMinus55.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3564,GridMinus.atNode 3564,GridMinus.atNode 3565,NodeMinus55.w44,CompactMinus3552.checked3564,CompactMinus3552.small3564,CompactMinus3552.nodes3564,NodeMinus55.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3565,GridMinus.atNode 3565,GridMinus.atNode 3566,NodeMinus55.w45,CompactMinus3552.checked3565,CompactMinus3552.small3565,CompactMinus3552.nodes3565,NodeMinus55.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3566,GridMinus.atNode 3566,GridMinus.atNode 3567,NodeMinus55.w46,CompactMinus3552.checked3566,CompactMinus3552.small3566,CompactMinus3552.nodes3566,NodeMinus55.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3552.p3567,GridMinus.atNode 3567,GridMinus.atNode 3568,NodeMinus55.w47,CompactMinus3552.checked3567,CompactMinus3552.small3567,CompactMinus3552.nodes3567,NodeMinus55.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3568,GridMinus.atNode 3568,GridMinus.atNode 3569,NodeMinus55.w48,CompactMinus3568.checked3568,CompactMinus3568.small3568,CompactMinus3568.nodes3568,NodeMinus55.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3569,GridMinus.atNode 3569,GridMinus.atNode 3570,NodeMinus55.w49,CompactMinus3568.checked3569,CompactMinus3568.small3569,CompactMinus3568.nodes3569,NodeMinus55.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3570,GridMinus.atNode 3570,GridMinus.atNode 3571,NodeMinus55.w50,CompactMinus3568.checked3570,CompactMinus3568.small3570,CompactMinus3568.nodes3570,NodeMinus55.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3571,GridMinus.atNode 3571,GridMinus.atNode 3572,NodeMinus55.w51,CompactMinus3568.checked3571,CompactMinus3568.small3571,CompactMinus3568.nodes3571,NodeMinus55.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3572,GridMinus.atNode 3572,GridMinus.atNode 3573,NodeMinus55.w52,CompactMinus3568.checked3572,CompactMinus3568.small3572,CompactMinus3568.nodes3572,NodeMinus55.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3573,GridMinus.atNode 3573,GridMinus.atNode 3574,NodeMinus55.w53,CompactMinus3568.checked3573,CompactMinus3568.small3573,CompactMinus3568.nodes3573,NodeMinus55.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3574,GridMinus.atNode 3574,GridMinus.atNode 3575,NodeMinus55.w54,CompactMinus3568.checked3574,CompactMinus3568.small3574,CompactMinus3568.nodes3574,NodeMinus55.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3575,GridMinus.atNode 3575,GridMinus.atNode 3576,NodeMinus55.w55,CompactMinus3568.checked3575,CompactMinus3568.small3575,CompactMinus3568.nodes3575,NodeMinus55.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3576,GridMinus.atNode 3576,GridMinus.atNode 3577,NodeMinus55.w56,CompactMinus3568.checked3576,CompactMinus3568.small3576,CompactMinus3568.nodes3576,NodeMinus55.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3577,GridMinus.atNode 3577,GridMinus.atNode 3578,NodeMinus55.w57,CompactMinus3568.checked3577,CompactMinus3568.small3577,CompactMinus3568.nodes3577,NodeMinus55.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3578,GridMinus.atNode 3578,GridMinus.atNode 3579,NodeMinus55.w58,CompactMinus3568.checked3578,CompactMinus3568.small3578,CompactMinus3568.nodes3578,NodeMinus55.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3579,GridMinus.atNode 3579,GridMinus.atNode 3580,NodeMinus55.w59,CompactMinus3568.checked3579,CompactMinus3568.small3579,CompactMinus3568.nodes3579,NodeMinus55.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3580,GridMinus.atNode 3580,GridMinus.atNode 3581,NodeMinus55.w60,CompactMinus3568.checked3580,CompactMinus3568.small3580,CompactMinus3568.nodes3580,NodeMinus55.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3581,GridMinus.atNode 3581,GridMinus.atNode 3582,NodeMinus55.w61,CompactMinus3568.checked3581,CompactMinus3568.small3581,CompactMinus3568.nodes3581,NodeMinus55.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3582,GridMinus.atNode 3582,GridMinus.atNode 3583,NodeMinus55.w62,CompactMinus3568.checked3582,CompactMinus3568.small3582,CompactMinus3568.nodes3582,NodeMinus55.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3568.p3583,GridMinus.atNode 3583,GridMinus.atNode 3584,NodeMinus55.w63,CompactMinus3568.checked3583,CompactMinus3568.small3583,CompactMinus3568.nodes3583,NodeMinus55.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3520+j) ∧
    (atRow j).right=GridMinus.atNode (3520+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus55
