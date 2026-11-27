import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3520
import SolitonClassification.Rotating.ResetPackedPlus3536
import SolitonClassification.Rotating.ResetPackedPlus3552
import SolitonClassification.Rotating.ResetPackedPlus3568
namespace SolitonClassification.Rotating.DyadicReset.TilePlus55
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3520,GridPlus.atNode 3520,GridPlus.atNode 3521,NodePlus55.w0,CompactPlus3520.checked3520,CompactPlus3520.small3520,CompactPlus3520.nodes3520,NodePlus55.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3521,GridPlus.atNode 3521,GridPlus.atNode 3522,NodePlus55.w1,CompactPlus3520.checked3521,CompactPlus3520.small3521,CompactPlus3520.nodes3521,NodePlus55.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3522,GridPlus.atNode 3522,GridPlus.atNode 3523,NodePlus55.w2,CompactPlus3520.checked3522,CompactPlus3520.small3522,CompactPlus3520.nodes3522,NodePlus55.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3523,GridPlus.atNode 3523,GridPlus.atNode 3524,NodePlus55.w3,CompactPlus3520.checked3523,CompactPlus3520.small3523,CompactPlus3520.nodes3523,NodePlus55.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3524,GridPlus.atNode 3524,GridPlus.atNode 3525,NodePlus55.w4,CompactPlus3520.checked3524,CompactPlus3520.small3524,CompactPlus3520.nodes3524,NodePlus55.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3525,GridPlus.atNode 3525,GridPlus.atNode 3526,NodePlus55.w5,CompactPlus3520.checked3525,CompactPlus3520.small3525,CompactPlus3520.nodes3525,NodePlus55.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3526,GridPlus.atNode 3526,GridPlus.atNode 3527,NodePlus55.w6,CompactPlus3520.checked3526,CompactPlus3520.small3526,CompactPlus3520.nodes3526,NodePlus55.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3527,GridPlus.atNode 3527,GridPlus.atNode 3528,NodePlus55.w7,CompactPlus3520.checked3527,CompactPlus3520.small3527,CompactPlus3520.nodes3527,NodePlus55.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3528,GridPlus.atNode 3528,GridPlus.atNode 3529,NodePlus55.w8,CompactPlus3520.checked3528,CompactPlus3520.small3528,CompactPlus3520.nodes3528,NodePlus55.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3529,GridPlus.atNode 3529,GridPlus.atNode 3530,NodePlus55.w9,CompactPlus3520.checked3529,CompactPlus3520.small3529,CompactPlus3520.nodes3529,NodePlus55.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3530,GridPlus.atNode 3530,GridPlus.atNode 3531,NodePlus55.w10,CompactPlus3520.checked3530,CompactPlus3520.small3530,CompactPlus3520.nodes3530,NodePlus55.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3531,GridPlus.atNode 3531,GridPlus.atNode 3532,NodePlus55.w11,CompactPlus3520.checked3531,CompactPlus3520.small3531,CompactPlus3520.nodes3531,NodePlus55.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3532,GridPlus.atNode 3532,GridPlus.atNode 3533,NodePlus55.w12,CompactPlus3520.checked3532,CompactPlus3520.small3532,CompactPlus3520.nodes3532,NodePlus55.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3533,GridPlus.atNode 3533,GridPlus.atNode 3534,NodePlus55.w13,CompactPlus3520.checked3533,CompactPlus3520.small3533,CompactPlus3520.nodes3533,NodePlus55.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3534,GridPlus.atNode 3534,GridPlus.atNode 3535,NodePlus55.w14,CompactPlus3520.checked3534,CompactPlus3520.small3534,CompactPlus3520.nodes3534,NodePlus55.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3520.p3535,GridPlus.atNode 3535,GridPlus.atNode 3536,NodePlus55.w15,CompactPlus3520.checked3535,CompactPlus3520.small3535,CompactPlus3520.nodes3535,NodePlus55.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3536,GridPlus.atNode 3536,GridPlus.atNode 3537,NodePlus55.w16,CompactPlus3536.checked3536,CompactPlus3536.small3536,CompactPlus3536.nodes3536,NodePlus55.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3537,GridPlus.atNode 3537,GridPlus.atNode 3538,NodePlus55.w17,CompactPlus3536.checked3537,CompactPlus3536.small3537,CompactPlus3536.nodes3537,NodePlus55.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3538,GridPlus.atNode 3538,GridPlus.atNode 3539,NodePlus55.w18,CompactPlus3536.checked3538,CompactPlus3536.small3538,CompactPlus3536.nodes3538,NodePlus55.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3539,GridPlus.atNode 3539,GridPlus.atNode 3540,NodePlus55.w19,CompactPlus3536.checked3539,CompactPlus3536.small3539,CompactPlus3536.nodes3539,NodePlus55.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3540,GridPlus.atNode 3540,GridPlus.atNode 3541,NodePlus55.w20,CompactPlus3536.checked3540,CompactPlus3536.small3540,CompactPlus3536.nodes3540,NodePlus55.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3541,GridPlus.atNode 3541,GridPlus.atNode 3542,NodePlus55.w21,CompactPlus3536.checked3541,CompactPlus3536.small3541,CompactPlus3536.nodes3541,NodePlus55.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3542,GridPlus.atNode 3542,GridPlus.atNode 3543,NodePlus55.w22,CompactPlus3536.checked3542,CompactPlus3536.small3542,CompactPlus3536.nodes3542,NodePlus55.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3543,GridPlus.atNode 3543,GridPlus.atNode 3544,NodePlus55.w23,CompactPlus3536.checked3543,CompactPlus3536.small3543,CompactPlus3536.nodes3543,NodePlus55.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3544,GridPlus.atNode 3544,GridPlus.atNode 3545,NodePlus55.w24,CompactPlus3536.checked3544,CompactPlus3536.small3544,CompactPlus3536.nodes3544,NodePlus55.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3545,GridPlus.atNode 3545,GridPlus.atNode 3546,NodePlus55.w25,CompactPlus3536.checked3545,CompactPlus3536.small3545,CompactPlus3536.nodes3545,NodePlus55.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3546,GridPlus.atNode 3546,GridPlus.atNode 3547,NodePlus55.w26,CompactPlus3536.checked3546,CompactPlus3536.small3546,CompactPlus3536.nodes3546,NodePlus55.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3547,GridPlus.atNode 3547,GridPlus.atNode 3548,NodePlus55.w27,CompactPlus3536.checked3547,CompactPlus3536.small3547,CompactPlus3536.nodes3547,NodePlus55.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3548,GridPlus.atNode 3548,GridPlus.atNode 3549,NodePlus55.w28,CompactPlus3536.checked3548,CompactPlus3536.small3548,CompactPlus3536.nodes3548,NodePlus55.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3549,GridPlus.atNode 3549,GridPlus.atNode 3550,NodePlus55.w29,CompactPlus3536.checked3549,CompactPlus3536.small3549,CompactPlus3536.nodes3549,NodePlus55.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3550,GridPlus.atNode 3550,GridPlus.atNode 3551,NodePlus55.w30,CompactPlus3536.checked3550,CompactPlus3536.small3550,CompactPlus3536.nodes3550,NodePlus55.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3536.p3551,GridPlus.atNode 3551,GridPlus.atNode 3552,NodePlus55.w31,CompactPlus3536.checked3551,CompactPlus3536.small3551,CompactPlus3536.nodes3551,NodePlus55.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3552,GridPlus.atNode 3552,GridPlus.atNode 3553,NodePlus55.w32,CompactPlus3552.checked3552,CompactPlus3552.small3552,CompactPlus3552.nodes3552,NodePlus55.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3553,GridPlus.atNode 3553,GridPlus.atNode 3554,NodePlus55.w33,CompactPlus3552.checked3553,CompactPlus3552.small3553,CompactPlus3552.nodes3553,NodePlus55.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3554,GridPlus.atNode 3554,GridPlus.atNode 3555,NodePlus55.w34,CompactPlus3552.checked3554,CompactPlus3552.small3554,CompactPlus3552.nodes3554,NodePlus55.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3555,GridPlus.atNode 3555,GridPlus.atNode 3556,NodePlus55.w35,CompactPlus3552.checked3555,CompactPlus3552.small3555,CompactPlus3552.nodes3555,NodePlus55.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3556,GridPlus.atNode 3556,GridPlus.atNode 3557,NodePlus55.w36,CompactPlus3552.checked3556,CompactPlus3552.small3556,CompactPlus3552.nodes3556,NodePlus55.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3557,GridPlus.atNode 3557,GridPlus.atNode 3558,NodePlus55.w37,CompactPlus3552.checked3557,CompactPlus3552.small3557,CompactPlus3552.nodes3557,NodePlus55.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3558,GridPlus.atNode 3558,GridPlus.atNode 3559,NodePlus55.w38,CompactPlus3552.checked3558,CompactPlus3552.small3558,CompactPlus3552.nodes3558,NodePlus55.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3559,GridPlus.atNode 3559,GridPlus.atNode 3560,NodePlus55.w39,CompactPlus3552.checked3559,CompactPlus3552.small3559,CompactPlus3552.nodes3559,NodePlus55.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3560,GridPlus.atNode 3560,GridPlus.atNode 3561,NodePlus55.w40,CompactPlus3552.checked3560,CompactPlus3552.small3560,CompactPlus3552.nodes3560,NodePlus55.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3561,GridPlus.atNode 3561,GridPlus.atNode 3562,NodePlus55.w41,CompactPlus3552.checked3561,CompactPlus3552.small3561,CompactPlus3552.nodes3561,NodePlus55.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3562,GridPlus.atNode 3562,GridPlus.atNode 3563,NodePlus55.w42,CompactPlus3552.checked3562,CompactPlus3552.small3562,CompactPlus3552.nodes3562,NodePlus55.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3563,GridPlus.atNode 3563,GridPlus.atNode 3564,NodePlus55.w43,CompactPlus3552.checked3563,CompactPlus3552.small3563,CompactPlus3552.nodes3563,NodePlus55.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3564,GridPlus.atNode 3564,GridPlus.atNode 3565,NodePlus55.w44,CompactPlus3552.checked3564,CompactPlus3552.small3564,CompactPlus3552.nodes3564,NodePlus55.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3565,GridPlus.atNode 3565,GridPlus.atNode 3566,NodePlus55.w45,CompactPlus3552.checked3565,CompactPlus3552.small3565,CompactPlus3552.nodes3565,NodePlus55.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3566,GridPlus.atNode 3566,GridPlus.atNode 3567,NodePlus55.w46,CompactPlus3552.checked3566,CompactPlus3552.small3566,CompactPlus3552.nodes3566,NodePlus55.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3552.p3567,GridPlus.atNode 3567,GridPlus.atNode 3568,NodePlus55.w47,CompactPlus3552.checked3567,CompactPlus3552.small3567,CompactPlus3552.nodes3567,NodePlus55.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3568,GridPlus.atNode 3568,GridPlus.atNode 3569,NodePlus55.w48,CompactPlus3568.checked3568,CompactPlus3568.small3568,CompactPlus3568.nodes3568,NodePlus55.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3569,GridPlus.atNode 3569,GridPlus.atNode 3570,NodePlus55.w49,CompactPlus3568.checked3569,CompactPlus3568.small3569,CompactPlus3568.nodes3569,NodePlus55.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3570,GridPlus.atNode 3570,GridPlus.atNode 3571,NodePlus55.w50,CompactPlus3568.checked3570,CompactPlus3568.small3570,CompactPlus3568.nodes3570,NodePlus55.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3571,GridPlus.atNode 3571,GridPlus.atNode 3572,NodePlus55.w51,CompactPlus3568.checked3571,CompactPlus3568.small3571,CompactPlus3568.nodes3571,NodePlus55.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3572,GridPlus.atNode 3572,GridPlus.atNode 3573,NodePlus55.w52,CompactPlus3568.checked3572,CompactPlus3568.small3572,CompactPlus3568.nodes3572,NodePlus55.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3573,GridPlus.atNode 3573,GridPlus.atNode 3574,NodePlus55.w53,CompactPlus3568.checked3573,CompactPlus3568.small3573,CompactPlus3568.nodes3573,NodePlus55.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3574,GridPlus.atNode 3574,GridPlus.atNode 3575,NodePlus55.w54,CompactPlus3568.checked3574,CompactPlus3568.small3574,CompactPlus3568.nodes3574,NodePlus55.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3575,GridPlus.atNode 3575,GridPlus.atNode 3576,NodePlus55.w55,CompactPlus3568.checked3575,CompactPlus3568.small3575,CompactPlus3568.nodes3575,NodePlus55.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3576,GridPlus.atNode 3576,GridPlus.atNode 3577,NodePlus55.w56,CompactPlus3568.checked3576,CompactPlus3568.small3576,CompactPlus3568.nodes3576,NodePlus55.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3577,GridPlus.atNode 3577,GridPlus.atNode 3578,NodePlus55.w57,CompactPlus3568.checked3577,CompactPlus3568.small3577,CompactPlus3568.nodes3577,NodePlus55.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3578,GridPlus.atNode 3578,GridPlus.atNode 3579,NodePlus55.w58,CompactPlus3568.checked3578,CompactPlus3568.small3578,CompactPlus3568.nodes3578,NodePlus55.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3579,GridPlus.atNode 3579,GridPlus.atNode 3580,NodePlus55.w59,CompactPlus3568.checked3579,CompactPlus3568.small3579,CompactPlus3568.nodes3579,NodePlus55.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3580,GridPlus.atNode 3580,GridPlus.atNode 3581,NodePlus55.w60,CompactPlus3568.checked3580,CompactPlus3568.small3580,CompactPlus3568.nodes3580,NodePlus55.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3581,GridPlus.atNode 3581,GridPlus.atNode 3582,NodePlus55.w61,CompactPlus3568.checked3581,CompactPlus3568.small3581,CompactPlus3568.nodes3581,NodePlus55.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3582,GridPlus.atNode 3582,GridPlus.atNode 3583,NodePlus55.w62,CompactPlus3568.checked3582,CompactPlus3568.small3582,CompactPlus3568.nodes3582,NodePlus55.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3568.p3583,GridPlus.atNode 3583,GridPlus.atNode 3584,NodePlus55.w63,CompactPlus3568.checked3583,CompactPlus3568.small3583,CompactPlus3568.nodes3583,NodePlus55.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3520+j) ∧
    (atRow j).right=GridPlus.atNode (3520+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus55
