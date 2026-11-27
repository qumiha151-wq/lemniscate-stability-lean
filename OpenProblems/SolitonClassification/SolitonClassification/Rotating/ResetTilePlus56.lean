import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3584
import SolitonClassification.Rotating.ResetPackedPlus3600
import SolitonClassification.Rotating.ResetPackedPlus3616
import SolitonClassification.Rotating.ResetPackedPlus3632
namespace SolitonClassification.Rotating.DyadicReset.TilePlus56
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3584,GridPlus.atNode 3584,GridPlus.atNode 3585,NodePlus56.w0,CompactPlus3584.checked3584,CompactPlus3584.small3584,CompactPlus3584.nodes3584,NodePlus56.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3585,GridPlus.atNode 3585,GridPlus.atNode 3586,NodePlus56.w1,CompactPlus3584.checked3585,CompactPlus3584.small3585,CompactPlus3584.nodes3585,NodePlus56.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3586,GridPlus.atNode 3586,GridPlus.atNode 3587,NodePlus56.w2,CompactPlus3584.checked3586,CompactPlus3584.small3586,CompactPlus3584.nodes3586,NodePlus56.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3587,GridPlus.atNode 3587,GridPlus.atNode 3588,NodePlus56.w3,CompactPlus3584.checked3587,CompactPlus3584.small3587,CompactPlus3584.nodes3587,NodePlus56.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3588,GridPlus.atNode 3588,GridPlus.atNode 3589,NodePlus56.w4,CompactPlus3584.checked3588,CompactPlus3584.small3588,CompactPlus3584.nodes3588,NodePlus56.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3589,GridPlus.atNode 3589,GridPlus.atNode 3590,NodePlus56.w5,CompactPlus3584.checked3589,CompactPlus3584.small3589,CompactPlus3584.nodes3589,NodePlus56.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3590,GridPlus.atNode 3590,GridPlus.atNode 3591,NodePlus56.w6,CompactPlus3584.checked3590,CompactPlus3584.small3590,CompactPlus3584.nodes3590,NodePlus56.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3591,GridPlus.atNode 3591,GridPlus.atNode 3592,NodePlus56.w7,CompactPlus3584.checked3591,CompactPlus3584.small3591,CompactPlus3584.nodes3591,NodePlus56.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3592,GridPlus.atNode 3592,GridPlus.atNode 3593,NodePlus56.w8,CompactPlus3584.checked3592,CompactPlus3584.small3592,CompactPlus3584.nodes3592,NodePlus56.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3593,GridPlus.atNode 3593,GridPlus.atNode 3594,NodePlus56.w9,CompactPlus3584.checked3593,CompactPlus3584.small3593,CompactPlus3584.nodes3593,NodePlus56.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3594,GridPlus.atNode 3594,GridPlus.atNode 3595,NodePlus56.w10,CompactPlus3584.checked3594,CompactPlus3584.small3594,CompactPlus3584.nodes3594,NodePlus56.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3595,GridPlus.atNode 3595,GridPlus.atNode 3596,NodePlus56.w11,CompactPlus3584.checked3595,CompactPlus3584.small3595,CompactPlus3584.nodes3595,NodePlus56.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3596,GridPlus.atNode 3596,GridPlus.atNode 3597,NodePlus56.w12,CompactPlus3584.checked3596,CompactPlus3584.small3596,CompactPlus3584.nodes3596,NodePlus56.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3597,GridPlus.atNode 3597,GridPlus.atNode 3598,NodePlus56.w13,CompactPlus3584.checked3597,CompactPlus3584.small3597,CompactPlus3584.nodes3597,NodePlus56.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3598,GridPlus.atNode 3598,GridPlus.atNode 3599,NodePlus56.w14,CompactPlus3584.checked3598,CompactPlus3584.small3598,CompactPlus3584.nodes3598,NodePlus56.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3584.p3599,GridPlus.atNode 3599,GridPlus.atNode 3600,NodePlus56.w15,CompactPlus3584.checked3599,CompactPlus3584.small3599,CompactPlus3584.nodes3599,NodePlus56.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3600,GridPlus.atNode 3600,GridPlus.atNode 3601,NodePlus56.w16,CompactPlus3600.checked3600,CompactPlus3600.small3600,CompactPlus3600.nodes3600,NodePlus56.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3601,GridPlus.atNode 3601,GridPlus.atNode 3602,NodePlus56.w17,CompactPlus3600.checked3601,CompactPlus3600.small3601,CompactPlus3600.nodes3601,NodePlus56.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3602,GridPlus.atNode 3602,GridPlus.atNode 3603,NodePlus56.w18,CompactPlus3600.checked3602,CompactPlus3600.small3602,CompactPlus3600.nodes3602,NodePlus56.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3603,GridPlus.atNode 3603,GridPlus.atNode 3604,NodePlus56.w19,CompactPlus3600.checked3603,CompactPlus3600.small3603,CompactPlus3600.nodes3603,NodePlus56.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3604,GridPlus.atNode 3604,GridPlus.atNode 3605,NodePlus56.w20,CompactPlus3600.checked3604,CompactPlus3600.small3604,CompactPlus3600.nodes3604,NodePlus56.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3605,GridPlus.atNode 3605,GridPlus.atNode 3606,NodePlus56.w21,CompactPlus3600.checked3605,CompactPlus3600.small3605,CompactPlus3600.nodes3605,NodePlus56.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3606,GridPlus.atNode 3606,GridPlus.atNode 3607,NodePlus56.w22,CompactPlus3600.checked3606,CompactPlus3600.small3606,CompactPlus3600.nodes3606,NodePlus56.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3607,GridPlus.atNode 3607,GridPlus.atNode 3608,NodePlus56.w23,CompactPlus3600.checked3607,CompactPlus3600.small3607,CompactPlus3600.nodes3607,NodePlus56.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3608,GridPlus.atNode 3608,GridPlus.atNode 3609,NodePlus56.w24,CompactPlus3600.checked3608,CompactPlus3600.small3608,CompactPlus3600.nodes3608,NodePlus56.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3609,GridPlus.atNode 3609,GridPlus.atNode 3610,NodePlus56.w25,CompactPlus3600.checked3609,CompactPlus3600.small3609,CompactPlus3600.nodes3609,NodePlus56.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3610,GridPlus.atNode 3610,GridPlus.atNode 3611,NodePlus56.w26,CompactPlus3600.checked3610,CompactPlus3600.small3610,CompactPlus3600.nodes3610,NodePlus56.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3611,GridPlus.atNode 3611,GridPlus.atNode 3612,NodePlus56.w27,CompactPlus3600.checked3611,CompactPlus3600.small3611,CompactPlus3600.nodes3611,NodePlus56.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3612,GridPlus.atNode 3612,GridPlus.atNode 3613,NodePlus56.w28,CompactPlus3600.checked3612,CompactPlus3600.small3612,CompactPlus3600.nodes3612,NodePlus56.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3613,GridPlus.atNode 3613,GridPlus.atNode 3614,NodePlus56.w29,CompactPlus3600.checked3613,CompactPlus3600.small3613,CompactPlus3600.nodes3613,NodePlus56.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3614,GridPlus.atNode 3614,GridPlus.atNode 3615,NodePlus56.w30,CompactPlus3600.checked3614,CompactPlus3600.small3614,CompactPlus3600.nodes3614,NodePlus56.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3600.p3615,GridPlus.atNode 3615,GridPlus.atNode 3616,NodePlus56.w31,CompactPlus3600.checked3615,CompactPlus3600.small3615,CompactPlus3600.nodes3615,NodePlus56.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3616,GridPlus.atNode 3616,GridPlus.atNode 3617,NodePlus56.w32,CompactPlus3616.checked3616,CompactPlus3616.small3616,CompactPlus3616.nodes3616,NodePlus56.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3617,GridPlus.atNode 3617,GridPlus.atNode 3618,NodePlus56.w33,CompactPlus3616.checked3617,CompactPlus3616.small3617,CompactPlus3616.nodes3617,NodePlus56.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3618,GridPlus.atNode 3618,GridPlus.atNode 3619,NodePlus56.w34,CompactPlus3616.checked3618,CompactPlus3616.small3618,CompactPlus3616.nodes3618,NodePlus56.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3619,GridPlus.atNode 3619,GridPlus.atNode 3620,NodePlus56.w35,CompactPlus3616.checked3619,CompactPlus3616.small3619,CompactPlus3616.nodes3619,NodePlus56.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3620,GridPlus.atNode 3620,GridPlus.atNode 3621,NodePlus56.w36,CompactPlus3616.checked3620,CompactPlus3616.small3620,CompactPlus3616.nodes3620,NodePlus56.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3621,GridPlus.atNode 3621,GridPlus.atNode 3622,NodePlus56.w37,CompactPlus3616.checked3621,CompactPlus3616.small3621,CompactPlus3616.nodes3621,NodePlus56.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3622,GridPlus.atNode 3622,GridPlus.atNode 3623,NodePlus56.w38,CompactPlus3616.checked3622,CompactPlus3616.small3622,CompactPlus3616.nodes3622,NodePlus56.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3623,GridPlus.atNode 3623,GridPlus.atNode 3624,NodePlus56.w39,CompactPlus3616.checked3623,CompactPlus3616.small3623,CompactPlus3616.nodes3623,NodePlus56.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3624,GridPlus.atNode 3624,GridPlus.atNode 3625,NodePlus56.w40,CompactPlus3616.checked3624,CompactPlus3616.small3624,CompactPlus3616.nodes3624,NodePlus56.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3625,GridPlus.atNode 3625,GridPlus.atNode 3626,NodePlus56.w41,CompactPlus3616.checked3625,CompactPlus3616.small3625,CompactPlus3616.nodes3625,NodePlus56.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3626,GridPlus.atNode 3626,GridPlus.atNode 3627,NodePlus56.w42,CompactPlus3616.checked3626,CompactPlus3616.small3626,CompactPlus3616.nodes3626,NodePlus56.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3627,GridPlus.atNode 3627,GridPlus.atNode 3628,NodePlus56.w43,CompactPlus3616.checked3627,CompactPlus3616.small3627,CompactPlus3616.nodes3627,NodePlus56.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3628,GridPlus.atNode 3628,GridPlus.atNode 3629,NodePlus56.w44,CompactPlus3616.checked3628,CompactPlus3616.small3628,CompactPlus3616.nodes3628,NodePlus56.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3629,GridPlus.atNode 3629,GridPlus.atNode 3630,NodePlus56.w45,CompactPlus3616.checked3629,CompactPlus3616.small3629,CompactPlus3616.nodes3629,NodePlus56.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3630,GridPlus.atNode 3630,GridPlus.atNode 3631,NodePlus56.w46,CompactPlus3616.checked3630,CompactPlus3616.small3630,CompactPlus3616.nodes3630,NodePlus56.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3616.p3631,GridPlus.atNode 3631,GridPlus.atNode 3632,NodePlus56.w47,CompactPlus3616.checked3631,CompactPlus3616.small3631,CompactPlus3616.nodes3631,NodePlus56.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3632,GridPlus.atNode 3632,GridPlus.atNode 3633,NodePlus56.w48,CompactPlus3632.checked3632,CompactPlus3632.small3632,CompactPlus3632.nodes3632,NodePlus56.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3633,GridPlus.atNode 3633,GridPlus.atNode 3634,NodePlus56.w49,CompactPlus3632.checked3633,CompactPlus3632.small3633,CompactPlus3632.nodes3633,NodePlus56.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3634,GridPlus.atNode 3634,GridPlus.atNode 3635,NodePlus56.w50,CompactPlus3632.checked3634,CompactPlus3632.small3634,CompactPlus3632.nodes3634,NodePlus56.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3635,GridPlus.atNode 3635,GridPlus.atNode 3636,NodePlus56.w51,CompactPlus3632.checked3635,CompactPlus3632.small3635,CompactPlus3632.nodes3635,NodePlus56.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3636,GridPlus.atNode 3636,GridPlus.atNode 3637,NodePlus56.w52,CompactPlus3632.checked3636,CompactPlus3632.small3636,CompactPlus3632.nodes3636,NodePlus56.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3637,GridPlus.atNode 3637,GridPlus.atNode 3638,NodePlus56.w53,CompactPlus3632.checked3637,CompactPlus3632.small3637,CompactPlus3632.nodes3637,NodePlus56.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3638,GridPlus.atNode 3638,GridPlus.atNode 3639,NodePlus56.w54,CompactPlus3632.checked3638,CompactPlus3632.small3638,CompactPlus3632.nodes3638,NodePlus56.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3639,GridPlus.atNode 3639,GridPlus.atNode 3640,NodePlus56.w55,CompactPlus3632.checked3639,CompactPlus3632.small3639,CompactPlus3632.nodes3639,NodePlus56.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3640,GridPlus.atNode 3640,GridPlus.atNode 3641,NodePlus56.w56,CompactPlus3632.checked3640,CompactPlus3632.small3640,CompactPlus3632.nodes3640,NodePlus56.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3641,GridPlus.atNode 3641,GridPlus.atNode 3642,NodePlus56.w57,CompactPlus3632.checked3641,CompactPlus3632.small3641,CompactPlus3632.nodes3641,NodePlus56.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3642,GridPlus.atNode 3642,GridPlus.atNode 3643,NodePlus56.w58,CompactPlus3632.checked3642,CompactPlus3632.small3642,CompactPlus3632.nodes3642,NodePlus56.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3643,GridPlus.atNode 3643,GridPlus.atNode 3644,NodePlus56.w59,CompactPlus3632.checked3643,CompactPlus3632.small3643,CompactPlus3632.nodes3643,NodePlus56.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3644,GridPlus.atNode 3644,GridPlus.atNode 3645,NodePlus56.w60,CompactPlus3632.checked3644,CompactPlus3632.small3644,CompactPlus3632.nodes3644,NodePlus56.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3645,GridPlus.atNode 3645,GridPlus.atNode 3646,NodePlus56.w61,CompactPlus3632.checked3645,CompactPlus3632.small3645,CompactPlus3632.nodes3645,NodePlus56.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3646,GridPlus.atNode 3646,GridPlus.atNode 3647,NodePlus56.w62,CompactPlus3632.checked3646,CompactPlus3632.small3646,CompactPlus3632.nodes3646,NodePlus56.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3632.p3647,GridPlus.atNode 3647,GridPlus.atNode 3648,NodePlus56.w63,CompactPlus3632.checked3647,CompactPlus3632.small3647,CompactPlus3632.nodes3647,NodePlus56.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3584+j) ∧
    (atRow j).right=GridPlus.atNode (3584+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus56
