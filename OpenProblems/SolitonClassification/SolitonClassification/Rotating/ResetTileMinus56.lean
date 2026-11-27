import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3584
import SolitonClassification.Rotating.ResetPackedMinus3600
import SolitonClassification.Rotating.ResetPackedMinus3616
import SolitonClassification.Rotating.ResetPackedMinus3632
namespace SolitonClassification.Rotating.DyadicReset.TileMinus56
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3584,GridMinus.atNode 3584,GridMinus.atNode 3585,NodeMinus56.w0,CompactMinus3584.checked3584,CompactMinus3584.small3584,CompactMinus3584.nodes3584,NodeMinus56.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3585,GridMinus.atNode 3585,GridMinus.atNode 3586,NodeMinus56.w1,CompactMinus3584.checked3585,CompactMinus3584.small3585,CompactMinus3584.nodes3585,NodeMinus56.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3586,GridMinus.atNode 3586,GridMinus.atNode 3587,NodeMinus56.w2,CompactMinus3584.checked3586,CompactMinus3584.small3586,CompactMinus3584.nodes3586,NodeMinus56.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3587,GridMinus.atNode 3587,GridMinus.atNode 3588,NodeMinus56.w3,CompactMinus3584.checked3587,CompactMinus3584.small3587,CompactMinus3584.nodes3587,NodeMinus56.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3588,GridMinus.atNode 3588,GridMinus.atNode 3589,NodeMinus56.w4,CompactMinus3584.checked3588,CompactMinus3584.small3588,CompactMinus3584.nodes3588,NodeMinus56.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3589,GridMinus.atNode 3589,GridMinus.atNode 3590,NodeMinus56.w5,CompactMinus3584.checked3589,CompactMinus3584.small3589,CompactMinus3584.nodes3589,NodeMinus56.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3590,GridMinus.atNode 3590,GridMinus.atNode 3591,NodeMinus56.w6,CompactMinus3584.checked3590,CompactMinus3584.small3590,CompactMinus3584.nodes3590,NodeMinus56.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3591,GridMinus.atNode 3591,GridMinus.atNode 3592,NodeMinus56.w7,CompactMinus3584.checked3591,CompactMinus3584.small3591,CompactMinus3584.nodes3591,NodeMinus56.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3592,GridMinus.atNode 3592,GridMinus.atNode 3593,NodeMinus56.w8,CompactMinus3584.checked3592,CompactMinus3584.small3592,CompactMinus3584.nodes3592,NodeMinus56.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3593,GridMinus.atNode 3593,GridMinus.atNode 3594,NodeMinus56.w9,CompactMinus3584.checked3593,CompactMinus3584.small3593,CompactMinus3584.nodes3593,NodeMinus56.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3594,GridMinus.atNode 3594,GridMinus.atNode 3595,NodeMinus56.w10,CompactMinus3584.checked3594,CompactMinus3584.small3594,CompactMinus3584.nodes3594,NodeMinus56.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3595,GridMinus.atNode 3595,GridMinus.atNode 3596,NodeMinus56.w11,CompactMinus3584.checked3595,CompactMinus3584.small3595,CompactMinus3584.nodes3595,NodeMinus56.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3596,GridMinus.atNode 3596,GridMinus.atNode 3597,NodeMinus56.w12,CompactMinus3584.checked3596,CompactMinus3584.small3596,CompactMinus3584.nodes3596,NodeMinus56.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3597,GridMinus.atNode 3597,GridMinus.atNode 3598,NodeMinus56.w13,CompactMinus3584.checked3597,CompactMinus3584.small3597,CompactMinus3584.nodes3597,NodeMinus56.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3598,GridMinus.atNode 3598,GridMinus.atNode 3599,NodeMinus56.w14,CompactMinus3584.checked3598,CompactMinus3584.small3598,CompactMinus3584.nodes3598,NodeMinus56.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3584.p3599,GridMinus.atNode 3599,GridMinus.atNode 3600,NodeMinus56.w15,CompactMinus3584.checked3599,CompactMinus3584.small3599,CompactMinus3584.nodes3599,NodeMinus56.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3600,GridMinus.atNode 3600,GridMinus.atNode 3601,NodeMinus56.w16,CompactMinus3600.checked3600,CompactMinus3600.small3600,CompactMinus3600.nodes3600,NodeMinus56.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3601,GridMinus.atNode 3601,GridMinus.atNode 3602,NodeMinus56.w17,CompactMinus3600.checked3601,CompactMinus3600.small3601,CompactMinus3600.nodes3601,NodeMinus56.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3602,GridMinus.atNode 3602,GridMinus.atNode 3603,NodeMinus56.w18,CompactMinus3600.checked3602,CompactMinus3600.small3602,CompactMinus3600.nodes3602,NodeMinus56.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3603,GridMinus.atNode 3603,GridMinus.atNode 3604,NodeMinus56.w19,CompactMinus3600.checked3603,CompactMinus3600.small3603,CompactMinus3600.nodes3603,NodeMinus56.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3604,GridMinus.atNode 3604,GridMinus.atNode 3605,NodeMinus56.w20,CompactMinus3600.checked3604,CompactMinus3600.small3604,CompactMinus3600.nodes3604,NodeMinus56.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3605,GridMinus.atNode 3605,GridMinus.atNode 3606,NodeMinus56.w21,CompactMinus3600.checked3605,CompactMinus3600.small3605,CompactMinus3600.nodes3605,NodeMinus56.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3606,GridMinus.atNode 3606,GridMinus.atNode 3607,NodeMinus56.w22,CompactMinus3600.checked3606,CompactMinus3600.small3606,CompactMinus3600.nodes3606,NodeMinus56.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3607,GridMinus.atNode 3607,GridMinus.atNode 3608,NodeMinus56.w23,CompactMinus3600.checked3607,CompactMinus3600.small3607,CompactMinus3600.nodes3607,NodeMinus56.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3608,GridMinus.atNode 3608,GridMinus.atNode 3609,NodeMinus56.w24,CompactMinus3600.checked3608,CompactMinus3600.small3608,CompactMinus3600.nodes3608,NodeMinus56.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3609,GridMinus.atNode 3609,GridMinus.atNode 3610,NodeMinus56.w25,CompactMinus3600.checked3609,CompactMinus3600.small3609,CompactMinus3600.nodes3609,NodeMinus56.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3610,GridMinus.atNode 3610,GridMinus.atNode 3611,NodeMinus56.w26,CompactMinus3600.checked3610,CompactMinus3600.small3610,CompactMinus3600.nodes3610,NodeMinus56.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3611,GridMinus.atNode 3611,GridMinus.atNode 3612,NodeMinus56.w27,CompactMinus3600.checked3611,CompactMinus3600.small3611,CompactMinus3600.nodes3611,NodeMinus56.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3612,GridMinus.atNode 3612,GridMinus.atNode 3613,NodeMinus56.w28,CompactMinus3600.checked3612,CompactMinus3600.small3612,CompactMinus3600.nodes3612,NodeMinus56.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3613,GridMinus.atNode 3613,GridMinus.atNode 3614,NodeMinus56.w29,CompactMinus3600.checked3613,CompactMinus3600.small3613,CompactMinus3600.nodes3613,NodeMinus56.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3614,GridMinus.atNode 3614,GridMinus.atNode 3615,NodeMinus56.w30,CompactMinus3600.checked3614,CompactMinus3600.small3614,CompactMinus3600.nodes3614,NodeMinus56.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3600.p3615,GridMinus.atNode 3615,GridMinus.atNode 3616,NodeMinus56.w31,CompactMinus3600.checked3615,CompactMinus3600.small3615,CompactMinus3600.nodes3615,NodeMinus56.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3616,GridMinus.atNode 3616,GridMinus.atNode 3617,NodeMinus56.w32,CompactMinus3616.checked3616,CompactMinus3616.small3616,CompactMinus3616.nodes3616,NodeMinus56.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3617,GridMinus.atNode 3617,GridMinus.atNode 3618,NodeMinus56.w33,CompactMinus3616.checked3617,CompactMinus3616.small3617,CompactMinus3616.nodes3617,NodeMinus56.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3618,GridMinus.atNode 3618,GridMinus.atNode 3619,NodeMinus56.w34,CompactMinus3616.checked3618,CompactMinus3616.small3618,CompactMinus3616.nodes3618,NodeMinus56.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3619,GridMinus.atNode 3619,GridMinus.atNode 3620,NodeMinus56.w35,CompactMinus3616.checked3619,CompactMinus3616.small3619,CompactMinus3616.nodes3619,NodeMinus56.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3620,GridMinus.atNode 3620,GridMinus.atNode 3621,NodeMinus56.w36,CompactMinus3616.checked3620,CompactMinus3616.small3620,CompactMinus3616.nodes3620,NodeMinus56.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3621,GridMinus.atNode 3621,GridMinus.atNode 3622,NodeMinus56.w37,CompactMinus3616.checked3621,CompactMinus3616.small3621,CompactMinus3616.nodes3621,NodeMinus56.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3622,GridMinus.atNode 3622,GridMinus.atNode 3623,NodeMinus56.w38,CompactMinus3616.checked3622,CompactMinus3616.small3622,CompactMinus3616.nodes3622,NodeMinus56.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3623,GridMinus.atNode 3623,GridMinus.atNode 3624,NodeMinus56.w39,CompactMinus3616.checked3623,CompactMinus3616.small3623,CompactMinus3616.nodes3623,NodeMinus56.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3624,GridMinus.atNode 3624,GridMinus.atNode 3625,NodeMinus56.w40,CompactMinus3616.checked3624,CompactMinus3616.small3624,CompactMinus3616.nodes3624,NodeMinus56.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3625,GridMinus.atNode 3625,GridMinus.atNode 3626,NodeMinus56.w41,CompactMinus3616.checked3625,CompactMinus3616.small3625,CompactMinus3616.nodes3625,NodeMinus56.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3626,GridMinus.atNode 3626,GridMinus.atNode 3627,NodeMinus56.w42,CompactMinus3616.checked3626,CompactMinus3616.small3626,CompactMinus3616.nodes3626,NodeMinus56.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3627,GridMinus.atNode 3627,GridMinus.atNode 3628,NodeMinus56.w43,CompactMinus3616.checked3627,CompactMinus3616.small3627,CompactMinus3616.nodes3627,NodeMinus56.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3628,GridMinus.atNode 3628,GridMinus.atNode 3629,NodeMinus56.w44,CompactMinus3616.checked3628,CompactMinus3616.small3628,CompactMinus3616.nodes3628,NodeMinus56.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3629,GridMinus.atNode 3629,GridMinus.atNode 3630,NodeMinus56.w45,CompactMinus3616.checked3629,CompactMinus3616.small3629,CompactMinus3616.nodes3629,NodeMinus56.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3630,GridMinus.atNode 3630,GridMinus.atNode 3631,NodeMinus56.w46,CompactMinus3616.checked3630,CompactMinus3616.small3630,CompactMinus3616.nodes3630,NodeMinus56.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3616.p3631,GridMinus.atNode 3631,GridMinus.atNode 3632,NodeMinus56.w47,CompactMinus3616.checked3631,CompactMinus3616.small3631,CompactMinus3616.nodes3631,NodeMinus56.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3632,GridMinus.atNode 3632,GridMinus.atNode 3633,NodeMinus56.w48,CompactMinus3632.checked3632,CompactMinus3632.small3632,CompactMinus3632.nodes3632,NodeMinus56.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3633,GridMinus.atNode 3633,GridMinus.atNode 3634,NodeMinus56.w49,CompactMinus3632.checked3633,CompactMinus3632.small3633,CompactMinus3632.nodes3633,NodeMinus56.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3634,GridMinus.atNode 3634,GridMinus.atNode 3635,NodeMinus56.w50,CompactMinus3632.checked3634,CompactMinus3632.small3634,CompactMinus3632.nodes3634,NodeMinus56.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3635,GridMinus.atNode 3635,GridMinus.atNode 3636,NodeMinus56.w51,CompactMinus3632.checked3635,CompactMinus3632.small3635,CompactMinus3632.nodes3635,NodeMinus56.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3636,GridMinus.atNode 3636,GridMinus.atNode 3637,NodeMinus56.w52,CompactMinus3632.checked3636,CompactMinus3632.small3636,CompactMinus3632.nodes3636,NodeMinus56.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3637,GridMinus.atNode 3637,GridMinus.atNode 3638,NodeMinus56.w53,CompactMinus3632.checked3637,CompactMinus3632.small3637,CompactMinus3632.nodes3637,NodeMinus56.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3638,GridMinus.atNode 3638,GridMinus.atNode 3639,NodeMinus56.w54,CompactMinus3632.checked3638,CompactMinus3632.small3638,CompactMinus3632.nodes3638,NodeMinus56.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3639,GridMinus.atNode 3639,GridMinus.atNode 3640,NodeMinus56.w55,CompactMinus3632.checked3639,CompactMinus3632.small3639,CompactMinus3632.nodes3639,NodeMinus56.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3640,GridMinus.atNode 3640,GridMinus.atNode 3641,NodeMinus56.w56,CompactMinus3632.checked3640,CompactMinus3632.small3640,CompactMinus3632.nodes3640,NodeMinus56.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3641,GridMinus.atNode 3641,GridMinus.atNode 3642,NodeMinus56.w57,CompactMinus3632.checked3641,CompactMinus3632.small3641,CompactMinus3632.nodes3641,NodeMinus56.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3642,GridMinus.atNode 3642,GridMinus.atNode 3643,NodeMinus56.w58,CompactMinus3632.checked3642,CompactMinus3632.small3642,CompactMinus3632.nodes3642,NodeMinus56.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3643,GridMinus.atNode 3643,GridMinus.atNode 3644,NodeMinus56.w59,CompactMinus3632.checked3643,CompactMinus3632.small3643,CompactMinus3632.nodes3643,NodeMinus56.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3644,GridMinus.atNode 3644,GridMinus.atNode 3645,NodeMinus56.w60,CompactMinus3632.checked3644,CompactMinus3632.small3644,CompactMinus3632.nodes3644,NodeMinus56.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3645,GridMinus.atNode 3645,GridMinus.atNode 3646,NodeMinus56.w61,CompactMinus3632.checked3645,CompactMinus3632.small3645,CompactMinus3632.nodes3645,NodeMinus56.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3646,GridMinus.atNode 3646,GridMinus.atNode 3647,NodeMinus56.w62,CompactMinus3632.checked3646,CompactMinus3632.small3646,CompactMinus3632.nodes3646,NodeMinus56.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3632.p3647,GridMinus.atNode 3647,GridMinus.atNode 3648,NodeMinus56.w63,CompactMinus3632.checked3647,CompactMinus3632.small3647,CompactMinus3632.nodes3647,NodeMinus56.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3584+j) ∧
    (atRow j).right=GridMinus.atNode (3584+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus56
