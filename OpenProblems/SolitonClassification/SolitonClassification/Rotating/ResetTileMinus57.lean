import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3648
import SolitonClassification.Rotating.ResetPackedMinus3664
import SolitonClassification.Rotating.ResetPackedMinus3680
import SolitonClassification.Rotating.ResetPackedMinus3696
namespace SolitonClassification.Rotating.DyadicReset.TileMinus57
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3648,GridMinus.atNode 3648,GridMinus.atNode 3649,NodeMinus57.w0,CompactMinus3648.checked3648,CompactMinus3648.small3648,CompactMinus3648.nodes3648,NodeMinus57.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3649,GridMinus.atNode 3649,GridMinus.atNode 3650,NodeMinus57.w1,CompactMinus3648.checked3649,CompactMinus3648.small3649,CompactMinus3648.nodes3649,NodeMinus57.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3650,GridMinus.atNode 3650,GridMinus.atNode 3651,NodeMinus57.w2,CompactMinus3648.checked3650,CompactMinus3648.small3650,CompactMinus3648.nodes3650,NodeMinus57.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3651,GridMinus.atNode 3651,GridMinus.atNode 3652,NodeMinus57.w3,CompactMinus3648.checked3651,CompactMinus3648.small3651,CompactMinus3648.nodes3651,NodeMinus57.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3652,GridMinus.atNode 3652,GridMinus.atNode 3653,NodeMinus57.w4,CompactMinus3648.checked3652,CompactMinus3648.small3652,CompactMinus3648.nodes3652,NodeMinus57.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3653,GridMinus.atNode 3653,GridMinus.atNode 3654,NodeMinus57.w5,CompactMinus3648.checked3653,CompactMinus3648.small3653,CompactMinus3648.nodes3653,NodeMinus57.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3654,GridMinus.atNode 3654,GridMinus.atNode 3655,NodeMinus57.w6,CompactMinus3648.checked3654,CompactMinus3648.small3654,CompactMinus3648.nodes3654,NodeMinus57.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3655,GridMinus.atNode 3655,GridMinus.atNode 3656,NodeMinus57.w7,CompactMinus3648.checked3655,CompactMinus3648.small3655,CompactMinus3648.nodes3655,NodeMinus57.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3656,GridMinus.atNode 3656,GridMinus.atNode 3657,NodeMinus57.w8,CompactMinus3648.checked3656,CompactMinus3648.small3656,CompactMinus3648.nodes3656,NodeMinus57.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3657,GridMinus.atNode 3657,GridMinus.atNode 3658,NodeMinus57.w9,CompactMinus3648.checked3657,CompactMinus3648.small3657,CompactMinus3648.nodes3657,NodeMinus57.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3658,GridMinus.atNode 3658,GridMinus.atNode 3659,NodeMinus57.w10,CompactMinus3648.checked3658,CompactMinus3648.small3658,CompactMinus3648.nodes3658,NodeMinus57.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3659,GridMinus.atNode 3659,GridMinus.atNode 3660,NodeMinus57.w11,CompactMinus3648.checked3659,CompactMinus3648.small3659,CompactMinus3648.nodes3659,NodeMinus57.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3660,GridMinus.atNode 3660,GridMinus.atNode 3661,NodeMinus57.w12,CompactMinus3648.checked3660,CompactMinus3648.small3660,CompactMinus3648.nodes3660,NodeMinus57.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3661,GridMinus.atNode 3661,GridMinus.atNode 3662,NodeMinus57.w13,CompactMinus3648.checked3661,CompactMinus3648.small3661,CompactMinus3648.nodes3661,NodeMinus57.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3662,GridMinus.atNode 3662,GridMinus.atNode 3663,NodeMinus57.w14,CompactMinus3648.checked3662,CompactMinus3648.small3662,CompactMinus3648.nodes3662,NodeMinus57.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3648.p3663,GridMinus.atNode 3663,GridMinus.atNode 3664,NodeMinus57.w15,CompactMinus3648.checked3663,CompactMinus3648.small3663,CompactMinus3648.nodes3663,NodeMinus57.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3664,GridMinus.atNode 3664,GridMinus.atNode 3665,NodeMinus57.w16,CompactMinus3664.checked3664,CompactMinus3664.small3664,CompactMinus3664.nodes3664,NodeMinus57.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3665,GridMinus.atNode 3665,GridMinus.atNode 3666,NodeMinus57.w17,CompactMinus3664.checked3665,CompactMinus3664.small3665,CompactMinus3664.nodes3665,NodeMinus57.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3666,GridMinus.atNode 3666,GridMinus.atNode 3667,NodeMinus57.w18,CompactMinus3664.checked3666,CompactMinus3664.small3666,CompactMinus3664.nodes3666,NodeMinus57.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3667,GridMinus.atNode 3667,GridMinus.atNode 3668,NodeMinus57.w19,CompactMinus3664.checked3667,CompactMinus3664.small3667,CompactMinus3664.nodes3667,NodeMinus57.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3668,GridMinus.atNode 3668,GridMinus.atNode 3669,NodeMinus57.w20,CompactMinus3664.checked3668,CompactMinus3664.small3668,CompactMinus3664.nodes3668,NodeMinus57.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3669,GridMinus.atNode 3669,GridMinus.atNode 3670,NodeMinus57.w21,CompactMinus3664.checked3669,CompactMinus3664.small3669,CompactMinus3664.nodes3669,NodeMinus57.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3670,GridMinus.atNode 3670,GridMinus.atNode 3671,NodeMinus57.w22,CompactMinus3664.checked3670,CompactMinus3664.small3670,CompactMinus3664.nodes3670,NodeMinus57.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3671,GridMinus.atNode 3671,GridMinus.atNode 3672,NodeMinus57.w23,CompactMinus3664.checked3671,CompactMinus3664.small3671,CompactMinus3664.nodes3671,NodeMinus57.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3672,GridMinus.atNode 3672,GridMinus.atNode 3673,NodeMinus57.w24,CompactMinus3664.checked3672,CompactMinus3664.small3672,CompactMinus3664.nodes3672,NodeMinus57.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3673,GridMinus.atNode 3673,GridMinus.atNode 3674,NodeMinus57.w25,CompactMinus3664.checked3673,CompactMinus3664.small3673,CompactMinus3664.nodes3673,NodeMinus57.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3674,GridMinus.atNode 3674,GridMinus.atNode 3675,NodeMinus57.w26,CompactMinus3664.checked3674,CompactMinus3664.small3674,CompactMinus3664.nodes3674,NodeMinus57.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3675,GridMinus.atNode 3675,GridMinus.atNode 3676,NodeMinus57.w27,CompactMinus3664.checked3675,CompactMinus3664.small3675,CompactMinus3664.nodes3675,NodeMinus57.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3676,GridMinus.atNode 3676,GridMinus.atNode 3677,NodeMinus57.w28,CompactMinus3664.checked3676,CompactMinus3664.small3676,CompactMinus3664.nodes3676,NodeMinus57.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3677,GridMinus.atNode 3677,GridMinus.atNode 3678,NodeMinus57.w29,CompactMinus3664.checked3677,CompactMinus3664.small3677,CompactMinus3664.nodes3677,NodeMinus57.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3678,GridMinus.atNode 3678,GridMinus.atNode 3679,NodeMinus57.w30,CompactMinus3664.checked3678,CompactMinus3664.small3678,CompactMinus3664.nodes3678,NodeMinus57.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3664.p3679,GridMinus.atNode 3679,GridMinus.atNode 3680,NodeMinus57.w31,CompactMinus3664.checked3679,CompactMinus3664.small3679,CompactMinus3664.nodes3679,NodeMinus57.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3680,GridMinus.atNode 3680,GridMinus.atNode 3681,NodeMinus57.w32,CompactMinus3680.checked3680,CompactMinus3680.small3680,CompactMinus3680.nodes3680,NodeMinus57.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3681,GridMinus.atNode 3681,GridMinus.atNode 3682,NodeMinus57.w33,CompactMinus3680.checked3681,CompactMinus3680.small3681,CompactMinus3680.nodes3681,NodeMinus57.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3682,GridMinus.atNode 3682,GridMinus.atNode 3683,NodeMinus57.w34,CompactMinus3680.checked3682,CompactMinus3680.small3682,CompactMinus3680.nodes3682,NodeMinus57.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3683,GridMinus.atNode 3683,GridMinus.atNode 3684,NodeMinus57.w35,CompactMinus3680.checked3683,CompactMinus3680.small3683,CompactMinus3680.nodes3683,NodeMinus57.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3684,GridMinus.atNode 3684,GridMinus.atNode 3685,NodeMinus57.w36,CompactMinus3680.checked3684,CompactMinus3680.small3684,CompactMinus3680.nodes3684,NodeMinus57.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3685,GridMinus.atNode 3685,GridMinus.atNode 3686,NodeMinus57.w37,CompactMinus3680.checked3685,CompactMinus3680.small3685,CompactMinus3680.nodes3685,NodeMinus57.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3686,GridMinus.atNode 3686,GridMinus.atNode 3687,NodeMinus57.w38,CompactMinus3680.checked3686,CompactMinus3680.small3686,CompactMinus3680.nodes3686,NodeMinus57.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3687,GridMinus.atNode 3687,GridMinus.atNode 3688,NodeMinus57.w39,CompactMinus3680.checked3687,CompactMinus3680.small3687,CompactMinus3680.nodes3687,NodeMinus57.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3688,GridMinus.atNode 3688,GridMinus.atNode 3689,NodeMinus57.w40,CompactMinus3680.checked3688,CompactMinus3680.small3688,CompactMinus3680.nodes3688,NodeMinus57.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3689,GridMinus.atNode 3689,GridMinus.atNode 3690,NodeMinus57.w41,CompactMinus3680.checked3689,CompactMinus3680.small3689,CompactMinus3680.nodes3689,NodeMinus57.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3690,GridMinus.atNode 3690,GridMinus.atNode 3691,NodeMinus57.w42,CompactMinus3680.checked3690,CompactMinus3680.small3690,CompactMinus3680.nodes3690,NodeMinus57.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3691,GridMinus.atNode 3691,GridMinus.atNode 3692,NodeMinus57.w43,CompactMinus3680.checked3691,CompactMinus3680.small3691,CompactMinus3680.nodes3691,NodeMinus57.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3692,GridMinus.atNode 3692,GridMinus.atNode 3693,NodeMinus57.w44,CompactMinus3680.checked3692,CompactMinus3680.small3692,CompactMinus3680.nodes3692,NodeMinus57.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3693,GridMinus.atNode 3693,GridMinus.atNode 3694,NodeMinus57.w45,CompactMinus3680.checked3693,CompactMinus3680.small3693,CompactMinus3680.nodes3693,NodeMinus57.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3694,GridMinus.atNode 3694,GridMinus.atNode 3695,NodeMinus57.w46,CompactMinus3680.checked3694,CompactMinus3680.small3694,CompactMinus3680.nodes3694,NodeMinus57.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3680.p3695,GridMinus.atNode 3695,GridMinus.atNode 3696,NodeMinus57.w47,CompactMinus3680.checked3695,CompactMinus3680.small3695,CompactMinus3680.nodes3695,NodeMinus57.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3696,GridMinus.atNode 3696,GridMinus.atNode 3697,NodeMinus57.w48,CompactMinus3696.checked3696,CompactMinus3696.small3696,CompactMinus3696.nodes3696,NodeMinus57.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3697,GridMinus.atNode 3697,GridMinus.atNode 3698,NodeMinus57.w49,CompactMinus3696.checked3697,CompactMinus3696.small3697,CompactMinus3696.nodes3697,NodeMinus57.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3698,GridMinus.atNode 3698,GridMinus.atNode 3699,NodeMinus57.w50,CompactMinus3696.checked3698,CompactMinus3696.small3698,CompactMinus3696.nodes3698,NodeMinus57.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3699,GridMinus.atNode 3699,GridMinus.atNode 3700,NodeMinus57.w51,CompactMinus3696.checked3699,CompactMinus3696.small3699,CompactMinus3696.nodes3699,NodeMinus57.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3700,GridMinus.atNode 3700,GridMinus.atNode 3701,NodeMinus57.w52,CompactMinus3696.checked3700,CompactMinus3696.small3700,CompactMinus3696.nodes3700,NodeMinus57.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3701,GridMinus.atNode 3701,GridMinus.atNode 3702,NodeMinus57.w53,CompactMinus3696.checked3701,CompactMinus3696.small3701,CompactMinus3696.nodes3701,NodeMinus57.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3702,GridMinus.atNode 3702,GridMinus.atNode 3703,NodeMinus57.w54,CompactMinus3696.checked3702,CompactMinus3696.small3702,CompactMinus3696.nodes3702,NodeMinus57.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3703,GridMinus.atNode 3703,GridMinus.atNode 3704,NodeMinus57.w55,CompactMinus3696.checked3703,CompactMinus3696.small3703,CompactMinus3696.nodes3703,NodeMinus57.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3704,GridMinus.atNode 3704,GridMinus.atNode 3705,NodeMinus57.w56,CompactMinus3696.checked3704,CompactMinus3696.small3704,CompactMinus3696.nodes3704,NodeMinus57.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3705,GridMinus.atNode 3705,GridMinus.atNode 3706,NodeMinus57.w57,CompactMinus3696.checked3705,CompactMinus3696.small3705,CompactMinus3696.nodes3705,NodeMinus57.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3706,GridMinus.atNode 3706,GridMinus.atNode 3707,NodeMinus57.w58,CompactMinus3696.checked3706,CompactMinus3696.small3706,CompactMinus3696.nodes3706,NodeMinus57.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3707,GridMinus.atNode 3707,GridMinus.atNode 3708,NodeMinus57.w59,CompactMinus3696.checked3707,CompactMinus3696.small3707,CompactMinus3696.nodes3707,NodeMinus57.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3708,GridMinus.atNode 3708,GridMinus.atNode 3709,NodeMinus57.w60,CompactMinus3696.checked3708,CompactMinus3696.small3708,CompactMinus3696.nodes3708,NodeMinus57.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3709,GridMinus.atNode 3709,GridMinus.atNode 3710,NodeMinus57.w61,CompactMinus3696.checked3709,CompactMinus3696.small3709,CompactMinus3696.nodes3709,NodeMinus57.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3710,GridMinus.atNode 3710,GridMinus.atNode 3711,NodeMinus57.w62,CompactMinus3696.checked3710,CompactMinus3696.small3710,CompactMinus3696.nodes3710,NodeMinus57.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3696.p3711,GridMinus.atNode 3711,GridMinus.atNode 3712,NodeMinus57.w63,CompactMinus3696.checked3711,CompactMinus3696.small3711,CompactMinus3696.nodes3711,NodeMinus57.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3648+j) ∧
    (atRow j).right=GridMinus.atNode (3648+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus57
