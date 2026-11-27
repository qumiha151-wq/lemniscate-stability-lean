import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3904
import SolitonClassification.Rotating.ResetPackedMinus3920
import SolitonClassification.Rotating.ResetPackedMinus3936
import SolitonClassification.Rotating.ResetPackedMinus3952
namespace SolitonClassification.Rotating.DyadicReset.TileMinus61
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3904,GridMinus.atNode 3904,GridMinus.atNode 3905,NodeMinus61.w0,CompactMinus3904.checked3904,CompactMinus3904.small3904,CompactMinus3904.nodes3904,NodeMinus61.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3905,GridMinus.atNode 3905,GridMinus.atNode 3906,NodeMinus61.w1,CompactMinus3904.checked3905,CompactMinus3904.small3905,CompactMinus3904.nodes3905,NodeMinus61.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3906,GridMinus.atNode 3906,GridMinus.atNode 3907,NodeMinus61.w2,CompactMinus3904.checked3906,CompactMinus3904.small3906,CompactMinus3904.nodes3906,NodeMinus61.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3907,GridMinus.atNode 3907,GridMinus.atNode 3908,NodeMinus61.w3,CompactMinus3904.checked3907,CompactMinus3904.small3907,CompactMinus3904.nodes3907,NodeMinus61.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3908,GridMinus.atNode 3908,GridMinus.atNode 3909,NodeMinus61.w4,CompactMinus3904.checked3908,CompactMinus3904.small3908,CompactMinus3904.nodes3908,NodeMinus61.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3909,GridMinus.atNode 3909,GridMinus.atNode 3910,NodeMinus61.w5,CompactMinus3904.checked3909,CompactMinus3904.small3909,CompactMinus3904.nodes3909,NodeMinus61.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3910,GridMinus.atNode 3910,GridMinus.atNode 3911,NodeMinus61.w6,CompactMinus3904.checked3910,CompactMinus3904.small3910,CompactMinus3904.nodes3910,NodeMinus61.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3911,GridMinus.atNode 3911,GridMinus.atNode 3912,NodeMinus61.w7,CompactMinus3904.checked3911,CompactMinus3904.small3911,CompactMinus3904.nodes3911,NodeMinus61.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3912,GridMinus.atNode 3912,GridMinus.atNode 3913,NodeMinus61.w8,CompactMinus3904.checked3912,CompactMinus3904.small3912,CompactMinus3904.nodes3912,NodeMinus61.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3913,GridMinus.atNode 3913,GridMinus.atNode 3914,NodeMinus61.w9,CompactMinus3904.checked3913,CompactMinus3904.small3913,CompactMinus3904.nodes3913,NodeMinus61.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3914,GridMinus.atNode 3914,GridMinus.atNode 3915,NodeMinus61.w10,CompactMinus3904.checked3914,CompactMinus3904.small3914,CompactMinus3904.nodes3914,NodeMinus61.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3915,GridMinus.atNode 3915,GridMinus.atNode 3916,NodeMinus61.w11,CompactMinus3904.checked3915,CompactMinus3904.small3915,CompactMinus3904.nodes3915,NodeMinus61.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3916,GridMinus.atNode 3916,GridMinus.atNode 3917,NodeMinus61.w12,CompactMinus3904.checked3916,CompactMinus3904.small3916,CompactMinus3904.nodes3916,NodeMinus61.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3917,GridMinus.atNode 3917,GridMinus.atNode 3918,NodeMinus61.w13,CompactMinus3904.checked3917,CompactMinus3904.small3917,CompactMinus3904.nodes3917,NodeMinus61.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3918,GridMinus.atNode 3918,GridMinus.atNode 3919,NodeMinus61.w14,CompactMinus3904.checked3918,CompactMinus3904.small3918,CompactMinus3904.nodes3918,NodeMinus61.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3904.p3919,GridMinus.atNode 3919,GridMinus.atNode 3920,NodeMinus61.w15,CompactMinus3904.checked3919,CompactMinus3904.small3919,CompactMinus3904.nodes3919,NodeMinus61.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3920,GridMinus.atNode 3920,GridMinus.atNode 3921,NodeMinus61.w16,CompactMinus3920.checked3920,CompactMinus3920.small3920,CompactMinus3920.nodes3920,NodeMinus61.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3921,GridMinus.atNode 3921,GridMinus.atNode 3922,NodeMinus61.w17,CompactMinus3920.checked3921,CompactMinus3920.small3921,CompactMinus3920.nodes3921,NodeMinus61.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3922,GridMinus.atNode 3922,GridMinus.atNode 3923,NodeMinus61.w18,CompactMinus3920.checked3922,CompactMinus3920.small3922,CompactMinus3920.nodes3922,NodeMinus61.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3923,GridMinus.atNode 3923,GridMinus.atNode 3924,NodeMinus61.w19,CompactMinus3920.checked3923,CompactMinus3920.small3923,CompactMinus3920.nodes3923,NodeMinus61.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3924,GridMinus.atNode 3924,GridMinus.atNode 3925,NodeMinus61.w20,CompactMinus3920.checked3924,CompactMinus3920.small3924,CompactMinus3920.nodes3924,NodeMinus61.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3925,GridMinus.atNode 3925,GridMinus.atNode 3926,NodeMinus61.w21,CompactMinus3920.checked3925,CompactMinus3920.small3925,CompactMinus3920.nodes3925,NodeMinus61.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3926,GridMinus.atNode 3926,GridMinus.atNode 3927,NodeMinus61.w22,CompactMinus3920.checked3926,CompactMinus3920.small3926,CompactMinus3920.nodes3926,NodeMinus61.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3927,GridMinus.atNode 3927,GridMinus.atNode 3928,NodeMinus61.w23,CompactMinus3920.checked3927,CompactMinus3920.small3927,CompactMinus3920.nodes3927,NodeMinus61.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3928,GridMinus.atNode 3928,GridMinus.atNode 3929,NodeMinus61.w24,CompactMinus3920.checked3928,CompactMinus3920.small3928,CompactMinus3920.nodes3928,NodeMinus61.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3929,GridMinus.atNode 3929,GridMinus.atNode 3930,NodeMinus61.w25,CompactMinus3920.checked3929,CompactMinus3920.small3929,CompactMinus3920.nodes3929,NodeMinus61.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3930,GridMinus.atNode 3930,GridMinus.atNode 3931,NodeMinus61.w26,CompactMinus3920.checked3930,CompactMinus3920.small3930,CompactMinus3920.nodes3930,NodeMinus61.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3931,GridMinus.atNode 3931,GridMinus.atNode 3932,NodeMinus61.w27,CompactMinus3920.checked3931,CompactMinus3920.small3931,CompactMinus3920.nodes3931,NodeMinus61.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3932,GridMinus.atNode 3932,GridMinus.atNode 3933,NodeMinus61.w28,CompactMinus3920.checked3932,CompactMinus3920.small3932,CompactMinus3920.nodes3932,NodeMinus61.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3933,GridMinus.atNode 3933,GridMinus.atNode 3934,NodeMinus61.w29,CompactMinus3920.checked3933,CompactMinus3920.small3933,CompactMinus3920.nodes3933,NodeMinus61.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3934,GridMinus.atNode 3934,GridMinus.atNode 3935,NodeMinus61.w30,CompactMinus3920.checked3934,CompactMinus3920.small3934,CompactMinus3920.nodes3934,NodeMinus61.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3920.p3935,GridMinus.atNode 3935,GridMinus.atNode 3936,NodeMinus61.w31,CompactMinus3920.checked3935,CompactMinus3920.small3935,CompactMinus3920.nodes3935,NodeMinus61.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3936,GridMinus.atNode 3936,GridMinus.atNode 3937,NodeMinus61.w32,CompactMinus3936.checked3936,CompactMinus3936.small3936,CompactMinus3936.nodes3936,NodeMinus61.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3937,GridMinus.atNode 3937,GridMinus.atNode 3938,NodeMinus61.w33,CompactMinus3936.checked3937,CompactMinus3936.small3937,CompactMinus3936.nodes3937,NodeMinus61.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3938,GridMinus.atNode 3938,GridMinus.atNode 3939,NodeMinus61.w34,CompactMinus3936.checked3938,CompactMinus3936.small3938,CompactMinus3936.nodes3938,NodeMinus61.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3939,GridMinus.atNode 3939,GridMinus.atNode 3940,NodeMinus61.w35,CompactMinus3936.checked3939,CompactMinus3936.small3939,CompactMinus3936.nodes3939,NodeMinus61.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3940,GridMinus.atNode 3940,GridMinus.atNode 3941,NodeMinus61.w36,CompactMinus3936.checked3940,CompactMinus3936.small3940,CompactMinus3936.nodes3940,NodeMinus61.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3941,GridMinus.atNode 3941,GridMinus.atNode 3942,NodeMinus61.w37,CompactMinus3936.checked3941,CompactMinus3936.small3941,CompactMinus3936.nodes3941,NodeMinus61.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3942,GridMinus.atNode 3942,GridMinus.atNode 3943,NodeMinus61.w38,CompactMinus3936.checked3942,CompactMinus3936.small3942,CompactMinus3936.nodes3942,NodeMinus61.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3943,GridMinus.atNode 3943,GridMinus.atNode 3944,NodeMinus61.w39,CompactMinus3936.checked3943,CompactMinus3936.small3943,CompactMinus3936.nodes3943,NodeMinus61.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3944,GridMinus.atNode 3944,GridMinus.atNode 3945,NodeMinus61.w40,CompactMinus3936.checked3944,CompactMinus3936.small3944,CompactMinus3936.nodes3944,NodeMinus61.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3945,GridMinus.atNode 3945,GridMinus.atNode 3946,NodeMinus61.w41,CompactMinus3936.checked3945,CompactMinus3936.small3945,CompactMinus3936.nodes3945,NodeMinus61.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3946,GridMinus.atNode 3946,GridMinus.atNode 3947,NodeMinus61.w42,CompactMinus3936.checked3946,CompactMinus3936.small3946,CompactMinus3936.nodes3946,NodeMinus61.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3947,GridMinus.atNode 3947,GridMinus.atNode 3948,NodeMinus61.w43,CompactMinus3936.checked3947,CompactMinus3936.small3947,CompactMinus3936.nodes3947,NodeMinus61.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3948,GridMinus.atNode 3948,GridMinus.atNode 3949,NodeMinus61.w44,CompactMinus3936.checked3948,CompactMinus3936.small3948,CompactMinus3936.nodes3948,NodeMinus61.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3949,GridMinus.atNode 3949,GridMinus.atNode 3950,NodeMinus61.w45,CompactMinus3936.checked3949,CompactMinus3936.small3949,CompactMinus3936.nodes3949,NodeMinus61.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3950,GridMinus.atNode 3950,GridMinus.atNode 3951,NodeMinus61.w46,CompactMinus3936.checked3950,CompactMinus3936.small3950,CompactMinus3936.nodes3950,NodeMinus61.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3936.p3951,GridMinus.atNode 3951,GridMinus.atNode 3952,NodeMinus61.w47,CompactMinus3936.checked3951,CompactMinus3936.small3951,CompactMinus3936.nodes3951,NodeMinus61.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3952,GridMinus.atNode 3952,GridMinus.atNode 3953,NodeMinus61.w48,CompactMinus3952.checked3952,CompactMinus3952.small3952,CompactMinus3952.nodes3952,NodeMinus61.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3953,GridMinus.atNode 3953,GridMinus.atNode 3954,NodeMinus61.w49,CompactMinus3952.checked3953,CompactMinus3952.small3953,CompactMinus3952.nodes3953,NodeMinus61.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3954,GridMinus.atNode 3954,GridMinus.atNode 3955,NodeMinus61.w50,CompactMinus3952.checked3954,CompactMinus3952.small3954,CompactMinus3952.nodes3954,NodeMinus61.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3955,GridMinus.atNode 3955,GridMinus.atNode 3956,NodeMinus61.w51,CompactMinus3952.checked3955,CompactMinus3952.small3955,CompactMinus3952.nodes3955,NodeMinus61.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3956,GridMinus.atNode 3956,GridMinus.atNode 3957,NodeMinus61.w52,CompactMinus3952.checked3956,CompactMinus3952.small3956,CompactMinus3952.nodes3956,NodeMinus61.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3957,GridMinus.atNode 3957,GridMinus.atNode 3958,NodeMinus61.w53,CompactMinus3952.checked3957,CompactMinus3952.small3957,CompactMinus3952.nodes3957,NodeMinus61.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3958,GridMinus.atNode 3958,GridMinus.atNode 3959,NodeMinus61.w54,CompactMinus3952.checked3958,CompactMinus3952.small3958,CompactMinus3952.nodes3958,NodeMinus61.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3959,GridMinus.atNode 3959,GridMinus.atNode 3960,NodeMinus61.w55,CompactMinus3952.checked3959,CompactMinus3952.small3959,CompactMinus3952.nodes3959,NodeMinus61.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3960,GridMinus.atNode 3960,GridMinus.atNode 3961,NodeMinus61.w56,CompactMinus3952.checked3960,CompactMinus3952.small3960,CompactMinus3952.nodes3960,NodeMinus61.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3961,GridMinus.atNode 3961,GridMinus.atNode 3962,NodeMinus61.w57,CompactMinus3952.checked3961,CompactMinus3952.small3961,CompactMinus3952.nodes3961,NodeMinus61.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3962,GridMinus.atNode 3962,GridMinus.atNode 3963,NodeMinus61.w58,CompactMinus3952.checked3962,CompactMinus3952.small3962,CompactMinus3952.nodes3962,NodeMinus61.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3963,GridMinus.atNode 3963,GridMinus.atNode 3964,NodeMinus61.w59,CompactMinus3952.checked3963,CompactMinus3952.small3963,CompactMinus3952.nodes3963,NodeMinus61.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3964,GridMinus.atNode 3964,GridMinus.atNode 3965,NodeMinus61.w60,CompactMinus3952.checked3964,CompactMinus3952.small3964,CompactMinus3952.nodes3964,NodeMinus61.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3965,GridMinus.atNode 3965,GridMinus.atNode 3966,NodeMinus61.w61,CompactMinus3952.checked3965,CompactMinus3952.small3965,CompactMinus3952.nodes3965,NodeMinus61.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3966,GridMinus.atNode 3966,GridMinus.atNode 3967,NodeMinus61.w62,CompactMinus3952.checked3966,CompactMinus3952.small3966,CompactMinus3952.nodes3966,NodeMinus61.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3952.p3967,GridMinus.atNode 3967,GridMinus.atNode 3968,NodeMinus61.w63,CompactMinus3952.checked3967,CompactMinus3952.small3967,CompactMinus3952.nodes3967,NodeMinus61.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3904+j) ∧
    (atRow j).right=GridMinus.atNode (3904+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus61
