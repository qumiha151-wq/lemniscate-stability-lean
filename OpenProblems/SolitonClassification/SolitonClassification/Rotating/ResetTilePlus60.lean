import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3840
import SolitonClassification.Rotating.ResetPackedPlus3856
import SolitonClassification.Rotating.ResetPackedPlus3872
import SolitonClassification.Rotating.ResetPackedPlus3888
namespace SolitonClassification.Rotating.DyadicReset.TilePlus60
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3840,GridPlus.atNode 3840,GridPlus.atNode 3841,NodePlus60.w0,CompactPlus3840.checked3840,CompactPlus3840.small3840,CompactPlus3840.nodes3840,NodePlus60.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3841,GridPlus.atNode 3841,GridPlus.atNode 3842,NodePlus60.w1,CompactPlus3840.checked3841,CompactPlus3840.small3841,CompactPlus3840.nodes3841,NodePlus60.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3842,GridPlus.atNode 3842,GridPlus.atNode 3843,NodePlus60.w2,CompactPlus3840.checked3842,CompactPlus3840.small3842,CompactPlus3840.nodes3842,NodePlus60.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3843,GridPlus.atNode 3843,GridPlus.atNode 3844,NodePlus60.w3,CompactPlus3840.checked3843,CompactPlus3840.small3843,CompactPlus3840.nodes3843,NodePlus60.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3844,GridPlus.atNode 3844,GridPlus.atNode 3845,NodePlus60.w4,CompactPlus3840.checked3844,CompactPlus3840.small3844,CompactPlus3840.nodes3844,NodePlus60.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3845,GridPlus.atNode 3845,GridPlus.atNode 3846,NodePlus60.w5,CompactPlus3840.checked3845,CompactPlus3840.small3845,CompactPlus3840.nodes3845,NodePlus60.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3846,GridPlus.atNode 3846,GridPlus.atNode 3847,NodePlus60.w6,CompactPlus3840.checked3846,CompactPlus3840.small3846,CompactPlus3840.nodes3846,NodePlus60.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3847,GridPlus.atNode 3847,GridPlus.atNode 3848,NodePlus60.w7,CompactPlus3840.checked3847,CompactPlus3840.small3847,CompactPlus3840.nodes3847,NodePlus60.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3848,GridPlus.atNode 3848,GridPlus.atNode 3849,NodePlus60.w8,CompactPlus3840.checked3848,CompactPlus3840.small3848,CompactPlus3840.nodes3848,NodePlus60.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3849,GridPlus.atNode 3849,GridPlus.atNode 3850,NodePlus60.w9,CompactPlus3840.checked3849,CompactPlus3840.small3849,CompactPlus3840.nodes3849,NodePlus60.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3850,GridPlus.atNode 3850,GridPlus.atNode 3851,NodePlus60.w10,CompactPlus3840.checked3850,CompactPlus3840.small3850,CompactPlus3840.nodes3850,NodePlus60.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3851,GridPlus.atNode 3851,GridPlus.atNode 3852,NodePlus60.w11,CompactPlus3840.checked3851,CompactPlus3840.small3851,CompactPlus3840.nodes3851,NodePlus60.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3852,GridPlus.atNode 3852,GridPlus.atNode 3853,NodePlus60.w12,CompactPlus3840.checked3852,CompactPlus3840.small3852,CompactPlus3840.nodes3852,NodePlus60.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3853,GridPlus.atNode 3853,GridPlus.atNode 3854,NodePlus60.w13,CompactPlus3840.checked3853,CompactPlus3840.small3853,CompactPlus3840.nodes3853,NodePlus60.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3854,GridPlus.atNode 3854,GridPlus.atNode 3855,NodePlus60.w14,CompactPlus3840.checked3854,CompactPlus3840.small3854,CompactPlus3840.nodes3854,NodePlus60.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3840.p3855,GridPlus.atNode 3855,GridPlus.atNode 3856,NodePlus60.w15,CompactPlus3840.checked3855,CompactPlus3840.small3855,CompactPlus3840.nodes3855,NodePlus60.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3856,GridPlus.atNode 3856,GridPlus.atNode 3857,NodePlus60.w16,CompactPlus3856.checked3856,CompactPlus3856.small3856,CompactPlus3856.nodes3856,NodePlus60.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3857,GridPlus.atNode 3857,GridPlus.atNode 3858,NodePlus60.w17,CompactPlus3856.checked3857,CompactPlus3856.small3857,CompactPlus3856.nodes3857,NodePlus60.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3858,GridPlus.atNode 3858,GridPlus.atNode 3859,NodePlus60.w18,CompactPlus3856.checked3858,CompactPlus3856.small3858,CompactPlus3856.nodes3858,NodePlus60.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3859,GridPlus.atNode 3859,GridPlus.atNode 3860,NodePlus60.w19,CompactPlus3856.checked3859,CompactPlus3856.small3859,CompactPlus3856.nodes3859,NodePlus60.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3860,GridPlus.atNode 3860,GridPlus.atNode 3861,NodePlus60.w20,CompactPlus3856.checked3860,CompactPlus3856.small3860,CompactPlus3856.nodes3860,NodePlus60.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3861,GridPlus.atNode 3861,GridPlus.atNode 3862,NodePlus60.w21,CompactPlus3856.checked3861,CompactPlus3856.small3861,CompactPlus3856.nodes3861,NodePlus60.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3862,GridPlus.atNode 3862,GridPlus.atNode 3863,NodePlus60.w22,CompactPlus3856.checked3862,CompactPlus3856.small3862,CompactPlus3856.nodes3862,NodePlus60.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3863,GridPlus.atNode 3863,GridPlus.atNode 3864,NodePlus60.w23,CompactPlus3856.checked3863,CompactPlus3856.small3863,CompactPlus3856.nodes3863,NodePlus60.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3864,GridPlus.atNode 3864,GridPlus.atNode 3865,NodePlus60.w24,CompactPlus3856.checked3864,CompactPlus3856.small3864,CompactPlus3856.nodes3864,NodePlus60.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3865,GridPlus.atNode 3865,GridPlus.atNode 3866,NodePlus60.w25,CompactPlus3856.checked3865,CompactPlus3856.small3865,CompactPlus3856.nodes3865,NodePlus60.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3866,GridPlus.atNode 3866,GridPlus.atNode 3867,NodePlus60.w26,CompactPlus3856.checked3866,CompactPlus3856.small3866,CompactPlus3856.nodes3866,NodePlus60.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3867,GridPlus.atNode 3867,GridPlus.atNode 3868,NodePlus60.w27,CompactPlus3856.checked3867,CompactPlus3856.small3867,CompactPlus3856.nodes3867,NodePlus60.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3868,GridPlus.atNode 3868,GridPlus.atNode 3869,NodePlus60.w28,CompactPlus3856.checked3868,CompactPlus3856.small3868,CompactPlus3856.nodes3868,NodePlus60.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3869,GridPlus.atNode 3869,GridPlus.atNode 3870,NodePlus60.w29,CompactPlus3856.checked3869,CompactPlus3856.small3869,CompactPlus3856.nodes3869,NodePlus60.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3870,GridPlus.atNode 3870,GridPlus.atNode 3871,NodePlus60.w30,CompactPlus3856.checked3870,CompactPlus3856.small3870,CompactPlus3856.nodes3870,NodePlus60.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3856.p3871,GridPlus.atNode 3871,GridPlus.atNode 3872,NodePlus60.w31,CompactPlus3856.checked3871,CompactPlus3856.small3871,CompactPlus3856.nodes3871,NodePlus60.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3872,GridPlus.atNode 3872,GridPlus.atNode 3873,NodePlus60.w32,CompactPlus3872.checked3872,CompactPlus3872.small3872,CompactPlus3872.nodes3872,NodePlus60.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3873,GridPlus.atNode 3873,GridPlus.atNode 3874,NodePlus60.w33,CompactPlus3872.checked3873,CompactPlus3872.small3873,CompactPlus3872.nodes3873,NodePlus60.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3874,GridPlus.atNode 3874,GridPlus.atNode 3875,NodePlus60.w34,CompactPlus3872.checked3874,CompactPlus3872.small3874,CompactPlus3872.nodes3874,NodePlus60.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3875,GridPlus.atNode 3875,GridPlus.atNode 3876,NodePlus60.w35,CompactPlus3872.checked3875,CompactPlus3872.small3875,CompactPlus3872.nodes3875,NodePlus60.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3876,GridPlus.atNode 3876,GridPlus.atNode 3877,NodePlus60.w36,CompactPlus3872.checked3876,CompactPlus3872.small3876,CompactPlus3872.nodes3876,NodePlus60.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3877,GridPlus.atNode 3877,GridPlus.atNode 3878,NodePlus60.w37,CompactPlus3872.checked3877,CompactPlus3872.small3877,CompactPlus3872.nodes3877,NodePlus60.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3878,GridPlus.atNode 3878,GridPlus.atNode 3879,NodePlus60.w38,CompactPlus3872.checked3878,CompactPlus3872.small3878,CompactPlus3872.nodes3878,NodePlus60.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3879,GridPlus.atNode 3879,GridPlus.atNode 3880,NodePlus60.w39,CompactPlus3872.checked3879,CompactPlus3872.small3879,CompactPlus3872.nodes3879,NodePlus60.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3880,GridPlus.atNode 3880,GridPlus.atNode 3881,NodePlus60.w40,CompactPlus3872.checked3880,CompactPlus3872.small3880,CompactPlus3872.nodes3880,NodePlus60.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3881,GridPlus.atNode 3881,GridPlus.atNode 3882,NodePlus60.w41,CompactPlus3872.checked3881,CompactPlus3872.small3881,CompactPlus3872.nodes3881,NodePlus60.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3882,GridPlus.atNode 3882,GridPlus.atNode 3883,NodePlus60.w42,CompactPlus3872.checked3882,CompactPlus3872.small3882,CompactPlus3872.nodes3882,NodePlus60.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3883,GridPlus.atNode 3883,GridPlus.atNode 3884,NodePlus60.w43,CompactPlus3872.checked3883,CompactPlus3872.small3883,CompactPlus3872.nodes3883,NodePlus60.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3884,GridPlus.atNode 3884,GridPlus.atNode 3885,NodePlus60.w44,CompactPlus3872.checked3884,CompactPlus3872.small3884,CompactPlus3872.nodes3884,NodePlus60.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3885,GridPlus.atNode 3885,GridPlus.atNode 3886,NodePlus60.w45,CompactPlus3872.checked3885,CompactPlus3872.small3885,CompactPlus3872.nodes3885,NodePlus60.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3886,GridPlus.atNode 3886,GridPlus.atNode 3887,NodePlus60.w46,CompactPlus3872.checked3886,CompactPlus3872.small3886,CompactPlus3872.nodes3886,NodePlus60.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3872.p3887,GridPlus.atNode 3887,GridPlus.atNode 3888,NodePlus60.w47,CompactPlus3872.checked3887,CompactPlus3872.small3887,CompactPlus3872.nodes3887,NodePlus60.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3888,GridPlus.atNode 3888,GridPlus.atNode 3889,NodePlus60.w48,CompactPlus3888.checked3888,CompactPlus3888.small3888,CompactPlus3888.nodes3888,NodePlus60.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3889,GridPlus.atNode 3889,GridPlus.atNode 3890,NodePlus60.w49,CompactPlus3888.checked3889,CompactPlus3888.small3889,CompactPlus3888.nodes3889,NodePlus60.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3890,GridPlus.atNode 3890,GridPlus.atNode 3891,NodePlus60.w50,CompactPlus3888.checked3890,CompactPlus3888.small3890,CompactPlus3888.nodes3890,NodePlus60.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3891,GridPlus.atNode 3891,GridPlus.atNode 3892,NodePlus60.w51,CompactPlus3888.checked3891,CompactPlus3888.small3891,CompactPlus3888.nodes3891,NodePlus60.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3892,GridPlus.atNode 3892,GridPlus.atNode 3893,NodePlus60.w52,CompactPlus3888.checked3892,CompactPlus3888.small3892,CompactPlus3888.nodes3892,NodePlus60.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3893,GridPlus.atNode 3893,GridPlus.atNode 3894,NodePlus60.w53,CompactPlus3888.checked3893,CompactPlus3888.small3893,CompactPlus3888.nodes3893,NodePlus60.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3894,GridPlus.atNode 3894,GridPlus.atNode 3895,NodePlus60.w54,CompactPlus3888.checked3894,CompactPlus3888.small3894,CompactPlus3888.nodes3894,NodePlus60.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3895,GridPlus.atNode 3895,GridPlus.atNode 3896,NodePlus60.w55,CompactPlus3888.checked3895,CompactPlus3888.small3895,CompactPlus3888.nodes3895,NodePlus60.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3896,GridPlus.atNode 3896,GridPlus.atNode 3897,NodePlus60.w56,CompactPlus3888.checked3896,CompactPlus3888.small3896,CompactPlus3888.nodes3896,NodePlus60.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3897,GridPlus.atNode 3897,GridPlus.atNode 3898,NodePlus60.w57,CompactPlus3888.checked3897,CompactPlus3888.small3897,CompactPlus3888.nodes3897,NodePlus60.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3898,GridPlus.atNode 3898,GridPlus.atNode 3899,NodePlus60.w58,CompactPlus3888.checked3898,CompactPlus3888.small3898,CompactPlus3888.nodes3898,NodePlus60.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3899,GridPlus.atNode 3899,GridPlus.atNode 3900,NodePlus60.w59,CompactPlus3888.checked3899,CompactPlus3888.small3899,CompactPlus3888.nodes3899,NodePlus60.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3900,GridPlus.atNode 3900,GridPlus.atNode 3901,NodePlus60.w60,CompactPlus3888.checked3900,CompactPlus3888.small3900,CompactPlus3888.nodes3900,NodePlus60.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3901,GridPlus.atNode 3901,GridPlus.atNode 3902,NodePlus60.w61,CompactPlus3888.checked3901,CompactPlus3888.small3901,CompactPlus3888.nodes3901,NodePlus60.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3902,GridPlus.atNode 3902,GridPlus.atNode 3903,NodePlus60.w62,CompactPlus3888.checked3902,CompactPlus3888.small3902,CompactPlus3888.nodes3902,NodePlus60.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3888.p3903,GridPlus.atNode 3903,GridPlus.atNode 3904,NodePlus60.w63,CompactPlus3888.checked3903,CompactPlus3888.small3903,CompactPlus3888.nodes3903,NodePlus60.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3840+j) ∧
    (atRow j).right=GridPlus.atNode (3840+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus60
