import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3840
import SolitonClassification.Rotating.ResetPackedMinus3856
import SolitonClassification.Rotating.ResetPackedMinus3872
import SolitonClassification.Rotating.ResetPackedMinus3888
namespace SolitonClassification.Rotating.DyadicReset.TileMinus60
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3840,GridMinus.atNode 3840,GridMinus.atNode 3841,NodeMinus60.w0,CompactMinus3840.checked3840,CompactMinus3840.small3840,CompactMinus3840.nodes3840,NodeMinus60.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3841,GridMinus.atNode 3841,GridMinus.atNode 3842,NodeMinus60.w1,CompactMinus3840.checked3841,CompactMinus3840.small3841,CompactMinus3840.nodes3841,NodeMinus60.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3842,GridMinus.atNode 3842,GridMinus.atNode 3843,NodeMinus60.w2,CompactMinus3840.checked3842,CompactMinus3840.small3842,CompactMinus3840.nodes3842,NodeMinus60.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3843,GridMinus.atNode 3843,GridMinus.atNode 3844,NodeMinus60.w3,CompactMinus3840.checked3843,CompactMinus3840.small3843,CompactMinus3840.nodes3843,NodeMinus60.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3844,GridMinus.atNode 3844,GridMinus.atNode 3845,NodeMinus60.w4,CompactMinus3840.checked3844,CompactMinus3840.small3844,CompactMinus3840.nodes3844,NodeMinus60.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3845,GridMinus.atNode 3845,GridMinus.atNode 3846,NodeMinus60.w5,CompactMinus3840.checked3845,CompactMinus3840.small3845,CompactMinus3840.nodes3845,NodeMinus60.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3846,GridMinus.atNode 3846,GridMinus.atNode 3847,NodeMinus60.w6,CompactMinus3840.checked3846,CompactMinus3840.small3846,CompactMinus3840.nodes3846,NodeMinus60.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3847,GridMinus.atNode 3847,GridMinus.atNode 3848,NodeMinus60.w7,CompactMinus3840.checked3847,CompactMinus3840.small3847,CompactMinus3840.nodes3847,NodeMinus60.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3848,GridMinus.atNode 3848,GridMinus.atNode 3849,NodeMinus60.w8,CompactMinus3840.checked3848,CompactMinus3840.small3848,CompactMinus3840.nodes3848,NodeMinus60.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3849,GridMinus.atNode 3849,GridMinus.atNode 3850,NodeMinus60.w9,CompactMinus3840.checked3849,CompactMinus3840.small3849,CompactMinus3840.nodes3849,NodeMinus60.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3850,GridMinus.atNode 3850,GridMinus.atNode 3851,NodeMinus60.w10,CompactMinus3840.checked3850,CompactMinus3840.small3850,CompactMinus3840.nodes3850,NodeMinus60.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3851,GridMinus.atNode 3851,GridMinus.atNode 3852,NodeMinus60.w11,CompactMinus3840.checked3851,CompactMinus3840.small3851,CompactMinus3840.nodes3851,NodeMinus60.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3852,GridMinus.atNode 3852,GridMinus.atNode 3853,NodeMinus60.w12,CompactMinus3840.checked3852,CompactMinus3840.small3852,CompactMinus3840.nodes3852,NodeMinus60.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3853,GridMinus.atNode 3853,GridMinus.atNode 3854,NodeMinus60.w13,CompactMinus3840.checked3853,CompactMinus3840.small3853,CompactMinus3840.nodes3853,NodeMinus60.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3854,GridMinus.atNode 3854,GridMinus.atNode 3855,NodeMinus60.w14,CompactMinus3840.checked3854,CompactMinus3840.small3854,CompactMinus3840.nodes3854,NodeMinus60.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3840.p3855,GridMinus.atNode 3855,GridMinus.atNode 3856,NodeMinus60.w15,CompactMinus3840.checked3855,CompactMinus3840.small3855,CompactMinus3840.nodes3855,NodeMinus60.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3856,GridMinus.atNode 3856,GridMinus.atNode 3857,NodeMinus60.w16,CompactMinus3856.checked3856,CompactMinus3856.small3856,CompactMinus3856.nodes3856,NodeMinus60.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3857,GridMinus.atNode 3857,GridMinus.atNode 3858,NodeMinus60.w17,CompactMinus3856.checked3857,CompactMinus3856.small3857,CompactMinus3856.nodes3857,NodeMinus60.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3858,GridMinus.atNode 3858,GridMinus.atNode 3859,NodeMinus60.w18,CompactMinus3856.checked3858,CompactMinus3856.small3858,CompactMinus3856.nodes3858,NodeMinus60.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3859,GridMinus.atNode 3859,GridMinus.atNode 3860,NodeMinus60.w19,CompactMinus3856.checked3859,CompactMinus3856.small3859,CompactMinus3856.nodes3859,NodeMinus60.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3860,GridMinus.atNode 3860,GridMinus.atNode 3861,NodeMinus60.w20,CompactMinus3856.checked3860,CompactMinus3856.small3860,CompactMinus3856.nodes3860,NodeMinus60.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3861,GridMinus.atNode 3861,GridMinus.atNode 3862,NodeMinus60.w21,CompactMinus3856.checked3861,CompactMinus3856.small3861,CompactMinus3856.nodes3861,NodeMinus60.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3862,GridMinus.atNode 3862,GridMinus.atNode 3863,NodeMinus60.w22,CompactMinus3856.checked3862,CompactMinus3856.small3862,CompactMinus3856.nodes3862,NodeMinus60.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3863,GridMinus.atNode 3863,GridMinus.atNode 3864,NodeMinus60.w23,CompactMinus3856.checked3863,CompactMinus3856.small3863,CompactMinus3856.nodes3863,NodeMinus60.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3864,GridMinus.atNode 3864,GridMinus.atNode 3865,NodeMinus60.w24,CompactMinus3856.checked3864,CompactMinus3856.small3864,CompactMinus3856.nodes3864,NodeMinus60.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3865,GridMinus.atNode 3865,GridMinus.atNode 3866,NodeMinus60.w25,CompactMinus3856.checked3865,CompactMinus3856.small3865,CompactMinus3856.nodes3865,NodeMinus60.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3866,GridMinus.atNode 3866,GridMinus.atNode 3867,NodeMinus60.w26,CompactMinus3856.checked3866,CompactMinus3856.small3866,CompactMinus3856.nodes3866,NodeMinus60.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3867,GridMinus.atNode 3867,GridMinus.atNode 3868,NodeMinus60.w27,CompactMinus3856.checked3867,CompactMinus3856.small3867,CompactMinus3856.nodes3867,NodeMinus60.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3868,GridMinus.atNode 3868,GridMinus.atNode 3869,NodeMinus60.w28,CompactMinus3856.checked3868,CompactMinus3856.small3868,CompactMinus3856.nodes3868,NodeMinus60.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3869,GridMinus.atNode 3869,GridMinus.atNode 3870,NodeMinus60.w29,CompactMinus3856.checked3869,CompactMinus3856.small3869,CompactMinus3856.nodes3869,NodeMinus60.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3870,GridMinus.atNode 3870,GridMinus.atNode 3871,NodeMinus60.w30,CompactMinus3856.checked3870,CompactMinus3856.small3870,CompactMinus3856.nodes3870,NodeMinus60.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3856.p3871,GridMinus.atNode 3871,GridMinus.atNode 3872,NodeMinus60.w31,CompactMinus3856.checked3871,CompactMinus3856.small3871,CompactMinus3856.nodes3871,NodeMinus60.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3872,GridMinus.atNode 3872,GridMinus.atNode 3873,NodeMinus60.w32,CompactMinus3872.checked3872,CompactMinus3872.small3872,CompactMinus3872.nodes3872,NodeMinus60.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3873,GridMinus.atNode 3873,GridMinus.atNode 3874,NodeMinus60.w33,CompactMinus3872.checked3873,CompactMinus3872.small3873,CompactMinus3872.nodes3873,NodeMinus60.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3874,GridMinus.atNode 3874,GridMinus.atNode 3875,NodeMinus60.w34,CompactMinus3872.checked3874,CompactMinus3872.small3874,CompactMinus3872.nodes3874,NodeMinus60.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3875,GridMinus.atNode 3875,GridMinus.atNode 3876,NodeMinus60.w35,CompactMinus3872.checked3875,CompactMinus3872.small3875,CompactMinus3872.nodes3875,NodeMinus60.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3876,GridMinus.atNode 3876,GridMinus.atNode 3877,NodeMinus60.w36,CompactMinus3872.checked3876,CompactMinus3872.small3876,CompactMinus3872.nodes3876,NodeMinus60.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3877,GridMinus.atNode 3877,GridMinus.atNode 3878,NodeMinus60.w37,CompactMinus3872.checked3877,CompactMinus3872.small3877,CompactMinus3872.nodes3877,NodeMinus60.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3878,GridMinus.atNode 3878,GridMinus.atNode 3879,NodeMinus60.w38,CompactMinus3872.checked3878,CompactMinus3872.small3878,CompactMinus3872.nodes3878,NodeMinus60.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3879,GridMinus.atNode 3879,GridMinus.atNode 3880,NodeMinus60.w39,CompactMinus3872.checked3879,CompactMinus3872.small3879,CompactMinus3872.nodes3879,NodeMinus60.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3880,GridMinus.atNode 3880,GridMinus.atNode 3881,NodeMinus60.w40,CompactMinus3872.checked3880,CompactMinus3872.small3880,CompactMinus3872.nodes3880,NodeMinus60.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3881,GridMinus.atNode 3881,GridMinus.atNode 3882,NodeMinus60.w41,CompactMinus3872.checked3881,CompactMinus3872.small3881,CompactMinus3872.nodes3881,NodeMinus60.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3882,GridMinus.atNode 3882,GridMinus.atNode 3883,NodeMinus60.w42,CompactMinus3872.checked3882,CompactMinus3872.small3882,CompactMinus3872.nodes3882,NodeMinus60.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3883,GridMinus.atNode 3883,GridMinus.atNode 3884,NodeMinus60.w43,CompactMinus3872.checked3883,CompactMinus3872.small3883,CompactMinus3872.nodes3883,NodeMinus60.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3884,GridMinus.atNode 3884,GridMinus.atNode 3885,NodeMinus60.w44,CompactMinus3872.checked3884,CompactMinus3872.small3884,CompactMinus3872.nodes3884,NodeMinus60.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3885,GridMinus.atNode 3885,GridMinus.atNode 3886,NodeMinus60.w45,CompactMinus3872.checked3885,CompactMinus3872.small3885,CompactMinus3872.nodes3885,NodeMinus60.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3886,GridMinus.atNode 3886,GridMinus.atNode 3887,NodeMinus60.w46,CompactMinus3872.checked3886,CompactMinus3872.small3886,CompactMinus3872.nodes3886,NodeMinus60.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3872.p3887,GridMinus.atNode 3887,GridMinus.atNode 3888,NodeMinus60.w47,CompactMinus3872.checked3887,CompactMinus3872.small3887,CompactMinus3872.nodes3887,NodeMinus60.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3888,GridMinus.atNode 3888,GridMinus.atNode 3889,NodeMinus60.w48,CompactMinus3888.checked3888,CompactMinus3888.small3888,CompactMinus3888.nodes3888,NodeMinus60.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3889,GridMinus.atNode 3889,GridMinus.atNode 3890,NodeMinus60.w49,CompactMinus3888.checked3889,CompactMinus3888.small3889,CompactMinus3888.nodes3889,NodeMinus60.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3890,GridMinus.atNode 3890,GridMinus.atNode 3891,NodeMinus60.w50,CompactMinus3888.checked3890,CompactMinus3888.small3890,CompactMinus3888.nodes3890,NodeMinus60.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3891,GridMinus.atNode 3891,GridMinus.atNode 3892,NodeMinus60.w51,CompactMinus3888.checked3891,CompactMinus3888.small3891,CompactMinus3888.nodes3891,NodeMinus60.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3892,GridMinus.atNode 3892,GridMinus.atNode 3893,NodeMinus60.w52,CompactMinus3888.checked3892,CompactMinus3888.small3892,CompactMinus3888.nodes3892,NodeMinus60.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3893,GridMinus.atNode 3893,GridMinus.atNode 3894,NodeMinus60.w53,CompactMinus3888.checked3893,CompactMinus3888.small3893,CompactMinus3888.nodes3893,NodeMinus60.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3894,GridMinus.atNode 3894,GridMinus.atNode 3895,NodeMinus60.w54,CompactMinus3888.checked3894,CompactMinus3888.small3894,CompactMinus3888.nodes3894,NodeMinus60.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3895,GridMinus.atNode 3895,GridMinus.atNode 3896,NodeMinus60.w55,CompactMinus3888.checked3895,CompactMinus3888.small3895,CompactMinus3888.nodes3895,NodeMinus60.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3896,GridMinus.atNode 3896,GridMinus.atNode 3897,NodeMinus60.w56,CompactMinus3888.checked3896,CompactMinus3888.small3896,CompactMinus3888.nodes3896,NodeMinus60.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3897,GridMinus.atNode 3897,GridMinus.atNode 3898,NodeMinus60.w57,CompactMinus3888.checked3897,CompactMinus3888.small3897,CompactMinus3888.nodes3897,NodeMinus60.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3898,GridMinus.atNode 3898,GridMinus.atNode 3899,NodeMinus60.w58,CompactMinus3888.checked3898,CompactMinus3888.small3898,CompactMinus3888.nodes3898,NodeMinus60.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3899,GridMinus.atNode 3899,GridMinus.atNode 3900,NodeMinus60.w59,CompactMinus3888.checked3899,CompactMinus3888.small3899,CompactMinus3888.nodes3899,NodeMinus60.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3900,GridMinus.atNode 3900,GridMinus.atNode 3901,NodeMinus60.w60,CompactMinus3888.checked3900,CompactMinus3888.small3900,CompactMinus3888.nodes3900,NodeMinus60.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3901,GridMinus.atNode 3901,GridMinus.atNode 3902,NodeMinus60.w61,CompactMinus3888.checked3901,CompactMinus3888.small3901,CompactMinus3888.nodes3901,NodeMinus60.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3902,GridMinus.atNode 3902,GridMinus.atNode 3903,NodeMinus60.w62,CompactMinus3888.checked3902,CompactMinus3888.small3902,CompactMinus3888.nodes3902,NodeMinus60.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3888.p3903,GridMinus.atNode 3903,GridMinus.atNode 3904,NodeMinus60.w63,CompactMinus3888.checked3903,CompactMinus3888.small3903,CompactMinus3888.nodes3903,NodeMinus60.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3840+j) ∧
    (atRow j).right=GridMinus.atNode (3840+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus60
