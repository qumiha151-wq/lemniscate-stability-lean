import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3968
import SolitonClassification.Rotating.ResetPackedPlus3984
namespace SolitonClassification.Rotating.DyadicReset.TilePlus62
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3968,GridPlus.atNode 3968,GridPlus.atNode 3969,NodePlus62.w0,CompactPlus3968.checked3968,CompactPlus3968.small3968,CompactPlus3968.nodes3968,NodePlus62.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3969,GridPlus.atNode 3969,GridPlus.atNode 3970,NodePlus62.w1,CompactPlus3968.checked3969,CompactPlus3968.small3969,CompactPlus3968.nodes3969,NodePlus62.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3970,GridPlus.atNode 3970,GridPlus.atNode 3971,NodePlus62.w2,CompactPlus3968.checked3970,CompactPlus3968.small3970,CompactPlus3968.nodes3970,NodePlus62.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3971,GridPlus.atNode 3971,GridPlus.atNode 3972,NodePlus62.w3,CompactPlus3968.checked3971,CompactPlus3968.small3971,CompactPlus3968.nodes3971,NodePlus62.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3972,GridPlus.atNode 3972,GridPlus.atNode 3973,NodePlus62.w4,CompactPlus3968.checked3972,CompactPlus3968.small3972,CompactPlus3968.nodes3972,NodePlus62.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3973,GridPlus.atNode 3973,GridPlus.atNode 3974,NodePlus62.w5,CompactPlus3968.checked3973,CompactPlus3968.small3973,CompactPlus3968.nodes3973,NodePlus62.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3974,GridPlus.atNode 3974,GridPlus.atNode 3975,NodePlus62.w6,CompactPlus3968.checked3974,CompactPlus3968.small3974,CompactPlus3968.nodes3974,NodePlus62.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3975,GridPlus.atNode 3975,GridPlus.atNode 3976,NodePlus62.w7,CompactPlus3968.checked3975,CompactPlus3968.small3975,CompactPlus3968.nodes3975,NodePlus62.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3976,GridPlus.atNode 3976,GridPlus.atNode 3977,NodePlus62.w8,CompactPlus3968.checked3976,CompactPlus3968.small3976,CompactPlus3968.nodes3976,NodePlus62.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3977,GridPlus.atNode 3977,GridPlus.atNode 3978,NodePlus62.w9,CompactPlus3968.checked3977,CompactPlus3968.small3977,CompactPlus3968.nodes3977,NodePlus62.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3978,GridPlus.atNode 3978,GridPlus.atNode 3979,NodePlus62.w10,CompactPlus3968.checked3978,CompactPlus3968.small3978,CompactPlus3968.nodes3978,NodePlus62.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3979,GridPlus.atNode 3979,GridPlus.atNode 3980,NodePlus62.w11,CompactPlus3968.checked3979,CompactPlus3968.small3979,CompactPlus3968.nodes3979,NodePlus62.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3980,GridPlus.atNode 3980,GridPlus.atNode 3981,NodePlus62.w12,CompactPlus3968.checked3980,CompactPlus3968.small3980,CompactPlus3968.nodes3980,NodePlus62.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3981,GridPlus.atNode 3981,GridPlus.atNode 3982,NodePlus62.w13,CompactPlus3968.checked3981,CompactPlus3968.small3981,CompactPlus3968.nodes3981,NodePlus62.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3982,GridPlus.atNode 3982,GridPlus.atNode 3983,NodePlus62.w14,CompactPlus3968.checked3982,CompactPlus3968.small3982,CompactPlus3968.nodes3982,NodePlus62.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3968.p3983,GridPlus.atNode 3983,GridPlus.atNode 3984,NodePlus62.w15,CompactPlus3968.checked3983,CompactPlus3968.small3983,CompactPlus3968.nodes3983,NodePlus62.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3984,GridPlus.atNode 3984,GridPlus.atNode 3985,NodePlus62.w16,CompactPlus3984.checked3984,CompactPlus3984.small3984,CompactPlus3984.nodes3984,NodePlus62.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3985,GridPlus.atNode 3985,GridPlus.atNode 3986,NodePlus62.w17,CompactPlus3984.checked3985,CompactPlus3984.small3985,CompactPlus3984.nodes3985,NodePlus62.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3986,GridPlus.atNode 3986,GridPlus.atNode 3987,NodePlus62.w18,CompactPlus3984.checked3986,CompactPlus3984.small3986,CompactPlus3984.nodes3986,NodePlus62.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3987,GridPlus.atNode 3987,GridPlus.atNode 3988,NodePlus62.w19,CompactPlus3984.checked3987,CompactPlus3984.small3987,CompactPlus3984.nodes3987,NodePlus62.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3988,GridPlus.atNode 3988,GridPlus.atNode 3989,NodePlus62.w20,CompactPlus3984.checked3988,CompactPlus3984.small3988,CompactPlus3984.nodes3988,NodePlus62.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3989,GridPlus.atNode 3989,GridPlus.atNode 3990,NodePlus62.w21,CompactPlus3984.checked3989,CompactPlus3984.small3989,CompactPlus3984.nodes3989,NodePlus62.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3990,GridPlus.atNode 3990,GridPlus.atNode 3991,NodePlus62.w22,CompactPlus3984.checked3990,CompactPlus3984.small3990,CompactPlus3984.nodes3990,NodePlus62.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3991,GridPlus.atNode 3991,GridPlus.atNode 3992,NodePlus62.w23,CompactPlus3984.checked3991,CompactPlus3984.small3991,CompactPlus3984.nodes3991,NodePlus62.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3992,GridPlus.atNode 3992,GridPlus.atNode 3993,NodePlus62.w24,CompactPlus3984.checked3992,CompactPlus3984.small3992,CompactPlus3984.nodes3992,NodePlus62.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3993,GridPlus.atNode 3993,GridPlus.atNode 3994,NodePlus62.w25,CompactPlus3984.checked3993,CompactPlus3984.small3993,CompactPlus3984.nodes3993,NodePlus62.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3994,GridPlus.atNode 3994,GridPlus.atNode 3995,NodePlus62.w26,CompactPlus3984.checked3994,CompactPlus3984.small3994,CompactPlus3984.nodes3994,NodePlus62.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3995,GridPlus.atNode 3995,GridPlus.atNode 3996,NodePlus62.w27,CompactPlus3984.checked3995,CompactPlus3984.small3995,CompactPlus3984.nodes3995,NodePlus62.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3996,GridPlus.atNode 3996,GridPlus.atNode 3997,NodePlus62.w28,CompactPlus3984.checked3996,CompactPlus3984.small3996,CompactPlus3984.nodes3996,NodePlus62.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3997,GridPlus.atNode 3997,GridPlus.atNode 3998,NodePlus62.w29,CompactPlus3984.checked3997,CompactPlus3984.small3997,CompactPlus3984.nodes3997,NodePlus62.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3998,GridPlus.atNode 3998,GridPlus.atNode 3999,NodePlus62.w30,CompactPlus3984.checked3998,CompactPlus3984.small3998,CompactPlus3984.nodes3998,NodePlus62.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3984.p3999,GridPlus.atNode 3999,GridPlus.atNode 4000,NodePlus62.w31,CompactPlus3984.checked3999,CompactPlus3984.small3999,CompactPlus3984.nodes3999,NodePlus62.bounds31⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<32) : (atRow j).left=GridPlus.atNode (3968+j) ∧
    (atRow j).right=GridPlus.atNode (3968+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus62
