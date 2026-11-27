import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3968
import SolitonClassification.Rotating.ResetPackedMinus3984
namespace SolitonClassification.Rotating.DyadicReset.TileMinus62
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3968,GridMinus.atNode 3968,GridMinus.atNode 3969,NodeMinus62.w0,CompactMinus3968.checked3968,CompactMinus3968.small3968,CompactMinus3968.nodes3968,NodeMinus62.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3969,GridMinus.atNode 3969,GridMinus.atNode 3970,NodeMinus62.w1,CompactMinus3968.checked3969,CompactMinus3968.small3969,CompactMinus3968.nodes3969,NodeMinus62.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3970,GridMinus.atNode 3970,GridMinus.atNode 3971,NodeMinus62.w2,CompactMinus3968.checked3970,CompactMinus3968.small3970,CompactMinus3968.nodes3970,NodeMinus62.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3971,GridMinus.atNode 3971,GridMinus.atNode 3972,NodeMinus62.w3,CompactMinus3968.checked3971,CompactMinus3968.small3971,CompactMinus3968.nodes3971,NodeMinus62.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3972,GridMinus.atNode 3972,GridMinus.atNode 3973,NodeMinus62.w4,CompactMinus3968.checked3972,CompactMinus3968.small3972,CompactMinus3968.nodes3972,NodeMinus62.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3973,GridMinus.atNode 3973,GridMinus.atNode 3974,NodeMinus62.w5,CompactMinus3968.checked3973,CompactMinus3968.small3973,CompactMinus3968.nodes3973,NodeMinus62.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3974,GridMinus.atNode 3974,GridMinus.atNode 3975,NodeMinus62.w6,CompactMinus3968.checked3974,CompactMinus3968.small3974,CompactMinus3968.nodes3974,NodeMinus62.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3975,GridMinus.atNode 3975,GridMinus.atNode 3976,NodeMinus62.w7,CompactMinus3968.checked3975,CompactMinus3968.small3975,CompactMinus3968.nodes3975,NodeMinus62.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3976,GridMinus.atNode 3976,GridMinus.atNode 3977,NodeMinus62.w8,CompactMinus3968.checked3976,CompactMinus3968.small3976,CompactMinus3968.nodes3976,NodeMinus62.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3977,GridMinus.atNode 3977,GridMinus.atNode 3978,NodeMinus62.w9,CompactMinus3968.checked3977,CompactMinus3968.small3977,CompactMinus3968.nodes3977,NodeMinus62.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3978,GridMinus.atNode 3978,GridMinus.atNode 3979,NodeMinus62.w10,CompactMinus3968.checked3978,CompactMinus3968.small3978,CompactMinus3968.nodes3978,NodeMinus62.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3979,GridMinus.atNode 3979,GridMinus.atNode 3980,NodeMinus62.w11,CompactMinus3968.checked3979,CompactMinus3968.small3979,CompactMinus3968.nodes3979,NodeMinus62.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3980,GridMinus.atNode 3980,GridMinus.atNode 3981,NodeMinus62.w12,CompactMinus3968.checked3980,CompactMinus3968.small3980,CompactMinus3968.nodes3980,NodeMinus62.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3981,GridMinus.atNode 3981,GridMinus.atNode 3982,NodeMinus62.w13,CompactMinus3968.checked3981,CompactMinus3968.small3981,CompactMinus3968.nodes3981,NodeMinus62.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3982,GridMinus.atNode 3982,GridMinus.atNode 3983,NodeMinus62.w14,CompactMinus3968.checked3982,CompactMinus3968.small3982,CompactMinus3968.nodes3982,NodeMinus62.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3968.p3983,GridMinus.atNode 3983,GridMinus.atNode 3984,NodeMinus62.w15,CompactMinus3968.checked3983,CompactMinus3968.small3983,CompactMinus3968.nodes3983,NodeMinus62.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3984,GridMinus.atNode 3984,GridMinus.atNode 3985,NodeMinus62.w16,CompactMinus3984.checked3984,CompactMinus3984.small3984,CompactMinus3984.nodes3984,NodeMinus62.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3985,GridMinus.atNode 3985,GridMinus.atNode 3986,NodeMinus62.w17,CompactMinus3984.checked3985,CompactMinus3984.small3985,CompactMinus3984.nodes3985,NodeMinus62.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3986,GridMinus.atNode 3986,GridMinus.atNode 3987,NodeMinus62.w18,CompactMinus3984.checked3986,CompactMinus3984.small3986,CompactMinus3984.nodes3986,NodeMinus62.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3987,GridMinus.atNode 3987,GridMinus.atNode 3988,NodeMinus62.w19,CompactMinus3984.checked3987,CompactMinus3984.small3987,CompactMinus3984.nodes3987,NodeMinus62.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3988,GridMinus.atNode 3988,GridMinus.atNode 3989,NodeMinus62.w20,CompactMinus3984.checked3988,CompactMinus3984.small3988,CompactMinus3984.nodes3988,NodeMinus62.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3989,GridMinus.atNode 3989,GridMinus.atNode 3990,NodeMinus62.w21,CompactMinus3984.checked3989,CompactMinus3984.small3989,CompactMinus3984.nodes3989,NodeMinus62.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3990,GridMinus.atNode 3990,GridMinus.atNode 3991,NodeMinus62.w22,CompactMinus3984.checked3990,CompactMinus3984.small3990,CompactMinus3984.nodes3990,NodeMinus62.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3991,GridMinus.atNode 3991,GridMinus.atNode 3992,NodeMinus62.w23,CompactMinus3984.checked3991,CompactMinus3984.small3991,CompactMinus3984.nodes3991,NodeMinus62.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3992,GridMinus.atNode 3992,GridMinus.atNode 3993,NodeMinus62.w24,CompactMinus3984.checked3992,CompactMinus3984.small3992,CompactMinus3984.nodes3992,NodeMinus62.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3993,GridMinus.atNode 3993,GridMinus.atNode 3994,NodeMinus62.w25,CompactMinus3984.checked3993,CompactMinus3984.small3993,CompactMinus3984.nodes3993,NodeMinus62.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3994,GridMinus.atNode 3994,GridMinus.atNode 3995,NodeMinus62.w26,CompactMinus3984.checked3994,CompactMinus3984.small3994,CompactMinus3984.nodes3994,NodeMinus62.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3995,GridMinus.atNode 3995,GridMinus.atNode 3996,NodeMinus62.w27,CompactMinus3984.checked3995,CompactMinus3984.small3995,CompactMinus3984.nodes3995,NodeMinus62.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3996,GridMinus.atNode 3996,GridMinus.atNode 3997,NodeMinus62.w28,CompactMinus3984.checked3996,CompactMinus3984.small3996,CompactMinus3984.nodes3996,NodeMinus62.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3997,GridMinus.atNode 3997,GridMinus.atNode 3998,NodeMinus62.w29,CompactMinus3984.checked3997,CompactMinus3984.small3997,CompactMinus3984.nodes3997,NodeMinus62.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3998,GridMinus.atNode 3998,GridMinus.atNode 3999,NodeMinus62.w30,CompactMinus3984.checked3998,CompactMinus3984.small3998,CompactMinus3984.nodes3998,NodeMinus62.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3984.p3999,GridMinus.atNode 3999,GridMinus.atNode 4000,NodeMinus62.w31,CompactMinus3984.checked3999,CompactMinus3984.small3999,CompactMinus3984.nodes3999,NodeMinus62.bounds31⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<32) : (atRow j).left=GridMinus.atNode (3968+j) ∧
    (atRow j).right=GridMinus.atNode (3968+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus62
