import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3008
import SolitonClassification.Rotating.ResetPackedMinus3024
import SolitonClassification.Rotating.ResetPackedMinus3040
import SolitonClassification.Rotating.ResetPackedMinus3056
namespace SolitonClassification.Rotating.DyadicReset.TileMinus47
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3008,GridMinus.atNode 3008,GridMinus.atNode 3009,NodeMinus47.w0,CompactMinus3008.checked3008,CompactMinus3008.small3008,CompactMinus3008.nodes3008,NodeMinus47.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3009,GridMinus.atNode 3009,GridMinus.atNode 3010,NodeMinus47.w1,CompactMinus3008.checked3009,CompactMinus3008.small3009,CompactMinus3008.nodes3009,NodeMinus47.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3010,GridMinus.atNode 3010,GridMinus.atNode 3011,NodeMinus47.w2,CompactMinus3008.checked3010,CompactMinus3008.small3010,CompactMinus3008.nodes3010,NodeMinus47.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3011,GridMinus.atNode 3011,GridMinus.atNode 3012,NodeMinus47.w3,CompactMinus3008.checked3011,CompactMinus3008.small3011,CompactMinus3008.nodes3011,NodeMinus47.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3012,GridMinus.atNode 3012,GridMinus.atNode 3013,NodeMinus47.w4,CompactMinus3008.checked3012,CompactMinus3008.small3012,CompactMinus3008.nodes3012,NodeMinus47.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3013,GridMinus.atNode 3013,GridMinus.atNode 3014,NodeMinus47.w5,CompactMinus3008.checked3013,CompactMinus3008.small3013,CompactMinus3008.nodes3013,NodeMinus47.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3014,GridMinus.atNode 3014,GridMinus.atNode 3015,NodeMinus47.w6,CompactMinus3008.checked3014,CompactMinus3008.small3014,CompactMinus3008.nodes3014,NodeMinus47.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3015,GridMinus.atNode 3015,GridMinus.atNode 3016,NodeMinus47.w7,CompactMinus3008.checked3015,CompactMinus3008.small3015,CompactMinus3008.nodes3015,NodeMinus47.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3016,GridMinus.atNode 3016,GridMinus.atNode 3017,NodeMinus47.w8,CompactMinus3008.checked3016,CompactMinus3008.small3016,CompactMinus3008.nodes3016,NodeMinus47.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3017,GridMinus.atNode 3017,GridMinus.atNode 3018,NodeMinus47.w9,CompactMinus3008.checked3017,CompactMinus3008.small3017,CompactMinus3008.nodes3017,NodeMinus47.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3018,GridMinus.atNode 3018,GridMinus.atNode 3019,NodeMinus47.w10,CompactMinus3008.checked3018,CompactMinus3008.small3018,CompactMinus3008.nodes3018,NodeMinus47.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3019,GridMinus.atNode 3019,GridMinus.atNode 3020,NodeMinus47.w11,CompactMinus3008.checked3019,CompactMinus3008.small3019,CompactMinus3008.nodes3019,NodeMinus47.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3020,GridMinus.atNode 3020,GridMinus.atNode 3021,NodeMinus47.w12,CompactMinus3008.checked3020,CompactMinus3008.small3020,CompactMinus3008.nodes3020,NodeMinus47.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3021,GridMinus.atNode 3021,GridMinus.atNode 3022,NodeMinus47.w13,CompactMinus3008.checked3021,CompactMinus3008.small3021,CompactMinus3008.nodes3021,NodeMinus47.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3022,GridMinus.atNode 3022,GridMinus.atNode 3023,NodeMinus47.w14,CompactMinus3008.checked3022,CompactMinus3008.small3022,CompactMinus3008.nodes3022,NodeMinus47.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3008.p3023,GridMinus.atNode 3023,GridMinus.atNode 3024,NodeMinus47.w15,CompactMinus3008.checked3023,CompactMinus3008.small3023,CompactMinus3008.nodes3023,NodeMinus47.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3024,GridMinus.atNode 3024,GridMinus.atNode 3025,NodeMinus47.w16,CompactMinus3024.checked3024,CompactMinus3024.small3024,CompactMinus3024.nodes3024,NodeMinus47.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3025,GridMinus.atNode 3025,GridMinus.atNode 3026,NodeMinus47.w17,CompactMinus3024.checked3025,CompactMinus3024.small3025,CompactMinus3024.nodes3025,NodeMinus47.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3026,GridMinus.atNode 3026,GridMinus.atNode 3027,NodeMinus47.w18,CompactMinus3024.checked3026,CompactMinus3024.small3026,CompactMinus3024.nodes3026,NodeMinus47.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3027,GridMinus.atNode 3027,GridMinus.atNode 3028,NodeMinus47.w19,CompactMinus3024.checked3027,CompactMinus3024.small3027,CompactMinus3024.nodes3027,NodeMinus47.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3028,GridMinus.atNode 3028,GridMinus.atNode 3029,NodeMinus47.w20,CompactMinus3024.checked3028,CompactMinus3024.small3028,CompactMinus3024.nodes3028,NodeMinus47.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3029,GridMinus.atNode 3029,GridMinus.atNode 3030,NodeMinus47.w21,CompactMinus3024.checked3029,CompactMinus3024.small3029,CompactMinus3024.nodes3029,NodeMinus47.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3030,GridMinus.atNode 3030,GridMinus.atNode 3031,NodeMinus47.w22,CompactMinus3024.checked3030,CompactMinus3024.small3030,CompactMinus3024.nodes3030,NodeMinus47.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3031,GridMinus.atNode 3031,GridMinus.atNode 3032,NodeMinus47.w23,CompactMinus3024.checked3031,CompactMinus3024.small3031,CompactMinus3024.nodes3031,NodeMinus47.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3032,GridMinus.atNode 3032,GridMinus.atNode 3033,NodeMinus47.w24,CompactMinus3024.checked3032,CompactMinus3024.small3032,CompactMinus3024.nodes3032,NodeMinus47.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3033,GridMinus.atNode 3033,GridMinus.atNode 3034,NodeMinus47.w25,CompactMinus3024.checked3033,CompactMinus3024.small3033,CompactMinus3024.nodes3033,NodeMinus47.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3034,GridMinus.atNode 3034,GridMinus.atNode 3035,NodeMinus47.w26,CompactMinus3024.checked3034,CompactMinus3024.small3034,CompactMinus3024.nodes3034,NodeMinus47.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3035,GridMinus.atNode 3035,GridMinus.atNode 3036,NodeMinus47.w27,CompactMinus3024.checked3035,CompactMinus3024.small3035,CompactMinus3024.nodes3035,NodeMinus47.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3036,GridMinus.atNode 3036,GridMinus.atNode 3037,NodeMinus47.w28,CompactMinus3024.checked3036,CompactMinus3024.small3036,CompactMinus3024.nodes3036,NodeMinus47.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3037,GridMinus.atNode 3037,GridMinus.atNode 3038,NodeMinus47.w29,CompactMinus3024.checked3037,CompactMinus3024.small3037,CompactMinus3024.nodes3037,NodeMinus47.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3038,GridMinus.atNode 3038,GridMinus.atNode 3039,NodeMinus47.w30,CompactMinus3024.checked3038,CompactMinus3024.small3038,CompactMinus3024.nodes3038,NodeMinus47.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3024.p3039,GridMinus.atNode 3039,GridMinus.atNode 3040,NodeMinus47.w31,CompactMinus3024.checked3039,CompactMinus3024.small3039,CompactMinus3024.nodes3039,NodeMinus47.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3040,GridMinus.atNode 3040,GridMinus.atNode 3041,NodeMinus47.w32,CompactMinus3040.checked3040,CompactMinus3040.small3040,CompactMinus3040.nodes3040,NodeMinus47.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3041,GridMinus.atNode 3041,GridMinus.atNode 3042,NodeMinus47.w33,CompactMinus3040.checked3041,CompactMinus3040.small3041,CompactMinus3040.nodes3041,NodeMinus47.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3042,GridMinus.atNode 3042,GridMinus.atNode 3043,NodeMinus47.w34,CompactMinus3040.checked3042,CompactMinus3040.small3042,CompactMinus3040.nodes3042,NodeMinus47.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3043,GridMinus.atNode 3043,GridMinus.atNode 3044,NodeMinus47.w35,CompactMinus3040.checked3043,CompactMinus3040.small3043,CompactMinus3040.nodes3043,NodeMinus47.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3044,GridMinus.atNode 3044,GridMinus.atNode 3045,NodeMinus47.w36,CompactMinus3040.checked3044,CompactMinus3040.small3044,CompactMinus3040.nodes3044,NodeMinus47.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3045,GridMinus.atNode 3045,GridMinus.atNode 3046,NodeMinus47.w37,CompactMinus3040.checked3045,CompactMinus3040.small3045,CompactMinus3040.nodes3045,NodeMinus47.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3046,GridMinus.atNode 3046,GridMinus.atNode 3047,NodeMinus47.w38,CompactMinus3040.checked3046,CompactMinus3040.small3046,CompactMinus3040.nodes3046,NodeMinus47.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3047,GridMinus.atNode 3047,GridMinus.atNode 3048,NodeMinus47.w39,CompactMinus3040.checked3047,CompactMinus3040.small3047,CompactMinus3040.nodes3047,NodeMinus47.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3048,GridMinus.atNode 3048,GridMinus.atNode 3049,NodeMinus47.w40,CompactMinus3040.checked3048,CompactMinus3040.small3048,CompactMinus3040.nodes3048,NodeMinus47.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3049,GridMinus.atNode 3049,GridMinus.atNode 3050,NodeMinus47.w41,CompactMinus3040.checked3049,CompactMinus3040.small3049,CompactMinus3040.nodes3049,NodeMinus47.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3050,GridMinus.atNode 3050,GridMinus.atNode 3051,NodeMinus47.w42,CompactMinus3040.checked3050,CompactMinus3040.small3050,CompactMinus3040.nodes3050,NodeMinus47.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3051,GridMinus.atNode 3051,GridMinus.atNode 3052,NodeMinus47.w43,CompactMinus3040.checked3051,CompactMinus3040.small3051,CompactMinus3040.nodes3051,NodeMinus47.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3052,GridMinus.atNode 3052,GridMinus.atNode 3053,NodeMinus47.w44,CompactMinus3040.checked3052,CompactMinus3040.small3052,CompactMinus3040.nodes3052,NodeMinus47.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3053,GridMinus.atNode 3053,GridMinus.atNode 3054,NodeMinus47.w45,CompactMinus3040.checked3053,CompactMinus3040.small3053,CompactMinus3040.nodes3053,NodeMinus47.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3054,GridMinus.atNode 3054,GridMinus.atNode 3055,NodeMinus47.w46,CompactMinus3040.checked3054,CompactMinus3040.small3054,CompactMinus3040.nodes3054,NodeMinus47.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3040.p3055,GridMinus.atNode 3055,GridMinus.atNode 3056,NodeMinus47.w47,CompactMinus3040.checked3055,CompactMinus3040.small3055,CompactMinus3040.nodes3055,NodeMinus47.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3056,GridMinus.atNode 3056,GridMinus.atNode 3057,NodeMinus47.w48,CompactMinus3056.checked3056,CompactMinus3056.small3056,CompactMinus3056.nodes3056,NodeMinus47.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3057,GridMinus.atNode 3057,GridMinus.atNode 3058,NodeMinus47.w49,CompactMinus3056.checked3057,CompactMinus3056.small3057,CompactMinus3056.nodes3057,NodeMinus47.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3058,GridMinus.atNode 3058,GridMinus.atNode 3059,NodeMinus47.w50,CompactMinus3056.checked3058,CompactMinus3056.small3058,CompactMinus3056.nodes3058,NodeMinus47.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3059,GridMinus.atNode 3059,GridMinus.atNode 3060,NodeMinus47.w51,CompactMinus3056.checked3059,CompactMinus3056.small3059,CompactMinus3056.nodes3059,NodeMinus47.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3060,GridMinus.atNode 3060,GridMinus.atNode 3061,NodeMinus47.w52,CompactMinus3056.checked3060,CompactMinus3056.small3060,CompactMinus3056.nodes3060,NodeMinus47.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3061,GridMinus.atNode 3061,GridMinus.atNode 3062,NodeMinus47.w53,CompactMinus3056.checked3061,CompactMinus3056.small3061,CompactMinus3056.nodes3061,NodeMinus47.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3062,GridMinus.atNode 3062,GridMinus.atNode 3063,NodeMinus47.w54,CompactMinus3056.checked3062,CompactMinus3056.small3062,CompactMinus3056.nodes3062,NodeMinus47.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3063,GridMinus.atNode 3063,GridMinus.atNode 3064,NodeMinus47.w55,CompactMinus3056.checked3063,CompactMinus3056.small3063,CompactMinus3056.nodes3063,NodeMinus47.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3064,GridMinus.atNode 3064,GridMinus.atNode 3065,NodeMinus47.w56,CompactMinus3056.checked3064,CompactMinus3056.small3064,CompactMinus3056.nodes3064,NodeMinus47.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3065,GridMinus.atNode 3065,GridMinus.atNode 3066,NodeMinus47.w57,CompactMinus3056.checked3065,CompactMinus3056.small3065,CompactMinus3056.nodes3065,NodeMinus47.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3066,GridMinus.atNode 3066,GridMinus.atNode 3067,NodeMinus47.w58,CompactMinus3056.checked3066,CompactMinus3056.small3066,CompactMinus3056.nodes3066,NodeMinus47.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3067,GridMinus.atNode 3067,GridMinus.atNode 3068,NodeMinus47.w59,CompactMinus3056.checked3067,CompactMinus3056.small3067,CompactMinus3056.nodes3067,NodeMinus47.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3068,GridMinus.atNode 3068,GridMinus.atNode 3069,NodeMinus47.w60,CompactMinus3056.checked3068,CompactMinus3056.small3068,CompactMinus3056.nodes3068,NodeMinus47.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3069,GridMinus.atNode 3069,GridMinus.atNode 3070,NodeMinus47.w61,CompactMinus3056.checked3069,CompactMinus3056.small3069,CompactMinus3056.nodes3069,NodeMinus47.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3070,GridMinus.atNode 3070,GridMinus.atNode 3071,NodeMinus47.w62,CompactMinus3056.checked3070,CompactMinus3056.small3070,CompactMinus3056.nodes3070,NodeMinus47.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3056.p3071,GridMinus.atNode 3071,GridMinus.atNode 3072,NodeMinus47.w63,CompactMinus3056.checked3071,CompactMinus3056.small3071,CompactMinus3056.nodes3071,NodeMinus47.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3008+j) ∧
    (atRow j).right=GridMinus.atNode (3008+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus47
