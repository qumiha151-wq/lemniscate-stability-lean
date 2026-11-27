import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3008
import SolitonClassification.Rotating.ResetPackedPlus3024
import SolitonClassification.Rotating.ResetPackedPlus3040
import SolitonClassification.Rotating.ResetPackedPlus3056
namespace SolitonClassification.Rotating.DyadicReset.TilePlus47
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3008,GridPlus.atNode 3008,GridPlus.atNode 3009,NodePlus47.w0,CompactPlus3008.checked3008,CompactPlus3008.small3008,CompactPlus3008.nodes3008,NodePlus47.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3009,GridPlus.atNode 3009,GridPlus.atNode 3010,NodePlus47.w1,CompactPlus3008.checked3009,CompactPlus3008.small3009,CompactPlus3008.nodes3009,NodePlus47.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3010,GridPlus.atNode 3010,GridPlus.atNode 3011,NodePlus47.w2,CompactPlus3008.checked3010,CompactPlus3008.small3010,CompactPlus3008.nodes3010,NodePlus47.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3011,GridPlus.atNode 3011,GridPlus.atNode 3012,NodePlus47.w3,CompactPlus3008.checked3011,CompactPlus3008.small3011,CompactPlus3008.nodes3011,NodePlus47.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3012,GridPlus.atNode 3012,GridPlus.atNode 3013,NodePlus47.w4,CompactPlus3008.checked3012,CompactPlus3008.small3012,CompactPlus3008.nodes3012,NodePlus47.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3013,GridPlus.atNode 3013,GridPlus.atNode 3014,NodePlus47.w5,CompactPlus3008.checked3013,CompactPlus3008.small3013,CompactPlus3008.nodes3013,NodePlus47.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3014,GridPlus.atNode 3014,GridPlus.atNode 3015,NodePlus47.w6,CompactPlus3008.checked3014,CompactPlus3008.small3014,CompactPlus3008.nodes3014,NodePlus47.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3015,GridPlus.atNode 3015,GridPlus.atNode 3016,NodePlus47.w7,CompactPlus3008.checked3015,CompactPlus3008.small3015,CompactPlus3008.nodes3015,NodePlus47.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3016,GridPlus.atNode 3016,GridPlus.atNode 3017,NodePlus47.w8,CompactPlus3008.checked3016,CompactPlus3008.small3016,CompactPlus3008.nodes3016,NodePlus47.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3017,GridPlus.atNode 3017,GridPlus.atNode 3018,NodePlus47.w9,CompactPlus3008.checked3017,CompactPlus3008.small3017,CompactPlus3008.nodes3017,NodePlus47.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3018,GridPlus.atNode 3018,GridPlus.atNode 3019,NodePlus47.w10,CompactPlus3008.checked3018,CompactPlus3008.small3018,CompactPlus3008.nodes3018,NodePlus47.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3019,GridPlus.atNode 3019,GridPlus.atNode 3020,NodePlus47.w11,CompactPlus3008.checked3019,CompactPlus3008.small3019,CompactPlus3008.nodes3019,NodePlus47.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3020,GridPlus.atNode 3020,GridPlus.atNode 3021,NodePlus47.w12,CompactPlus3008.checked3020,CompactPlus3008.small3020,CompactPlus3008.nodes3020,NodePlus47.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3021,GridPlus.atNode 3021,GridPlus.atNode 3022,NodePlus47.w13,CompactPlus3008.checked3021,CompactPlus3008.small3021,CompactPlus3008.nodes3021,NodePlus47.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3022,GridPlus.atNode 3022,GridPlus.atNode 3023,NodePlus47.w14,CompactPlus3008.checked3022,CompactPlus3008.small3022,CompactPlus3008.nodes3022,NodePlus47.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3008.p3023,GridPlus.atNode 3023,GridPlus.atNode 3024,NodePlus47.w15,CompactPlus3008.checked3023,CompactPlus3008.small3023,CompactPlus3008.nodes3023,NodePlus47.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3024,GridPlus.atNode 3024,GridPlus.atNode 3025,NodePlus47.w16,CompactPlus3024.checked3024,CompactPlus3024.small3024,CompactPlus3024.nodes3024,NodePlus47.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3025,GridPlus.atNode 3025,GridPlus.atNode 3026,NodePlus47.w17,CompactPlus3024.checked3025,CompactPlus3024.small3025,CompactPlus3024.nodes3025,NodePlus47.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3026,GridPlus.atNode 3026,GridPlus.atNode 3027,NodePlus47.w18,CompactPlus3024.checked3026,CompactPlus3024.small3026,CompactPlus3024.nodes3026,NodePlus47.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3027,GridPlus.atNode 3027,GridPlus.atNode 3028,NodePlus47.w19,CompactPlus3024.checked3027,CompactPlus3024.small3027,CompactPlus3024.nodes3027,NodePlus47.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3028,GridPlus.atNode 3028,GridPlus.atNode 3029,NodePlus47.w20,CompactPlus3024.checked3028,CompactPlus3024.small3028,CompactPlus3024.nodes3028,NodePlus47.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3029,GridPlus.atNode 3029,GridPlus.atNode 3030,NodePlus47.w21,CompactPlus3024.checked3029,CompactPlus3024.small3029,CompactPlus3024.nodes3029,NodePlus47.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3030,GridPlus.atNode 3030,GridPlus.atNode 3031,NodePlus47.w22,CompactPlus3024.checked3030,CompactPlus3024.small3030,CompactPlus3024.nodes3030,NodePlus47.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3031,GridPlus.atNode 3031,GridPlus.atNode 3032,NodePlus47.w23,CompactPlus3024.checked3031,CompactPlus3024.small3031,CompactPlus3024.nodes3031,NodePlus47.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3032,GridPlus.atNode 3032,GridPlus.atNode 3033,NodePlus47.w24,CompactPlus3024.checked3032,CompactPlus3024.small3032,CompactPlus3024.nodes3032,NodePlus47.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3033,GridPlus.atNode 3033,GridPlus.atNode 3034,NodePlus47.w25,CompactPlus3024.checked3033,CompactPlus3024.small3033,CompactPlus3024.nodes3033,NodePlus47.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3034,GridPlus.atNode 3034,GridPlus.atNode 3035,NodePlus47.w26,CompactPlus3024.checked3034,CompactPlus3024.small3034,CompactPlus3024.nodes3034,NodePlus47.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3035,GridPlus.atNode 3035,GridPlus.atNode 3036,NodePlus47.w27,CompactPlus3024.checked3035,CompactPlus3024.small3035,CompactPlus3024.nodes3035,NodePlus47.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3036,GridPlus.atNode 3036,GridPlus.atNode 3037,NodePlus47.w28,CompactPlus3024.checked3036,CompactPlus3024.small3036,CompactPlus3024.nodes3036,NodePlus47.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3037,GridPlus.atNode 3037,GridPlus.atNode 3038,NodePlus47.w29,CompactPlus3024.checked3037,CompactPlus3024.small3037,CompactPlus3024.nodes3037,NodePlus47.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3038,GridPlus.atNode 3038,GridPlus.atNode 3039,NodePlus47.w30,CompactPlus3024.checked3038,CompactPlus3024.small3038,CompactPlus3024.nodes3038,NodePlus47.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3024.p3039,GridPlus.atNode 3039,GridPlus.atNode 3040,NodePlus47.w31,CompactPlus3024.checked3039,CompactPlus3024.small3039,CompactPlus3024.nodes3039,NodePlus47.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3040,GridPlus.atNode 3040,GridPlus.atNode 3041,NodePlus47.w32,CompactPlus3040.checked3040,CompactPlus3040.small3040,CompactPlus3040.nodes3040,NodePlus47.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3041,GridPlus.atNode 3041,GridPlus.atNode 3042,NodePlus47.w33,CompactPlus3040.checked3041,CompactPlus3040.small3041,CompactPlus3040.nodes3041,NodePlus47.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3042,GridPlus.atNode 3042,GridPlus.atNode 3043,NodePlus47.w34,CompactPlus3040.checked3042,CompactPlus3040.small3042,CompactPlus3040.nodes3042,NodePlus47.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3043,GridPlus.atNode 3043,GridPlus.atNode 3044,NodePlus47.w35,CompactPlus3040.checked3043,CompactPlus3040.small3043,CompactPlus3040.nodes3043,NodePlus47.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3044,GridPlus.atNode 3044,GridPlus.atNode 3045,NodePlus47.w36,CompactPlus3040.checked3044,CompactPlus3040.small3044,CompactPlus3040.nodes3044,NodePlus47.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3045,GridPlus.atNode 3045,GridPlus.atNode 3046,NodePlus47.w37,CompactPlus3040.checked3045,CompactPlus3040.small3045,CompactPlus3040.nodes3045,NodePlus47.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3046,GridPlus.atNode 3046,GridPlus.atNode 3047,NodePlus47.w38,CompactPlus3040.checked3046,CompactPlus3040.small3046,CompactPlus3040.nodes3046,NodePlus47.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3047,GridPlus.atNode 3047,GridPlus.atNode 3048,NodePlus47.w39,CompactPlus3040.checked3047,CompactPlus3040.small3047,CompactPlus3040.nodes3047,NodePlus47.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3048,GridPlus.atNode 3048,GridPlus.atNode 3049,NodePlus47.w40,CompactPlus3040.checked3048,CompactPlus3040.small3048,CompactPlus3040.nodes3048,NodePlus47.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3049,GridPlus.atNode 3049,GridPlus.atNode 3050,NodePlus47.w41,CompactPlus3040.checked3049,CompactPlus3040.small3049,CompactPlus3040.nodes3049,NodePlus47.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3050,GridPlus.atNode 3050,GridPlus.atNode 3051,NodePlus47.w42,CompactPlus3040.checked3050,CompactPlus3040.small3050,CompactPlus3040.nodes3050,NodePlus47.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3051,GridPlus.atNode 3051,GridPlus.atNode 3052,NodePlus47.w43,CompactPlus3040.checked3051,CompactPlus3040.small3051,CompactPlus3040.nodes3051,NodePlus47.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3052,GridPlus.atNode 3052,GridPlus.atNode 3053,NodePlus47.w44,CompactPlus3040.checked3052,CompactPlus3040.small3052,CompactPlus3040.nodes3052,NodePlus47.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3053,GridPlus.atNode 3053,GridPlus.atNode 3054,NodePlus47.w45,CompactPlus3040.checked3053,CompactPlus3040.small3053,CompactPlus3040.nodes3053,NodePlus47.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3054,GridPlus.atNode 3054,GridPlus.atNode 3055,NodePlus47.w46,CompactPlus3040.checked3054,CompactPlus3040.small3054,CompactPlus3040.nodes3054,NodePlus47.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3040.p3055,GridPlus.atNode 3055,GridPlus.atNode 3056,NodePlus47.w47,CompactPlus3040.checked3055,CompactPlus3040.small3055,CompactPlus3040.nodes3055,NodePlus47.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3056,GridPlus.atNode 3056,GridPlus.atNode 3057,NodePlus47.w48,CompactPlus3056.checked3056,CompactPlus3056.small3056,CompactPlus3056.nodes3056,NodePlus47.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3057,GridPlus.atNode 3057,GridPlus.atNode 3058,NodePlus47.w49,CompactPlus3056.checked3057,CompactPlus3056.small3057,CompactPlus3056.nodes3057,NodePlus47.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3058,GridPlus.atNode 3058,GridPlus.atNode 3059,NodePlus47.w50,CompactPlus3056.checked3058,CompactPlus3056.small3058,CompactPlus3056.nodes3058,NodePlus47.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3059,GridPlus.atNode 3059,GridPlus.atNode 3060,NodePlus47.w51,CompactPlus3056.checked3059,CompactPlus3056.small3059,CompactPlus3056.nodes3059,NodePlus47.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3060,GridPlus.atNode 3060,GridPlus.atNode 3061,NodePlus47.w52,CompactPlus3056.checked3060,CompactPlus3056.small3060,CompactPlus3056.nodes3060,NodePlus47.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3061,GridPlus.atNode 3061,GridPlus.atNode 3062,NodePlus47.w53,CompactPlus3056.checked3061,CompactPlus3056.small3061,CompactPlus3056.nodes3061,NodePlus47.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3062,GridPlus.atNode 3062,GridPlus.atNode 3063,NodePlus47.w54,CompactPlus3056.checked3062,CompactPlus3056.small3062,CompactPlus3056.nodes3062,NodePlus47.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3063,GridPlus.atNode 3063,GridPlus.atNode 3064,NodePlus47.w55,CompactPlus3056.checked3063,CompactPlus3056.small3063,CompactPlus3056.nodes3063,NodePlus47.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3064,GridPlus.atNode 3064,GridPlus.atNode 3065,NodePlus47.w56,CompactPlus3056.checked3064,CompactPlus3056.small3064,CompactPlus3056.nodes3064,NodePlus47.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3065,GridPlus.atNode 3065,GridPlus.atNode 3066,NodePlus47.w57,CompactPlus3056.checked3065,CompactPlus3056.small3065,CompactPlus3056.nodes3065,NodePlus47.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3066,GridPlus.atNode 3066,GridPlus.atNode 3067,NodePlus47.w58,CompactPlus3056.checked3066,CompactPlus3056.small3066,CompactPlus3056.nodes3066,NodePlus47.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3067,GridPlus.atNode 3067,GridPlus.atNode 3068,NodePlus47.w59,CompactPlus3056.checked3067,CompactPlus3056.small3067,CompactPlus3056.nodes3067,NodePlus47.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3068,GridPlus.atNode 3068,GridPlus.atNode 3069,NodePlus47.w60,CompactPlus3056.checked3068,CompactPlus3056.small3068,CompactPlus3056.nodes3068,NodePlus47.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3069,GridPlus.atNode 3069,GridPlus.atNode 3070,NodePlus47.w61,CompactPlus3056.checked3069,CompactPlus3056.small3069,CompactPlus3056.nodes3069,NodePlus47.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3070,GridPlus.atNode 3070,GridPlus.atNode 3071,NodePlus47.w62,CompactPlus3056.checked3070,CompactPlus3056.small3070,CompactPlus3056.nodes3070,NodePlus47.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3056.p3071,GridPlus.atNode 3071,GridPlus.atNode 3072,NodePlus47.w63,CompactPlus3056.checked3071,CompactPlus3056.small3071,CompactPlus3056.nodes3071,NodePlus47.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3008+j) ∧
    (atRow j).right=GridPlus.atNode (3008+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus47
