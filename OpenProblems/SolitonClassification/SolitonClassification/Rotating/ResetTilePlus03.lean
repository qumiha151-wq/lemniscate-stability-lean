import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0192
import SolitonClassification.Rotating.ResetPackedPlus0208
import SolitonClassification.Rotating.ResetPackedPlus0224
import SolitonClassification.Rotating.ResetPackedPlus0240
namespace SolitonClassification.Rotating.DyadicReset.TilePlus03
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p192,GridPlus.atNode 192,GridPlus.atNode 193,NodePlus03.w0,CompactPlus0192.checked192,CompactPlus0192.small192,CompactPlus0192.nodes192,NodePlus03.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p193,GridPlus.atNode 193,GridPlus.atNode 194,NodePlus03.w1,CompactPlus0192.checked193,CompactPlus0192.small193,CompactPlus0192.nodes193,NodePlus03.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p194,GridPlus.atNode 194,GridPlus.atNode 195,NodePlus03.w2,CompactPlus0192.checked194,CompactPlus0192.small194,CompactPlus0192.nodes194,NodePlus03.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p195,GridPlus.atNode 195,GridPlus.atNode 196,NodePlus03.w3,CompactPlus0192.checked195,CompactPlus0192.small195,CompactPlus0192.nodes195,NodePlus03.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p196,GridPlus.atNode 196,GridPlus.atNode 197,NodePlus03.w4,CompactPlus0192.checked196,CompactPlus0192.small196,CompactPlus0192.nodes196,NodePlus03.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p197,GridPlus.atNode 197,GridPlus.atNode 198,NodePlus03.w5,CompactPlus0192.checked197,CompactPlus0192.small197,CompactPlus0192.nodes197,NodePlus03.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p198,GridPlus.atNode 198,GridPlus.atNode 199,NodePlus03.w6,CompactPlus0192.checked198,CompactPlus0192.small198,CompactPlus0192.nodes198,NodePlus03.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p199,GridPlus.atNode 199,GridPlus.atNode 200,NodePlus03.w7,CompactPlus0192.checked199,CompactPlus0192.small199,CompactPlus0192.nodes199,NodePlus03.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p200,GridPlus.atNode 200,GridPlus.atNode 201,NodePlus03.w8,CompactPlus0192.checked200,CompactPlus0192.small200,CompactPlus0192.nodes200,NodePlus03.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p201,GridPlus.atNode 201,GridPlus.atNode 202,NodePlus03.w9,CompactPlus0192.checked201,CompactPlus0192.small201,CompactPlus0192.nodes201,NodePlus03.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p202,GridPlus.atNode 202,GridPlus.atNode 203,NodePlus03.w10,CompactPlus0192.checked202,CompactPlus0192.small202,CompactPlus0192.nodes202,NodePlus03.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p203,GridPlus.atNode 203,GridPlus.atNode 204,NodePlus03.w11,CompactPlus0192.checked203,CompactPlus0192.small203,CompactPlus0192.nodes203,NodePlus03.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p204,GridPlus.atNode 204,GridPlus.atNode 205,NodePlus03.w12,CompactPlus0192.checked204,CompactPlus0192.small204,CompactPlus0192.nodes204,NodePlus03.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p205,GridPlus.atNode 205,GridPlus.atNode 206,NodePlus03.w13,CompactPlus0192.checked205,CompactPlus0192.small205,CompactPlus0192.nodes205,NodePlus03.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p206,GridPlus.atNode 206,GridPlus.atNode 207,NodePlus03.w14,CompactPlus0192.checked206,CompactPlus0192.small206,CompactPlus0192.nodes206,NodePlus03.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0192.p207,GridPlus.atNode 207,GridPlus.atNode 208,NodePlus03.w15,CompactPlus0192.checked207,CompactPlus0192.small207,CompactPlus0192.nodes207,NodePlus03.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p208,GridPlus.atNode 208,GridPlus.atNode 209,NodePlus03.w16,CompactPlus0208.checked208,CompactPlus0208.small208,CompactPlus0208.nodes208,NodePlus03.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p209,GridPlus.atNode 209,GridPlus.atNode 210,NodePlus03.w17,CompactPlus0208.checked209,CompactPlus0208.small209,CompactPlus0208.nodes209,NodePlus03.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p210,GridPlus.atNode 210,GridPlus.atNode 211,NodePlus03.w18,CompactPlus0208.checked210,CompactPlus0208.small210,CompactPlus0208.nodes210,NodePlus03.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p211,GridPlus.atNode 211,GridPlus.atNode 212,NodePlus03.w19,CompactPlus0208.checked211,CompactPlus0208.small211,CompactPlus0208.nodes211,NodePlus03.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p212,GridPlus.atNode 212,GridPlus.atNode 213,NodePlus03.w20,CompactPlus0208.checked212,CompactPlus0208.small212,CompactPlus0208.nodes212,NodePlus03.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p213,GridPlus.atNode 213,GridPlus.atNode 214,NodePlus03.w21,CompactPlus0208.checked213,CompactPlus0208.small213,CompactPlus0208.nodes213,NodePlus03.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p214,GridPlus.atNode 214,GridPlus.atNode 215,NodePlus03.w22,CompactPlus0208.checked214,CompactPlus0208.small214,CompactPlus0208.nodes214,NodePlus03.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p215,GridPlus.atNode 215,GridPlus.atNode 216,NodePlus03.w23,CompactPlus0208.checked215,CompactPlus0208.small215,CompactPlus0208.nodes215,NodePlus03.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p216,GridPlus.atNode 216,GridPlus.atNode 217,NodePlus03.w24,CompactPlus0208.checked216,CompactPlus0208.small216,CompactPlus0208.nodes216,NodePlus03.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p217,GridPlus.atNode 217,GridPlus.atNode 218,NodePlus03.w25,CompactPlus0208.checked217,CompactPlus0208.small217,CompactPlus0208.nodes217,NodePlus03.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p218,GridPlus.atNode 218,GridPlus.atNode 219,NodePlus03.w26,CompactPlus0208.checked218,CompactPlus0208.small218,CompactPlus0208.nodes218,NodePlus03.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p219,GridPlus.atNode 219,GridPlus.atNode 220,NodePlus03.w27,CompactPlus0208.checked219,CompactPlus0208.small219,CompactPlus0208.nodes219,NodePlus03.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p220,GridPlus.atNode 220,GridPlus.atNode 221,NodePlus03.w28,CompactPlus0208.checked220,CompactPlus0208.small220,CompactPlus0208.nodes220,NodePlus03.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p221,GridPlus.atNode 221,GridPlus.atNode 222,NodePlus03.w29,CompactPlus0208.checked221,CompactPlus0208.small221,CompactPlus0208.nodes221,NodePlus03.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p222,GridPlus.atNode 222,GridPlus.atNode 223,NodePlus03.w30,CompactPlus0208.checked222,CompactPlus0208.small222,CompactPlus0208.nodes222,NodePlus03.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0208.p223,GridPlus.atNode 223,GridPlus.atNode 224,NodePlus03.w31,CompactPlus0208.checked223,CompactPlus0208.small223,CompactPlus0208.nodes223,NodePlus03.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p224,GridPlus.atNode 224,GridPlus.atNode 225,NodePlus03.w32,CompactPlus0224.checked224,CompactPlus0224.small224,CompactPlus0224.nodes224,NodePlus03.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p225,GridPlus.atNode 225,GridPlus.atNode 226,NodePlus03.w33,CompactPlus0224.checked225,CompactPlus0224.small225,CompactPlus0224.nodes225,NodePlus03.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p226,GridPlus.atNode 226,GridPlus.atNode 227,NodePlus03.w34,CompactPlus0224.checked226,CompactPlus0224.small226,CompactPlus0224.nodes226,NodePlus03.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p227,GridPlus.atNode 227,GridPlus.atNode 228,NodePlus03.w35,CompactPlus0224.checked227,CompactPlus0224.small227,CompactPlus0224.nodes227,NodePlus03.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p228,GridPlus.atNode 228,GridPlus.atNode 229,NodePlus03.w36,CompactPlus0224.checked228,CompactPlus0224.small228,CompactPlus0224.nodes228,NodePlus03.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p229,GridPlus.atNode 229,GridPlus.atNode 230,NodePlus03.w37,CompactPlus0224.checked229,CompactPlus0224.small229,CompactPlus0224.nodes229,NodePlus03.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p230,GridPlus.atNode 230,GridPlus.atNode 231,NodePlus03.w38,CompactPlus0224.checked230,CompactPlus0224.small230,CompactPlus0224.nodes230,NodePlus03.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p231,GridPlus.atNode 231,GridPlus.atNode 232,NodePlus03.w39,CompactPlus0224.checked231,CompactPlus0224.small231,CompactPlus0224.nodes231,NodePlus03.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p232,GridPlus.atNode 232,GridPlus.atNode 233,NodePlus03.w40,CompactPlus0224.checked232,CompactPlus0224.small232,CompactPlus0224.nodes232,NodePlus03.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p233,GridPlus.atNode 233,GridPlus.atNode 234,NodePlus03.w41,CompactPlus0224.checked233,CompactPlus0224.small233,CompactPlus0224.nodes233,NodePlus03.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p234,GridPlus.atNode 234,GridPlus.atNode 235,NodePlus03.w42,CompactPlus0224.checked234,CompactPlus0224.small234,CompactPlus0224.nodes234,NodePlus03.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p235,GridPlus.atNode 235,GridPlus.atNode 236,NodePlus03.w43,CompactPlus0224.checked235,CompactPlus0224.small235,CompactPlus0224.nodes235,NodePlus03.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p236,GridPlus.atNode 236,GridPlus.atNode 237,NodePlus03.w44,CompactPlus0224.checked236,CompactPlus0224.small236,CompactPlus0224.nodes236,NodePlus03.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p237,GridPlus.atNode 237,GridPlus.atNode 238,NodePlus03.w45,CompactPlus0224.checked237,CompactPlus0224.small237,CompactPlus0224.nodes237,NodePlus03.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p238,GridPlus.atNode 238,GridPlus.atNode 239,NodePlus03.w46,CompactPlus0224.checked238,CompactPlus0224.small238,CompactPlus0224.nodes238,NodePlus03.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0224.p239,GridPlus.atNode 239,GridPlus.atNode 240,NodePlus03.w47,CompactPlus0224.checked239,CompactPlus0224.small239,CompactPlus0224.nodes239,NodePlus03.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p240,GridPlus.atNode 240,GridPlus.atNode 241,NodePlus03.w48,CompactPlus0240.checked240,CompactPlus0240.small240,CompactPlus0240.nodes240,NodePlus03.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p241,GridPlus.atNode 241,GridPlus.atNode 242,NodePlus03.w49,CompactPlus0240.checked241,CompactPlus0240.small241,CompactPlus0240.nodes241,NodePlus03.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p242,GridPlus.atNode 242,GridPlus.atNode 243,NodePlus03.w50,CompactPlus0240.checked242,CompactPlus0240.small242,CompactPlus0240.nodes242,NodePlus03.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p243,GridPlus.atNode 243,GridPlus.atNode 244,NodePlus03.w51,CompactPlus0240.checked243,CompactPlus0240.small243,CompactPlus0240.nodes243,NodePlus03.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p244,GridPlus.atNode 244,GridPlus.atNode 245,NodePlus03.w52,CompactPlus0240.checked244,CompactPlus0240.small244,CompactPlus0240.nodes244,NodePlus03.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p245,GridPlus.atNode 245,GridPlus.atNode 246,NodePlus03.w53,CompactPlus0240.checked245,CompactPlus0240.small245,CompactPlus0240.nodes245,NodePlus03.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p246,GridPlus.atNode 246,GridPlus.atNode 247,NodePlus03.w54,CompactPlus0240.checked246,CompactPlus0240.small246,CompactPlus0240.nodes246,NodePlus03.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p247,GridPlus.atNode 247,GridPlus.atNode 248,NodePlus03.w55,CompactPlus0240.checked247,CompactPlus0240.small247,CompactPlus0240.nodes247,NodePlus03.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p248,GridPlus.atNode 248,GridPlus.atNode 249,NodePlus03.w56,CompactPlus0240.checked248,CompactPlus0240.small248,CompactPlus0240.nodes248,NodePlus03.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p249,GridPlus.atNode 249,GridPlus.atNode 250,NodePlus03.w57,CompactPlus0240.checked249,CompactPlus0240.small249,CompactPlus0240.nodes249,NodePlus03.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p250,GridPlus.atNode 250,GridPlus.atNode 251,NodePlus03.w58,CompactPlus0240.checked250,CompactPlus0240.small250,CompactPlus0240.nodes250,NodePlus03.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p251,GridPlus.atNode 251,GridPlus.atNode 252,NodePlus03.w59,CompactPlus0240.checked251,CompactPlus0240.small251,CompactPlus0240.nodes251,NodePlus03.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p252,GridPlus.atNode 252,GridPlus.atNode 253,NodePlus03.w60,CompactPlus0240.checked252,CompactPlus0240.small252,CompactPlus0240.nodes252,NodePlus03.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p253,GridPlus.atNode 253,GridPlus.atNode 254,NodePlus03.w61,CompactPlus0240.checked253,CompactPlus0240.small253,CompactPlus0240.nodes253,NodePlus03.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p254,GridPlus.atNode 254,GridPlus.atNode 255,NodePlus03.w62,CompactPlus0240.checked254,CompactPlus0240.small254,CompactPlus0240.nodes254,NodePlus03.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0240.p255,GridPlus.atNode 255,GridPlus.atNode 256,NodePlus03.w63,CompactPlus0240.checked255,CompactPlus0240.small255,CompactPlus0240.nodes255,NodePlus03.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (192+j) ∧
    (atRow j).right=GridPlus.atNode (192+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus03
