import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0192
import SolitonClassification.Rotating.ResetPackedMinus0208
import SolitonClassification.Rotating.ResetPackedMinus0224
import SolitonClassification.Rotating.ResetPackedMinus0240
namespace SolitonClassification.Rotating.DyadicReset.TileMinus03
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p192,GridMinus.atNode 192,GridMinus.atNode 193,NodeMinus03.w0,CompactMinus0192.checked192,CompactMinus0192.small192,CompactMinus0192.nodes192,NodeMinus03.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p193,GridMinus.atNode 193,GridMinus.atNode 194,NodeMinus03.w1,CompactMinus0192.checked193,CompactMinus0192.small193,CompactMinus0192.nodes193,NodeMinus03.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p194,GridMinus.atNode 194,GridMinus.atNode 195,NodeMinus03.w2,CompactMinus0192.checked194,CompactMinus0192.small194,CompactMinus0192.nodes194,NodeMinus03.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p195,GridMinus.atNode 195,GridMinus.atNode 196,NodeMinus03.w3,CompactMinus0192.checked195,CompactMinus0192.small195,CompactMinus0192.nodes195,NodeMinus03.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p196,GridMinus.atNode 196,GridMinus.atNode 197,NodeMinus03.w4,CompactMinus0192.checked196,CompactMinus0192.small196,CompactMinus0192.nodes196,NodeMinus03.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p197,GridMinus.atNode 197,GridMinus.atNode 198,NodeMinus03.w5,CompactMinus0192.checked197,CompactMinus0192.small197,CompactMinus0192.nodes197,NodeMinus03.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p198,GridMinus.atNode 198,GridMinus.atNode 199,NodeMinus03.w6,CompactMinus0192.checked198,CompactMinus0192.small198,CompactMinus0192.nodes198,NodeMinus03.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p199,GridMinus.atNode 199,GridMinus.atNode 200,NodeMinus03.w7,CompactMinus0192.checked199,CompactMinus0192.small199,CompactMinus0192.nodes199,NodeMinus03.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p200,GridMinus.atNode 200,GridMinus.atNode 201,NodeMinus03.w8,CompactMinus0192.checked200,CompactMinus0192.small200,CompactMinus0192.nodes200,NodeMinus03.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p201,GridMinus.atNode 201,GridMinus.atNode 202,NodeMinus03.w9,CompactMinus0192.checked201,CompactMinus0192.small201,CompactMinus0192.nodes201,NodeMinus03.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p202,GridMinus.atNode 202,GridMinus.atNode 203,NodeMinus03.w10,CompactMinus0192.checked202,CompactMinus0192.small202,CompactMinus0192.nodes202,NodeMinus03.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p203,GridMinus.atNode 203,GridMinus.atNode 204,NodeMinus03.w11,CompactMinus0192.checked203,CompactMinus0192.small203,CompactMinus0192.nodes203,NodeMinus03.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p204,GridMinus.atNode 204,GridMinus.atNode 205,NodeMinus03.w12,CompactMinus0192.checked204,CompactMinus0192.small204,CompactMinus0192.nodes204,NodeMinus03.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p205,GridMinus.atNode 205,GridMinus.atNode 206,NodeMinus03.w13,CompactMinus0192.checked205,CompactMinus0192.small205,CompactMinus0192.nodes205,NodeMinus03.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p206,GridMinus.atNode 206,GridMinus.atNode 207,NodeMinus03.w14,CompactMinus0192.checked206,CompactMinus0192.small206,CompactMinus0192.nodes206,NodeMinus03.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0192.p207,GridMinus.atNode 207,GridMinus.atNode 208,NodeMinus03.w15,CompactMinus0192.checked207,CompactMinus0192.small207,CompactMinus0192.nodes207,NodeMinus03.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p208,GridMinus.atNode 208,GridMinus.atNode 209,NodeMinus03.w16,CompactMinus0208.checked208,CompactMinus0208.small208,CompactMinus0208.nodes208,NodeMinus03.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p209,GridMinus.atNode 209,GridMinus.atNode 210,NodeMinus03.w17,CompactMinus0208.checked209,CompactMinus0208.small209,CompactMinus0208.nodes209,NodeMinus03.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p210,GridMinus.atNode 210,GridMinus.atNode 211,NodeMinus03.w18,CompactMinus0208.checked210,CompactMinus0208.small210,CompactMinus0208.nodes210,NodeMinus03.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p211,GridMinus.atNode 211,GridMinus.atNode 212,NodeMinus03.w19,CompactMinus0208.checked211,CompactMinus0208.small211,CompactMinus0208.nodes211,NodeMinus03.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p212,GridMinus.atNode 212,GridMinus.atNode 213,NodeMinus03.w20,CompactMinus0208.checked212,CompactMinus0208.small212,CompactMinus0208.nodes212,NodeMinus03.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p213,GridMinus.atNode 213,GridMinus.atNode 214,NodeMinus03.w21,CompactMinus0208.checked213,CompactMinus0208.small213,CompactMinus0208.nodes213,NodeMinus03.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p214,GridMinus.atNode 214,GridMinus.atNode 215,NodeMinus03.w22,CompactMinus0208.checked214,CompactMinus0208.small214,CompactMinus0208.nodes214,NodeMinus03.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p215,GridMinus.atNode 215,GridMinus.atNode 216,NodeMinus03.w23,CompactMinus0208.checked215,CompactMinus0208.small215,CompactMinus0208.nodes215,NodeMinus03.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p216,GridMinus.atNode 216,GridMinus.atNode 217,NodeMinus03.w24,CompactMinus0208.checked216,CompactMinus0208.small216,CompactMinus0208.nodes216,NodeMinus03.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p217,GridMinus.atNode 217,GridMinus.atNode 218,NodeMinus03.w25,CompactMinus0208.checked217,CompactMinus0208.small217,CompactMinus0208.nodes217,NodeMinus03.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p218,GridMinus.atNode 218,GridMinus.atNode 219,NodeMinus03.w26,CompactMinus0208.checked218,CompactMinus0208.small218,CompactMinus0208.nodes218,NodeMinus03.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p219,GridMinus.atNode 219,GridMinus.atNode 220,NodeMinus03.w27,CompactMinus0208.checked219,CompactMinus0208.small219,CompactMinus0208.nodes219,NodeMinus03.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p220,GridMinus.atNode 220,GridMinus.atNode 221,NodeMinus03.w28,CompactMinus0208.checked220,CompactMinus0208.small220,CompactMinus0208.nodes220,NodeMinus03.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p221,GridMinus.atNode 221,GridMinus.atNode 222,NodeMinus03.w29,CompactMinus0208.checked221,CompactMinus0208.small221,CompactMinus0208.nodes221,NodeMinus03.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p222,GridMinus.atNode 222,GridMinus.atNode 223,NodeMinus03.w30,CompactMinus0208.checked222,CompactMinus0208.small222,CompactMinus0208.nodes222,NodeMinus03.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0208.p223,GridMinus.atNode 223,GridMinus.atNode 224,NodeMinus03.w31,CompactMinus0208.checked223,CompactMinus0208.small223,CompactMinus0208.nodes223,NodeMinus03.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p224,GridMinus.atNode 224,GridMinus.atNode 225,NodeMinus03.w32,CompactMinus0224.checked224,CompactMinus0224.small224,CompactMinus0224.nodes224,NodeMinus03.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p225,GridMinus.atNode 225,GridMinus.atNode 226,NodeMinus03.w33,CompactMinus0224.checked225,CompactMinus0224.small225,CompactMinus0224.nodes225,NodeMinus03.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p226,GridMinus.atNode 226,GridMinus.atNode 227,NodeMinus03.w34,CompactMinus0224.checked226,CompactMinus0224.small226,CompactMinus0224.nodes226,NodeMinus03.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p227,GridMinus.atNode 227,GridMinus.atNode 228,NodeMinus03.w35,CompactMinus0224.checked227,CompactMinus0224.small227,CompactMinus0224.nodes227,NodeMinus03.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p228,GridMinus.atNode 228,GridMinus.atNode 229,NodeMinus03.w36,CompactMinus0224.checked228,CompactMinus0224.small228,CompactMinus0224.nodes228,NodeMinus03.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p229,GridMinus.atNode 229,GridMinus.atNode 230,NodeMinus03.w37,CompactMinus0224.checked229,CompactMinus0224.small229,CompactMinus0224.nodes229,NodeMinus03.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p230,GridMinus.atNode 230,GridMinus.atNode 231,NodeMinus03.w38,CompactMinus0224.checked230,CompactMinus0224.small230,CompactMinus0224.nodes230,NodeMinus03.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p231,GridMinus.atNode 231,GridMinus.atNode 232,NodeMinus03.w39,CompactMinus0224.checked231,CompactMinus0224.small231,CompactMinus0224.nodes231,NodeMinus03.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p232,GridMinus.atNode 232,GridMinus.atNode 233,NodeMinus03.w40,CompactMinus0224.checked232,CompactMinus0224.small232,CompactMinus0224.nodes232,NodeMinus03.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p233,GridMinus.atNode 233,GridMinus.atNode 234,NodeMinus03.w41,CompactMinus0224.checked233,CompactMinus0224.small233,CompactMinus0224.nodes233,NodeMinus03.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p234,GridMinus.atNode 234,GridMinus.atNode 235,NodeMinus03.w42,CompactMinus0224.checked234,CompactMinus0224.small234,CompactMinus0224.nodes234,NodeMinus03.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p235,GridMinus.atNode 235,GridMinus.atNode 236,NodeMinus03.w43,CompactMinus0224.checked235,CompactMinus0224.small235,CompactMinus0224.nodes235,NodeMinus03.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p236,GridMinus.atNode 236,GridMinus.atNode 237,NodeMinus03.w44,CompactMinus0224.checked236,CompactMinus0224.small236,CompactMinus0224.nodes236,NodeMinus03.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p237,GridMinus.atNode 237,GridMinus.atNode 238,NodeMinus03.w45,CompactMinus0224.checked237,CompactMinus0224.small237,CompactMinus0224.nodes237,NodeMinus03.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p238,GridMinus.atNode 238,GridMinus.atNode 239,NodeMinus03.w46,CompactMinus0224.checked238,CompactMinus0224.small238,CompactMinus0224.nodes238,NodeMinus03.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0224.p239,GridMinus.atNode 239,GridMinus.atNode 240,NodeMinus03.w47,CompactMinus0224.checked239,CompactMinus0224.small239,CompactMinus0224.nodes239,NodeMinus03.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p240,GridMinus.atNode 240,GridMinus.atNode 241,NodeMinus03.w48,CompactMinus0240.checked240,CompactMinus0240.small240,CompactMinus0240.nodes240,NodeMinus03.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p241,GridMinus.atNode 241,GridMinus.atNode 242,NodeMinus03.w49,CompactMinus0240.checked241,CompactMinus0240.small241,CompactMinus0240.nodes241,NodeMinus03.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p242,GridMinus.atNode 242,GridMinus.atNode 243,NodeMinus03.w50,CompactMinus0240.checked242,CompactMinus0240.small242,CompactMinus0240.nodes242,NodeMinus03.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p243,GridMinus.atNode 243,GridMinus.atNode 244,NodeMinus03.w51,CompactMinus0240.checked243,CompactMinus0240.small243,CompactMinus0240.nodes243,NodeMinus03.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p244,GridMinus.atNode 244,GridMinus.atNode 245,NodeMinus03.w52,CompactMinus0240.checked244,CompactMinus0240.small244,CompactMinus0240.nodes244,NodeMinus03.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p245,GridMinus.atNode 245,GridMinus.atNode 246,NodeMinus03.w53,CompactMinus0240.checked245,CompactMinus0240.small245,CompactMinus0240.nodes245,NodeMinus03.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p246,GridMinus.atNode 246,GridMinus.atNode 247,NodeMinus03.w54,CompactMinus0240.checked246,CompactMinus0240.small246,CompactMinus0240.nodes246,NodeMinus03.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p247,GridMinus.atNode 247,GridMinus.atNode 248,NodeMinus03.w55,CompactMinus0240.checked247,CompactMinus0240.small247,CompactMinus0240.nodes247,NodeMinus03.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p248,GridMinus.atNode 248,GridMinus.atNode 249,NodeMinus03.w56,CompactMinus0240.checked248,CompactMinus0240.small248,CompactMinus0240.nodes248,NodeMinus03.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p249,GridMinus.atNode 249,GridMinus.atNode 250,NodeMinus03.w57,CompactMinus0240.checked249,CompactMinus0240.small249,CompactMinus0240.nodes249,NodeMinus03.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p250,GridMinus.atNode 250,GridMinus.atNode 251,NodeMinus03.w58,CompactMinus0240.checked250,CompactMinus0240.small250,CompactMinus0240.nodes250,NodeMinus03.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p251,GridMinus.atNode 251,GridMinus.atNode 252,NodeMinus03.w59,CompactMinus0240.checked251,CompactMinus0240.small251,CompactMinus0240.nodes251,NodeMinus03.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p252,GridMinus.atNode 252,GridMinus.atNode 253,NodeMinus03.w60,CompactMinus0240.checked252,CompactMinus0240.small252,CompactMinus0240.nodes252,NodeMinus03.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p253,GridMinus.atNode 253,GridMinus.atNode 254,NodeMinus03.w61,CompactMinus0240.checked253,CompactMinus0240.small253,CompactMinus0240.nodes253,NodeMinus03.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p254,GridMinus.atNode 254,GridMinus.atNode 255,NodeMinus03.w62,CompactMinus0240.checked254,CompactMinus0240.small254,CompactMinus0240.nodes254,NodeMinus03.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0240.p255,GridMinus.atNode 255,GridMinus.atNode 256,NodeMinus03.w63,CompactMinus0240.checked255,CompactMinus0240.small255,CompactMinus0240.nodes255,NodeMinus03.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (192+j) ∧
    (atRow j).right=GridMinus.atNode (192+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus03
