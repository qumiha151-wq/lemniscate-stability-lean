import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2112
import SolitonClassification.Rotating.ResetPackedPlus2128
import SolitonClassification.Rotating.ResetPackedPlus2144
import SolitonClassification.Rotating.ResetPackedPlus2160
namespace SolitonClassification.Rotating.DyadicReset.TilePlus33
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2112,GridPlus.atNode 2112,GridPlus.atNode 2113,NodePlus33.w0,CompactPlus2112.checked2112,CompactPlus2112.small2112,CompactPlus2112.nodes2112,NodePlus33.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2113,GridPlus.atNode 2113,GridPlus.atNode 2114,NodePlus33.w1,CompactPlus2112.checked2113,CompactPlus2112.small2113,CompactPlus2112.nodes2113,NodePlus33.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2114,GridPlus.atNode 2114,GridPlus.atNode 2115,NodePlus33.w2,CompactPlus2112.checked2114,CompactPlus2112.small2114,CompactPlus2112.nodes2114,NodePlus33.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2115,GridPlus.atNode 2115,GridPlus.atNode 2116,NodePlus33.w3,CompactPlus2112.checked2115,CompactPlus2112.small2115,CompactPlus2112.nodes2115,NodePlus33.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2116,GridPlus.atNode 2116,GridPlus.atNode 2117,NodePlus33.w4,CompactPlus2112.checked2116,CompactPlus2112.small2116,CompactPlus2112.nodes2116,NodePlus33.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2117,GridPlus.atNode 2117,GridPlus.atNode 2118,NodePlus33.w5,CompactPlus2112.checked2117,CompactPlus2112.small2117,CompactPlus2112.nodes2117,NodePlus33.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2118,GridPlus.atNode 2118,GridPlus.atNode 2119,NodePlus33.w6,CompactPlus2112.checked2118,CompactPlus2112.small2118,CompactPlus2112.nodes2118,NodePlus33.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2119,GridPlus.atNode 2119,GridPlus.atNode 2120,NodePlus33.w7,CompactPlus2112.checked2119,CompactPlus2112.small2119,CompactPlus2112.nodes2119,NodePlus33.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2120,GridPlus.atNode 2120,GridPlus.atNode 2121,NodePlus33.w8,CompactPlus2112.checked2120,CompactPlus2112.small2120,CompactPlus2112.nodes2120,NodePlus33.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2121,GridPlus.atNode 2121,GridPlus.atNode 2122,NodePlus33.w9,CompactPlus2112.checked2121,CompactPlus2112.small2121,CompactPlus2112.nodes2121,NodePlus33.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2122,GridPlus.atNode 2122,GridPlus.atNode 2123,NodePlus33.w10,CompactPlus2112.checked2122,CompactPlus2112.small2122,CompactPlus2112.nodes2122,NodePlus33.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2123,GridPlus.atNode 2123,GridPlus.atNode 2124,NodePlus33.w11,CompactPlus2112.checked2123,CompactPlus2112.small2123,CompactPlus2112.nodes2123,NodePlus33.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2124,GridPlus.atNode 2124,GridPlus.atNode 2125,NodePlus33.w12,CompactPlus2112.checked2124,CompactPlus2112.small2124,CompactPlus2112.nodes2124,NodePlus33.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2125,GridPlus.atNode 2125,GridPlus.atNode 2126,NodePlus33.w13,CompactPlus2112.checked2125,CompactPlus2112.small2125,CompactPlus2112.nodes2125,NodePlus33.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2126,GridPlus.atNode 2126,GridPlus.atNode 2127,NodePlus33.w14,CompactPlus2112.checked2126,CompactPlus2112.small2126,CompactPlus2112.nodes2126,NodePlus33.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2112.p2127,GridPlus.atNode 2127,GridPlus.atNode 2128,NodePlus33.w15,CompactPlus2112.checked2127,CompactPlus2112.small2127,CompactPlus2112.nodes2127,NodePlus33.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2128,GridPlus.atNode 2128,GridPlus.atNode 2129,NodePlus33.w16,CompactPlus2128.checked2128,CompactPlus2128.small2128,CompactPlus2128.nodes2128,NodePlus33.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2129,GridPlus.atNode 2129,GridPlus.atNode 2130,NodePlus33.w17,CompactPlus2128.checked2129,CompactPlus2128.small2129,CompactPlus2128.nodes2129,NodePlus33.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2130,GridPlus.atNode 2130,GridPlus.atNode 2131,NodePlus33.w18,CompactPlus2128.checked2130,CompactPlus2128.small2130,CompactPlus2128.nodes2130,NodePlus33.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2131,GridPlus.atNode 2131,GridPlus.atNode 2132,NodePlus33.w19,CompactPlus2128.checked2131,CompactPlus2128.small2131,CompactPlus2128.nodes2131,NodePlus33.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2132,GridPlus.atNode 2132,GridPlus.atNode 2133,NodePlus33.w20,CompactPlus2128.checked2132,CompactPlus2128.small2132,CompactPlus2128.nodes2132,NodePlus33.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2133,GridPlus.atNode 2133,GridPlus.atNode 2134,NodePlus33.w21,CompactPlus2128.checked2133,CompactPlus2128.small2133,CompactPlus2128.nodes2133,NodePlus33.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2134,GridPlus.atNode 2134,GridPlus.atNode 2135,NodePlus33.w22,CompactPlus2128.checked2134,CompactPlus2128.small2134,CompactPlus2128.nodes2134,NodePlus33.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2135,GridPlus.atNode 2135,GridPlus.atNode 2136,NodePlus33.w23,CompactPlus2128.checked2135,CompactPlus2128.small2135,CompactPlus2128.nodes2135,NodePlus33.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2136,GridPlus.atNode 2136,GridPlus.atNode 2137,NodePlus33.w24,CompactPlus2128.checked2136,CompactPlus2128.small2136,CompactPlus2128.nodes2136,NodePlus33.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2137,GridPlus.atNode 2137,GridPlus.atNode 2138,NodePlus33.w25,CompactPlus2128.checked2137,CompactPlus2128.small2137,CompactPlus2128.nodes2137,NodePlus33.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2138,GridPlus.atNode 2138,GridPlus.atNode 2139,NodePlus33.w26,CompactPlus2128.checked2138,CompactPlus2128.small2138,CompactPlus2128.nodes2138,NodePlus33.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2139,GridPlus.atNode 2139,GridPlus.atNode 2140,NodePlus33.w27,CompactPlus2128.checked2139,CompactPlus2128.small2139,CompactPlus2128.nodes2139,NodePlus33.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2140,GridPlus.atNode 2140,GridPlus.atNode 2141,NodePlus33.w28,CompactPlus2128.checked2140,CompactPlus2128.small2140,CompactPlus2128.nodes2140,NodePlus33.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2141,GridPlus.atNode 2141,GridPlus.atNode 2142,NodePlus33.w29,CompactPlus2128.checked2141,CompactPlus2128.small2141,CompactPlus2128.nodes2141,NodePlus33.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2142,GridPlus.atNode 2142,GridPlus.atNode 2143,NodePlus33.w30,CompactPlus2128.checked2142,CompactPlus2128.small2142,CompactPlus2128.nodes2142,NodePlus33.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2128.p2143,GridPlus.atNode 2143,GridPlus.atNode 2144,NodePlus33.w31,CompactPlus2128.checked2143,CompactPlus2128.small2143,CompactPlus2128.nodes2143,NodePlus33.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2144,GridPlus.atNode 2144,GridPlus.atNode 2145,NodePlus33.w32,CompactPlus2144.checked2144,CompactPlus2144.small2144,CompactPlus2144.nodes2144,NodePlus33.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2145,GridPlus.atNode 2145,GridPlus.atNode 2146,NodePlus33.w33,CompactPlus2144.checked2145,CompactPlus2144.small2145,CompactPlus2144.nodes2145,NodePlus33.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2146,GridPlus.atNode 2146,GridPlus.atNode 2147,NodePlus33.w34,CompactPlus2144.checked2146,CompactPlus2144.small2146,CompactPlus2144.nodes2146,NodePlus33.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2147,GridPlus.atNode 2147,GridPlus.atNode 2148,NodePlus33.w35,CompactPlus2144.checked2147,CompactPlus2144.small2147,CompactPlus2144.nodes2147,NodePlus33.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2148,GridPlus.atNode 2148,GridPlus.atNode 2149,NodePlus33.w36,CompactPlus2144.checked2148,CompactPlus2144.small2148,CompactPlus2144.nodes2148,NodePlus33.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2149,GridPlus.atNode 2149,GridPlus.atNode 2150,NodePlus33.w37,CompactPlus2144.checked2149,CompactPlus2144.small2149,CompactPlus2144.nodes2149,NodePlus33.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2150,GridPlus.atNode 2150,GridPlus.atNode 2151,NodePlus33.w38,CompactPlus2144.checked2150,CompactPlus2144.small2150,CompactPlus2144.nodes2150,NodePlus33.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2151,GridPlus.atNode 2151,GridPlus.atNode 2152,NodePlus33.w39,CompactPlus2144.checked2151,CompactPlus2144.small2151,CompactPlus2144.nodes2151,NodePlus33.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2152,GridPlus.atNode 2152,GridPlus.atNode 2153,NodePlus33.w40,CompactPlus2144.checked2152,CompactPlus2144.small2152,CompactPlus2144.nodes2152,NodePlus33.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2153,GridPlus.atNode 2153,GridPlus.atNode 2154,NodePlus33.w41,CompactPlus2144.checked2153,CompactPlus2144.small2153,CompactPlus2144.nodes2153,NodePlus33.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2154,GridPlus.atNode 2154,GridPlus.atNode 2155,NodePlus33.w42,CompactPlus2144.checked2154,CompactPlus2144.small2154,CompactPlus2144.nodes2154,NodePlus33.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2155,GridPlus.atNode 2155,GridPlus.atNode 2156,NodePlus33.w43,CompactPlus2144.checked2155,CompactPlus2144.small2155,CompactPlus2144.nodes2155,NodePlus33.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2156,GridPlus.atNode 2156,GridPlus.atNode 2157,NodePlus33.w44,CompactPlus2144.checked2156,CompactPlus2144.small2156,CompactPlus2144.nodes2156,NodePlus33.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2157,GridPlus.atNode 2157,GridPlus.atNode 2158,NodePlus33.w45,CompactPlus2144.checked2157,CompactPlus2144.small2157,CompactPlus2144.nodes2157,NodePlus33.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2158,GridPlus.atNode 2158,GridPlus.atNode 2159,NodePlus33.w46,CompactPlus2144.checked2158,CompactPlus2144.small2158,CompactPlus2144.nodes2158,NodePlus33.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2144.p2159,GridPlus.atNode 2159,GridPlus.atNode 2160,NodePlus33.w47,CompactPlus2144.checked2159,CompactPlus2144.small2159,CompactPlus2144.nodes2159,NodePlus33.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2160,GridPlus.atNode 2160,GridPlus.atNode 2161,NodePlus33.w48,CompactPlus2160.checked2160,CompactPlus2160.small2160,CompactPlus2160.nodes2160,NodePlus33.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2161,GridPlus.atNode 2161,GridPlus.atNode 2162,NodePlus33.w49,CompactPlus2160.checked2161,CompactPlus2160.small2161,CompactPlus2160.nodes2161,NodePlus33.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2162,GridPlus.atNode 2162,GridPlus.atNode 2163,NodePlus33.w50,CompactPlus2160.checked2162,CompactPlus2160.small2162,CompactPlus2160.nodes2162,NodePlus33.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2163,GridPlus.atNode 2163,GridPlus.atNode 2164,NodePlus33.w51,CompactPlus2160.checked2163,CompactPlus2160.small2163,CompactPlus2160.nodes2163,NodePlus33.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2164,GridPlus.atNode 2164,GridPlus.atNode 2165,NodePlus33.w52,CompactPlus2160.checked2164,CompactPlus2160.small2164,CompactPlus2160.nodes2164,NodePlus33.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2165,GridPlus.atNode 2165,GridPlus.atNode 2166,NodePlus33.w53,CompactPlus2160.checked2165,CompactPlus2160.small2165,CompactPlus2160.nodes2165,NodePlus33.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2166,GridPlus.atNode 2166,GridPlus.atNode 2167,NodePlus33.w54,CompactPlus2160.checked2166,CompactPlus2160.small2166,CompactPlus2160.nodes2166,NodePlus33.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2167,GridPlus.atNode 2167,GridPlus.atNode 2168,NodePlus33.w55,CompactPlus2160.checked2167,CompactPlus2160.small2167,CompactPlus2160.nodes2167,NodePlus33.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2168,GridPlus.atNode 2168,GridPlus.atNode 2169,NodePlus33.w56,CompactPlus2160.checked2168,CompactPlus2160.small2168,CompactPlus2160.nodes2168,NodePlus33.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2169,GridPlus.atNode 2169,GridPlus.atNode 2170,NodePlus33.w57,CompactPlus2160.checked2169,CompactPlus2160.small2169,CompactPlus2160.nodes2169,NodePlus33.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2170,GridPlus.atNode 2170,GridPlus.atNode 2171,NodePlus33.w58,CompactPlus2160.checked2170,CompactPlus2160.small2170,CompactPlus2160.nodes2170,NodePlus33.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2171,GridPlus.atNode 2171,GridPlus.atNode 2172,NodePlus33.w59,CompactPlus2160.checked2171,CompactPlus2160.small2171,CompactPlus2160.nodes2171,NodePlus33.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2172,GridPlus.atNode 2172,GridPlus.atNode 2173,NodePlus33.w60,CompactPlus2160.checked2172,CompactPlus2160.small2172,CompactPlus2160.nodes2172,NodePlus33.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2173,GridPlus.atNode 2173,GridPlus.atNode 2174,NodePlus33.w61,CompactPlus2160.checked2173,CompactPlus2160.small2173,CompactPlus2160.nodes2173,NodePlus33.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2174,GridPlus.atNode 2174,GridPlus.atNode 2175,NodePlus33.w62,CompactPlus2160.checked2174,CompactPlus2160.small2174,CompactPlus2160.nodes2174,NodePlus33.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2160.p2175,GridPlus.atNode 2175,GridPlus.atNode 2176,NodePlus33.w63,CompactPlus2160.checked2175,CompactPlus2160.small2175,CompactPlus2160.nodes2175,NodePlus33.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2112+j) ∧
    (atRow j).right=GridPlus.atNode (2112+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus33
