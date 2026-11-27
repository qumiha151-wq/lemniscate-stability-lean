import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2048
import SolitonClassification.Rotating.ResetPackedPlus2064
import SolitonClassification.Rotating.ResetPackedPlus2080
import SolitonClassification.Rotating.ResetPackedPlus2096
namespace SolitonClassification.Rotating.DyadicReset.TilePlus32
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2048,GridPlus.atNode 2048,GridPlus.atNode 2049,NodePlus32.w0,CompactPlus2048.checked2048,CompactPlus2048.small2048,CompactPlus2048.nodes2048,NodePlus32.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2049,GridPlus.atNode 2049,GridPlus.atNode 2050,NodePlus32.w1,CompactPlus2048.checked2049,CompactPlus2048.small2049,CompactPlus2048.nodes2049,NodePlus32.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2050,GridPlus.atNode 2050,GridPlus.atNode 2051,NodePlus32.w2,CompactPlus2048.checked2050,CompactPlus2048.small2050,CompactPlus2048.nodes2050,NodePlus32.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2051,GridPlus.atNode 2051,GridPlus.atNode 2052,NodePlus32.w3,CompactPlus2048.checked2051,CompactPlus2048.small2051,CompactPlus2048.nodes2051,NodePlus32.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2052,GridPlus.atNode 2052,GridPlus.atNode 2053,NodePlus32.w4,CompactPlus2048.checked2052,CompactPlus2048.small2052,CompactPlus2048.nodes2052,NodePlus32.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2053,GridPlus.atNode 2053,GridPlus.atNode 2054,NodePlus32.w5,CompactPlus2048.checked2053,CompactPlus2048.small2053,CompactPlus2048.nodes2053,NodePlus32.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2054,GridPlus.atNode 2054,GridPlus.atNode 2055,NodePlus32.w6,CompactPlus2048.checked2054,CompactPlus2048.small2054,CompactPlus2048.nodes2054,NodePlus32.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2055,GridPlus.atNode 2055,GridPlus.atNode 2056,NodePlus32.w7,CompactPlus2048.checked2055,CompactPlus2048.small2055,CompactPlus2048.nodes2055,NodePlus32.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2056,GridPlus.atNode 2056,GridPlus.atNode 2057,NodePlus32.w8,CompactPlus2048.checked2056,CompactPlus2048.small2056,CompactPlus2048.nodes2056,NodePlus32.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2057,GridPlus.atNode 2057,GridPlus.atNode 2058,NodePlus32.w9,CompactPlus2048.checked2057,CompactPlus2048.small2057,CompactPlus2048.nodes2057,NodePlus32.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2058,GridPlus.atNode 2058,GridPlus.atNode 2059,NodePlus32.w10,CompactPlus2048.checked2058,CompactPlus2048.small2058,CompactPlus2048.nodes2058,NodePlus32.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2059,GridPlus.atNode 2059,GridPlus.atNode 2060,NodePlus32.w11,CompactPlus2048.checked2059,CompactPlus2048.small2059,CompactPlus2048.nodes2059,NodePlus32.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2060,GridPlus.atNode 2060,GridPlus.atNode 2061,NodePlus32.w12,CompactPlus2048.checked2060,CompactPlus2048.small2060,CompactPlus2048.nodes2060,NodePlus32.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2061,GridPlus.atNode 2061,GridPlus.atNode 2062,NodePlus32.w13,CompactPlus2048.checked2061,CompactPlus2048.small2061,CompactPlus2048.nodes2061,NodePlus32.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2062,GridPlus.atNode 2062,GridPlus.atNode 2063,NodePlus32.w14,CompactPlus2048.checked2062,CompactPlus2048.small2062,CompactPlus2048.nodes2062,NodePlus32.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2048.p2063,GridPlus.atNode 2063,GridPlus.atNode 2064,NodePlus32.w15,CompactPlus2048.checked2063,CompactPlus2048.small2063,CompactPlus2048.nodes2063,NodePlus32.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2064,GridPlus.atNode 2064,GridPlus.atNode 2065,NodePlus32.w16,CompactPlus2064.checked2064,CompactPlus2064.small2064,CompactPlus2064.nodes2064,NodePlus32.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2065,GridPlus.atNode 2065,GridPlus.atNode 2066,NodePlus32.w17,CompactPlus2064.checked2065,CompactPlus2064.small2065,CompactPlus2064.nodes2065,NodePlus32.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2066,GridPlus.atNode 2066,GridPlus.atNode 2067,NodePlus32.w18,CompactPlus2064.checked2066,CompactPlus2064.small2066,CompactPlus2064.nodes2066,NodePlus32.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2067,GridPlus.atNode 2067,GridPlus.atNode 2068,NodePlus32.w19,CompactPlus2064.checked2067,CompactPlus2064.small2067,CompactPlus2064.nodes2067,NodePlus32.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2068,GridPlus.atNode 2068,GridPlus.atNode 2069,NodePlus32.w20,CompactPlus2064.checked2068,CompactPlus2064.small2068,CompactPlus2064.nodes2068,NodePlus32.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2069,GridPlus.atNode 2069,GridPlus.atNode 2070,NodePlus32.w21,CompactPlus2064.checked2069,CompactPlus2064.small2069,CompactPlus2064.nodes2069,NodePlus32.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2070,GridPlus.atNode 2070,GridPlus.atNode 2071,NodePlus32.w22,CompactPlus2064.checked2070,CompactPlus2064.small2070,CompactPlus2064.nodes2070,NodePlus32.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2071,GridPlus.atNode 2071,GridPlus.atNode 2072,NodePlus32.w23,CompactPlus2064.checked2071,CompactPlus2064.small2071,CompactPlus2064.nodes2071,NodePlus32.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2072,GridPlus.atNode 2072,GridPlus.atNode 2073,NodePlus32.w24,CompactPlus2064.checked2072,CompactPlus2064.small2072,CompactPlus2064.nodes2072,NodePlus32.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2073,GridPlus.atNode 2073,GridPlus.atNode 2074,NodePlus32.w25,CompactPlus2064.checked2073,CompactPlus2064.small2073,CompactPlus2064.nodes2073,NodePlus32.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2074,GridPlus.atNode 2074,GridPlus.atNode 2075,NodePlus32.w26,CompactPlus2064.checked2074,CompactPlus2064.small2074,CompactPlus2064.nodes2074,NodePlus32.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2075,GridPlus.atNode 2075,GridPlus.atNode 2076,NodePlus32.w27,CompactPlus2064.checked2075,CompactPlus2064.small2075,CompactPlus2064.nodes2075,NodePlus32.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2076,GridPlus.atNode 2076,GridPlus.atNode 2077,NodePlus32.w28,CompactPlus2064.checked2076,CompactPlus2064.small2076,CompactPlus2064.nodes2076,NodePlus32.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2077,GridPlus.atNode 2077,GridPlus.atNode 2078,NodePlus32.w29,CompactPlus2064.checked2077,CompactPlus2064.small2077,CompactPlus2064.nodes2077,NodePlus32.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2078,GridPlus.atNode 2078,GridPlus.atNode 2079,NodePlus32.w30,CompactPlus2064.checked2078,CompactPlus2064.small2078,CompactPlus2064.nodes2078,NodePlus32.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2064.p2079,GridPlus.atNode 2079,GridPlus.atNode 2080,NodePlus32.w31,CompactPlus2064.checked2079,CompactPlus2064.small2079,CompactPlus2064.nodes2079,NodePlus32.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2080,GridPlus.atNode 2080,GridPlus.atNode 2081,NodePlus32.w32,CompactPlus2080.checked2080,CompactPlus2080.small2080,CompactPlus2080.nodes2080,NodePlus32.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2081,GridPlus.atNode 2081,GridPlus.atNode 2082,NodePlus32.w33,CompactPlus2080.checked2081,CompactPlus2080.small2081,CompactPlus2080.nodes2081,NodePlus32.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2082,GridPlus.atNode 2082,GridPlus.atNode 2083,NodePlus32.w34,CompactPlus2080.checked2082,CompactPlus2080.small2082,CompactPlus2080.nodes2082,NodePlus32.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2083,GridPlus.atNode 2083,GridPlus.atNode 2084,NodePlus32.w35,CompactPlus2080.checked2083,CompactPlus2080.small2083,CompactPlus2080.nodes2083,NodePlus32.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2084,GridPlus.atNode 2084,GridPlus.atNode 2085,NodePlus32.w36,CompactPlus2080.checked2084,CompactPlus2080.small2084,CompactPlus2080.nodes2084,NodePlus32.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2085,GridPlus.atNode 2085,GridPlus.atNode 2086,NodePlus32.w37,CompactPlus2080.checked2085,CompactPlus2080.small2085,CompactPlus2080.nodes2085,NodePlus32.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2086,GridPlus.atNode 2086,GridPlus.atNode 2087,NodePlus32.w38,CompactPlus2080.checked2086,CompactPlus2080.small2086,CompactPlus2080.nodes2086,NodePlus32.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2087,GridPlus.atNode 2087,GridPlus.atNode 2088,NodePlus32.w39,CompactPlus2080.checked2087,CompactPlus2080.small2087,CompactPlus2080.nodes2087,NodePlus32.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2088,GridPlus.atNode 2088,GridPlus.atNode 2089,NodePlus32.w40,CompactPlus2080.checked2088,CompactPlus2080.small2088,CompactPlus2080.nodes2088,NodePlus32.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2089,GridPlus.atNode 2089,GridPlus.atNode 2090,NodePlus32.w41,CompactPlus2080.checked2089,CompactPlus2080.small2089,CompactPlus2080.nodes2089,NodePlus32.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2090,GridPlus.atNode 2090,GridPlus.atNode 2091,NodePlus32.w42,CompactPlus2080.checked2090,CompactPlus2080.small2090,CompactPlus2080.nodes2090,NodePlus32.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2091,GridPlus.atNode 2091,GridPlus.atNode 2092,NodePlus32.w43,CompactPlus2080.checked2091,CompactPlus2080.small2091,CompactPlus2080.nodes2091,NodePlus32.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2092,GridPlus.atNode 2092,GridPlus.atNode 2093,NodePlus32.w44,CompactPlus2080.checked2092,CompactPlus2080.small2092,CompactPlus2080.nodes2092,NodePlus32.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2093,GridPlus.atNode 2093,GridPlus.atNode 2094,NodePlus32.w45,CompactPlus2080.checked2093,CompactPlus2080.small2093,CompactPlus2080.nodes2093,NodePlus32.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2094,GridPlus.atNode 2094,GridPlus.atNode 2095,NodePlus32.w46,CompactPlus2080.checked2094,CompactPlus2080.small2094,CompactPlus2080.nodes2094,NodePlus32.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2080.p2095,GridPlus.atNode 2095,GridPlus.atNode 2096,NodePlus32.w47,CompactPlus2080.checked2095,CompactPlus2080.small2095,CompactPlus2080.nodes2095,NodePlus32.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2096,GridPlus.atNode 2096,GridPlus.atNode 2097,NodePlus32.w48,CompactPlus2096.checked2096,CompactPlus2096.small2096,CompactPlus2096.nodes2096,NodePlus32.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2097,GridPlus.atNode 2097,GridPlus.atNode 2098,NodePlus32.w49,CompactPlus2096.checked2097,CompactPlus2096.small2097,CompactPlus2096.nodes2097,NodePlus32.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2098,GridPlus.atNode 2098,GridPlus.atNode 2099,NodePlus32.w50,CompactPlus2096.checked2098,CompactPlus2096.small2098,CompactPlus2096.nodes2098,NodePlus32.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2099,GridPlus.atNode 2099,GridPlus.atNode 2100,NodePlus32.w51,CompactPlus2096.checked2099,CompactPlus2096.small2099,CompactPlus2096.nodes2099,NodePlus32.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2100,GridPlus.atNode 2100,GridPlus.atNode 2101,NodePlus32.w52,CompactPlus2096.checked2100,CompactPlus2096.small2100,CompactPlus2096.nodes2100,NodePlus32.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2101,GridPlus.atNode 2101,GridPlus.atNode 2102,NodePlus32.w53,CompactPlus2096.checked2101,CompactPlus2096.small2101,CompactPlus2096.nodes2101,NodePlus32.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2102,GridPlus.atNode 2102,GridPlus.atNode 2103,NodePlus32.w54,CompactPlus2096.checked2102,CompactPlus2096.small2102,CompactPlus2096.nodes2102,NodePlus32.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2103,GridPlus.atNode 2103,GridPlus.atNode 2104,NodePlus32.w55,CompactPlus2096.checked2103,CompactPlus2096.small2103,CompactPlus2096.nodes2103,NodePlus32.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2104,GridPlus.atNode 2104,GridPlus.atNode 2105,NodePlus32.w56,CompactPlus2096.checked2104,CompactPlus2096.small2104,CompactPlus2096.nodes2104,NodePlus32.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2105,GridPlus.atNode 2105,GridPlus.atNode 2106,NodePlus32.w57,CompactPlus2096.checked2105,CompactPlus2096.small2105,CompactPlus2096.nodes2105,NodePlus32.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2106,GridPlus.atNode 2106,GridPlus.atNode 2107,NodePlus32.w58,CompactPlus2096.checked2106,CompactPlus2096.small2106,CompactPlus2096.nodes2106,NodePlus32.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2107,GridPlus.atNode 2107,GridPlus.atNode 2108,NodePlus32.w59,CompactPlus2096.checked2107,CompactPlus2096.small2107,CompactPlus2096.nodes2107,NodePlus32.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2108,GridPlus.atNode 2108,GridPlus.atNode 2109,NodePlus32.w60,CompactPlus2096.checked2108,CompactPlus2096.small2108,CompactPlus2096.nodes2108,NodePlus32.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2109,GridPlus.atNode 2109,GridPlus.atNode 2110,NodePlus32.w61,CompactPlus2096.checked2109,CompactPlus2096.small2109,CompactPlus2096.nodes2109,NodePlus32.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2110,GridPlus.atNode 2110,GridPlus.atNode 2111,NodePlus32.w62,CompactPlus2096.checked2110,CompactPlus2096.small2110,CompactPlus2096.nodes2110,NodePlus32.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2096.p2111,GridPlus.atNode 2111,GridPlus.atNode 2112,NodePlus32.w63,CompactPlus2096.checked2111,CompactPlus2096.small2111,CompactPlus2096.nodes2111,NodePlus32.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2048+j) ∧
    (atRow j).right=GridPlus.atNode (2048+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus32
