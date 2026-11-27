import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1984
import SolitonClassification.Rotating.ResetPackedMinus2000
import SolitonClassification.Rotating.ResetPackedMinus2016
import SolitonClassification.Rotating.ResetPackedMinus2032
namespace SolitonClassification.Rotating.DyadicReset.TileMinus31
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1984,GridMinus.atNode 1984,GridMinus.atNode 1985,NodeMinus31.w0,CompactMinus1984.checked1984,CompactMinus1984.small1984,CompactMinus1984.nodes1984,NodeMinus31.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1985,GridMinus.atNode 1985,GridMinus.atNode 1986,NodeMinus31.w1,CompactMinus1984.checked1985,CompactMinus1984.small1985,CompactMinus1984.nodes1985,NodeMinus31.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1986,GridMinus.atNode 1986,GridMinus.atNode 1987,NodeMinus31.w2,CompactMinus1984.checked1986,CompactMinus1984.small1986,CompactMinus1984.nodes1986,NodeMinus31.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1987,GridMinus.atNode 1987,GridMinus.atNode 1988,NodeMinus31.w3,CompactMinus1984.checked1987,CompactMinus1984.small1987,CompactMinus1984.nodes1987,NodeMinus31.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1988,GridMinus.atNode 1988,GridMinus.atNode 1989,NodeMinus31.w4,CompactMinus1984.checked1988,CompactMinus1984.small1988,CompactMinus1984.nodes1988,NodeMinus31.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1989,GridMinus.atNode 1989,GridMinus.atNode 1990,NodeMinus31.w5,CompactMinus1984.checked1989,CompactMinus1984.small1989,CompactMinus1984.nodes1989,NodeMinus31.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1990,GridMinus.atNode 1990,GridMinus.atNode 1991,NodeMinus31.w6,CompactMinus1984.checked1990,CompactMinus1984.small1990,CompactMinus1984.nodes1990,NodeMinus31.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1991,GridMinus.atNode 1991,GridMinus.atNode 1992,NodeMinus31.w7,CompactMinus1984.checked1991,CompactMinus1984.small1991,CompactMinus1984.nodes1991,NodeMinus31.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1992,GridMinus.atNode 1992,GridMinus.atNode 1993,NodeMinus31.w8,CompactMinus1984.checked1992,CompactMinus1984.small1992,CompactMinus1984.nodes1992,NodeMinus31.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1993,GridMinus.atNode 1993,GridMinus.atNode 1994,NodeMinus31.w9,CompactMinus1984.checked1993,CompactMinus1984.small1993,CompactMinus1984.nodes1993,NodeMinus31.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1994,GridMinus.atNode 1994,GridMinus.atNode 1995,NodeMinus31.w10,CompactMinus1984.checked1994,CompactMinus1984.small1994,CompactMinus1984.nodes1994,NodeMinus31.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1995,GridMinus.atNode 1995,GridMinus.atNode 1996,NodeMinus31.w11,CompactMinus1984.checked1995,CompactMinus1984.small1995,CompactMinus1984.nodes1995,NodeMinus31.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1996,GridMinus.atNode 1996,GridMinus.atNode 1997,NodeMinus31.w12,CompactMinus1984.checked1996,CompactMinus1984.small1996,CompactMinus1984.nodes1996,NodeMinus31.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1997,GridMinus.atNode 1997,GridMinus.atNode 1998,NodeMinus31.w13,CompactMinus1984.checked1997,CompactMinus1984.small1997,CompactMinus1984.nodes1997,NodeMinus31.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1998,GridMinus.atNode 1998,GridMinus.atNode 1999,NodeMinus31.w14,CompactMinus1984.checked1998,CompactMinus1984.small1998,CompactMinus1984.nodes1998,NodeMinus31.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1984.p1999,GridMinus.atNode 1999,GridMinus.atNode 2000,NodeMinus31.w15,CompactMinus1984.checked1999,CompactMinus1984.small1999,CompactMinus1984.nodes1999,NodeMinus31.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2000,GridMinus.atNode 2000,GridMinus.atNode 2001,NodeMinus31.w16,CompactMinus2000.checked2000,CompactMinus2000.small2000,CompactMinus2000.nodes2000,NodeMinus31.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2001,GridMinus.atNode 2001,GridMinus.atNode 2002,NodeMinus31.w17,CompactMinus2000.checked2001,CompactMinus2000.small2001,CompactMinus2000.nodes2001,NodeMinus31.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2002,GridMinus.atNode 2002,GridMinus.atNode 2003,NodeMinus31.w18,CompactMinus2000.checked2002,CompactMinus2000.small2002,CompactMinus2000.nodes2002,NodeMinus31.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2003,GridMinus.atNode 2003,GridMinus.atNode 2004,NodeMinus31.w19,CompactMinus2000.checked2003,CompactMinus2000.small2003,CompactMinus2000.nodes2003,NodeMinus31.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2004,GridMinus.atNode 2004,GridMinus.atNode 2005,NodeMinus31.w20,CompactMinus2000.checked2004,CompactMinus2000.small2004,CompactMinus2000.nodes2004,NodeMinus31.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2005,GridMinus.atNode 2005,GridMinus.atNode 2006,NodeMinus31.w21,CompactMinus2000.checked2005,CompactMinus2000.small2005,CompactMinus2000.nodes2005,NodeMinus31.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2006,GridMinus.atNode 2006,GridMinus.atNode 2007,NodeMinus31.w22,CompactMinus2000.checked2006,CompactMinus2000.small2006,CompactMinus2000.nodes2006,NodeMinus31.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2007,GridMinus.atNode 2007,GridMinus.atNode 2008,NodeMinus31.w23,CompactMinus2000.checked2007,CompactMinus2000.small2007,CompactMinus2000.nodes2007,NodeMinus31.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2008,GridMinus.atNode 2008,GridMinus.atNode 2009,NodeMinus31.w24,CompactMinus2000.checked2008,CompactMinus2000.small2008,CompactMinus2000.nodes2008,NodeMinus31.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2009,GridMinus.atNode 2009,GridMinus.atNode 2010,NodeMinus31.w25,CompactMinus2000.checked2009,CompactMinus2000.small2009,CompactMinus2000.nodes2009,NodeMinus31.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2010,GridMinus.atNode 2010,GridMinus.atNode 2011,NodeMinus31.w26,CompactMinus2000.checked2010,CompactMinus2000.small2010,CompactMinus2000.nodes2010,NodeMinus31.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2011,GridMinus.atNode 2011,GridMinus.atNode 2012,NodeMinus31.w27,CompactMinus2000.checked2011,CompactMinus2000.small2011,CompactMinus2000.nodes2011,NodeMinus31.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2012,GridMinus.atNode 2012,GridMinus.atNode 2013,NodeMinus31.w28,CompactMinus2000.checked2012,CompactMinus2000.small2012,CompactMinus2000.nodes2012,NodeMinus31.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2013,GridMinus.atNode 2013,GridMinus.atNode 2014,NodeMinus31.w29,CompactMinus2000.checked2013,CompactMinus2000.small2013,CompactMinus2000.nodes2013,NodeMinus31.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2014,GridMinus.atNode 2014,GridMinus.atNode 2015,NodeMinus31.w30,CompactMinus2000.checked2014,CompactMinus2000.small2014,CompactMinus2000.nodes2014,NodeMinus31.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2000.p2015,GridMinus.atNode 2015,GridMinus.atNode 2016,NodeMinus31.w31,CompactMinus2000.checked2015,CompactMinus2000.small2015,CompactMinus2000.nodes2015,NodeMinus31.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2016,GridMinus.atNode 2016,GridMinus.atNode 2017,NodeMinus31.w32,CompactMinus2016.checked2016,CompactMinus2016.small2016,CompactMinus2016.nodes2016,NodeMinus31.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2017,GridMinus.atNode 2017,GridMinus.atNode 2018,NodeMinus31.w33,CompactMinus2016.checked2017,CompactMinus2016.small2017,CompactMinus2016.nodes2017,NodeMinus31.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2018,GridMinus.atNode 2018,GridMinus.atNode 2019,NodeMinus31.w34,CompactMinus2016.checked2018,CompactMinus2016.small2018,CompactMinus2016.nodes2018,NodeMinus31.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2019,GridMinus.atNode 2019,GridMinus.atNode 2020,NodeMinus31.w35,CompactMinus2016.checked2019,CompactMinus2016.small2019,CompactMinus2016.nodes2019,NodeMinus31.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2020,GridMinus.atNode 2020,GridMinus.atNode 2021,NodeMinus31.w36,CompactMinus2016.checked2020,CompactMinus2016.small2020,CompactMinus2016.nodes2020,NodeMinus31.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2021,GridMinus.atNode 2021,GridMinus.atNode 2022,NodeMinus31.w37,CompactMinus2016.checked2021,CompactMinus2016.small2021,CompactMinus2016.nodes2021,NodeMinus31.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2022,GridMinus.atNode 2022,GridMinus.atNode 2023,NodeMinus31.w38,CompactMinus2016.checked2022,CompactMinus2016.small2022,CompactMinus2016.nodes2022,NodeMinus31.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2023,GridMinus.atNode 2023,GridMinus.atNode 2024,NodeMinus31.w39,CompactMinus2016.checked2023,CompactMinus2016.small2023,CompactMinus2016.nodes2023,NodeMinus31.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2024,GridMinus.atNode 2024,GridMinus.atNode 2025,NodeMinus31.w40,CompactMinus2016.checked2024,CompactMinus2016.small2024,CompactMinus2016.nodes2024,NodeMinus31.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2025,GridMinus.atNode 2025,GridMinus.atNode 2026,NodeMinus31.w41,CompactMinus2016.checked2025,CompactMinus2016.small2025,CompactMinus2016.nodes2025,NodeMinus31.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2026,GridMinus.atNode 2026,GridMinus.atNode 2027,NodeMinus31.w42,CompactMinus2016.checked2026,CompactMinus2016.small2026,CompactMinus2016.nodes2026,NodeMinus31.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2027,GridMinus.atNode 2027,GridMinus.atNode 2028,NodeMinus31.w43,CompactMinus2016.checked2027,CompactMinus2016.small2027,CompactMinus2016.nodes2027,NodeMinus31.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2028,GridMinus.atNode 2028,GridMinus.atNode 2029,NodeMinus31.w44,CompactMinus2016.checked2028,CompactMinus2016.small2028,CompactMinus2016.nodes2028,NodeMinus31.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2029,GridMinus.atNode 2029,GridMinus.atNode 2030,NodeMinus31.w45,CompactMinus2016.checked2029,CompactMinus2016.small2029,CompactMinus2016.nodes2029,NodeMinus31.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2030,GridMinus.atNode 2030,GridMinus.atNode 2031,NodeMinus31.w46,CompactMinus2016.checked2030,CompactMinus2016.small2030,CompactMinus2016.nodes2030,NodeMinus31.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2016.p2031,GridMinus.atNode 2031,GridMinus.atNode 2032,NodeMinus31.w47,CompactMinus2016.checked2031,CompactMinus2016.small2031,CompactMinus2016.nodes2031,NodeMinus31.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2032,GridMinus.atNode 2032,GridMinus.atNode 2033,NodeMinus31.w48,CompactMinus2032.checked2032,CompactMinus2032.small2032,CompactMinus2032.nodes2032,NodeMinus31.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2033,GridMinus.atNode 2033,GridMinus.atNode 2034,NodeMinus31.w49,CompactMinus2032.checked2033,CompactMinus2032.small2033,CompactMinus2032.nodes2033,NodeMinus31.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2034,GridMinus.atNode 2034,GridMinus.atNode 2035,NodeMinus31.w50,CompactMinus2032.checked2034,CompactMinus2032.small2034,CompactMinus2032.nodes2034,NodeMinus31.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2035,GridMinus.atNode 2035,GridMinus.atNode 2036,NodeMinus31.w51,CompactMinus2032.checked2035,CompactMinus2032.small2035,CompactMinus2032.nodes2035,NodeMinus31.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2036,GridMinus.atNode 2036,GridMinus.atNode 2037,NodeMinus31.w52,CompactMinus2032.checked2036,CompactMinus2032.small2036,CompactMinus2032.nodes2036,NodeMinus31.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2037,GridMinus.atNode 2037,GridMinus.atNode 2038,NodeMinus31.w53,CompactMinus2032.checked2037,CompactMinus2032.small2037,CompactMinus2032.nodes2037,NodeMinus31.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2038,GridMinus.atNode 2038,GridMinus.atNode 2039,NodeMinus31.w54,CompactMinus2032.checked2038,CompactMinus2032.small2038,CompactMinus2032.nodes2038,NodeMinus31.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2039,GridMinus.atNode 2039,GridMinus.atNode 2040,NodeMinus31.w55,CompactMinus2032.checked2039,CompactMinus2032.small2039,CompactMinus2032.nodes2039,NodeMinus31.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2040,GridMinus.atNode 2040,GridMinus.atNode 2041,NodeMinus31.w56,CompactMinus2032.checked2040,CompactMinus2032.small2040,CompactMinus2032.nodes2040,NodeMinus31.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2041,GridMinus.atNode 2041,GridMinus.atNode 2042,NodeMinus31.w57,CompactMinus2032.checked2041,CompactMinus2032.small2041,CompactMinus2032.nodes2041,NodeMinus31.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2042,GridMinus.atNode 2042,GridMinus.atNode 2043,NodeMinus31.w58,CompactMinus2032.checked2042,CompactMinus2032.small2042,CompactMinus2032.nodes2042,NodeMinus31.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2043,GridMinus.atNode 2043,GridMinus.atNode 2044,NodeMinus31.w59,CompactMinus2032.checked2043,CompactMinus2032.small2043,CompactMinus2032.nodes2043,NodeMinus31.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2044,GridMinus.atNode 2044,GridMinus.atNode 2045,NodeMinus31.w60,CompactMinus2032.checked2044,CompactMinus2032.small2044,CompactMinus2032.nodes2044,NodeMinus31.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2045,GridMinus.atNode 2045,GridMinus.atNode 2046,NodeMinus31.w61,CompactMinus2032.checked2045,CompactMinus2032.small2045,CompactMinus2032.nodes2045,NodeMinus31.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2046,GridMinus.atNode 2046,GridMinus.atNode 2047,NodeMinus31.w62,CompactMinus2032.checked2046,CompactMinus2032.small2046,CompactMinus2032.nodes2046,NodeMinus31.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2032.p2047,GridMinus.atNode 2047,GridMinus.atNode 2048,NodeMinus31.w63,CompactMinus2032.checked2047,CompactMinus2032.small2047,CompactMinus2032.nodes2047,NodeMinus31.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1984+j) ∧
    (atRow j).right=GridMinus.atNode (1984+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus31
