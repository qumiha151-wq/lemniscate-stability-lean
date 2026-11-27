import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1984
import SolitonClassification.Rotating.ResetPackedPlus2000
import SolitonClassification.Rotating.ResetPackedPlus2016
import SolitonClassification.Rotating.ResetPackedPlus2032
namespace SolitonClassification.Rotating.DyadicReset.TilePlus31
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1984,GridPlus.atNode 1984,GridPlus.atNode 1985,NodePlus31.w0,CompactPlus1984.checked1984,CompactPlus1984.small1984,CompactPlus1984.nodes1984,NodePlus31.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1985,GridPlus.atNode 1985,GridPlus.atNode 1986,NodePlus31.w1,CompactPlus1984.checked1985,CompactPlus1984.small1985,CompactPlus1984.nodes1985,NodePlus31.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1986,GridPlus.atNode 1986,GridPlus.atNode 1987,NodePlus31.w2,CompactPlus1984.checked1986,CompactPlus1984.small1986,CompactPlus1984.nodes1986,NodePlus31.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1987,GridPlus.atNode 1987,GridPlus.atNode 1988,NodePlus31.w3,CompactPlus1984.checked1987,CompactPlus1984.small1987,CompactPlus1984.nodes1987,NodePlus31.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1988,GridPlus.atNode 1988,GridPlus.atNode 1989,NodePlus31.w4,CompactPlus1984.checked1988,CompactPlus1984.small1988,CompactPlus1984.nodes1988,NodePlus31.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1989,GridPlus.atNode 1989,GridPlus.atNode 1990,NodePlus31.w5,CompactPlus1984.checked1989,CompactPlus1984.small1989,CompactPlus1984.nodes1989,NodePlus31.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1990,GridPlus.atNode 1990,GridPlus.atNode 1991,NodePlus31.w6,CompactPlus1984.checked1990,CompactPlus1984.small1990,CompactPlus1984.nodes1990,NodePlus31.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1991,GridPlus.atNode 1991,GridPlus.atNode 1992,NodePlus31.w7,CompactPlus1984.checked1991,CompactPlus1984.small1991,CompactPlus1984.nodes1991,NodePlus31.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1992,GridPlus.atNode 1992,GridPlus.atNode 1993,NodePlus31.w8,CompactPlus1984.checked1992,CompactPlus1984.small1992,CompactPlus1984.nodes1992,NodePlus31.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1993,GridPlus.atNode 1993,GridPlus.atNode 1994,NodePlus31.w9,CompactPlus1984.checked1993,CompactPlus1984.small1993,CompactPlus1984.nodes1993,NodePlus31.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1994,GridPlus.atNode 1994,GridPlus.atNode 1995,NodePlus31.w10,CompactPlus1984.checked1994,CompactPlus1984.small1994,CompactPlus1984.nodes1994,NodePlus31.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1995,GridPlus.atNode 1995,GridPlus.atNode 1996,NodePlus31.w11,CompactPlus1984.checked1995,CompactPlus1984.small1995,CompactPlus1984.nodes1995,NodePlus31.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1996,GridPlus.atNode 1996,GridPlus.atNode 1997,NodePlus31.w12,CompactPlus1984.checked1996,CompactPlus1984.small1996,CompactPlus1984.nodes1996,NodePlus31.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1997,GridPlus.atNode 1997,GridPlus.atNode 1998,NodePlus31.w13,CompactPlus1984.checked1997,CompactPlus1984.small1997,CompactPlus1984.nodes1997,NodePlus31.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1998,GridPlus.atNode 1998,GridPlus.atNode 1999,NodePlus31.w14,CompactPlus1984.checked1998,CompactPlus1984.small1998,CompactPlus1984.nodes1998,NodePlus31.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1984.p1999,GridPlus.atNode 1999,GridPlus.atNode 2000,NodePlus31.w15,CompactPlus1984.checked1999,CompactPlus1984.small1999,CompactPlus1984.nodes1999,NodePlus31.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2000,GridPlus.atNode 2000,GridPlus.atNode 2001,NodePlus31.w16,CompactPlus2000.checked2000,CompactPlus2000.small2000,CompactPlus2000.nodes2000,NodePlus31.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2001,GridPlus.atNode 2001,GridPlus.atNode 2002,NodePlus31.w17,CompactPlus2000.checked2001,CompactPlus2000.small2001,CompactPlus2000.nodes2001,NodePlus31.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2002,GridPlus.atNode 2002,GridPlus.atNode 2003,NodePlus31.w18,CompactPlus2000.checked2002,CompactPlus2000.small2002,CompactPlus2000.nodes2002,NodePlus31.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2003,GridPlus.atNode 2003,GridPlus.atNode 2004,NodePlus31.w19,CompactPlus2000.checked2003,CompactPlus2000.small2003,CompactPlus2000.nodes2003,NodePlus31.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2004,GridPlus.atNode 2004,GridPlus.atNode 2005,NodePlus31.w20,CompactPlus2000.checked2004,CompactPlus2000.small2004,CompactPlus2000.nodes2004,NodePlus31.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2005,GridPlus.atNode 2005,GridPlus.atNode 2006,NodePlus31.w21,CompactPlus2000.checked2005,CompactPlus2000.small2005,CompactPlus2000.nodes2005,NodePlus31.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2006,GridPlus.atNode 2006,GridPlus.atNode 2007,NodePlus31.w22,CompactPlus2000.checked2006,CompactPlus2000.small2006,CompactPlus2000.nodes2006,NodePlus31.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2007,GridPlus.atNode 2007,GridPlus.atNode 2008,NodePlus31.w23,CompactPlus2000.checked2007,CompactPlus2000.small2007,CompactPlus2000.nodes2007,NodePlus31.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2008,GridPlus.atNode 2008,GridPlus.atNode 2009,NodePlus31.w24,CompactPlus2000.checked2008,CompactPlus2000.small2008,CompactPlus2000.nodes2008,NodePlus31.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2009,GridPlus.atNode 2009,GridPlus.atNode 2010,NodePlus31.w25,CompactPlus2000.checked2009,CompactPlus2000.small2009,CompactPlus2000.nodes2009,NodePlus31.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2010,GridPlus.atNode 2010,GridPlus.atNode 2011,NodePlus31.w26,CompactPlus2000.checked2010,CompactPlus2000.small2010,CompactPlus2000.nodes2010,NodePlus31.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2011,GridPlus.atNode 2011,GridPlus.atNode 2012,NodePlus31.w27,CompactPlus2000.checked2011,CompactPlus2000.small2011,CompactPlus2000.nodes2011,NodePlus31.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2012,GridPlus.atNode 2012,GridPlus.atNode 2013,NodePlus31.w28,CompactPlus2000.checked2012,CompactPlus2000.small2012,CompactPlus2000.nodes2012,NodePlus31.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2013,GridPlus.atNode 2013,GridPlus.atNode 2014,NodePlus31.w29,CompactPlus2000.checked2013,CompactPlus2000.small2013,CompactPlus2000.nodes2013,NodePlus31.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2014,GridPlus.atNode 2014,GridPlus.atNode 2015,NodePlus31.w30,CompactPlus2000.checked2014,CompactPlus2000.small2014,CompactPlus2000.nodes2014,NodePlus31.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2000.p2015,GridPlus.atNode 2015,GridPlus.atNode 2016,NodePlus31.w31,CompactPlus2000.checked2015,CompactPlus2000.small2015,CompactPlus2000.nodes2015,NodePlus31.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2016,GridPlus.atNode 2016,GridPlus.atNode 2017,NodePlus31.w32,CompactPlus2016.checked2016,CompactPlus2016.small2016,CompactPlus2016.nodes2016,NodePlus31.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2017,GridPlus.atNode 2017,GridPlus.atNode 2018,NodePlus31.w33,CompactPlus2016.checked2017,CompactPlus2016.small2017,CompactPlus2016.nodes2017,NodePlus31.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2018,GridPlus.atNode 2018,GridPlus.atNode 2019,NodePlus31.w34,CompactPlus2016.checked2018,CompactPlus2016.small2018,CompactPlus2016.nodes2018,NodePlus31.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2019,GridPlus.atNode 2019,GridPlus.atNode 2020,NodePlus31.w35,CompactPlus2016.checked2019,CompactPlus2016.small2019,CompactPlus2016.nodes2019,NodePlus31.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2020,GridPlus.atNode 2020,GridPlus.atNode 2021,NodePlus31.w36,CompactPlus2016.checked2020,CompactPlus2016.small2020,CompactPlus2016.nodes2020,NodePlus31.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2021,GridPlus.atNode 2021,GridPlus.atNode 2022,NodePlus31.w37,CompactPlus2016.checked2021,CompactPlus2016.small2021,CompactPlus2016.nodes2021,NodePlus31.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2022,GridPlus.atNode 2022,GridPlus.atNode 2023,NodePlus31.w38,CompactPlus2016.checked2022,CompactPlus2016.small2022,CompactPlus2016.nodes2022,NodePlus31.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2023,GridPlus.atNode 2023,GridPlus.atNode 2024,NodePlus31.w39,CompactPlus2016.checked2023,CompactPlus2016.small2023,CompactPlus2016.nodes2023,NodePlus31.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2024,GridPlus.atNode 2024,GridPlus.atNode 2025,NodePlus31.w40,CompactPlus2016.checked2024,CompactPlus2016.small2024,CompactPlus2016.nodes2024,NodePlus31.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2025,GridPlus.atNode 2025,GridPlus.atNode 2026,NodePlus31.w41,CompactPlus2016.checked2025,CompactPlus2016.small2025,CompactPlus2016.nodes2025,NodePlus31.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2026,GridPlus.atNode 2026,GridPlus.atNode 2027,NodePlus31.w42,CompactPlus2016.checked2026,CompactPlus2016.small2026,CompactPlus2016.nodes2026,NodePlus31.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2027,GridPlus.atNode 2027,GridPlus.atNode 2028,NodePlus31.w43,CompactPlus2016.checked2027,CompactPlus2016.small2027,CompactPlus2016.nodes2027,NodePlus31.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2028,GridPlus.atNode 2028,GridPlus.atNode 2029,NodePlus31.w44,CompactPlus2016.checked2028,CompactPlus2016.small2028,CompactPlus2016.nodes2028,NodePlus31.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2029,GridPlus.atNode 2029,GridPlus.atNode 2030,NodePlus31.w45,CompactPlus2016.checked2029,CompactPlus2016.small2029,CompactPlus2016.nodes2029,NodePlus31.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2030,GridPlus.atNode 2030,GridPlus.atNode 2031,NodePlus31.w46,CompactPlus2016.checked2030,CompactPlus2016.small2030,CompactPlus2016.nodes2030,NodePlus31.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2016.p2031,GridPlus.atNode 2031,GridPlus.atNode 2032,NodePlus31.w47,CompactPlus2016.checked2031,CompactPlus2016.small2031,CompactPlus2016.nodes2031,NodePlus31.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2032,GridPlus.atNode 2032,GridPlus.atNode 2033,NodePlus31.w48,CompactPlus2032.checked2032,CompactPlus2032.small2032,CompactPlus2032.nodes2032,NodePlus31.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2033,GridPlus.atNode 2033,GridPlus.atNode 2034,NodePlus31.w49,CompactPlus2032.checked2033,CompactPlus2032.small2033,CompactPlus2032.nodes2033,NodePlus31.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2034,GridPlus.atNode 2034,GridPlus.atNode 2035,NodePlus31.w50,CompactPlus2032.checked2034,CompactPlus2032.small2034,CompactPlus2032.nodes2034,NodePlus31.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2035,GridPlus.atNode 2035,GridPlus.atNode 2036,NodePlus31.w51,CompactPlus2032.checked2035,CompactPlus2032.small2035,CompactPlus2032.nodes2035,NodePlus31.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2036,GridPlus.atNode 2036,GridPlus.atNode 2037,NodePlus31.w52,CompactPlus2032.checked2036,CompactPlus2032.small2036,CompactPlus2032.nodes2036,NodePlus31.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2037,GridPlus.atNode 2037,GridPlus.atNode 2038,NodePlus31.w53,CompactPlus2032.checked2037,CompactPlus2032.small2037,CompactPlus2032.nodes2037,NodePlus31.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2038,GridPlus.atNode 2038,GridPlus.atNode 2039,NodePlus31.w54,CompactPlus2032.checked2038,CompactPlus2032.small2038,CompactPlus2032.nodes2038,NodePlus31.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2039,GridPlus.atNode 2039,GridPlus.atNode 2040,NodePlus31.w55,CompactPlus2032.checked2039,CompactPlus2032.small2039,CompactPlus2032.nodes2039,NodePlus31.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2040,GridPlus.atNode 2040,GridPlus.atNode 2041,NodePlus31.w56,CompactPlus2032.checked2040,CompactPlus2032.small2040,CompactPlus2032.nodes2040,NodePlus31.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2041,GridPlus.atNode 2041,GridPlus.atNode 2042,NodePlus31.w57,CompactPlus2032.checked2041,CompactPlus2032.small2041,CompactPlus2032.nodes2041,NodePlus31.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2042,GridPlus.atNode 2042,GridPlus.atNode 2043,NodePlus31.w58,CompactPlus2032.checked2042,CompactPlus2032.small2042,CompactPlus2032.nodes2042,NodePlus31.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2043,GridPlus.atNode 2043,GridPlus.atNode 2044,NodePlus31.w59,CompactPlus2032.checked2043,CompactPlus2032.small2043,CompactPlus2032.nodes2043,NodePlus31.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2044,GridPlus.atNode 2044,GridPlus.atNode 2045,NodePlus31.w60,CompactPlus2032.checked2044,CompactPlus2032.small2044,CompactPlus2032.nodes2044,NodePlus31.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2045,GridPlus.atNode 2045,GridPlus.atNode 2046,NodePlus31.w61,CompactPlus2032.checked2045,CompactPlus2032.small2045,CompactPlus2032.nodes2045,NodePlus31.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2046,GridPlus.atNode 2046,GridPlus.atNode 2047,NodePlus31.w62,CompactPlus2032.checked2046,CompactPlus2032.small2046,CompactPlus2032.nodes2046,NodePlus31.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2032.p2047,GridPlus.atNode 2047,GridPlus.atNode 2048,NodePlus31.w63,CompactPlus2032.checked2047,CompactPlus2032.small2047,CompactPlus2032.nodes2047,NodePlus31.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1984+j) ∧
    (atRow j).right=GridPlus.atNode (1984+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus31
