import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0256
import SolitonClassification.Rotating.ResetPackedMinus0272
import SolitonClassification.Rotating.ResetPackedMinus0288
import SolitonClassification.Rotating.ResetPackedMinus0304
namespace SolitonClassification.Rotating.DyadicReset.TileMinus04
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p256,GridMinus.atNode 256,GridMinus.atNode 257,NodeMinus04.w0,CompactMinus0256.checked256,CompactMinus0256.small256,CompactMinus0256.nodes256,NodeMinus04.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p257,GridMinus.atNode 257,GridMinus.atNode 258,NodeMinus04.w1,CompactMinus0256.checked257,CompactMinus0256.small257,CompactMinus0256.nodes257,NodeMinus04.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p258,GridMinus.atNode 258,GridMinus.atNode 259,NodeMinus04.w2,CompactMinus0256.checked258,CompactMinus0256.small258,CompactMinus0256.nodes258,NodeMinus04.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p259,GridMinus.atNode 259,GridMinus.atNode 260,NodeMinus04.w3,CompactMinus0256.checked259,CompactMinus0256.small259,CompactMinus0256.nodes259,NodeMinus04.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p260,GridMinus.atNode 260,GridMinus.atNode 261,NodeMinus04.w4,CompactMinus0256.checked260,CompactMinus0256.small260,CompactMinus0256.nodes260,NodeMinus04.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p261,GridMinus.atNode 261,GridMinus.atNode 262,NodeMinus04.w5,CompactMinus0256.checked261,CompactMinus0256.small261,CompactMinus0256.nodes261,NodeMinus04.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p262,GridMinus.atNode 262,GridMinus.atNode 263,NodeMinus04.w6,CompactMinus0256.checked262,CompactMinus0256.small262,CompactMinus0256.nodes262,NodeMinus04.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p263,GridMinus.atNode 263,GridMinus.atNode 264,NodeMinus04.w7,CompactMinus0256.checked263,CompactMinus0256.small263,CompactMinus0256.nodes263,NodeMinus04.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p264,GridMinus.atNode 264,GridMinus.atNode 265,NodeMinus04.w8,CompactMinus0256.checked264,CompactMinus0256.small264,CompactMinus0256.nodes264,NodeMinus04.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p265,GridMinus.atNode 265,GridMinus.atNode 266,NodeMinus04.w9,CompactMinus0256.checked265,CompactMinus0256.small265,CompactMinus0256.nodes265,NodeMinus04.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p266,GridMinus.atNode 266,GridMinus.atNode 267,NodeMinus04.w10,CompactMinus0256.checked266,CompactMinus0256.small266,CompactMinus0256.nodes266,NodeMinus04.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p267,GridMinus.atNode 267,GridMinus.atNode 268,NodeMinus04.w11,CompactMinus0256.checked267,CompactMinus0256.small267,CompactMinus0256.nodes267,NodeMinus04.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p268,GridMinus.atNode 268,GridMinus.atNode 269,NodeMinus04.w12,CompactMinus0256.checked268,CompactMinus0256.small268,CompactMinus0256.nodes268,NodeMinus04.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p269,GridMinus.atNode 269,GridMinus.atNode 270,NodeMinus04.w13,CompactMinus0256.checked269,CompactMinus0256.small269,CompactMinus0256.nodes269,NodeMinus04.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p270,GridMinus.atNode 270,GridMinus.atNode 271,NodeMinus04.w14,CompactMinus0256.checked270,CompactMinus0256.small270,CompactMinus0256.nodes270,NodeMinus04.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0256.p271,GridMinus.atNode 271,GridMinus.atNode 272,NodeMinus04.w15,CompactMinus0256.checked271,CompactMinus0256.small271,CompactMinus0256.nodes271,NodeMinus04.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p272,GridMinus.atNode 272,GridMinus.atNode 273,NodeMinus04.w16,CompactMinus0272.checked272,CompactMinus0272.small272,CompactMinus0272.nodes272,NodeMinus04.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p273,GridMinus.atNode 273,GridMinus.atNode 274,NodeMinus04.w17,CompactMinus0272.checked273,CompactMinus0272.small273,CompactMinus0272.nodes273,NodeMinus04.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p274,GridMinus.atNode 274,GridMinus.atNode 275,NodeMinus04.w18,CompactMinus0272.checked274,CompactMinus0272.small274,CompactMinus0272.nodes274,NodeMinus04.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p275,GridMinus.atNode 275,GridMinus.atNode 276,NodeMinus04.w19,CompactMinus0272.checked275,CompactMinus0272.small275,CompactMinus0272.nodes275,NodeMinus04.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p276,GridMinus.atNode 276,GridMinus.atNode 277,NodeMinus04.w20,CompactMinus0272.checked276,CompactMinus0272.small276,CompactMinus0272.nodes276,NodeMinus04.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p277,GridMinus.atNode 277,GridMinus.atNode 278,NodeMinus04.w21,CompactMinus0272.checked277,CompactMinus0272.small277,CompactMinus0272.nodes277,NodeMinus04.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p278,GridMinus.atNode 278,GridMinus.atNode 279,NodeMinus04.w22,CompactMinus0272.checked278,CompactMinus0272.small278,CompactMinus0272.nodes278,NodeMinus04.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p279,GridMinus.atNode 279,GridMinus.atNode 280,NodeMinus04.w23,CompactMinus0272.checked279,CompactMinus0272.small279,CompactMinus0272.nodes279,NodeMinus04.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p280,GridMinus.atNode 280,GridMinus.atNode 281,NodeMinus04.w24,CompactMinus0272.checked280,CompactMinus0272.small280,CompactMinus0272.nodes280,NodeMinus04.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p281,GridMinus.atNode 281,GridMinus.atNode 282,NodeMinus04.w25,CompactMinus0272.checked281,CompactMinus0272.small281,CompactMinus0272.nodes281,NodeMinus04.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p282,GridMinus.atNode 282,GridMinus.atNode 283,NodeMinus04.w26,CompactMinus0272.checked282,CompactMinus0272.small282,CompactMinus0272.nodes282,NodeMinus04.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p283,GridMinus.atNode 283,GridMinus.atNode 284,NodeMinus04.w27,CompactMinus0272.checked283,CompactMinus0272.small283,CompactMinus0272.nodes283,NodeMinus04.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p284,GridMinus.atNode 284,GridMinus.atNode 285,NodeMinus04.w28,CompactMinus0272.checked284,CompactMinus0272.small284,CompactMinus0272.nodes284,NodeMinus04.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p285,GridMinus.atNode 285,GridMinus.atNode 286,NodeMinus04.w29,CompactMinus0272.checked285,CompactMinus0272.small285,CompactMinus0272.nodes285,NodeMinus04.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p286,GridMinus.atNode 286,GridMinus.atNode 287,NodeMinus04.w30,CompactMinus0272.checked286,CompactMinus0272.small286,CompactMinus0272.nodes286,NodeMinus04.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0272.p287,GridMinus.atNode 287,GridMinus.atNode 288,NodeMinus04.w31,CompactMinus0272.checked287,CompactMinus0272.small287,CompactMinus0272.nodes287,NodeMinus04.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p288,GridMinus.atNode 288,GridMinus.atNode 289,NodeMinus04.w32,CompactMinus0288.checked288,CompactMinus0288.small288,CompactMinus0288.nodes288,NodeMinus04.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p289,GridMinus.atNode 289,GridMinus.atNode 290,NodeMinus04.w33,CompactMinus0288.checked289,CompactMinus0288.small289,CompactMinus0288.nodes289,NodeMinus04.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p290,GridMinus.atNode 290,GridMinus.atNode 291,NodeMinus04.w34,CompactMinus0288.checked290,CompactMinus0288.small290,CompactMinus0288.nodes290,NodeMinus04.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p291,GridMinus.atNode 291,GridMinus.atNode 292,NodeMinus04.w35,CompactMinus0288.checked291,CompactMinus0288.small291,CompactMinus0288.nodes291,NodeMinus04.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p292,GridMinus.atNode 292,GridMinus.atNode 293,NodeMinus04.w36,CompactMinus0288.checked292,CompactMinus0288.small292,CompactMinus0288.nodes292,NodeMinus04.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p293,GridMinus.atNode 293,GridMinus.atNode 294,NodeMinus04.w37,CompactMinus0288.checked293,CompactMinus0288.small293,CompactMinus0288.nodes293,NodeMinus04.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p294,GridMinus.atNode 294,GridMinus.atNode 295,NodeMinus04.w38,CompactMinus0288.checked294,CompactMinus0288.small294,CompactMinus0288.nodes294,NodeMinus04.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p295,GridMinus.atNode 295,GridMinus.atNode 296,NodeMinus04.w39,CompactMinus0288.checked295,CompactMinus0288.small295,CompactMinus0288.nodes295,NodeMinus04.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p296,GridMinus.atNode 296,GridMinus.atNode 297,NodeMinus04.w40,CompactMinus0288.checked296,CompactMinus0288.small296,CompactMinus0288.nodes296,NodeMinus04.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p297,GridMinus.atNode 297,GridMinus.atNode 298,NodeMinus04.w41,CompactMinus0288.checked297,CompactMinus0288.small297,CompactMinus0288.nodes297,NodeMinus04.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p298,GridMinus.atNode 298,GridMinus.atNode 299,NodeMinus04.w42,CompactMinus0288.checked298,CompactMinus0288.small298,CompactMinus0288.nodes298,NodeMinus04.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p299,GridMinus.atNode 299,GridMinus.atNode 300,NodeMinus04.w43,CompactMinus0288.checked299,CompactMinus0288.small299,CompactMinus0288.nodes299,NodeMinus04.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p300,GridMinus.atNode 300,GridMinus.atNode 301,NodeMinus04.w44,CompactMinus0288.checked300,CompactMinus0288.small300,CompactMinus0288.nodes300,NodeMinus04.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p301,GridMinus.atNode 301,GridMinus.atNode 302,NodeMinus04.w45,CompactMinus0288.checked301,CompactMinus0288.small301,CompactMinus0288.nodes301,NodeMinus04.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p302,GridMinus.atNode 302,GridMinus.atNode 303,NodeMinus04.w46,CompactMinus0288.checked302,CompactMinus0288.small302,CompactMinus0288.nodes302,NodeMinus04.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0288.p303,GridMinus.atNode 303,GridMinus.atNode 304,NodeMinus04.w47,CompactMinus0288.checked303,CompactMinus0288.small303,CompactMinus0288.nodes303,NodeMinus04.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p304,GridMinus.atNode 304,GridMinus.atNode 305,NodeMinus04.w48,CompactMinus0304.checked304,CompactMinus0304.small304,CompactMinus0304.nodes304,NodeMinus04.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p305,GridMinus.atNode 305,GridMinus.atNode 306,NodeMinus04.w49,CompactMinus0304.checked305,CompactMinus0304.small305,CompactMinus0304.nodes305,NodeMinus04.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p306,GridMinus.atNode 306,GridMinus.atNode 307,NodeMinus04.w50,CompactMinus0304.checked306,CompactMinus0304.small306,CompactMinus0304.nodes306,NodeMinus04.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p307,GridMinus.atNode 307,GridMinus.atNode 308,NodeMinus04.w51,CompactMinus0304.checked307,CompactMinus0304.small307,CompactMinus0304.nodes307,NodeMinus04.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p308,GridMinus.atNode 308,GridMinus.atNode 309,NodeMinus04.w52,CompactMinus0304.checked308,CompactMinus0304.small308,CompactMinus0304.nodes308,NodeMinus04.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p309,GridMinus.atNode 309,GridMinus.atNode 310,NodeMinus04.w53,CompactMinus0304.checked309,CompactMinus0304.small309,CompactMinus0304.nodes309,NodeMinus04.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p310,GridMinus.atNode 310,GridMinus.atNode 311,NodeMinus04.w54,CompactMinus0304.checked310,CompactMinus0304.small310,CompactMinus0304.nodes310,NodeMinus04.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p311,GridMinus.atNode 311,GridMinus.atNode 312,NodeMinus04.w55,CompactMinus0304.checked311,CompactMinus0304.small311,CompactMinus0304.nodes311,NodeMinus04.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p312,GridMinus.atNode 312,GridMinus.atNode 313,NodeMinus04.w56,CompactMinus0304.checked312,CompactMinus0304.small312,CompactMinus0304.nodes312,NodeMinus04.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p313,GridMinus.atNode 313,GridMinus.atNode 314,NodeMinus04.w57,CompactMinus0304.checked313,CompactMinus0304.small313,CompactMinus0304.nodes313,NodeMinus04.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p314,GridMinus.atNode 314,GridMinus.atNode 315,NodeMinus04.w58,CompactMinus0304.checked314,CompactMinus0304.small314,CompactMinus0304.nodes314,NodeMinus04.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p315,GridMinus.atNode 315,GridMinus.atNode 316,NodeMinus04.w59,CompactMinus0304.checked315,CompactMinus0304.small315,CompactMinus0304.nodes315,NodeMinus04.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p316,GridMinus.atNode 316,GridMinus.atNode 317,NodeMinus04.w60,CompactMinus0304.checked316,CompactMinus0304.small316,CompactMinus0304.nodes316,NodeMinus04.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p317,GridMinus.atNode 317,GridMinus.atNode 318,NodeMinus04.w61,CompactMinus0304.checked317,CompactMinus0304.small317,CompactMinus0304.nodes317,NodeMinus04.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p318,GridMinus.atNode 318,GridMinus.atNode 319,NodeMinus04.w62,CompactMinus0304.checked318,CompactMinus0304.small318,CompactMinus0304.nodes318,NodeMinus04.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0304.p319,GridMinus.atNode 319,GridMinus.atNode 320,NodeMinus04.w63,CompactMinus0304.checked319,CompactMinus0304.small319,CompactMinus0304.nodes319,NodeMinus04.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (256+j) ∧
    (atRow j).right=GridMinus.atNode (256+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus04
