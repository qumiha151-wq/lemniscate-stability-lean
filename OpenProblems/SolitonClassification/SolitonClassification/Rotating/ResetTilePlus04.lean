import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0256
import SolitonClassification.Rotating.ResetPackedPlus0272
import SolitonClassification.Rotating.ResetPackedPlus0288
import SolitonClassification.Rotating.ResetPackedPlus0304
namespace SolitonClassification.Rotating.DyadicReset.TilePlus04
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p256,GridPlus.atNode 256,GridPlus.atNode 257,NodePlus04.w0,CompactPlus0256.checked256,CompactPlus0256.small256,CompactPlus0256.nodes256,NodePlus04.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p257,GridPlus.atNode 257,GridPlus.atNode 258,NodePlus04.w1,CompactPlus0256.checked257,CompactPlus0256.small257,CompactPlus0256.nodes257,NodePlus04.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p258,GridPlus.atNode 258,GridPlus.atNode 259,NodePlus04.w2,CompactPlus0256.checked258,CompactPlus0256.small258,CompactPlus0256.nodes258,NodePlus04.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p259,GridPlus.atNode 259,GridPlus.atNode 260,NodePlus04.w3,CompactPlus0256.checked259,CompactPlus0256.small259,CompactPlus0256.nodes259,NodePlus04.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p260,GridPlus.atNode 260,GridPlus.atNode 261,NodePlus04.w4,CompactPlus0256.checked260,CompactPlus0256.small260,CompactPlus0256.nodes260,NodePlus04.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p261,GridPlus.atNode 261,GridPlus.atNode 262,NodePlus04.w5,CompactPlus0256.checked261,CompactPlus0256.small261,CompactPlus0256.nodes261,NodePlus04.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p262,GridPlus.atNode 262,GridPlus.atNode 263,NodePlus04.w6,CompactPlus0256.checked262,CompactPlus0256.small262,CompactPlus0256.nodes262,NodePlus04.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p263,GridPlus.atNode 263,GridPlus.atNode 264,NodePlus04.w7,CompactPlus0256.checked263,CompactPlus0256.small263,CompactPlus0256.nodes263,NodePlus04.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p264,GridPlus.atNode 264,GridPlus.atNode 265,NodePlus04.w8,CompactPlus0256.checked264,CompactPlus0256.small264,CompactPlus0256.nodes264,NodePlus04.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p265,GridPlus.atNode 265,GridPlus.atNode 266,NodePlus04.w9,CompactPlus0256.checked265,CompactPlus0256.small265,CompactPlus0256.nodes265,NodePlus04.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p266,GridPlus.atNode 266,GridPlus.atNode 267,NodePlus04.w10,CompactPlus0256.checked266,CompactPlus0256.small266,CompactPlus0256.nodes266,NodePlus04.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p267,GridPlus.atNode 267,GridPlus.atNode 268,NodePlus04.w11,CompactPlus0256.checked267,CompactPlus0256.small267,CompactPlus0256.nodes267,NodePlus04.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p268,GridPlus.atNode 268,GridPlus.atNode 269,NodePlus04.w12,CompactPlus0256.checked268,CompactPlus0256.small268,CompactPlus0256.nodes268,NodePlus04.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p269,GridPlus.atNode 269,GridPlus.atNode 270,NodePlus04.w13,CompactPlus0256.checked269,CompactPlus0256.small269,CompactPlus0256.nodes269,NodePlus04.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p270,GridPlus.atNode 270,GridPlus.atNode 271,NodePlus04.w14,CompactPlus0256.checked270,CompactPlus0256.small270,CompactPlus0256.nodes270,NodePlus04.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0256.p271,GridPlus.atNode 271,GridPlus.atNode 272,NodePlus04.w15,CompactPlus0256.checked271,CompactPlus0256.small271,CompactPlus0256.nodes271,NodePlus04.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p272,GridPlus.atNode 272,GridPlus.atNode 273,NodePlus04.w16,CompactPlus0272.checked272,CompactPlus0272.small272,CompactPlus0272.nodes272,NodePlus04.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p273,GridPlus.atNode 273,GridPlus.atNode 274,NodePlus04.w17,CompactPlus0272.checked273,CompactPlus0272.small273,CompactPlus0272.nodes273,NodePlus04.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p274,GridPlus.atNode 274,GridPlus.atNode 275,NodePlus04.w18,CompactPlus0272.checked274,CompactPlus0272.small274,CompactPlus0272.nodes274,NodePlus04.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p275,GridPlus.atNode 275,GridPlus.atNode 276,NodePlus04.w19,CompactPlus0272.checked275,CompactPlus0272.small275,CompactPlus0272.nodes275,NodePlus04.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p276,GridPlus.atNode 276,GridPlus.atNode 277,NodePlus04.w20,CompactPlus0272.checked276,CompactPlus0272.small276,CompactPlus0272.nodes276,NodePlus04.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p277,GridPlus.atNode 277,GridPlus.atNode 278,NodePlus04.w21,CompactPlus0272.checked277,CompactPlus0272.small277,CompactPlus0272.nodes277,NodePlus04.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p278,GridPlus.atNode 278,GridPlus.atNode 279,NodePlus04.w22,CompactPlus0272.checked278,CompactPlus0272.small278,CompactPlus0272.nodes278,NodePlus04.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p279,GridPlus.atNode 279,GridPlus.atNode 280,NodePlus04.w23,CompactPlus0272.checked279,CompactPlus0272.small279,CompactPlus0272.nodes279,NodePlus04.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p280,GridPlus.atNode 280,GridPlus.atNode 281,NodePlus04.w24,CompactPlus0272.checked280,CompactPlus0272.small280,CompactPlus0272.nodes280,NodePlus04.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p281,GridPlus.atNode 281,GridPlus.atNode 282,NodePlus04.w25,CompactPlus0272.checked281,CompactPlus0272.small281,CompactPlus0272.nodes281,NodePlus04.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p282,GridPlus.atNode 282,GridPlus.atNode 283,NodePlus04.w26,CompactPlus0272.checked282,CompactPlus0272.small282,CompactPlus0272.nodes282,NodePlus04.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p283,GridPlus.atNode 283,GridPlus.atNode 284,NodePlus04.w27,CompactPlus0272.checked283,CompactPlus0272.small283,CompactPlus0272.nodes283,NodePlus04.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p284,GridPlus.atNode 284,GridPlus.atNode 285,NodePlus04.w28,CompactPlus0272.checked284,CompactPlus0272.small284,CompactPlus0272.nodes284,NodePlus04.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p285,GridPlus.atNode 285,GridPlus.atNode 286,NodePlus04.w29,CompactPlus0272.checked285,CompactPlus0272.small285,CompactPlus0272.nodes285,NodePlus04.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p286,GridPlus.atNode 286,GridPlus.atNode 287,NodePlus04.w30,CompactPlus0272.checked286,CompactPlus0272.small286,CompactPlus0272.nodes286,NodePlus04.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0272.p287,GridPlus.atNode 287,GridPlus.atNode 288,NodePlus04.w31,CompactPlus0272.checked287,CompactPlus0272.small287,CompactPlus0272.nodes287,NodePlus04.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p288,GridPlus.atNode 288,GridPlus.atNode 289,NodePlus04.w32,CompactPlus0288.checked288,CompactPlus0288.small288,CompactPlus0288.nodes288,NodePlus04.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p289,GridPlus.atNode 289,GridPlus.atNode 290,NodePlus04.w33,CompactPlus0288.checked289,CompactPlus0288.small289,CompactPlus0288.nodes289,NodePlus04.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p290,GridPlus.atNode 290,GridPlus.atNode 291,NodePlus04.w34,CompactPlus0288.checked290,CompactPlus0288.small290,CompactPlus0288.nodes290,NodePlus04.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p291,GridPlus.atNode 291,GridPlus.atNode 292,NodePlus04.w35,CompactPlus0288.checked291,CompactPlus0288.small291,CompactPlus0288.nodes291,NodePlus04.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p292,GridPlus.atNode 292,GridPlus.atNode 293,NodePlus04.w36,CompactPlus0288.checked292,CompactPlus0288.small292,CompactPlus0288.nodes292,NodePlus04.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p293,GridPlus.atNode 293,GridPlus.atNode 294,NodePlus04.w37,CompactPlus0288.checked293,CompactPlus0288.small293,CompactPlus0288.nodes293,NodePlus04.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p294,GridPlus.atNode 294,GridPlus.atNode 295,NodePlus04.w38,CompactPlus0288.checked294,CompactPlus0288.small294,CompactPlus0288.nodes294,NodePlus04.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p295,GridPlus.atNode 295,GridPlus.atNode 296,NodePlus04.w39,CompactPlus0288.checked295,CompactPlus0288.small295,CompactPlus0288.nodes295,NodePlus04.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p296,GridPlus.atNode 296,GridPlus.atNode 297,NodePlus04.w40,CompactPlus0288.checked296,CompactPlus0288.small296,CompactPlus0288.nodes296,NodePlus04.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p297,GridPlus.atNode 297,GridPlus.atNode 298,NodePlus04.w41,CompactPlus0288.checked297,CompactPlus0288.small297,CompactPlus0288.nodes297,NodePlus04.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p298,GridPlus.atNode 298,GridPlus.atNode 299,NodePlus04.w42,CompactPlus0288.checked298,CompactPlus0288.small298,CompactPlus0288.nodes298,NodePlus04.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p299,GridPlus.atNode 299,GridPlus.atNode 300,NodePlus04.w43,CompactPlus0288.checked299,CompactPlus0288.small299,CompactPlus0288.nodes299,NodePlus04.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p300,GridPlus.atNode 300,GridPlus.atNode 301,NodePlus04.w44,CompactPlus0288.checked300,CompactPlus0288.small300,CompactPlus0288.nodes300,NodePlus04.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p301,GridPlus.atNode 301,GridPlus.atNode 302,NodePlus04.w45,CompactPlus0288.checked301,CompactPlus0288.small301,CompactPlus0288.nodes301,NodePlus04.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p302,GridPlus.atNode 302,GridPlus.atNode 303,NodePlus04.w46,CompactPlus0288.checked302,CompactPlus0288.small302,CompactPlus0288.nodes302,NodePlus04.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0288.p303,GridPlus.atNode 303,GridPlus.atNode 304,NodePlus04.w47,CompactPlus0288.checked303,CompactPlus0288.small303,CompactPlus0288.nodes303,NodePlus04.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p304,GridPlus.atNode 304,GridPlus.atNode 305,NodePlus04.w48,CompactPlus0304.checked304,CompactPlus0304.small304,CompactPlus0304.nodes304,NodePlus04.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p305,GridPlus.atNode 305,GridPlus.atNode 306,NodePlus04.w49,CompactPlus0304.checked305,CompactPlus0304.small305,CompactPlus0304.nodes305,NodePlus04.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p306,GridPlus.atNode 306,GridPlus.atNode 307,NodePlus04.w50,CompactPlus0304.checked306,CompactPlus0304.small306,CompactPlus0304.nodes306,NodePlus04.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p307,GridPlus.atNode 307,GridPlus.atNode 308,NodePlus04.w51,CompactPlus0304.checked307,CompactPlus0304.small307,CompactPlus0304.nodes307,NodePlus04.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p308,GridPlus.atNode 308,GridPlus.atNode 309,NodePlus04.w52,CompactPlus0304.checked308,CompactPlus0304.small308,CompactPlus0304.nodes308,NodePlus04.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p309,GridPlus.atNode 309,GridPlus.atNode 310,NodePlus04.w53,CompactPlus0304.checked309,CompactPlus0304.small309,CompactPlus0304.nodes309,NodePlus04.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p310,GridPlus.atNode 310,GridPlus.atNode 311,NodePlus04.w54,CompactPlus0304.checked310,CompactPlus0304.small310,CompactPlus0304.nodes310,NodePlus04.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p311,GridPlus.atNode 311,GridPlus.atNode 312,NodePlus04.w55,CompactPlus0304.checked311,CompactPlus0304.small311,CompactPlus0304.nodes311,NodePlus04.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p312,GridPlus.atNode 312,GridPlus.atNode 313,NodePlus04.w56,CompactPlus0304.checked312,CompactPlus0304.small312,CompactPlus0304.nodes312,NodePlus04.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p313,GridPlus.atNode 313,GridPlus.atNode 314,NodePlus04.w57,CompactPlus0304.checked313,CompactPlus0304.small313,CompactPlus0304.nodes313,NodePlus04.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p314,GridPlus.atNode 314,GridPlus.atNode 315,NodePlus04.w58,CompactPlus0304.checked314,CompactPlus0304.small314,CompactPlus0304.nodes314,NodePlus04.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p315,GridPlus.atNode 315,GridPlus.atNode 316,NodePlus04.w59,CompactPlus0304.checked315,CompactPlus0304.small315,CompactPlus0304.nodes315,NodePlus04.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p316,GridPlus.atNode 316,GridPlus.atNode 317,NodePlus04.w60,CompactPlus0304.checked316,CompactPlus0304.small316,CompactPlus0304.nodes316,NodePlus04.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p317,GridPlus.atNode 317,GridPlus.atNode 318,NodePlus04.w61,CompactPlus0304.checked317,CompactPlus0304.small317,CompactPlus0304.nodes317,NodePlus04.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p318,GridPlus.atNode 318,GridPlus.atNode 319,NodePlus04.w62,CompactPlus0304.checked318,CompactPlus0304.small318,CompactPlus0304.nodes318,NodePlus04.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0304.p319,GridPlus.atNode 319,GridPlus.atNode 320,NodePlus04.w63,CompactPlus0304.checked319,CompactPlus0304.small319,CompactPlus0304.nodes319,NodePlus04.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (256+j) ∧
    (atRow j).right=GridPlus.atNode (256+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus04
