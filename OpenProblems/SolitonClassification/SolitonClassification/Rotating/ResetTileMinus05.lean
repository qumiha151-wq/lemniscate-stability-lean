import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0320
import SolitonClassification.Rotating.ResetPackedMinus0336
import SolitonClassification.Rotating.ResetPackedMinus0352
import SolitonClassification.Rotating.ResetPackedMinus0368
namespace SolitonClassification.Rotating.DyadicReset.TileMinus05
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p320,GridMinus.atNode 320,GridMinus.atNode 321,NodeMinus05.w0,CompactMinus0320.checked320,CompactMinus0320.small320,CompactMinus0320.nodes320,NodeMinus05.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p321,GridMinus.atNode 321,GridMinus.atNode 322,NodeMinus05.w1,CompactMinus0320.checked321,CompactMinus0320.small321,CompactMinus0320.nodes321,NodeMinus05.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p322,GridMinus.atNode 322,GridMinus.atNode 323,NodeMinus05.w2,CompactMinus0320.checked322,CompactMinus0320.small322,CompactMinus0320.nodes322,NodeMinus05.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p323,GridMinus.atNode 323,GridMinus.atNode 324,NodeMinus05.w3,CompactMinus0320.checked323,CompactMinus0320.small323,CompactMinus0320.nodes323,NodeMinus05.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p324,GridMinus.atNode 324,GridMinus.atNode 325,NodeMinus05.w4,CompactMinus0320.checked324,CompactMinus0320.small324,CompactMinus0320.nodes324,NodeMinus05.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p325,GridMinus.atNode 325,GridMinus.atNode 326,NodeMinus05.w5,CompactMinus0320.checked325,CompactMinus0320.small325,CompactMinus0320.nodes325,NodeMinus05.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p326,GridMinus.atNode 326,GridMinus.atNode 327,NodeMinus05.w6,CompactMinus0320.checked326,CompactMinus0320.small326,CompactMinus0320.nodes326,NodeMinus05.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p327,GridMinus.atNode 327,GridMinus.atNode 328,NodeMinus05.w7,CompactMinus0320.checked327,CompactMinus0320.small327,CompactMinus0320.nodes327,NodeMinus05.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p328,GridMinus.atNode 328,GridMinus.atNode 329,NodeMinus05.w8,CompactMinus0320.checked328,CompactMinus0320.small328,CompactMinus0320.nodes328,NodeMinus05.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p329,GridMinus.atNode 329,GridMinus.atNode 330,NodeMinus05.w9,CompactMinus0320.checked329,CompactMinus0320.small329,CompactMinus0320.nodes329,NodeMinus05.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p330,GridMinus.atNode 330,GridMinus.atNode 331,NodeMinus05.w10,CompactMinus0320.checked330,CompactMinus0320.small330,CompactMinus0320.nodes330,NodeMinus05.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p331,GridMinus.atNode 331,GridMinus.atNode 332,NodeMinus05.w11,CompactMinus0320.checked331,CompactMinus0320.small331,CompactMinus0320.nodes331,NodeMinus05.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p332,GridMinus.atNode 332,GridMinus.atNode 333,NodeMinus05.w12,CompactMinus0320.checked332,CompactMinus0320.small332,CompactMinus0320.nodes332,NodeMinus05.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p333,GridMinus.atNode 333,GridMinus.atNode 334,NodeMinus05.w13,CompactMinus0320.checked333,CompactMinus0320.small333,CompactMinus0320.nodes333,NodeMinus05.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p334,GridMinus.atNode 334,GridMinus.atNode 335,NodeMinus05.w14,CompactMinus0320.checked334,CompactMinus0320.small334,CompactMinus0320.nodes334,NodeMinus05.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0320.p335,GridMinus.atNode 335,GridMinus.atNode 336,NodeMinus05.w15,CompactMinus0320.checked335,CompactMinus0320.small335,CompactMinus0320.nodes335,NodeMinus05.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p336,GridMinus.atNode 336,GridMinus.atNode 337,NodeMinus05.w16,CompactMinus0336.checked336,CompactMinus0336.small336,CompactMinus0336.nodes336,NodeMinus05.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p337,GridMinus.atNode 337,GridMinus.atNode 338,NodeMinus05.w17,CompactMinus0336.checked337,CompactMinus0336.small337,CompactMinus0336.nodes337,NodeMinus05.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p338,GridMinus.atNode 338,GridMinus.atNode 339,NodeMinus05.w18,CompactMinus0336.checked338,CompactMinus0336.small338,CompactMinus0336.nodes338,NodeMinus05.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p339,GridMinus.atNode 339,GridMinus.atNode 340,NodeMinus05.w19,CompactMinus0336.checked339,CompactMinus0336.small339,CompactMinus0336.nodes339,NodeMinus05.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p340,GridMinus.atNode 340,GridMinus.atNode 341,NodeMinus05.w20,CompactMinus0336.checked340,CompactMinus0336.small340,CompactMinus0336.nodes340,NodeMinus05.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p341,GridMinus.atNode 341,GridMinus.atNode 342,NodeMinus05.w21,CompactMinus0336.checked341,CompactMinus0336.small341,CompactMinus0336.nodes341,NodeMinus05.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p342,GridMinus.atNode 342,GridMinus.atNode 343,NodeMinus05.w22,CompactMinus0336.checked342,CompactMinus0336.small342,CompactMinus0336.nodes342,NodeMinus05.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p343,GridMinus.atNode 343,GridMinus.atNode 344,NodeMinus05.w23,CompactMinus0336.checked343,CompactMinus0336.small343,CompactMinus0336.nodes343,NodeMinus05.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p344,GridMinus.atNode 344,GridMinus.atNode 345,NodeMinus05.w24,CompactMinus0336.checked344,CompactMinus0336.small344,CompactMinus0336.nodes344,NodeMinus05.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p345,GridMinus.atNode 345,GridMinus.atNode 346,NodeMinus05.w25,CompactMinus0336.checked345,CompactMinus0336.small345,CompactMinus0336.nodes345,NodeMinus05.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p346,GridMinus.atNode 346,GridMinus.atNode 347,NodeMinus05.w26,CompactMinus0336.checked346,CompactMinus0336.small346,CompactMinus0336.nodes346,NodeMinus05.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p347,GridMinus.atNode 347,GridMinus.atNode 348,NodeMinus05.w27,CompactMinus0336.checked347,CompactMinus0336.small347,CompactMinus0336.nodes347,NodeMinus05.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p348,GridMinus.atNode 348,GridMinus.atNode 349,NodeMinus05.w28,CompactMinus0336.checked348,CompactMinus0336.small348,CompactMinus0336.nodes348,NodeMinus05.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p349,GridMinus.atNode 349,GridMinus.atNode 350,NodeMinus05.w29,CompactMinus0336.checked349,CompactMinus0336.small349,CompactMinus0336.nodes349,NodeMinus05.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p350,GridMinus.atNode 350,GridMinus.atNode 351,NodeMinus05.w30,CompactMinus0336.checked350,CompactMinus0336.small350,CompactMinus0336.nodes350,NodeMinus05.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0336.p351,GridMinus.atNode 351,GridMinus.atNode 352,NodeMinus05.w31,CompactMinus0336.checked351,CompactMinus0336.small351,CompactMinus0336.nodes351,NodeMinus05.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p352,GridMinus.atNode 352,GridMinus.atNode 353,NodeMinus05.w32,CompactMinus0352.checked352,CompactMinus0352.small352,CompactMinus0352.nodes352,NodeMinus05.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p353,GridMinus.atNode 353,GridMinus.atNode 354,NodeMinus05.w33,CompactMinus0352.checked353,CompactMinus0352.small353,CompactMinus0352.nodes353,NodeMinus05.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p354,GridMinus.atNode 354,GridMinus.atNode 355,NodeMinus05.w34,CompactMinus0352.checked354,CompactMinus0352.small354,CompactMinus0352.nodes354,NodeMinus05.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p355,GridMinus.atNode 355,GridMinus.atNode 356,NodeMinus05.w35,CompactMinus0352.checked355,CompactMinus0352.small355,CompactMinus0352.nodes355,NodeMinus05.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p356,GridMinus.atNode 356,GridMinus.atNode 357,NodeMinus05.w36,CompactMinus0352.checked356,CompactMinus0352.small356,CompactMinus0352.nodes356,NodeMinus05.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p357,GridMinus.atNode 357,GridMinus.atNode 358,NodeMinus05.w37,CompactMinus0352.checked357,CompactMinus0352.small357,CompactMinus0352.nodes357,NodeMinus05.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p358,GridMinus.atNode 358,GridMinus.atNode 359,NodeMinus05.w38,CompactMinus0352.checked358,CompactMinus0352.small358,CompactMinus0352.nodes358,NodeMinus05.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p359,GridMinus.atNode 359,GridMinus.atNode 360,NodeMinus05.w39,CompactMinus0352.checked359,CompactMinus0352.small359,CompactMinus0352.nodes359,NodeMinus05.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p360,GridMinus.atNode 360,GridMinus.atNode 361,NodeMinus05.w40,CompactMinus0352.checked360,CompactMinus0352.small360,CompactMinus0352.nodes360,NodeMinus05.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p361,GridMinus.atNode 361,GridMinus.atNode 362,NodeMinus05.w41,CompactMinus0352.checked361,CompactMinus0352.small361,CompactMinus0352.nodes361,NodeMinus05.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p362,GridMinus.atNode 362,GridMinus.atNode 363,NodeMinus05.w42,CompactMinus0352.checked362,CompactMinus0352.small362,CompactMinus0352.nodes362,NodeMinus05.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p363,GridMinus.atNode 363,GridMinus.atNode 364,NodeMinus05.w43,CompactMinus0352.checked363,CompactMinus0352.small363,CompactMinus0352.nodes363,NodeMinus05.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p364,GridMinus.atNode 364,GridMinus.atNode 365,NodeMinus05.w44,CompactMinus0352.checked364,CompactMinus0352.small364,CompactMinus0352.nodes364,NodeMinus05.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p365,GridMinus.atNode 365,GridMinus.atNode 366,NodeMinus05.w45,CompactMinus0352.checked365,CompactMinus0352.small365,CompactMinus0352.nodes365,NodeMinus05.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p366,GridMinus.atNode 366,GridMinus.atNode 367,NodeMinus05.w46,CompactMinus0352.checked366,CompactMinus0352.small366,CompactMinus0352.nodes366,NodeMinus05.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0352.p367,GridMinus.atNode 367,GridMinus.atNode 368,NodeMinus05.w47,CompactMinus0352.checked367,CompactMinus0352.small367,CompactMinus0352.nodes367,NodeMinus05.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p368,GridMinus.atNode 368,GridMinus.atNode 369,NodeMinus05.w48,CompactMinus0368.checked368,CompactMinus0368.small368,CompactMinus0368.nodes368,NodeMinus05.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p369,GridMinus.atNode 369,GridMinus.atNode 370,NodeMinus05.w49,CompactMinus0368.checked369,CompactMinus0368.small369,CompactMinus0368.nodes369,NodeMinus05.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p370,GridMinus.atNode 370,GridMinus.atNode 371,NodeMinus05.w50,CompactMinus0368.checked370,CompactMinus0368.small370,CompactMinus0368.nodes370,NodeMinus05.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p371,GridMinus.atNode 371,GridMinus.atNode 372,NodeMinus05.w51,CompactMinus0368.checked371,CompactMinus0368.small371,CompactMinus0368.nodes371,NodeMinus05.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p372,GridMinus.atNode 372,GridMinus.atNode 373,NodeMinus05.w52,CompactMinus0368.checked372,CompactMinus0368.small372,CompactMinus0368.nodes372,NodeMinus05.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p373,GridMinus.atNode 373,GridMinus.atNode 374,NodeMinus05.w53,CompactMinus0368.checked373,CompactMinus0368.small373,CompactMinus0368.nodes373,NodeMinus05.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p374,GridMinus.atNode 374,GridMinus.atNode 375,NodeMinus05.w54,CompactMinus0368.checked374,CompactMinus0368.small374,CompactMinus0368.nodes374,NodeMinus05.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p375,GridMinus.atNode 375,GridMinus.atNode 376,NodeMinus05.w55,CompactMinus0368.checked375,CompactMinus0368.small375,CompactMinus0368.nodes375,NodeMinus05.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p376,GridMinus.atNode 376,GridMinus.atNode 377,NodeMinus05.w56,CompactMinus0368.checked376,CompactMinus0368.small376,CompactMinus0368.nodes376,NodeMinus05.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p377,GridMinus.atNode 377,GridMinus.atNode 378,NodeMinus05.w57,CompactMinus0368.checked377,CompactMinus0368.small377,CompactMinus0368.nodes377,NodeMinus05.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p378,GridMinus.atNode 378,GridMinus.atNode 379,NodeMinus05.w58,CompactMinus0368.checked378,CompactMinus0368.small378,CompactMinus0368.nodes378,NodeMinus05.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p379,GridMinus.atNode 379,GridMinus.atNode 380,NodeMinus05.w59,CompactMinus0368.checked379,CompactMinus0368.small379,CompactMinus0368.nodes379,NodeMinus05.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p380,GridMinus.atNode 380,GridMinus.atNode 381,NodeMinus05.w60,CompactMinus0368.checked380,CompactMinus0368.small380,CompactMinus0368.nodes380,NodeMinus05.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p381,GridMinus.atNode 381,GridMinus.atNode 382,NodeMinus05.w61,CompactMinus0368.checked381,CompactMinus0368.small381,CompactMinus0368.nodes381,NodeMinus05.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p382,GridMinus.atNode 382,GridMinus.atNode 383,NodeMinus05.w62,CompactMinus0368.checked382,CompactMinus0368.small382,CompactMinus0368.nodes382,NodeMinus05.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0368.p383,GridMinus.atNode 383,GridMinus.atNode 384,NodeMinus05.w63,CompactMinus0368.checked383,CompactMinus0368.small383,CompactMinus0368.nodes383,NodeMinus05.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (320+j) ∧
    (atRow j).right=GridMinus.atNode (320+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus05
