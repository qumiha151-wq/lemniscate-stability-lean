import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0320
import SolitonClassification.Rotating.ResetPackedPlus0336
import SolitonClassification.Rotating.ResetPackedPlus0352
import SolitonClassification.Rotating.ResetPackedPlus0368
namespace SolitonClassification.Rotating.DyadicReset.TilePlus05
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p320,GridPlus.atNode 320,GridPlus.atNode 321,NodePlus05.w0,CompactPlus0320.checked320,CompactPlus0320.small320,CompactPlus0320.nodes320,NodePlus05.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p321,GridPlus.atNode 321,GridPlus.atNode 322,NodePlus05.w1,CompactPlus0320.checked321,CompactPlus0320.small321,CompactPlus0320.nodes321,NodePlus05.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p322,GridPlus.atNode 322,GridPlus.atNode 323,NodePlus05.w2,CompactPlus0320.checked322,CompactPlus0320.small322,CompactPlus0320.nodes322,NodePlus05.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p323,GridPlus.atNode 323,GridPlus.atNode 324,NodePlus05.w3,CompactPlus0320.checked323,CompactPlus0320.small323,CompactPlus0320.nodes323,NodePlus05.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p324,GridPlus.atNode 324,GridPlus.atNode 325,NodePlus05.w4,CompactPlus0320.checked324,CompactPlus0320.small324,CompactPlus0320.nodes324,NodePlus05.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p325,GridPlus.atNode 325,GridPlus.atNode 326,NodePlus05.w5,CompactPlus0320.checked325,CompactPlus0320.small325,CompactPlus0320.nodes325,NodePlus05.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p326,GridPlus.atNode 326,GridPlus.atNode 327,NodePlus05.w6,CompactPlus0320.checked326,CompactPlus0320.small326,CompactPlus0320.nodes326,NodePlus05.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p327,GridPlus.atNode 327,GridPlus.atNode 328,NodePlus05.w7,CompactPlus0320.checked327,CompactPlus0320.small327,CompactPlus0320.nodes327,NodePlus05.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p328,GridPlus.atNode 328,GridPlus.atNode 329,NodePlus05.w8,CompactPlus0320.checked328,CompactPlus0320.small328,CompactPlus0320.nodes328,NodePlus05.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p329,GridPlus.atNode 329,GridPlus.atNode 330,NodePlus05.w9,CompactPlus0320.checked329,CompactPlus0320.small329,CompactPlus0320.nodes329,NodePlus05.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p330,GridPlus.atNode 330,GridPlus.atNode 331,NodePlus05.w10,CompactPlus0320.checked330,CompactPlus0320.small330,CompactPlus0320.nodes330,NodePlus05.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p331,GridPlus.atNode 331,GridPlus.atNode 332,NodePlus05.w11,CompactPlus0320.checked331,CompactPlus0320.small331,CompactPlus0320.nodes331,NodePlus05.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p332,GridPlus.atNode 332,GridPlus.atNode 333,NodePlus05.w12,CompactPlus0320.checked332,CompactPlus0320.small332,CompactPlus0320.nodes332,NodePlus05.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p333,GridPlus.atNode 333,GridPlus.atNode 334,NodePlus05.w13,CompactPlus0320.checked333,CompactPlus0320.small333,CompactPlus0320.nodes333,NodePlus05.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p334,GridPlus.atNode 334,GridPlus.atNode 335,NodePlus05.w14,CompactPlus0320.checked334,CompactPlus0320.small334,CompactPlus0320.nodes334,NodePlus05.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0320.p335,GridPlus.atNode 335,GridPlus.atNode 336,NodePlus05.w15,CompactPlus0320.checked335,CompactPlus0320.small335,CompactPlus0320.nodes335,NodePlus05.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p336,GridPlus.atNode 336,GridPlus.atNode 337,NodePlus05.w16,CompactPlus0336.checked336,CompactPlus0336.small336,CompactPlus0336.nodes336,NodePlus05.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p337,GridPlus.atNode 337,GridPlus.atNode 338,NodePlus05.w17,CompactPlus0336.checked337,CompactPlus0336.small337,CompactPlus0336.nodes337,NodePlus05.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p338,GridPlus.atNode 338,GridPlus.atNode 339,NodePlus05.w18,CompactPlus0336.checked338,CompactPlus0336.small338,CompactPlus0336.nodes338,NodePlus05.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p339,GridPlus.atNode 339,GridPlus.atNode 340,NodePlus05.w19,CompactPlus0336.checked339,CompactPlus0336.small339,CompactPlus0336.nodes339,NodePlus05.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p340,GridPlus.atNode 340,GridPlus.atNode 341,NodePlus05.w20,CompactPlus0336.checked340,CompactPlus0336.small340,CompactPlus0336.nodes340,NodePlus05.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p341,GridPlus.atNode 341,GridPlus.atNode 342,NodePlus05.w21,CompactPlus0336.checked341,CompactPlus0336.small341,CompactPlus0336.nodes341,NodePlus05.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p342,GridPlus.atNode 342,GridPlus.atNode 343,NodePlus05.w22,CompactPlus0336.checked342,CompactPlus0336.small342,CompactPlus0336.nodes342,NodePlus05.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p343,GridPlus.atNode 343,GridPlus.atNode 344,NodePlus05.w23,CompactPlus0336.checked343,CompactPlus0336.small343,CompactPlus0336.nodes343,NodePlus05.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p344,GridPlus.atNode 344,GridPlus.atNode 345,NodePlus05.w24,CompactPlus0336.checked344,CompactPlus0336.small344,CompactPlus0336.nodes344,NodePlus05.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p345,GridPlus.atNode 345,GridPlus.atNode 346,NodePlus05.w25,CompactPlus0336.checked345,CompactPlus0336.small345,CompactPlus0336.nodes345,NodePlus05.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p346,GridPlus.atNode 346,GridPlus.atNode 347,NodePlus05.w26,CompactPlus0336.checked346,CompactPlus0336.small346,CompactPlus0336.nodes346,NodePlus05.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p347,GridPlus.atNode 347,GridPlus.atNode 348,NodePlus05.w27,CompactPlus0336.checked347,CompactPlus0336.small347,CompactPlus0336.nodes347,NodePlus05.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p348,GridPlus.atNode 348,GridPlus.atNode 349,NodePlus05.w28,CompactPlus0336.checked348,CompactPlus0336.small348,CompactPlus0336.nodes348,NodePlus05.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p349,GridPlus.atNode 349,GridPlus.atNode 350,NodePlus05.w29,CompactPlus0336.checked349,CompactPlus0336.small349,CompactPlus0336.nodes349,NodePlus05.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p350,GridPlus.atNode 350,GridPlus.atNode 351,NodePlus05.w30,CompactPlus0336.checked350,CompactPlus0336.small350,CompactPlus0336.nodes350,NodePlus05.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0336.p351,GridPlus.atNode 351,GridPlus.atNode 352,NodePlus05.w31,CompactPlus0336.checked351,CompactPlus0336.small351,CompactPlus0336.nodes351,NodePlus05.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p352,GridPlus.atNode 352,GridPlus.atNode 353,NodePlus05.w32,CompactPlus0352.checked352,CompactPlus0352.small352,CompactPlus0352.nodes352,NodePlus05.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p353,GridPlus.atNode 353,GridPlus.atNode 354,NodePlus05.w33,CompactPlus0352.checked353,CompactPlus0352.small353,CompactPlus0352.nodes353,NodePlus05.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p354,GridPlus.atNode 354,GridPlus.atNode 355,NodePlus05.w34,CompactPlus0352.checked354,CompactPlus0352.small354,CompactPlus0352.nodes354,NodePlus05.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p355,GridPlus.atNode 355,GridPlus.atNode 356,NodePlus05.w35,CompactPlus0352.checked355,CompactPlus0352.small355,CompactPlus0352.nodes355,NodePlus05.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p356,GridPlus.atNode 356,GridPlus.atNode 357,NodePlus05.w36,CompactPlus0352.checked356,CompactPlus0352.small356,CompactPlus0352.nodes356,NodePlus05.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p357,GridPlus.atNode 357,GridPlus.atNode 358,NodePlus05.w37,CompactPlus0352.checked357,CompactPlus0352.small357,CompactPlus0352.nodes357,NodePlus05.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p358,GridPlus.atNode 358,GridPlus.atNode 359,NodePlus05.w38,CompactPlus0352.checked358,CompactPlus0352.small358,CompactPlus0352.nodes358,NodePlus05.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p359,GridPlus.atNode 359,GridPlus.atNode 360,NodePlus05.w39,CompactPlus0352.checked359,CompactPlus0352.small359,CompactPlus0352.nodes359,NodePlus05.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p360,GridPlus.atNode 360,GridPlus.atNode 361,NodePlus05.w40,CompactPlus0352.checked360,CompactPlus0352.small360,CompactPlus0352.nodes360,NodePlus05.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p361,GridPlus.atNode 361,GridPlus.atNode 362,NodePlus05.w41,CompactPlus0352.checked361,CompactPlus0352.small361,CompactPlus0352.nodes361,NodePlus05.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p362,GridPlus.atNode 362,GridPlus.atNode 363,NodePlus05.w42,CompactPlus0352.checked362,CompactPlus0352.small362,CompactPlus0352.nodes362,NodePlus05.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p363,GridPlus.atNode 363,GridPlus.atNode 364,NodePlus05.w43,CompactPlus0352.checked363,CompactPlus0352.small363,CompactPlus0352.nodes363,NodePlus05.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p364,GridPlus.atNode 364,GridPlus.atNode 365,NodePlus05.w44,CompactPlus0352.checked364,CompactPlus0352.small364,CompactPlus0352.nodes364,NodePlus05.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p365,GridPlus.atNode 365,GridPlus.atNode 366,NodePlus05.w45,CompactPlus0352.checked365,CompactPlus0352.small365,CompactPlus0352.nodes365,NodePlus05.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p366,GridPlus.atNode 366,GridPlus.atNode 367,NodePlus05.w46,CompactPlus0352.checked366,CompactPlus0352.small366,CompactPlus0352.nodes366,NodePlus05.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0352.p367,GridPlus.atNode 367,GridPlus.atNode 368,NodePlus05.w47,CompactPlus0352.checked367,CompactPlus0352.small367,CompactPlus0352.nodes367,NodePlus05.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p368,GridPlus.atNode 368,GridPlus.atNode 369,NodePlus05.w48,CompactPlus0368.checked368,CompactPlus0368.small368,CompactPlus0368.nodes368,NodePlus05.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p369,GridPlus.atNode 369,GridPlus.atNode 370,NodePlus05.w49,CompactPlus0368.checked369,CompactPlus0368.small369,CompactPlus0368.nodes369,NodePlus05.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p370,GridPlus.atNode 370,GridPlus.atNode 371,NodePlus05.w50,CompactPlus0368.checked370,CompactPlus0368.small370,CompactPlus0368.nodes370,NodePlus05.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p371,GridPlus.atNode 371,GridPlus.atNode 372,NodePlus05.w51,CompactPlus0368.checked371,CompactPlus0368.small371,CompactPlus0368.nodes371,NodePlus05.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p372,GridPlus.atNode 372,GridPlus.atNode 373,NodePlus05.w52,CompactPlus0368.checked372,CompactPlus0368.small372,CompactPlus0368.nodes372,NodePlus05.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p373,GridPlus.atNode 373,GridPlus.atNode 374,NodePlus05.w53,CompactPlus0368.checked373,CompactPlus0368.small373,CompactPlus0368.nodes373,NodePlus05.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p374,GridPlus.atNode 374,GridPlus.atNode 375,NodePlus05.w54,CompactPlus0368.checked374,CompactPlus0368.small374,CompactPlus0368.nodes374,NodePlus05.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p375,GridPlus.atNode 375,GridPlus.atNode 376,NodePlus05.w55,CompactPlus0368.checked375,CompactPlus0368.small375,CompactPlus0368.nodes375,NodePlus05.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p376,GridPlus.atNode 376,GridPlus.atNode 377,NodePlus05.w56,CompactPlus0368.checked376,CompactPlus0368.small376,CompactPlus0368.nodes376,NodePlus05.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p377,GridPlus.atNode 377,GridPlus.atNode 378,NodePlus05.w57,CompactPlus0368.checked377,CompactPlus0368.small377,CompactPlus0368.nodes377,NodePlus05.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p378,GridPlus.atNode 378,GridPlus.atNode 379,NodePlus05.w58,CompactPlus0368.checked378,CompactPlus0368.small378,CompactPlus0368.nodes378,NodePlus05.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p379,GridPlus.atNode 379,GridPlus.atNode 380,NodePlus05.w59,CompactPlus0368.checked379,CompactPlus0368.small379,CompactPlus0368.nodes379,NodePlus05.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p380,GridPlus.atNode 380,GridPlus.atNode 381,NodePlus05.w60,CompactPlus0368.checked380,CompactPlus0368.small380,CompactPlus0368.nodes380,NodePlus05.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p381,GridPlus.atNode 381,GridPlus.atNode 382,NodePlus05.w61,CompactPlus0368.checked381,CompactPlus0368.small381,CompactPlus0368.nodes381,NodePlus05.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p382,GridPlus.atNode 382,GridPlus.atNode 383,NodePlus05.w62,CompactPlus0368.checked382,CompactPlus0368.small382,CompactPlus0368.nodes382,NodePlus05.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0368.p383,GridPlus.atNode 383,GridPlus.atNode 384,NodePlus05.w63,CompactPlus0368.checked383,CompactPlus0368.small383,CompactPlus0368.nodes383,NodePlus05.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (320+j) ∧
    (atRow j).right=GridPlus.atNode (320+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus05
