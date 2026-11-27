import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0704
import SolitonClassification.Rotating.ResetPackedPlus0720
import SolitonClassification.Rotating.ResetPackedPlus0736
import SolitonClassification.Rotating.ResetPackedPlus0752
namespace SolitonClassification.Rotating.DyadicReset.TilePlus11
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p704,GridPlus.atNode 704,GridPlus.atNode 705,NodePlus11.w0,CompactPlus0704.checked704,CompactPlus0704.small704,CompactPlus0704.nodes704,NodePlus11.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p705,GridPlus.atNode 705,GridPlus.atNode 706,NodePlus11.w1,CompactPlus0704.checked705,CompactPlus0704.small705,CompactPlus0704.nodes705,NodePlus11.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p706,GridPlus.atNode 706,GridPlus.atNode 707,NodePlus11.w2,CompactPlus0704.checked706,CompactPlus0704.small706,CompactPlus0704.nodes706,NodePlus11.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p707,GridPlus.atNode 707,GridPlus.atNode 708,NodePlus11.w3,CompactPlus0704.checked707,CompactPlus0704.small707,CompactPlus0704.nodes707,NodePlus11.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p708,GridPlus.atNode 708,GridPlus.atNode 709,NodePlus11.w4,CompactPlus0704.checked708,CompactPlus0704.small708,CompactPlus0704.nodes708,NodePlus11.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p709,GridPlus.atNode 709,GridPlus.atNode 710,NodePlus11.w5,CompactPlus0704.checked709,CompactPlus0704.small709,CompactPlus0704.nodes709,NodePlus11.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p710,GridPlus.atNode 710,GridPlus.atNode 711,NodePlus11.w6,CompactPlus0704.checked710,CompactPlus0704.small710,CompactPlus0704.nodes710,NodePlus11.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p711,GridPlus.atNode 711,GridPlus.atNode 712,NodePlus11.w7,CompactPlus0704.checked711,CompactPlus0704.small711,CompactPlus0704.nodes711,NodePlus11.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p712,GridPlus.atNode 712,GridPlus.atNode 713,NodePlus11.w8,CompactPlus0704.checked712,CompactPlus0704.small712,CompactPlus0704.nodes712,NodePlus11.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p713,GridPlus.atNode 713,GridPlus.atNode 714,NodePlus11.w9,CompactPlus0704.checked713,CompactPlus0704.small713,CompactPlus0704.nodes713,NodePlus11.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p714,GridPlus.atNode 714,GridPlus.atNode 715,NodePlus11.w10,CompactPlus0704.checked714,CompactPlus0704.small714,CompactPlus0704.nodes714,NodePlus11.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p715,GridPlus.atNode 715,GridPlus.atNode 716,NodePlus11.w11,CompactPlus0704.checked715,CompactPlus0704.small715,CompactPlus0704.nodes715,NodePlus11.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p716,GridPlus.atNode 716,GridPlus.atNode 717,NodePlus11.w12,CompactPlus0704.checked716,CompactPlus0704.small716,CompactPlus0704.nodes716,NodePlus11.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p717,GridPlus.atNode 717,GridPlus.atNode 718,NodePlus11.w13,CompactPlus0704.checked717,CompactPlus0704.small717,CompactPlus0704.nodes717,NodePlus11.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p718,GridPlus.atNode 718,GridPlus.atNode 719,NodePlus11.w14,CompactPlus0704.checked718,CompactPlus0704.small718,CompactPlus0704.nodes718,NodePlus11.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0704.p719,GridPlus.atNode 719,GridPlus.atNode 720,NodePlus11.w15,CompactPlus0704.checked719,CompactPlus0704.small719,CompactPlus0704.nodes719,NodePlus11.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p720,GridPlus.atNode 720,GridPlus.atNode 721,NodePlus11.w16,CompactPlus0720.checked720,CompactPlus0720.small720,CompactPlus0720.nodes720,NodePlus11.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p721,GridPlus.atNode 721,GridPlus.atNode 722,NodePlus11.w17,CompactPlus0720.checked721,CompactPlus0720.small721,CompactPlus0720.nodes721,NodePlus11.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p722,GridPlus.atNode 722,GridPlus.atNode 723,NodePlus11.w18,CompactPlus0720.checked722,CompactPlus0720.small722,CompactPlus0720.nodes722,NodePlus11.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p723,GridPlus.atNode 723,GridPlus.atNode 724,NodePlus11.w19,CompactPlus0720.checked723,CompactPlus0720.small723,CompactPlus0720.nodes723,NodePlus11.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p724,GridPlus.atNode 724,GridPlus.atNode 725,NodePlus11.w20,CompactPlus0720.checked724,CompactPlus0720.small724,CompactPlus0720.nodes724,NodePlus11.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p725,GridPlus.atNode 725,GridPlus.atNode 726,NodePlus11.w21,CompactPlus0720.checked725,CompactPlus0720.small725,CompactPlus0720.nodes725,NodePlus11.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p726,GridPlus.atNode 726,GridPlus.atNode 727,NodePlus11.w22,CompactPlus0720.checked726,CompactPlus0720.small726,CompactPlus0720.nodes726,NodePlus11.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p727,GridPlus.atNode 727,GridPlus.atNode 728,NodePlus11.w23,CompactPlus0720.checked727,CompactPlus0720.small727,CompactPlus0720.nodes727,NodePlus11.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p728,GridPlus.atNode 728,GridPlus.atNode 729,NodePlus11.w24,CompactPlus0720.checked728,CompactPlus0720.small728,CompactPlus0720.nodes728,NodePlus11.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p729,GridPlus.atNode 729,GridPlus.atNode 730,NodePlus11.w25,CompactPlus0720.checked729,CompactPlus0720.small729,CompactPlus0720.nodes729,NodePlus11.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p730,GridPlus.atNode 730,GridPlus.atNode 731,NodePlus11.w26,CompactPlus0720.checked730,CompactPlus0720.small730,CompactPlus0720.nodes730,NodePlus11.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p731,GridPlus.atNode 731,GridPlus.atNode 732,NodePlus11.w27,CompactPlus0720.checked731,CompactPlus0720.small731,CompactPlus0720.nodes731,NodePlus11.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p732,GridPlus.atNode 732,GridPlus.atNode 733,NodePlus11.w28,CompactPlus0720.checked732,CompactPlus0720.small732,CompactPlus0720.nodes732,NodePlus11.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p733,GridPlus.atNode 733,GridPlus.atNode 734,NodePlus11.w29,CompactPlus0720.checked733,CompactPlus0720.small733,CompactPlus0720.nodes733,NodePlus11.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p734,GridPlus.atNode 734,GridPlus.atNode 735,NodePlus11.w30,CompactPlus0720.checked734,CompactPlus0720.small734,CompactPlus0720.nodes734,NodePlus11.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0720.p735,GridPlus.atNode 735,GridPlus.atNode 736,NodePlus11.w31,CompactPlus0720.checked735,CompactPlus0720.small735,CompactPlus0720.nodes735,NodePlus11.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p736,GridPlus.atNode 736,GridPlus.atNode 737,NodePlus11.w32,CompactPlus0736.checked736,CompactPlus0736.small736,CompactPlus0736.nodes736,NodePlus11.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p737,GridPlus.atNode 737,GridPlus.atNode 738,NodePlus11.w33,CompactPlus0736.checked737,CompactPlus0736.small737,CompactPlus0736.nodes737,NodePlus11.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p738,GridPlus.atNode 738,GridPlus.atNode 739,NodePlus11.w34,CompactPlus0736.checked738,CompactPlus0736.small738,CompactPlus0736.nodes738,NodePlus11.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p739,GridPlus.atNode 739,GridPlus.atNode 740,NodePlus11.w35,CompactPlus0736.checked739,CompactPlus0736.small739,CompactPlus0736.nodes739,NodePlus11.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p740,GridPlus.atNode 740,GridPlus.atNode 741,NodePlus11.w36,CompactPlus0736.checked740,CompactPlus0736.small740,CompactPlus0736.nodes740,NodePlus11.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p741,GridPlus.atNode 741,GridPlus.atNode 742,NodePlus11.w37,CompactPlus0736.checked741,CompactPlus0736.small741,CompactPlus0736.nodes741,NodePlus11.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p742,GridPlus.atNode 742,GridPlus.atNode 743,NodePlus11.w38,CompactPlus0736.checked742,CompactPlus0736.small742,CompactPlus0736.nodes742,NodePlus11.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p743,GridPlus.atNode 743,GridPlus.atNode 744,NodePlus11.w39,CompactPlus0736.checked743,CompactPlus0736.small743,CompactPlus0736.nodes743,NodePlus11.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p744,GridPlus.atNode 744,GridPlus.atNode 745,NodePlus11.w40,CompactPlus0736.checked744,CompactPlus0736.small744,CompactPlus0736.nodes744,NodePlus11.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p745,GridPlus.atNode 745,GridPlus.atNode 746,NodePlus11.w41,CompactPlus0736.checked745,CompactPlus0736.small745,CompactPlus0736.nodes745,NodePlus11.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p746,GridPlus.atNode 746,GridPlus.atNode 747,NodePlus11.w42,CompactPlus0736.checked746,CompactPlus0736.small746,CompactPlus0736.nodes746,NodePlus11.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p747,GridPlus.atNode 747,GridPlus.atNode 748,NodePlus11.w43,CompactPlus0736.checked747,CompactPlus0736.small747,CompactPlus0736.nodes747,NodePlus11.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p748,GridPlus.atNode 748,GridPlus.atNode 749,NodePlus11.w44,CompactPlus0736.checked748,CompactPlus0736.small748,CompactPlus0736.nodes748,NodePlus11.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p749,GridPlus.atNode 749,GridPlus.atNode 750,NodePlus11.w45,CompactPlus0736.checked749,CompactPlus0736.small749,CompactPlus0736.nodes749,NodePlus11.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p750,GridPlus.atNode 750,GridPlus.atNode 751,NodePlus11.w46,CompactPlus0736.checked750,CompactPlus0736.small750,CompactPlus0736.nodes750,NodePlus11.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0736.p751,GridPlus.atNode 751,GridPlus.atNode 752,NodePlus11.w47,CompactPlus0736.checked751,CompactPlus0736.small751,CompactPlus0736.nodes751,NodePlus11.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p752,GridPlus.atNode 752,GridPlus.atNode 753,NodePlus11.w48,CompactPlus0752.checked752,CompactPlus0752.small752,CompactPlus0752.nodes752,NodePlus11.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p753,GridPlus.atNode 753,GridPlus.atNode 754,NodePlus11.w49,CompactPlus0752.checked753,CompactPlus0752.small753,CompactPlus0752.nodes753,NodePlus11.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p754,GridPlus.atNode 754,GridPlus.atNode 755,NodePlus11.w50,CompactPlus0752.checked754,CompactPlus0752.small754,CompactPlus0752.nodes754,NodePlus11.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p755,GridPlus.atNode 755,GridPlus.atNode 756,NodePlus11.w51,CompactPlus0752.checked755,CompactPlus0752.small755,CompactPlus0752.nodes755,NodePlus11.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p756,GridPlus.atNode 756,GridPlus.atNode 757,NodePlus11.w52,CompactPlus0752.checked756,CompactPlus0752.small756,CompactPlus0752.nodes756,NodePlus11.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p757,GridPlus.atNode 757,GridPlus.atNode 758,NodePlus11.w53,CompactPlus0752.checked757,CompactPlus0752.small757,CompactPlus0752.nodes757,NodePlus11.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p758,GridPlus.atNode 758,GridPlus.atNode 759,NodePlus11.w54,CompactPlus0752.checked758,CompactPlus0752.small758,CompactPlus0752.nodes758,NodePlus11.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p759,GridPlus.atNode 759,GridPlus.atNode 760,NodePlus11.w55,CompactPlus0752.checked759,CompactPlus0752.small759,CompactPlus0752.nodes759,NodePlus11.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p760,GridPlus.atNode 760,GridPlus.atNode 761,NodePlus11.w56,CompactPlus0752.checked760,CompactPlus0752.small760,CompactPlus0752.nodes760,NodePlus11.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p761,GridPlus.atNode 761,GridPlus.atNode 762,NodePlus11.w57,CompactPlus0752.checked761,CompactPlus0752.small761,CompactPlus0752.nodes761,NodePlus11.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p762,GridPlus.atNode 762,GridPlus.atNode 763,NodePlus11.w58,CompactPlus0752.checked762,CompactPlus0752.small762,CompactPlus0752.nodes762,NodePlus11.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p763,GridPlus.atNode 763,GridPlus.atNode 764,NodePlus11.w59,CompactPlus0752.checked763,CompactPlus0752.small763,CompactPlus0752.nodes763,NodePlus11.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p764,GridPlus.atNode 764,GridPlus.atNode 765,NodePlus11.w60,CompactPlus0752.checked764,CompactPlus0752.small764,CompactPlus0752.nodes764,NodePlus11.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p765,GridPlus.atNode 765,GridPlus.atNode 766,NodePlus11.w61,CompactPlus0752.checked765,CompactPlus0752.small765,CompactPlus0752.nodes765,NodePlus11.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p766,GridPlus.atNode 766,GridPlus.atNode 767,NodePlus11.w62,CompactPlus0752.checked766,CompactPlus0752.small766,CompactPlus0752.nodes766,NodePlus11.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0752.p767,GridPlus.atNode 767,GridPlus.atNode 768,NodePlus11.w63,CompactPlus0752.checked767,CompactPlus0752.small767,CompactPlus0752.nodes767,NodePlus11.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (704+j) ∧
    (atRow j).right=GridPlus.atNode (704+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus11
