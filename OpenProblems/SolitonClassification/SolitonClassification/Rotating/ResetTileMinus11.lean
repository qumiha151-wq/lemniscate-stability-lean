import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0704
import SolitonClassification.Rotating.ResetPackedMinus0720
import SolitonClassification.Rotating.ResetPackedMinus0736
import SolitonClassification.Rotating.ResetPackedMinus0752
namespace SolitonClassification.Rotating.DyadicReset.TileMinus11
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p704,GridMinus.atNode 704,GridMinus.atNode 705,NodeMinus11.w0,CompactMinus0704.checked704,CompactMinus0704.small704,CompactMinus0704.nodes704,NodeMinus11.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p705,GridMinus.atNode 705,GridMinus.atNode 706,NodeMinus11.w1,CompactMinus0704.checked705,CompactMinus0704.small705,CompactMinus0704.nodes705,NodeMinus11.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p706,GridMinus.atNode 706,GridMinus.atNode 707,NodeMinus11.w2,CompactMinus0704.checked706,CompactMinus0704.small706,CompactMinus0704.nodes706,NodeMinus11.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p707,GridMinus.atNode 707,GridMinus.atNode 708,NodeMinus11.w3,CompactMinus0704.checked707,CompactMinus0704.small707,CompactMinus0704.nodes707,NodeMinus11.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p708,GridMinus.atNode 708,GridMinus.atNode 709,NodeMinus11.w4,CompactMinus0704.checked708,CompactMinus0704.small708,CompactMinus0704.nodes708,NodeMinus11.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p709,GridMinus.atNode 709,GridMinus.atNode 710,NodeMinus11.w5,CompactMinus0704.checked709,CompactMinus0704.small709,CompactMinus0704.nodes709,NodeMinus11.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p710,GridMinus.atNode 710,GridMinus.atNode 711,NodeMinus11.w6,CompactMinus0704.checked710,CompactMinus0704.small710,CompactMinus0704.nodes710,NodeMinus11.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p711,GridMinus.atNode 711,GridMinus.atNode 712,NodeMinus11.w7,CompactMinus0704.checked711,CompactMinus0704.small711,CompactMinus0704.nodes711,NodeMinus11.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p712,GridMinus.atNode 712,GridMinus.atNode 713,NodeMinus11.w8,CompactMinus0704.checked712,CompactMinus0704.small712,CompactMinus0704.nodes712,NodeMinus11.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p713,GridMinus.atNode 713,GridMinus.atNode 714,NodeMinus11.w9,CompactMinus0704.checked713,CompactMinus0704.small713,CompactMinus0704.nodes713,NodeMinus11.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p714,GridMinus.atNode 714,GridMinus.atNode 715,NodeMinus11.w10,CompactMinus0704.checked714,CompactMinus0704.small714,CompactMinus0704.nodes714,NodeMinus11.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p715,GridMinus.atNode 715,GridMinus.atNode 716,NodeMinus11.w11,CompactMinus0704.checked715,CompactMinus0704.small715,CompactMinus0704.nodes715,NodeMinus11.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p716,GridMinus.atNode 716,GridMinus.atNode 717,NodeMinus11.w12,CompactMinus0704.checked716,CompactMinus0704.small716,CompactMinus0704.nodes716,NodeMinus11.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p717,GridMinus.atNode 717,GridMinus.atNode 718,NodeMinus11.w13,CompactMinus0704.checked717,CompactMinus0704.small717,CompactMinus0704.nodes717,NodeMinus11.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p718,GridMinus.atNode 718,GridMinus.atNode 719,NodeMinus11.w14,CompactMinus0704.checked718,CompactMinus0704.small718,CompactMinus0704.nodes718,NodeMinus11.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0704.p719,GridMinus.atNode 719,GridMinus.atNode 720,NodeMinus11.w15,CompactMinus0704.checked719,CompactMinus0704.small719,CompactMinus0704.nodes719,NodeMinus11.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p720,GridMinus.atNode 720,GridMinus.atNode 721,NodeMinus11.w16,CompactMinus0720.checked720,CompactMinus0720.small720,CompactMinus0720.nodes720,NodeMinus11.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p721,GridMinus.atNode 721,GridMinus.atNode 722,NodeMinus11.w17,CompactMinus0720.checked721,CompactMinus0720.small721,CompactMinus0720.nodes721,NodeMinus11.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p722,GridMinus.atNode 722,GridMinus.atNode 723,NodeMinus11.w18,CompactMinus0720.checked722,CompactMinus0720.small722,CompactMinus0720.nodes722,NodeMinus11.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p723,GridMinus.atNode 723,GridMinus.atNode 724,NodeMinus11.w19,CompactMinus0720.checked723,CompactMinus0720.small723,CompactMinus0720.nodes723,NodeMinus11.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p724,GridMinus.atNode 724,GridMinus.atNode 725,NodeMinus11.w20,CompactMinus0720.checked724,CompactMinus0720.small724,CompactMinus0720.nodes724,NodeMinus11.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p725,GridMinus.atNode 725,GridMinus.atNode 726,NodeMinus11.w21,CompactMinus0720.checked725,CompactMinus0720.small725,CompactMinus0720.nodes725,NodeMinus11.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p726,GridMinus.atNode 726,GridMinus.atNode 727,NodeMinus11.w22,CompactMinus0720.checked726,CompactMinus0720.small726,CompactMinus0720.nodes726,NodeMinus11.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p727,GridMinus.atNode 727,GridMinus.atNode 728,NodeMinus11.w23,CompactMinus0720.checked727,CompactMinus0720.small727,CompactMinus0720.nodes727,NodeMinus11.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p728,GridMinus.atNode 728,GridMinus.atNode 729,NodeMinus11.w24,CompactMinus0720.checked728,CompactMinus0720.small728,CompactMinus0720.nodes728,NodeMinus11.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p729,GridMinus.atNode 729,GridMinus.atNode 730,NodeMinus11.w25,CompactMinus0720.checked729,CompactMinus0720.small729,CompactMinus0720.nodes729,NodeMinus11.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p730,GridMinus.atNode 730,GridMinus.atNode 731,NodeMinus11.w26,CompactMinus0720.checked730,CompactMinus0720.small730,CompactMinus0720.nodes730,NodeMinus11.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p731,GridMinus.atNode 731,GridMinus.atNode 732,NodeMinus11.w27,CompactMinus0720.checked731,CompactMinus0720.small731,CompactMinus0720.nodes731,NodeMinus11.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p732,GridMinus.atNode 732,GridMinus.atNode 733,NodeMinus11.w28,CompactMinus0720.checked732,CompactMinus0720.small732,CompactMinus0720.nodes732,NodeMinus11.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p733,GridMinus.atNode 733,GridMinus.atNode 734,NodeMinus11.w29,CompactMinus0720.checked733,CompactMinus0720.small733,CompactMinus0720.nodes733,NodeMinus11.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p734,GridMinus.atNode 734,GridMinus.atNode 735,NodeMinus11.w30,CompactMinus0720.checked734,CompactMinus0720.small734,CompactMinus0720.nodes734,NodeMinus11.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0720.p735,GridMinus.atNode 735,GridMinus.atNode 736,NodeMinus11.w31,CompactMinus0720.checked735,CompactMinus0720.small735,CompactMinus0720.nodes735,NodeMinus11.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p736,GridMinus.atNode 736,GridMinus.atNode 737,NodeMinus11.w32,CompactMinus0736.checked736,CompactMinus0736.small736,CompactMinus0736.nodes736,NodeMinus11.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p737,GridMinus.atNode 737,GridMinus.atNode 738,NodeMinus11.w33,CompactMinus0736.checked737,CompactMinus0736.small737,CompactMinus0736.nodes737,NodeMinus11.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p738,GridMinus.atNode 738,GridMinus.atNode 739,NodeMinus11.w34,CompactMinus0736.checked738,CompactMinus0736.small738,CompactMinus0736.nodes738,NodeMinus11.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p739,GridMinus.atNode 739,GridMinus.atNode 740,NodeMinus11.w35,CompactMinus0736.checked739,CompactMinus0736.small739,CompactMinus0736.nodes739,NodeMinus11.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p740,GridMinus.atNode 740,GridMinus.atNode 741,NodeMinus11.w36,CompactMinus0736.checked740,CompactMinus0736.small740,CompactMinus0736.nodes740,NodeMinus11.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p741,GridMinus.atNode 741,GridMinus.atNode 742,NodeMinus11.w37,CompactMinus0736.checked741,CompactMinus0736.small741,CompactMinus0736.nodes741,NodeMinus11.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p742,GridMinus.atNode 742,GridMinus.atNode 743,NodeMinus11.w38,CompactMinus0736.checked742,CompactMinus0736.small742,CompactMinus0736.nodes742,NodeMinus11.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p743,GridMinus.atNode 743,GridMinus.atNode 744,NodeMinus11.w39,CompactMinus0736.checked743,CompactMinus0736.small743,CompactMinus0736.nodes743,NodeMinus11.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p744,GridMinus.atNode 744,GridMinus.atNode 745,NodeMinus11.w40,CompactMinus0736.checked744,CompactMinus0736.small744,CompactMinus0736.nodes744,NodeMinus11.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p745,GridMinus.atNode 745,GridMinus.atNode 746,NodeMinus11.w41,CompactMinus0736.checked745,CompactMinus0736.small745,CompactMinus0736.nodes745,NodeMinus11.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p746,GridMinus.atNode 746,GridMinus.atNode 747,NodeMinus11.w42,CompactMinus0736.checked746,CompactMinus0736.small746,CompactMinus0736.nodes746,NodeMinus11.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p747,GridMinus.atNode 747,GridMinus.atNode 748,NodeMinus11.w43,CompactMinus0736.checked747,CompactMinus0736.small747,CompactMinus0736.nodes747,NodeMinus11.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p748,GridMinus.atNode 748,GridMinus.atNode 749,NodeMinus11.w44,CompactMinus0736.checked748,CompactMinus0736.small748,CompactMinus0736.nodes748,NodeMinus11.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p749,GridMinus.atNode 749,GridMinus.atNode 750,NodeMinus11.w45,CompactMinus0736.checked749,CompactMinus0736.small749,CompactMinus0736.nodes749,NodeMinus11.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p750,GridMinus.atNode 750,GridMinus.atNode 751,NodeMinus11.w46,CompactMinus0736.checked750,CompactMinus0736.small750,CompactMinus0736.nodes750,NodeMinus11.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0736.p751,GridMinus.atNode 751,GridMinus.atNode 752,NodeMinus11.w47,CompactMinus0736.checked751,CompactMinus0736.small751,CompactMinus0736.nodes751,NodeMinus11.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p752,GridMinus.atNode 752,GridMinus.atNode 753,NodeMinus11.w48,CompactMinus0752.checked752,CompactMinus0752.small752,CompactMinus0752.nodes752,NodeMinus11.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p753,GridMinus.atNode 753,GridMinus.atNode 754,NodeMinus11.w49,CompactMinus0752.checked753,CompactMinus0752.small753,CompactMinus0752.nodes753,NodeMinus11.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p754,GridMinus.atNode 754,GridMinus.atNode 755,NodeMinus11.w50,CompactMinus0752.checked754,CompactMinus0752.small754,CompactMinus0752.nodes754,NodeMinus11.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p755,GridMinus.atNode 755,GridMinus.atNode 756,NodeMinus11.w51,CompactMinus0752.checked755,CompactMinus0752.small755,CompactMinus0752.nodes755,NodeMinus11.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p756,GridMinus.atNode 756,GridMinus.atNode 757,NodeMinus11.w52,CompactMinus0752.checked756,CompactMinus0752.small756,CompactMinus0752.nodes756,NodeMinus11.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p757,GridMinus.atNode 757,GridMinus.atNode 758,NodeMinus11.w53,CompactMinus0752.checked757,CompactMinus0752.small757,CompactMinus0752.nodes757,NodeMinus11.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p758,GridMinus.atNode 758,GridMinus.atNode 759,NodeMinus11.w54,CompactMinus0752.checked758,CompactMinus0752.small758,CompactMinus0752.nodes758,NodeMinus11.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p759,GridMinus.atNode 759,GridMinus.atNode 760,NodeMinus11.w55,CompactMinus0752.checked759,CompactMinus0752.small759,CompactMinus0752.nodes759,NodeMinus11.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p760,GridMinus.atNode 760,GridMinus.atNode 761,NodeMinus11.w56,CompactMinus0752.checked760,CompactMinus0752.small760,CompactMinus0752.nodes760,NodeMinus11.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p761,GridMinus.atNode 761,GridMinus.atNode 762,NodeMinus11.w57,CompactMinus0752.checked761,CompactMinus0752.small761,CompactMinus0752.nodes761,NodeMinus11.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p762,GridMinus.atNode 762,GridMinus.atNode 763,NodeMinus11.w58,CompactMinus0752.checked762,CompactMinus0752.small762,CompactMinus0752.nodes762,NodeMinus11.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p763,GridMinus.atNode 763,GridMinus.atNode 764,NodeMinus11.w59,CompactMinus0752.checked763,CompactMinus0752.small763,CompactMinus0752.nodes763,NodeMinus11.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p764,GridMinus.atNode 764,GridMinus.atNode 765,NodeMinus11.w60,CompactMinus0752.checked764,CompactMinus0752.small764,CompactMinus0752.nodes764,NodeMinus11.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p765,GridMinus.atNode 765,GridMinus.atNode 766,NodeMinus11.w61,CompactMinus0752.checked765,CompactMinus0752.small765,CompactMinus0752.nodes765,NodeMinus11.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p766,GridMinus.atNode 766,GridMinus.atNode 767,NodeMinus11.w62,CompactMinus0752.checked766,CompactMinus0752.small766,CompactMinus0752.nodes766,NodeMinus11.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0752.p767,GridMinus.atNode 767,GridMinus.atNode 768,NodeMinus11.w63,CompactMinus0752.checked767,CompactMinus0752.small767,CompactMinus0752.nodes767,NodeMinus11.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (704+j) ∧
    (atRow j).right=GridMinus.atNode (704+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus11
