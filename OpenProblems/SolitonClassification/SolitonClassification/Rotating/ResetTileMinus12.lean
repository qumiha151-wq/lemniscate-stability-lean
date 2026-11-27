import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0768
import SolitonClassification.Rotating.ResetPackedMinus0784
import SolitonClassification.Rotating.ResetPackedMinus0800
import SolitonClassification.Rotating.ResetPackedMinus0816
namespace SolitonClassification.Rotating.DyadicReset.TileMinus12
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p768,GridMinus.atNode 768,GridMinus.atNode 769,NodeMinus12.w0,CompactMinus0768.checked768,CompactMinus0768.small768,CompactMinus0768.nodes768,NodeMinus12.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p769,GridMinus.atNode 769,GridMinus.atNode 770,NodeMinus12.w1,CompactMinus0768.checked769,CompactMinus0768.small769,CompactMinus0768.nodes769,NodeMinus12.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p770,GridMinus.atNode 770,GridMinus.atNode 771,NodeMinus12.w2,CompactMinus0768.checked770,CompactMinus0768.small770,CompactMinus0768.nodes770,NodeMinus12.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p771,GridMinus.atNode 771,GridMinus.atNode 772,NodeMinus12.w3,CompactMinus0768.checked771,CompactMinus0768.small771,CompactMinus0768.nodes771,NodeMinus12.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p772,GridMinus.atNode 772,GridMinus.atNode 773,NodeMinus12.w4,CompactMinus0768.checked772,CompactMinus0768.small772,CompactMinus0768.nodes772,NodeMinus12.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p773,GridMinus.atNode 773,GridMinus.atNode 774,NodeMinus12.w5,CompactMinus0768.checked773,CompactMinus0768.small773,CompactMinus0768.nodes773,NodeMinus12.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p774,GridMinus.atNode 774,GridMinus.atNode 775,NodeMinus12.w6,CompactMinus0768.checked774,CompactMinus0768.small774,CompactMinus0768.nodes774,NodeMinus12.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p775,GridMinus.atNode 775,GridMinus.atNode 776,NodeMinus12.w7,CompactMinus0768.checked775,CompactMinus0768.small775,CompactMinus0768.nodes775,NodeMinus12.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p776,GridMinus.atNode 776,GridMinus.atNode 777,NodeMinus12.w8,CompactMinus0768.checked776,CompactMinus0768.small776,CompactMinus0768.nodes776,NodeMinus12.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p777,GridMinus.atNode 777,GridMinus.atNode 778,NodeMinus12.w9,CompactMinus0768.checked777,CompactMinus0768.small777,CompactMinus0768.nodes777,NodeMinus12.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p778,GridMinus.atNode 778,GridMinus.atNode 779,NodeMinus12.w10,CompactMinus0768.checked778,CompactMinus0768.small778,CompactMinus0768.nodes778,NodeMinus12.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p779,GridMinus.atNode 779,GridMinus.atNode 780,NodeMinus12.w11,CompactMinus0768.checked779,CompactMinus0768.small779,CompactMinus0768.nodes779,NodeMinus12.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p780,GridMinus.atNode 780,GridMinus.atNode 781,NodeMinus12.w12,CompactMinus0768.checked780,CompactMinus0768.small780,CompactMinus0768.nodes780,NodeMinus12.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p781,GridMinus.atNode 781,GridMinus.atNode 782,NodeMinus12.w13,CompactMinus0768.checked781,CompactMinus0768.small781,CompactMinus0768.nodes781,NodeMinus12.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p782,GridMinus.atNode 782,GridMinus.atNode 783,NodeMinus12.w14,CompactMinus0768.checked782,CompactMinus0768.small782,CompactMinus0768.nodes782,NodeMinus12.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0768.p783,GridMinus.atNode 783,GridMinus.atNode 784,NodeMinus12.w15,CompactMinus0768.checked783,CompactMinus0768.small783,CompactMinus0768.nodes783,NodeMinus12.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p784,GridMinus.atNode 784,GridMinus.atNode 785,NodeMinus12.w16,CompactMinus0784.checked784,CompactMinus0784.small784,CompactMinus0784.nodes784,NodeMinus12.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p785,GridMinus.atNode 785,GridMinus.atNode 786,NodeMinus12.w17,CompactMinus0784.checked785,CompactMinus0784.small785,CompactMinus0784.nodes785,NodeMinus12.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p786,GridMinus.atNode 786,GridMinus.atNode 787,NodeMinus12.w18,CompactMinus0784.checked786,CompactMinus0784.small786,CompactMinus0784.nodes786,NodeMinus12.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p787,GridMinus.atNode 787,GridMinus.atNode 788,NodeMinus12.w19,CompactMinus0784.checked787,CompactMinus0784.small787,CompactMinus0784.nodes787,NodeMinus12.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p788,GridMinus.atNode 788,GridMinus.atNode 789,NodeMinus12.w20,CompactMinus0784.checked788,CompactMinus0784.small788,CompactMinus0784.nodes788,NodeMinus12.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p789,GridMinus.atNode 789,GridMinus.atNode 790,NodeMinus12.w21,CompactMinus0784.checked789,CompactMinus0784.small789,CompactMinus0784.nodes789,NodeMinus12.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p790,GridMinus.atNode 790,GridMinus.atNode 791,NodeMinus12.w22,CompactMinus0784.checked790,CompactMinus0784.small790,CompactMinus0784.nodes790,NodeMinus12.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p791,GridMinus.atNode 791,GridMinus.atNode 792,NodeMinus12.w23,CompactMinus0784.checked791,CompactMinus0784.small791,CompactMinus0784.nodes791,NodeMinus12.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p792,GridMinus.atNode 792,GridMinus.atNode 793,NodeMinus12.w24,CompactMinus0784.checked792,CompactMinus0784.small792,CompactMinus0784.nodes792,NodeMinus12.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p793,GridMinus.atNode 793,GridMinus.atNode 794,NodeMinus12.w25,CompactMinus0784.checked793,CompactMinus0784.small793,CompactMinus0784.nodes793,NodeMinus12.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p794,GridMinus.atNode 794,GridMinus.atNode 795,NodeMinus12.w26,CompactMinus0784.checked794,CompactMinus0784.small794,CompactMinus0784.nodes794,NodeMinus12.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p795,GridMinus.atNode 795,GridMinus.atNode 796,NodeMinus12.w27,CompactMinus0784.checked795,CompactMinus0784.small795,CompactMinus0784.nodes795,NodeMinus12.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p796,GridMinus.atNode 796,GridMinus.atNode 797,NodeMinus12.w28,CompactMinus0784.checked796,CompactMinus0784.small796,CompactMinus0784.nodes796,NodeMinus12.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p797,GridMinus.atNode 797,GridMinus.atNode 798,NodeMinus12.w29,CompactMinus0784.checked797,CompactMinus0784.small797,CompactMinus0784.nodes797,NodeMinus12.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p798,GridMinus.atNode 798,GridMinus.atNode 799,NodeMinus12.w30,CompactMinus0784.checked798,CompactMinus0784.small798,CompactMinus0784.nodes798,NodeMinus12.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0784.p799,GridMinus.atNode 799,GridMinus.atNode 800,NodeMinus12.w31,CompactMinus0784.checked799,CompactMinus0784.small799,CompactMinus0784.nodes799,NodeMinus12.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p800,GridMinus.atNode 800,GridMinus.atNode 801,NodeMinus12.w32,CompactMinus0800.checked800,CompactMinus0800.small800,CompactMinus0800.nodes800,NodeMinus12.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p801,GridMinus.atNode 801,GridMinus.atNode 802,NodeMinus12.w33,CompactMinus0800.checked801,CompactMinus0800.small801,CompactMinus0800.nodes801,NodeMinus12.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p802,GridMinus.atNode 802,GridMinus.atNode 803,NodeMinus12.w34,CompactMinus0800.checked802,CompactMinus0800.small802,CompactMinus0800.nodes802,NodeMinus12.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p803,GridMinus.atNode 803,GridMinus.atNode 804,NodeMinus12.w35,CompactMinus0800.checked803,CompactMinus0800.small803,CompactMinus0800.nodes803,NodeMinus12.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p804,GridMinus.atNode 804,GridMinus.atNode 805,NodeMinus12.w36,CompactMinus0800.checked804,CompactMinus0800.small804,CompactMinus0800.nodes804,NodeMinus12.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p805,GridMinus.atNode 805,GridMinus.atNode 806,NodeMinus12.w37,CompactMinus0800.checked805,CompactMinus0800.small805,CompactMinus0800.nodes805,NodeMinus12.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p806,GridMinus.atNode 806,GridMinus.atNode 807,NodeMinus12.w38,CompactMinus0800.checked806,CompactMinus0800.small806,CompactMinus0800.nodes806,NodeMinus12.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p807,GridMinus.atNode 807,GridMinus.atNode 808,NodeMinus12.w39,CompactMinus0800.checked807,CompactMinus0800.small807,CompactMinus0800.nodes807,NodeMinus12.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p808,GridMinus.atNode 808,GridMinus.atNode 809,NodeMinus12.w40,CompactMinus0800.checked808,CompactMinus0800.small808,CompactMinus0800.nodes808,NodeMinus12.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p809,GridMinus.atNode 809,GridMinus.atNode 810,NodeMinus12.w41,CompactMinus0800.checked809,CompactMinus0800.small809,CompactMinus0800.nodes809,NodeMinus12.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p810,GridMinus.atNode 810,GridMinus.atNode 811,NodeMinus12.w42,CompactMinus0800.checked810,CompactMinus0800.small810,CompactMinus0800.nodes810,NodeMinus12.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p811,GridMinus.atNode 811,GridMinus.atNode 812,NodeMinus12.w43,CompactMinus0800.checked811,CompactMinus0800.small811,CompactMinus0800.nodes811,NodeMinus12.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p812,GridMinus.atNode 812,GridMinus.atNode 813,NodeMinus12.w44,CompactMinus0800.checked812,CompactMinus0800.small812,CompactMinus0800.nodes812,NodeMinus12.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p813,GridMinus.atNode 813,GridMinus.atNode 814,NodeMinus12.w45,CompactMinus0800.checked813,CompactMinus0800.small813,CompactMinus0800.nodes813,NodeMinus12.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p814,GridMinus.atNode 814,GridMinus.atNode 815,NodeMinus12.w46,CompactMinus0800.checked814,CompactMinus0800.small814,CompactMinus0800.nodes814,NodeMinus12.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0800.p815,GridMinus.atNode 815,GridMinus.atNode 816,NodeMinus12.w47,CompactMinus0800.checked815,CompactMinus0800.small815,CompactMinus0800.nodes815,NodeMinus12.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p816,GridMinus.atNode 816,GridMinus.atNode 817,NodeMinus12.w48,CompactMinus0816.checked816,CompactMinus0816.small816,CompactMinus0816.nodes816,NodeMinus12.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p817,GridMinus.atNode 817,GridMinus.atNode 818,NodeMinus12.w49,CompactMinus0816.checked817,CompactMinus0816.small817,CompactMinus0816.nodes817,NodeMinus12.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p818,GridMinus.atNode 818,GridMinus.atNode 819,NodeMinus12.w50,CompactMinus0816.checked818,CompactMinus0816.small818,CompactMinus0816.nodes818,NodeMinus12.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p819,GridMinus.atNode 819,GridMinus.atNode 820,NodeMinus12.w51,CompactMinus0816.checked819,CompactMinus0816.small819,CompactMinus0816.nodes819,NodeMinus12.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p820,GridMinus.atNode 820,GridMinus.atNode 821,NodeMinus12.w52,CompactMinus0816.checked820,CompactMinus0816.small820,CompactMinus0816.nodes820,NodeMinus12.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p821,GridMinus.atNode 821,GridMinus.atNode 822,NodeMinus12.w53,CompactMinus0816.checked821,CompactMinus0816.small821,CompactMinus0816.nodes821,NodeMinus12.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p822,GridMinus.atNode 822,GridMinus.atNode 823,NodeMinus12.w54,CompactMinus0816.checked822,CompactMinus0816.small822,CompactMinus0816.nodes822,NodeMinus12.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p823,GridMinus.atNode 823,GridMinus.atNode 824,NodeMinus12.w55,CompactMinus0816.checked823,CompactMinus0816.small823,CompactMinus0816.nodes823,NodeMinus12.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p824,GridMinus.atNode 824,GridMinus.atNode 825,NodeMinus12.w56,CompactMinus0816.checked824,CompactMinus0816.small824,CompactMinus0816.nodes824,NodeMinus12.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p825,GridMinus.atNode 825,GridMinus.atNode 826,NodeMinus12.w57,CompactMinus0816.checked825,CompactMinus0816.small825,CompactMinus0816.nodes825,NodeMinus12.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p826,GridMinus.atNode 826,GridMinus.atNode 827,NodeMinus12.w58,CompactMinus0816.checked826,CompactMinus0816.small826,CompactMinus0816.nodes826,NodeMinus12.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p827,GridMinus.atNode 827,GridMinus.atNode 828,NodeMinus12.w59,CompactMinus0816.checked827,CompactMinus0816.small827,CompactMinus0816.nodes827,NodeMinus12.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p828,GridMinus.atNode 828,GridMinus.atNode 829,NodeMinus12.w60,CompactMinus0816.checked828,CompactMinus0816.small828,CompactMinus0816.nodes828,NodeMinus12.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p829,GridMinus.atNode 829,GridMinus.atNode 830,NodeMinus12.w61,CompactMinus0816.checked829,CompactMinus0816.small829,CompactMinus0816.nodes829,NodeMinus12.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p830,GridMinus.atNode 830,GridMinus.atNode 831,NodeMinus12.w62,CompactMinus0816.checked830,CompactMinus0816.small830,CompactMinus0816.nodes830,NodeMinus12.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0816.p831,GridMinus.atNode 831,GridMinus.atNode 832,NodeMinus12.w63,CompactMinus0816.checked831,CompactMinus0816.small831,CompactMinus0816.nodes831,NodeMinus12.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (768+j) ∧
    (atRow j).right=GridMinus.atNode (768+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus12
