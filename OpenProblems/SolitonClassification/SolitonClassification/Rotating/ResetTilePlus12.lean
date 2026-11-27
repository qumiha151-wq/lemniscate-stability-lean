import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0768
import SolitonClassification.Rotating.ResetPackedPlus0784
import SolitonClassification.Rotating.ResetPackedPlus0800
import SolitonClassification.Rotating.ResetPackedPlus0816
namespace SolitonClassification.Rotating.DyadicReset.TilePlus12
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p768,GridPlus.atNode 768,GridPlus.atNode 769,NodePlus12.w0,CompactPlus0768.checked768,CompactPlus0768.small768,CompactPlus0768.nodes768,NodePlus12.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p769,GridPlus.atNode 769,GridPlus.atNode 770,NodePlus12.w1,CompactPlus0768.checked769,CompactPlus0768.small769,CompactPlus0768.nodes769,NodePlus12.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p770,GridPlus.atNode 770,GridPlus.atNode 771,NodePlus12.w2,CompactPlus0768.checked770,CompactPlus0768.small770,CompactPlus0768.nodes770,NodePlus12.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p771,GridPlus.atNode 771,GridPlus.atNode 772,NodePlus12.w3,CompactPlus0768.checked771,CompactPlus0768.small771,CompactPlus0768.nodes771,NodePlus12.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p772,GridPlus.atNode 772,GridPlus.atNode 773,NodePlus12.w4,CompactPlus0768.checked772,CompactPlus0768.small772,CompactPlus0768.nodes772,NodePlus12.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p773,GridPlus.atNode 773,GridPlus.atNode 774,NodePlus12.w5,CompactPlus0768.checked773,CompactPlus0768.small773,CompactPlus0768.nodes773,NodePlus12.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p774,GridPlus.atNode 774,GridPlus.atNode 775,NodePlus12.w6,CompactPlus0768.checked774,CompactPlus0768.small774,CompactPlus0768.nodes774,NodePlus12.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p775,GridPlus.atNode 775,GridPlus.atNode 776,NodePlus12.w7,CompactPlus0768.checked775,CompactPlus0768.small775,CompactPlus0768.nodes775,NodePlus12.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p776,GridPlus.atNode 776,GridPlus.atNode 777,NodePlus12.w8,CompactPlus0768.checked776,CompactPlus0768.small776,CompactPlus0768.nodes776,NodePlus12.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p777,GridPlus.atNode 777,GridPlus.atNode 778,NodePlus12.w9,CompactPlus0768.checked777,CompactPlus0768.small777,CompactPlus0768.nodes777,NodePlus12.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p778,GridPlus.atNode 778,GridPlus.atNode 779,NodePlus12.w10,CompactPlus0768.checked778,CompactPlus0768.small778,CompactPlus0768.nodes778,NodePlus12.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p779,GridPlus.atNode 779,GridPlus.atNode 780,NodePlus12.w11,CompactPlus0768.checked779,CompactPlus0768.small779,CompactPlus0768.nodes779,NodePlus12.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p780,GridPlus.atNode 780,GridPlus.atNode 781,NodePlus12.w12,CompactPlus0768.checked780,CompactPlus0768.small780,CompactPlus0768.nodes780,NodePlus12.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p781,GridPlus.atNode 781,GridPlus.atNode 782,NodePlus12.w13,CompactPlus0768.checked781,CompactPlus0768.small781,CompactPlus0768.nodes781,NodePlus12.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p782,GridPlus.atNode 782,GridPlus.atNode 783,NodePlus12.w14,CompactPlus0768.checked782,CompactPlus0768.small782,CompactPlus0768.nodes782,NodePlus12.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0768.p783,GridPlus.atNode 783,GridPlus.atNode 784,NodePlus12.w15,CompactPlus0768.checked783,CompactPlus0768.small783,CompactPlus0768.nodes783,NodePlus12.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p784,GridPlus.atNode 784,GridPlus.atNode 785,NodePlus12.w16,CompactPlus0784.checked784,CompactPlus0784.small784,CompactPlus0784.nodes784,NodePlus12.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p785,GridPlus.atNode 785,GridPlus.atNode 786,NodePlus12.w17,CompactPlus0784.checked785,CompactPlus0784.small785,CompactPlus0784.nodes785,NodePlus12.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p786,GridPlus.atNode 786,GridPlus.atNode 787,NodePlus12.w18,CompactPlus0784.checked786,CompactPlus0784.small786,CompactPlus0784.nodes786,NodePlus12.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p787,GridPlus.atNode 787,GridPlus.atNode 788,NodePlus12.w19,CompactPlus0784.checked787,CompactPlus0784.small787,CompactPlus0784.nodes787,NodePlus12.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p788,GridPlus.atNode 788,GridPlus.atNode 789,NodePlus12.w20,CompactPlus0784.checked788,CompactPlus0784.small788,CompactPlus0784.nodes788,NodePlus12.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p789,GridPlus.atNode 789,GridPlus.atNode 790,NodePlus12.w21,CompactPlus0784.checked789,CompactPlus0784.small789,CompactPlus0784.nodes789,NodePlus12.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p790,GridPlus.atNode 790,GridPlus.atNode 791,NodePlus12.w22,CompactPlus0784.checked790,CompactPlus0784.small790,CompactPlus0784.nodes790,NodePlus12.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p791,GridPlus.atNode 791,GridPlus.atNode 792,NodePlus12.w23,CompactPlus0784.checked791,CompactPlus0784.small791,CompactPlus0784.nodes791,NodePlus12.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p792,GridPlus.atNode 792,GridPlus.atNode 793,NodePlus12.w24,CompactPlus0784.checked792,CompactPlus0784.small792,CompactPlus0784.nodes792,NodePlus12.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p793,GridPlus.atNode 793,GridPlus.atNode 794,NodePlus12.w25,CompactPlus0784.checked793,CompactPlus0784.small793,CompactPlus0784.nodes793,NodePlus12.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p794,GridPlus.atNode 794,GridPlus.atNode 795,NodePlus12.w26,CompactPlus0784.checked794,CompactPlus0784.small794,CompactPlus0784.nodes794,NodePlus12.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p795,GridPlus.atNode 795,GridPlus.atNode 796,NodePlus12.w27,CompactPlus0784.checked795,CompactPlus0784.small795,CompactPlus0784.nodes795,NodePlus12.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p796,GridPlus.atNode 796,GridPlus.atNode 797,NodePlus12.w28,CompactPlus0784.checked796,CompactPlus0784.small796,CompactPlus0784.nodes796,NodePlus12.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p797,GridPlus.atNode 797,GridPlus.atNode 798,NodePlus12.w29,CompactPlus0784.checked797,CompactPlus0784.small797,CompactPlus0784.nodes797,NodePlus12.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p798,GridPlus.atNode 798,GridPlus.atNode 799,NodePlus12.w30,CompactPlus0784.checked798,CompactPlus0784.small798,CompactPlus0784.nodes798,NodePlus12.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0784.p799,GridPlus.atNode 799,GridPlus.atNode 800,NodePlus12.w31,CompactPlus0784.checked799,CompactPlus0784.small799,CompactPlus0784.nodes799,NodePlus12.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p800,GridPlus.atNode 800,GridPlus.atNode 801,NodePlus12.w32,CompactPlus0800.checked800,CompactPlus0800.small800,CompactPlus0800.nodes800,NodePlus12.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p801,GridPlus.atNode 801,GridPlus.atNode 802,NodePlus12.w33,CompactPlus0800.checked801,CompactPlus0800.small801,CompactPlus0800.nodes801,NodePlus12.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p802,GridPlus.atNode 802,GridPlus.atNode 803,NodePlus12.w34,CompactPlus0800.checked802,CompactPlus0800.small802,CompactPlus0800.nodes802,NodePlus12.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p803,GridPlus.atNode 803,GridPlus.atNode 804,NodePlus12.w35,CompactPlus0800.checked803,CompactPlus0800.small803,CompactPlus0800.nodes803,NodePlus12.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p804,GridPlus.atNode 804,GridPlus.atNode 805,NodePlus12.w36,CompactPlus0800.checked804,CompactPlus0800.small804,CompactPlus0800.nodes804,NodePlus12.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p805,GridPlus.atNode 805,GridPlus.atNode 806,NodePlus12.w37,CompactPlus0800.checked805,CompactPlus0800.small805,CompactPlus0800.nodes805,NodePlus12.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p806,GridPlus.atNode 806,GridPlus.atNode 807,NodePlus12.w38,CompactPlus0800.checked806,CompactPlus0800.small806,CompactPlus0800.nodes806,NodePlus12.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p807,GridPlus.atNode 807,GridPlus.atNode 808,NodePlus12.w39,CompactPlus0800.checked807,CompactPlus0800.small807,CompactPlus0800.nodes807,NodePlus12.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p808,GridPlus.atNode 808,GridPlus.atNode 809,NodePlus12.w40,CompactPlus0800.checked808,CompactPlus0800.small808,CompactPlus0800.nodes808,NodePlus12.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p809,GridPlus.atNode 809,GridPlus.atNode 810,NodePlus12.w41,CompactPlus0800.checked809,CompactPlus0800.small809,CompactPlus0800.nodes809,NodePlus12.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p810,GridPlus.atNode 810,GridPlus.atNode 811,NodePlus12.w42,CompactPlus0800.checked810,CompactPlus0800.small810,CompactPlus0800.nodes810,NodePlus12.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p811,GridPlus.atNode 811,GridPlus.atNode 812,NodePlus12.w43,CompactPlus0800.checked811,CompactPlus0800.small811,CompactPlus0800.nodes811,NodePlus12.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p812,GridPlus.atNode 812,GridPlus.atNode 813,NodePlus12.w44,CompactPlus0800.checked812,CompactPlus0800.small812,CompactPlus0800.nodes812,NodePlus12.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p813,GridPlus.atNode 813,GridPlus.atNode 814,NodePlus12.w45,CompactPlus0800.checked813,CompactPlus0800.small813,CompactPlus0800.nodes813,NodePlus12.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p814,GridPlus.atNode 814,GridPlus.atNode 815,NodePlus12.w46,CompactPlus0800.checked814,CompactPlus0800.small814,CompactPlus0800.nodes814,NodePlus12.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0800.p815,GridPlus.atNode 815,GridPlus.atNode 816,NodePlus12.w47,CompactPlus0800.checked815,CompactPlus0800.small815,CompactPlus0800.nodes815,NodePlus12.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p816,GridPlus.atNode 816,GridPlus.atNode 817,NodePlus12.w48,CompactPlus0816.checked816,CompactPlus0816.small816,CompactPlus0816.nodes816,NodePlus12.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p817,GridPlus.atNode 817,GridPlus.atNode 818,NodePlus12.w49,CompactPlus0816.checked817,CompactPlus0816.small817,CompactPlus0816.nodes817,NodePlus12.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p818,GridPlus.atNode 818,GridPlus.atNode 819,NodePlus12.w50,CompactPlus0816.checked818,CompactPlus0816.small818,CompactPlus0816.nodes818,NodePlus12.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p819,GridPlus.atNode 819,GridPlus.atNode 820,NodePlus12.w51,CompactPlus0816.checked819,CompactPlus0816.small819,CompactPlus0816.nodes819,NodePlus12.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p820,GridPlus.atNode 820,GridPlus.atNode 821,NodePlus12.w52,CompactPlus0816.checked820,CompactPlus0816.small820,CompactPlus0816.nodes820,NodePlus12.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p821,GridPlus.atNode 821,GridPlus.atNode 822,NodePlus12.w53,CompactPlus0816.checked821,CompactPlus0816.small821,CompactPlus0816.nodes821,NodePlus12.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p822,GridPlus.atNode 822,GridPlus.atNode 823,NodePlus12.w54,CompactPlus0816.checked822,CompactPlus0816.small822,CompactPlus0816.nodes822,NodePlus12.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p823,GridPlus.atNode 823,GridPlus.atNode 824,NodePlus12.w55,CompactPlus0816.checked823,CompactPlus0816.small823,CompactPlus0816.nodes823,NodePlus12.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p824,GridPlus.atNode 824,GridPlus.atNode 825,NodePlus12.w56,CompactPlus0816.checked824,CompactPlus0816.small824,CompactPlus0816.nodes824,NodePlus12.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p825,GridPlus.atNode 825,GridPlus.atNode 826,NodePlus12.w57,CompactPlus0816.checked825,CompactPlus0816.small825,CompactPlus0816.nodes825,NodePlus12.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p826,GridPlus.atNode 826,GridPlus.atNode 827,NodePlus12.w58,CompactPlus0816.checked826,CompactPlus0816.small826,CompactPlus0816.nodes826,NodePlus12.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p827,GridPlus.atNode 827,GridPlus.atNode 828,NodePlus12.w59,CompactPlus0816.checked827,CompactPlus0816.small827,CompactPlus0816.nodes827,NodePlus12.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p828,GridPlus.atNode 828,GridPlus.atNode 829,NodePlus12.w60,CompactPlus0816.checked828,CompactPlus0816.small828,CompactPlus0816.nodes828,NodePlus12.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p829,GridPlus.atNode 829,GridPlus.atNode 830,NodePlus12.w61,CompactPlus0816.checked829,CompactPlus0816.small829,CompactPlus0816.nodes829,NodePlus12.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p830,GridPlus.atNode 830,GridPlus.atNode 831,NodePlus12.w62,CompactPlus0816.checked830,CompactPlus0816.small830,CompactPlus0816.nodes830,NodePlus12.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0816.p831,GridPlus.atNode 831,GridPlus.atNode 832,NodePlus12.w63,CompactPlus0816.checked831,CompactPlus0816.small831,CompactPlus0816.nodes831,NodePlus12.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (768+j) ∧
    (atRow j).right=GridPlus.atNode (768+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus12
