import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetPackedMinus0000
import SolitonClassification.Rotating.ResetNodeMinus00
import SolitonClassification.Rotating.IntegerWindingFirstBox
namespace SolitonClassification.Rotating.DyadicReset.PrefixMinus
noncomputable section
open Set
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p0,NodeMinus00.n0,NodeMinus00.n1,NodeMinus00.w0,CompactMinus0000.checked0,CompactMinus0000.small0,CompactMinus0000.nodes0,NodeMinus00.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p1,NodeMinus00.n1,NodeMinus00.n2,NodeMinus00.w1,CompactMinus0000.checked1,CompactMinus0000.small1,CompactMinus0000.nodes1,NodeMinus00.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p2,NodeMinus00.n2,NodeMinus00.n3,NodeMinus00.w2,CompactMinus0000.checked2,CompactMinus0000.small2,CompactMinus0000.nodes2,NodeMinus00.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p3,NodeMinus00.n3,NodeMinus00.n4,NodeMinus00.w3,CompactMinus0000.checked3,CompactMinus0000.small3,CompactMinus0000.nodes3,NodeMinus00.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p4,NodeMinus00.n4,NodeMinus00.n5,NodeMinus00.w4,CompactMinus0000.checked4,CompactMinus0000.small4,CompactMinus0000.nodes4,NodeMinus00.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p5,NodeMinus00.n5,NodeMinus00.n6,NodeMinus00.w5,CompactMinus0000.checked5,CompactMinus0000.small5,CompactMinus0000.nodes5,NodeMinus00.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p6,NodeMinus00.n6,NodeMinus00.n7,NodeMinus00.w6,CompactMinus0000.checked6,CompactMinus0000.small6,CompactMinus0000.nodes6,NodeMinus00.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p7,NodeMinus00.n7,NodeMinus00.n8,NodeMinus00.w7,CompactMinus0000.checked7,CompactMinus0000.small7,CompactMinus0000.nodes7,NodeMinus00.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p8,NodeMinus00.n8,NodeMinus00.n9,NodeMinus00.w8,CompactMinus0000.checked8,CompactMinus0000.small8,CompactMinus0000.nodes8,NodeMinus00.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p9,NodeMinus00.n9,NodeMinus00.n10,NodeMinus00.w9,CompactMinus0000.checked9,CompactMinus0000.small9,CompactMinus0000.nodes9,NodeMinus00.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p10,NodeMinus00.n10,NodeMinus00.n11,NodeMinus00.w10,CompactMinus0000.checked10,CompactMinus0000.small10,CompactMinus0000.nodes10,NodeMinus00.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p11,NodeMinus00.n11,NodeMinus00.n12,NodeMinus00.w11,CompactMinus0000.checked11,CompactMinus0000.small11,CompactMinus0000.nodes11,NodeMinus00.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p12,NodeMinus00.n12,NodeMinus00.n13,NodeMinus00.w12,CompactMinus0000.checked12,CompactMinus0000.small12,CompactMinus0000.nodes12,NodeMinus00.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p13,NodeMinus00.n13,NodeMinus00.n14,NodeMinus00.w13,CompactMinus0000.checked13,CompactMinus0000.small13,CompactMinus0000.nodes13,NodeMinus00.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p14,NodeMinus00.n14,NodeMinus00.n15,NodeMinus00.w14,CompactMinus0000.checked14,CompactMinus0000.small14,CompactMinus0000.nodes14,NodeMinus00.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0000.p15,NodeMinus00.n15,NodeMinus00.n16,NodeMinus00.w15,CompactMinus0000.checked15,CompactMinus0000.small15,CompactMinus0000.nodes15,NodeMinus00.bounds15⟩
def rows : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15]
def atRow (i : ℕ) := (rows[i]?).getD r0
theorem links (i : ℕ) (hi : i+1<16) : (atRow i).right=(atRow (i+1)).left := by
  have b : i≤14 := by omega
  interval_cases i <;> rfl
def tape : PolynomialTape (-Middle.hn) 16 := assemble atRow links
theorem at_zero : matrixPath (tape.data 0) 0=1 := by
  have eq := matrixPath_zero_eq (p:=tape.data 0) (tape.initial 0 (by decide))
  rw [eq]
  have b (j : Fin 6) : pointMatrixOperator commonGrid (forwardNode (tape.node 0)) (coordinateBasis j)=coordinateBasis j := by
    funext i;rw [pointMatrixOperator_basis];
    fin_cases i <;> fin_cases j <;> norm_num [tape,assemble,atRow,rows,r0,forwardNode,nodeLane,coordinateBasis,NodeMinus00.n0,commonGrid,nodeGrid,invGrid]
  ext v i
  have f := congrArg (fun L : State=>L i) (state_basis_expansion v)
  conv_lhs => rw [state_basis_expansion v]
  simp only [map_sum,map_smul,b]
  exact f.symm
theorem centre_seed : ‖IntegerWinding.initial (fun i=>(IntegerWinding.center i:ℝ))-path (tape.data 0) d 0‖≤1/10^71 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  change |IntegerWinding.initial _ i-eval 0 (tape.data 0 i)/(d:ℝ)|≤_
  rw [eval_zero,tape.initial 0 (by decide)]
  fin_cases i <;> norm_num [tape,assemble,atRow,rows,r0,NodeMinus00.n0,d,Middle.den,IntegerWinding.initial,IntegerWinding.center,IntegerWinding.phaseE,IntegerWinding.phaseG]
theorem actual_centre : ∃x : ℕ→ℝ→State, ∀i,i<16 →
    x i 0=(if i=0 then IntegerWinding.initial (fun j=>(IntegerWinding.center j:ℝ)) else x (i-1) 1) ∧
    FollowsState (step (-Middle.hn)) (x i) ∧ ∀t∈unitCell,‖x i t-path (tape.data i) d t‖≤5/10^52 := by
  have begin0 : ‖Ring.inverse (matrixPath (tape.data 0) 0) (IntegerWinding.initial (fun j=>(IntegerWinding.center j:ℝ))-path (tape.data 0) d 0)‖≤1/10^71 := by
    have idApp (v : State) : (1:FlowEnd) v=v := rfl
    simpa only [at_zero,Ring.inverse_one,idApp] using centre_seed
  obtain ⟨x,hx⟩ := tape_transport tape (by decide) (by norm_num [step,Middle.hn,Middle.hd]) _
    (by norm_num : (0:ℝ)≤1/10^55) centre_4000_budget.1 centre_4000_budget.2.1 begin0
    (by norm_num [roughPhysical,increment,eps])
  refine ⟨x,fun i hi=>⟨(hx i hi).1,(hx i hi).2.1,fun t ht=>((hx i hi).2.2 t ht).trans_eq ?_⟩⟩
  norm_num
end
end SolitonClassification.Rotating.DyadicReset.PrefixMinus
#print axioms SolitonClassification.Rotating.DyadicReset.PrefixMinus.actual_centre
