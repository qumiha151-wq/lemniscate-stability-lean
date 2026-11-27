import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetPackedPlus0000
import SolitonClassification.Rotating.ResetNodePlus00
import SolitonClassification.Rotating.IntegerWindingFirstBox
namespace SolitonClassification.Rotating.DyadicReset.PrefixPlus
noncomputable section
open Set
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p0,NodePlus00.n0,NodePlus00.n1,NodePlus00.w0,CompactPlus0000.checked0,CompactPlus0000.small0,CompactPlus0000.nodes0,NodePlus00.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p1,NodePlus00.n1,NodePlus00.n2,NodePlus00.w1,CompactPlus0000.checked1,CompactPlus0000.small1,CompactPlus0000.nodes1,NodePlus00.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p2,NodePlus00.n2,NodePlus00.n3,NodePlus00.w2,CompactPlus0000.checked2,CompactPlus0000.small2,CompactPlus0000.nodes2,NodePlus00.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p3,NodePlus00.n3,NodePlus00.n4,NodePlus00.w3,CompactPlus0000.checked3,CompactPlus0000.small3,CompactPlus0000.nodes3,NodePlus00.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p4,NodePlus00.n4,NodePlus00.n5,NodePlus00.w4,CompactPlus0000.checked4,CompactPlus0000.small4,CompactPlus0000.nodes4,NodePlus00.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p5,NodePlus00.n5,NodePlus00.n6,NodePlus00.w5,CompactPlus0000.checked5,CompactPlus0000.small5,CompactPlus0000.nodes5,NodePlus00.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p6,NodePlus00.n6,NodePlus00.n7,NodePlus00.w6,CompactPlus0000.checked6,CompactPlus0000.small6,CompactPlus0000.nodes6,NodePlus00.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p7,NodePlus00.n7,NodePlus00.n8,NodePlus00.w7,CompactPlus0000.checked7,CompactPlus0000.small7,CompactPlus0000.nodes7,NodePlus00.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p8,NodePlus00.n8,NodePlus00.n9,NodePlus00.w8,CompactPlus0000.checked8,CompactPlus0000.small8,CompactPlus0000.nodes8,NodePlus00.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p9,NodePlus00.n9,NodePlus00.n10,NodePlus00.w9,CompactPlus0000.checked9,CompactPlus0000.small9,CompactPlus0000.nodes9,NodePlus00.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p10,NodePlus00.n10,NodePlus00.n11,NodePlus00.w10,CompactPlus0000.checked10,CompactPlus0000.small10,CompactPlus0000.nodes10,NodePlus00.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p11,NodePlus00.n11,NodePlus00.n12,NodePlus00.w11,CompactPlus0000.checked11,CompactPlus0000.small11,CompactPlus0000.nodes11,NodePlus00.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p12,NodePlus00.n12,NodePlus00.n13,NodePlus00.w12,CompactPlus0000.checked12,CompactPlus0000.small12,CompactPlus0000.nodes12,NodePlus00.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p13,NodePlus00.n13,NodePlus00.n14,NodePlus00.w13,CompactPlus0000.checked13,CompactPlus0000.small13,CompactPlus0000.nodes13,NodePlus00.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p14,NodePlus00.n14,NodePlus00.n15,NodePlus00.w14,CompactPlus0000.checked14,CompactPlus0000.small14,CompactPlus0000.nodes14,NodePlus00.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0000.p15,NodePlus00.n15,NodePlus00.n16,NodePlus00.w15,CompactPlus0000.checked15,CompactPlus0000.small15,CompactPlus0000.nodes15,NodePlus00.bounds15⟩
def rows : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15]
def atRow (i : ℕ) := (rows[i]?).getD r0
theorem links (i : ℕ) (hi : i+1<16) : (atRow i).right=(atRow (i+1)).left := by
  have b : i≤14 := by omega
  interval_cases i <;> rfl
def tape : PolynomialTape Middle.hn 16 := assemble atRow links
theorem at_zero : matrixPath (tape.data 0) 0=1 := by
  have eq := matrixPath_zero_eq (p:=tape.data 0) (tape.initial 0 (by decide))
  rw [eq]
  have b (j : Fin 6) : pointMatrixOperator commonGrid (forwardNode (tape.node 0)) (coordinateBasis j)=coordinateBasis j := by
    funext i;rw [pointMatrixOperator_basis];
    fin_cases i <;> fin_cases j <;> norm_num [tape,assemble,atRow,rows,r0,forwardNode,nodeLane,coordinateBasis,NodePlus00.n0,commonGrid,nodeGrid,invGrid]
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
  fin_cases i <;> norm_num [tape,assemble,atRow,rows,r0,NodePlus00.n0,d,Middle.den,IntegerWinding.initial,IntegerWinding.center,IntegerWinding.phaseE,IntegerWinding.phaseG]
theorem actual_centre : ∃x : ℕ→ℝ→State, ∀i,i<16 →
    x i 0=(if i=0 then IntegerWinding.initial (fun j=>(IntegerWinding.center j:ℝ)) else x (i-1) 1) ∧
    FollowsState (step Middle.hn) (x i) ∧ ∀t∈unitCell,‖x i t-path (tape.data i) d t‖≤5/10^52 := by
  have begin0 : ‖Ring.inverse (matrixPath (tape.data 0) 0) (IntegerWinding.initial (fun j=>(IntegerWinding.center j:ℝ))-path (tape.data 0) d 0)‖≤1/10^71 := by
    have idApp (v : State) : (1:FlowEnd) v=v := rfl
    simpa only [at_zero,Ring.inverse_one,idApp] using centre_seed
  obtain ⟨x,hx⟩ := tape_transport tape (by decide) (by norm_num [step,Middle.hn,Middle.hd]) _
    (by norm_num : (0:ℝ)≤1/10^55) centre_4000_budget.1 centre_4000_budget.2.1 begin0
    (by norm_num [roughPhysical,increment,eps])
  refine ⟨x,fun i hi=>⟨(hx i hi).1,(hx i hi).2.1,fun t ht=>((hx i hi).2.2 t ht).trans_eq ?_⟩⟩
  norm_num
end
end SolitonClassification.Rotating.DyadicReset.PrefixPlus
#print axioms SolitonClassification.Rotating.DyadicReset.PrefixPlus.actual_centre
