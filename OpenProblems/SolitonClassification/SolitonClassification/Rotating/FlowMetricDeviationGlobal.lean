import SolitonClassification.Rotating.FlowMetricDeviationSegment
import SolitonClassification.Rotating.FlowMetricDeviationReset
import SolitonClassification.Rotating.FlowMetricGlobal

/-! Global deviation of the actual variational matrix P from the real
reference M, with differential residuals and every matrix reset retained.
The shifted norm ||inverse M*P-Id||+1 satisfies homogeneous grid growth. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
set_option backward.isDefEq.respectTransparency false

namespace FlowMetricGridData
variable {σ : ℝ} {hσ : |σ|≤1} {a : State} {N : ℕ} {T K I E ρ : ℝ}

def deviationNode (g : FlowMetricGridData σ hσ a N T K I E ρ) (j : ℕ) : ℝ :=
  ‖flowMetricForward σ hσ a (g.matrix j) (g.time j)-1‖+1

theorem deviationNode_zero (g : FlowMetricGridData σ hσ a N T K I E ρ) : g.deviationNode 0=1 := by
  simp only [deviationNode,g.timeZero,flowMetricForward,g.matrixInitial,supportFlow_fderiv_initial]
  change ‖Ring.inverse (1:FlowEnd)*1-1‖+1=1
  simp only [Ring.inverse_one,one_mul,sub_self,norm_zero,zero_add]

theorem deviation_segment_growth (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hρ : 0≤ρ) {j : ℕ} (hj : j<N) :
    ∀t∈Icc (g.time j) (g.time (j+1)),
      ‖flowMetricForward σ hσ a (g.matrix j) t-1‖+1≤g.deviationNode j*Real.exp (g.rate*(t-g.time j)) := by
  have hrate : 0≤g.rate := by dsimp [rate]; positivity
  apply actual_metric_segment_deviation σ hσ hrate hreg ha (g.timeMem j (by omega)).1
    (g.timeMem (j+1) (by omega)).2 (g.matrixContinuous j hj) (g.matrixUnit j hj) (g.matrixDerivative j hj)
  intro t ht
  have ht' := Ico_subset_Icc_self ht
  have htT : t∈Icc 0 T := ⟨(g.timeMem j (by omega)).1.trans ht.1,
    ht.2.le.trans (g.timeMem (j+1) (by omega)).2⟩
  exact actual_flowMetricCoefficient_norm_bound σ hσ (hreg a ha t htT)
    (g.referenceTube j hj t ht') hE hI (g.stateError j hj t ht')
    (g.inverseBound j hj t ht') (g.matrixBound j hj t ht') (g.residualBound j hj t ht')

theorem deviation_step (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hρ : 0≤ρ) {j : ℕ} (hj : j<N) :
    g.deviationNode (j+1)≤(1+I*g.jump j)*g.deviationNode j*Real.exp (g.rate*g.duration j) := by
  have hend : g.time (j+1)∈Icc (g.time j) (g.time (j+1)) := ⟨g.timeStep j hj,le_rfl⟩
  have hs := g.deviation_segment_growth hreg ha hK hE hI hρ hj (g.time (j+1)) hend
  have hr := metric_forward_deviation_reset_bound
    (P:=fderiv ℝ (supportFlow σ hσ (g.time (j+1))) a)
    (g.matrixUnit j hj _ hend) (g.nodeUnit (j+1) (by omega)) hI
    (g.nodeInverseBound (j+1) (by omega)) (g.resetBound j hj)
  change g.deviationNode (j+1)≤(1+I*g.jump j)*
    (‖flowMetricForward σ hσ a (g.matrix j) (g.time (j+1))-1‖+1) at hr
  have hjn := g.jumpNonneg j hj
  exact hr.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by dsimp [duration]; ring))

theorem metric_deviation_on_segment (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) {j : ℕ} (hj : j<N)
    {t : ℝ} (ht : t∈Icc (g.time j) (g.time (j+1))) :
    ‖flowMetricForward σ hσ a (g.matrix j) t-1‖≤Real.exp (g.rate*T+I*J)-1 := by
  have hrate : 0≤g.rate := by dsimp [rate]; positivity
  have htime : (∑i∈range j,g.duration i)+(t-g.time j)≤T := by
    rw [g.duration_sum]
    linarith [ht.2,(g.timeMem (j+1) (by omega)).2]
  have hh := metric_grid_inside_growth (B:=1) (by norm_num) hrate hI g.jumpNonneg
    g.deviationNode_zero.le (fun i hi => g.deviation_step hreg ha hK hE hI hρ hi)
    (by omega : j≤N) (g.deviation_segment_growth hreg ha hK hE hI hρ hj t ht)
    htime (g.prefix_jump_bound (by omega : j≤N) hJ)
  linarith

/-- Comparison with the reference belonging to this closed segment.
At a shared endpoint this also applies to the following segment when it
exists. The terminal post-reset node is treated separately below. -/
theorem actual_deviation_on_segment (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) {j : ℕ} (hj : j<N)
    {t : ℝ} (ht : t∈Icc (g.time j) (g.time (j+1))) :
    ‖fderiv ℝ (supportFlow σ hσ t) a-g.matrix j t‖≤K*(Real.exp (g.rate*T+I*J)-1) := by
  rw [actual_fderiv_deviation_from_metric σ hσ a (g.matrix j) t (g.matrixUnit j hj t ht)]
  exact (norm_mul_le _ _).trans (mul_le_mul (g.matrixBound j hj t ht)
    (g.metric_deviation_on_segment hreg ha hK hI hE hρ hJ hj ht) (norm_nonneg _) hK)

theorem metric_deviation_at_node (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) {n : ℕ} (hn : n≤N) :
    ‖flowMetricForward σ hσ a (g.matrix n) (g.time n)-1‖≤Real.exp (g.rate*T+I*J)-1 := by
  have hrate : 0≤g.rate := by dsimp [rate]; positivity
  have hz : g.deviationNode n≤g.deviationNode n*Real.exp (g.rate*0) := by simp
  have htime : (∑i∈range n,g.duration i)+0≤T := by
    simpa only [g.duration_sum,add_zero] using (g.timeMem n hn).2
  have hh := metric_grid_inside_growth (B:=1) (by norm_num) hrate hI g.jumpNonneg
    g.deviationNode_zero.le (fun i hi => g.deviation_step hreg ha hK hE hI hρ hi)
    hn hz htime (g.prefix_jump_bound hn hJ)
  dsimp [deviationNode] at hh
  linarith

/-- Includes the post-reset terminal node. Its matrix norm is retained
explicitly because the grid bounds K only on actual reference segments. -/
theorem actual_deviation_at_node (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) {n : ℕ} (hn : n≤N) :
    ‖fderiv ℝ (supportFlow σ hσ (g.time n)) a-g.matrix n (g.time n)‖≤
      ‖g.matrix n (g.time n)‖*(Real.exp (g.rate*T+I*J)-1) := by
  rw [actual_fderiv_deviation_from_metric σ hσ a (g.matrix n) (g.time n) (g.nodeUnit n hn)]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
    (g.metric_deviation_at_node hreg ha hK hI hE hρ hJ hn) (norm_nonneg _))

theorem actual_deviation_every_time (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hN : 0<N) (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) {t : ℝ} (ht : t∈Icc 0 T) :
    ∃j<N,t∈Icc (g.time j) (g.time (j+1)) ∧
      ‖fderiv ℝ (supportFlow σ hσ t) a-g.matrix j t‖≤K*(Real.exp (g.rate*T+I*J)-1) := by
  have ht' : t∈Icc (g.time 0) (g.time N) := by simpa only [g.timeZero,g.timeLast] using ht
  obtain ⟨j,hj,hjt⟩ := metric_grid_cover g.time hN g.timeStep ht'
  exact ⟨j,hj,hjt,g.actual_deviation_on_segment hreg ha hK hI hE hρ hJ hj hjt⟩

theorem actual_deviation_on_segment_of_budget (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J δrel : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) (hbudget : Real.exp (g.rate*T+I*J)≤1+δrel)
    {j : ℕ} (hj : j<N) {t : ℝ} (ht : t∈Icc (g.time j) (g.time (j+1))) :
    ‖fderiv ℝ (supportFlow σ hσ t) a-g.matrix j t‖≤K*δrel := by
  exact (g.actual_deviation_on_segment hreg ha hK hI hE hρ hJ hj ht).trans
    (mul_le_mul_of_nonneg_left (by linarith : Real.exp (g.rate*T+I*J)-1≤δrel) hK)

/-- A bound at any reset node, including n=N, with the norm of that
actual reference node supplied explicitly. No actual P deviation is assumed. -/
theorem actual_deviation_at_node_of_budget (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J δrel Knode : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) (hbudget : Real.exp (g.rate*T+I*J)≤1+δrel)
    {n : ℕ} (hn : n≤N) (hnode : ‖g.matrix n (g.time n)‖≤Knode) :
    ‖fderiv ℝ (supportFlow σ hσ (g.time n)) a-g.matrix n (g.time n)‖≤Knode*δrel := by
  have hV := g.metric_deviation_at_node hreg ha hK hI hE hρ hJ hn
  have hVq : ‖flowMetricForward σ hσ a (g.matrix n) (g.time n)-1‖≤δrel := by linarith
  have hnK : 0≤Knode := (norm_nonneg _).trans hnode
  rw [actual_fderiv_deviation_from_metric σ hσ a (g.matrix n) (g.time n) (g.nodeUnit n hn)]
  exact (norm_mul_le _ _).trans (mul_le_mul hnode hVq (norm_nonneg _) hnK)

theorem matrix_node_bound_from_reset (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {n : ℕ} (hn0 : 0<n) (hn : n≤N) :
    ‖g.matrix n (g.time n)‖≤K+g.jump (n-1) := by
  have hj : n-1<N := by omega
  have he : n-1+1=n := by omega
  have hend : g.time n∈Icc (g.time (n-1)) (g.time (n-1+1)) := by
    simpa only [Set.mem_Icc,he] using And.intro (g.timeStep (n-1) hj) (le_refl (g.time (n-1+1)))
  have hb := g.matrixBound (n-1) hj (g.time n) hend
  have hr := g.resetBound (n-1) hj
  rw [he] at hr
  have htri : ‖g.matrix n (g.time n)‖≤‖g.matrix (n-1) (g.time n)‖+
      ‖g.matrix (n-1) (g.time n)-g.matrix n (g.time n)‖ := by
    have h := norm_add_le (g.matrix n (g.time n)-g.matrix (n-1) (g.time n)) (g.matrix (n-1) (g.time n))
    rw [sub_add_cancel,norm_sub_rev] at h
    linarith
  linarith

end FlowMetricGridData
end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual global matrix-deviation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual global matrix-deviation audit passed for {count} declarations."
