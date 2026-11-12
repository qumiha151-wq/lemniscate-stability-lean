import SolitonClassification.Rotating.FlowMetricGridData

/-! Global actual P/Q norm bounds from the finite moving-reference grid.
The numerical certificate must supply the real grid hypotheses; no norm
bound for the actual variational flow is a premise of this theorem. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
open scoped Topology
set_option backward.isDefEq.respectTransparency false

lemma metric_grid_cover (time : ℕ → ℝ) {N : ℕ} (hN : 0<N)
    (hmono : ∀j<N,time j≤time (j+1)) {t : ℝ} (ht : t∈Icc (time 0) (time N)) :
    ∃j<N,t∈Icc (time j) (time (j+1)) := by
  induction N generalizing t with
  | zero => omega
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      exact ⟨0,by omega,ht⟩
    · by_cases ht' : t≤time n
      · obtain ⟨j,hj,hjt⟩ := ih (by omega) (fun j hj => hmono j (by omega)) ⟨ht.1,ht'⟩
        exact ⟨j,by omega,hjt⟩
      · exact ⟨n,by omega,⟨(lt_of_not_ge ht').le,ht.2⟩⟩

namespace FlowMetricGridData
variable {σ : ℝ} {hσ : |σ|≤1} {a : State} {N : ℕ} {T K I E ρ : ℝ}

theorem duration_sum (g : FlowMetricGridData σ hσ a N T K I E ρ) (n : ℕ) :
    (∑j∈range n,g.duration j)=g.time n := by
  induction n with
  | zero => simp [g.timeZero]
  | succ n ih =>
    rw [sum_range_succ,ih,duration]
    ring

theorem prefix_jump_bound (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {n : ℕ} {J : ℝ} (hn : n≤N) (hJ : (∑j∈range N,g.jump j)≤J) :
    (∑j∈range n,g.jump j)≤J := by
  apply le_trans _ hJ
  apply sum_le_sum_of_subset_of_nonneg (range_mono hn)
  intro j hj _
  exact g.jumpNonneg j (mem_range.mp hj)

theorem actual_bounds_on_segment (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) {j : ℕ} (hj : j<N)
    {t : ℝ} (ht : t∈Icc (g.time j) (g.time (j+1))) :
    (‖fderiv ℝ (supportFlow σ hσ t) a‖≤K*Real.exp (g.rate*T+I*J)) ∧
    (‖supportFlowInverse σ hσ a t‖≤I*Real.exp (g.rate*T+I*J)) := by
  have hrate : 0≤g.rate := by dsimp [rate]; positivity
  have htime : (∑i∈range j,g.duration i)+(t-g.time j)≤T := by
    rw [g.duration_sum]
    linarith [ht.2,(g.timeMem (j+1) (by omega)).2]
  have hsum := g.prefix_jump_bound (by omega : j≤N) hJ
  have hs := g.segment_growth hreg ha hE hI hj t ht
  have hV := metric_grid_inside_growth (B:=1) (by norm_num) hrate hI g.jumpNonneg
    g.forwardNode_zero.le (fun i hi => g.forward_step hreg ha hE hI hi)
    (by omega : j≤N) hs.1 htime hsum
  have hU := metric_grid_inside_growth (B:=1) (by norm_num) hrate hI g.jumpNonneg
    g.inverseNode_zero.le (fun i hi => g.inverse_step hreg ha hE hI hi)
    (by omega : j≤N) hs.2 htime hsum
  simp only [one_mul] at hV hU
  constructor
  · rw [actual_fderiv_from_metric σ hσ a (g.matrix j) t (g.matrixUnit j hj t ht)]
    exact (norm_mul_le _ _).trans (mul_le_mul (g.matrixBound j hj t ht) hV (norm_nonneg _) hK)
  · rw [actual_inverse_from_metric σ hσ a (g.matrix j) t (g.matrixUnit j hj t ht)]
    exact (norm_mul_le _ _).trans ((mul_le_mul hU (g.inverseBound j hj t ht)
      (norm_nonneg _) (Real.exp_pos _).le).trans_eq (mul_comm _ _))

/-- The total exponent is I*(4*E*K+rho)*T + I*sum(reset defects).
For true reference variational solutions rho=0. A polynomial reference
must retain its actual residual budget rho. -/
theorem actual_matrix_bounds (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hN : 0<N) (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) :
    ∀t∈Icc 0 T,
      (‖fderiv ℝ (supportFlow σ hσ t) a‖≤K*Real.exp (g.rate*T+I*J)) ∧
      (‖supportFlowInverse σ hσ a t‖≤I*Real.exp (g.rate*T+I*J)) := by
  intro t ht
  have ht' : t∈Icc (g.time 0) (g.time N) := by simpa only [g.timeZero,g.timeLast] using ht
  obtain ⟨j,hj,hjt⟩ := metric_grid_cover g.time hN g.timeStep ht'
  exact g.actual_bounds_on_segment hreg ha hK hI hE hρ hJ hj hjt

theorem actual_matrix_bounds_of_budget (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R J B : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hN : 0<N) (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (hJ : (∑j∈range N,g.jump j)≤J) (hbudget : Real.exp (g.rate*T+I*J)≤B) :
    ∀t∈Icc 0 T,
      (‖fderiv ℝ (supportFlow σ hσ t) a‖≤K*B) ∧
      (‖supportFlowInverse σ hσ a t‖≤I*B) := by
  intro t ht
  have h := g.actual_matrix_bounds hreg ha hN hK hI hE hρ hJ t ht
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_left hbudget hK),
    h.2.trans (mul_le_mul_of_nonneg_left hbudget hI)⟩

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
          throwError "Rotating global actual P/Q grid audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating global actual P/Q grid audit passed for {count} declarations."
