import SolitonClassification.Rotating.IntegerJointTime
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric Filter DyadicReset
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem short_displacement (a : State) (t : ℝ) :
    ‖wideFlow (t,a)-a‖≤110*|t| := by
  simpa only [wideFlow_zero,sub_zero,Real.norm_eq_abs,NNReal.coe_ofNat] using
    lipschitzWith_iff_norm_sub_le.mp (wide_time_lip a) t 0

theorem short_space_derivative (a : State) {τ : ℝ} (ht : |τ|≤1/10^30)
    (ha : ∀i : Fin 6, i.val<5 → |a i|≤9) :
    ∃ K : FlowEnd, HasFDerivAt (fun b => wideFlow (τ,b)) K a ∧
      ‖K-1‖≤400080*|τ| := by
  let U := ball a (1/4)
  let X := fun (b : State) (_ : ℕ) (t : ℝ) => wideFlow (t*τ,b)
  have near (b : State) (hb : b∈U) : ‖b-a‖≤1/4 := (mem_ball.mp hb).le
  have disp (b : State) (t : ℝ) (ht' : t∈unitCell) : ‖wideFlow (t*τ,b)-b‖≤110*|τ| := by
    apply (short_displacement b (t*τ)).trans
    rw [abs_mul,abs_of_nonneg ht'.1]
    nlinarith only [mul_le_mul_of_nonneg_right ht'.2 (abs_nonneg τ)]
  have box_of_dist (y : State) (hy : ‖y-a‖≤1) : StateBox y := by
    intro j hj
    have d := (coordinate_bound (y-a) j).trans hy
    change |y j-a j|≤1 at d
    have tri := abs_add_le (y j-a j) (a j)
    rw [sub_add_cancel] at tri
    linarith [ha j hj]
  have box (b : State) (hb : b∈U) (i : ℕ) (_ : i<1) (t : ℝ) (h1 : t∈unitCell) :
      StateBox (X b i t) := by
    apply box_of_dist
    exact (norm_sub_le_norm_sub_add_norm_sub _ b _).trans (by linarith [disp b t h1,near b hb])
  have xd (b : State) (hb : b∈U) (i : ℕ) (hi : i<1) : FollowsState τ (X b i) := by
    intro t h1
    have diff := (wideFlow_time b (t*τ)).scomp t ((hasDerivAt_id t).mul_const τ)
    have eq : wideField (X b i t)=field (X b i t) := by rw [wideField,wideClip_id (box b hb i hi t h1)]
    change HasDerivWithinAt (fun t=>wideFlow (t*τ,b)) (τ • field (X b i t)) unitCell t
    rw [←eq]
    simpa only [X,Function.comp_def,id_eq,one_mul] using diff.hasDerivWithinAt (s:=unitCell)
  have nj (b : State) (_ : b∈U) : Joined 1 b (X b) := by
    intro i hi
    have : i=0 := by omega
    subst i
    simp [X,wideFlow_zero]
  have close (b : State) (hb : b∈U) (i : ℕ) (_ : i<1) (t : ℝ) (h1 : t∈unitCell) :
      ‖X b i t-X a i t‖≤1 := by
    have x := norm_sub_le_norm_sub_add_norm_sub (X b i t) b (X a i t)
    have y := norm_sub_le_norm_sub_add_norm_sub b a (X a i t)
    rw [norm_sub_rev a (X a i t)] at y
    linarith [disp b t h1,disp a t h1,near b hb]
  obtain ⟨x,J,ini,jini,dx,dj,bounds⟩ := short_state_and_matrix ht a
    (fun i h => (ha i h).trans (by norm_num)) 1 (by norm_num)
  have eq (t : ℝ) (hx : t∈unitCell) : x t=X a 0 t := by
    have eq' : x 0=wideFlow (0,a) := by rw [ini,wideFlow_zero]
    simpa only [zero_add,X] using cell_identification (ht.trans (by norm_num)) a eq' dx
      (fun u hu => box_of_dist _ ((bounds u hu).1.trans (by linarith))) t hx
  have jJ : JoinedMatrix 1 (fun _ => J) := by
    intro i hi
    have : i=0 := by omega
    subst i
    simpa using jini
  have odeJ (i : ℕ) (hi : i<1) (t : ℝ) (hh : t∈unitCell) :
      HasDerivWithinAt J (actualCoefficient τ (X a i) t*J t) unitCell t := by
    have : i=0 := by omega
    subst i
    simpa only [actualCoefficient,eq t hh] using dj t hh
  have df := actual_endpoint_fderiv (ht.trans (by norm_num)) (ball_mem_nhds a (by norm_num : 0<(1:ℝ)/4))
    X nj xd box close (fun _ => J) jJ odeJ 0 (by decide) 1 (by norm_num [unitCell])
  refine ⟨J 1,?_,?_⟩
  · simpa only [X,one_mul] using df
  · simpa only [jini] using (bounds 1 (by norm_num [unitCell])).2

/-- Move the physical endpoint time by its third shooting coordinate.
The terminal state and actual derivative use the same globally selected flow. -/
theorem move_endpoint {a : State} {s τ : ℝ} (ht : |τ|≤1/10^30) {J : FlowEnd}
    (d : HasFDerivAt (fun b => wideFlow (s,b)) J a)
    (margin : ∀i : Fin 6, i.val<5→|wideFlow (s,a) i|≤9) (nj : ‖J‖≤5001) :
    ∃ M : FlowEnd,
      HasFDerivAt wideFlow (fullDifferential (s+τ) a M) (s+τ,a) ∧
      ‖M-J‖≤400080*5001*|τ| ∧
      ‖wideFlow (s+τ,a)-wideFlow (s,a)‖≤110*|τ| := by
  obtain ⟨K,dk,near⟩ := short_space_derivative _ ht margin
  let M := K.comp J
  have dM : HasFDerivAt (fun b => wideFlow (s+τ,b)) M a := by
    simpa only [Function.comp_def,←wideFlow_add] using dk.comp a d
  refine ⟨M,joint_of_space dM,?_,?_⟩
  · have eq : M-J=(K-1).comp J := by ext v i; simp [M]
    rw [eq]
    exact ((K-1).opNorm_comp_le J).trans ((mul_le_mul near nj (norm_nonneg _) (by positivity)).trans_eq (by ring))
  · rw [wideFlow_add]
    exact short_displacement _ _

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.move_endpoint
