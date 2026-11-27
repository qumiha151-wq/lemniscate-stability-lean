import SolitonClassification.Rotating.IntegerFamilyIdentification
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric Filter Asymptotics
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem wideFlow_add (a : State) (s t : ℝ) :
    wideFlow (s+t,a)=wideFlow (t,wideFlow (s,a)) := by
  let y := fun u : ℝ => wideFlow (s+u,a)
  have hy (u : ℝ) : HasDerivAt y (wideField (y u)) u := by
    simpa only [y,Function.comp_def,id_eq,one_smul] using
      (wideFlow_time a (s+u)).scomp u ((hasDerivAt_id u).const_add s)
  have eq : y=(fun u => wideFlow (u,wideFlow (s,a))) :=
    (exists_unique_global_bounded_flow wideField_lipschitz wideField_bound (wideFlow (s,a))).unique
      ⟨by simp [y],hy⟩ ⟨wideFlow_zero _,wideFlow_time _⟩
  exact congrFun eq t

theorem wide_time_lip (a : State) : LipschitzWith 110 (fun t : ℝ => wideFlow (t,a)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro t
    exact (wideFlow_time a t).differentiableAt
  · intro t
    rw [←NNReal.coe_le_coe,coe_nnnorm,(wideFlow_time a t).deriv]
    exact wideField_bound _

theorem wide_time_increment (a : State) (s t : ℝ) :
    ‖wideFlow (s+t,a)-wideFlow (s,a)-t • wideField (wideFlow (s,a))‖≤4400*|t|^2 := by
  let f := fun u : ℝ => wideFlow (s+u*t,a)-u • (t • wideField (wideFlow (s,a)))
  let v := fun u : ℝ => t • (wideField (wideFlow (s+u*t,a))-wideField (wideFlow (s,a)))
  have df (u : ℝ) : HasDerivAt f (v u) u := by
    have dt := ((hasDerivAt_id u).mul_const t).const_add s
    have h := ((wideFlow_time a (s+u*t)).scomp u dt).sub
      ((hasDerivAt_id u).smul_const (t • wideField (wideFlow (s,a))))
    dsimp only [v]
    rw [smul_sub]
    simpa only [f,Function.comp_def,id_eq,one_mul,one_smul,Pi.sub_def] using h
  have vel (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : ‖v u‖≤4400*|t|^2 := by
    have ds := lipschitzWith_iff_norm_sub_le.mp (wide_time_lip a) (s+u*t) s
    have dw := lipschitzWith_iff_norm_sub_le.mp wideField_lipschitz
      (wideFlow (s+u*t,a)) (wideFlow (s,a))
    simp only [add_sub_cancel_left,Real.norm_eq_abs,abs_mul,abs_of_nonneg hu.1,NNReal.coe_ofNat] at ds
    have va : ‖v u‖≤|t| * (40*(110*(u*|t|))) := by
      dsimp only [v]
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (dw.trans (mul_le_mul_of_nonneg_left ds (by norm_num))) (abs_nonneg _)
    exact va.trans (by nlinarith only [mul_le_mul_of_nonneg_right hu.2 (sq_nonneg |t|)])
  have w := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (df u).hasDerivWithinAt) vel (x:=0) (y:=1) (by norm_num) (by norm_num)
  simp only [f,one_mul,zero_mul,one_smul,zero_smul,add_zero,sub_zero,Real.norm_eq_abs,
    abs_one,mul_one] at w
  rwa [show wideFlow (s+t,a)-t • wideField (wideFlow (s,a))-wideFlow (s,a)=
      wideFlow (s+t,a)-wideFlow (s,a)-t • wideField (wideFlow (s,a)) by abel] at w

def fullDifferential (s : ℝ) (a : State) (J : State →L[ℝ] State) :
    (ℝ×State) →L[ℝ] State :=
  (ContinuousLinearMap.toSpanSingleton ℝ (wideField (wideFlow (s,a)))).coprod J

/-- For this autonomous flow a space derivative at one point already supplies
the joint derivative. No assumed continuous family of space derivatives is
needed to account for the moving endpoint time. -/
theorem joint_of_space {s : ℝ} {a : State} {J : State →L[ℝ] State}
    (d : HasFDerivAt (fun b => wideFlow (s,b)) J a) :
    HasFDerivAt wideFlow (fullDifferential s a J) (s,a) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]
  intro ε pos
  let inc := fun h : ℝ×State => a+h.2
  have ti : Tendsto inc (𝓝 0) (𝓝 a) := by
    have h : Continuous inc := continuous_const.add continuous_snd
    simpa only [inc,Prod.snd_zero,add_zero] using (h.continuousAt (x:=0)).tendsto
  have dc := d.continuousAt.tendsto.comp ti
  have smallF : ∀ᶠ h : ℝ×State in 𝓝 0,
      dist (wideField (wideFlow (s,a+h.2))) (wideField (wideFlow (s,a))) < ε/3 :=
    (Metric.tendsto_nhds.mp (wideField_lipschitz.continuous.continuousAt.tendsto.comp dc)) _
      (by positivity)
  have proj : Tendsto (fun h : ℝ×State => h.2) (𝓝 0) (𝓝 0) := continuous_snd.continuousAt
  have rem := proj ((isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp d)) (show 0<ε/3 by positivity))
  have small : ∀ᶠ h : ℝ×State in 𝓝 0, ‖h‖<ε/13200 := by
    exact (tendsto_norm_zero.eventually (eventually_lt_nhds (by positivity)))
  filter_upwards [smallF,small,rem] with h hf hs hr
  let R := wideFlow (s+h.1,a+h.2)-wideFlow (s,a+h.2)-h.1 • wideField (wideFlow (s,a+h.2))
  let Q := h.1 • (wideField (wideFlow (s,a+h.2))-wideField (wideFlow (s,a)))
  let A := wideFlow (s,a+h.2)-wideFlow (s,a)-J h.2
  have decomp : wideFlow ((s,a)+h)-wideFlow (s,a)-fullDifferential s a J h = R+Q+A := by
    change wideFlow (s+h.1,a+h.2)-wideFlow (s,a)-(h.1 • wideField (wideFlow (s,a))+J h.2)=_
    dsimp only [R,Q,A]
    rw [smul_sub]
    abel
  have timele : |h.1|≤‖h‖ := norm_fst_le h
  have qle : ‖Q‖≤(ε/3)*‖h‖ := by
    dsimp [Q]
    rw [norm_smul,Real.norm_eq_abs,mul_comm]
    exact mul_le_mul (by simpa only [dist_eq_norm] using hf.le) timele (abs_nonneg _) (by positivity)
  have rle : ‖R‖≤(ε/3)*‖h‖ := by
    apply (wide_time_increment (a+h.2) s h.1).trans
    have z := mul_le_mul (timele.trans hs.le) timele (abs_nonneg _) (by positivity)
    nlinarith only [z]
  have ale : ‖A‖≤(ε/3)*‖h‖ :=
    hr.trans (mul_le_mul_of_nonneg_left (norm_snd_le h) (by positivity))
  rw [decomp]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add rle qle)) ale)).trans_eq (by ring)

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.joint_of_space
