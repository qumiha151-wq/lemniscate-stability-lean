module

public import SolitonClassification.Rotating.QuantitativeJoint
public import SolitonClassification.Rotating.ActualShooting

@[expose] public section

/-! Quantitative derivative variation of the actual five-parameter shooting
map from true fundamental/inverse matrix bounds. No shooting Hessian bound
or assumed smooth flow is used as a premise. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem shootingInitial_norm_bound (e : Fin 2 → ℝ) (he0 : |e 0|≤1) (he1 : |e 1|≤1)
    (u : Parameters) : ‖shootingInitial e u‖≤‖u‖ := by
  have hc (i : Fin 5) : |u i|≤‖u‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
  have hn := norm_nonneg u
  rw [pi_norm_le_iff_of_nonneg hn,shootingInitial_apply]
  intro i
  fin_cases i
  · exact hc 0
  · change |u 3*e 0/8|≤‖u‖
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : 0<(8:ℝ))]
    have hm := mul_le_mul (hc 3) he0 (abs_nonneg _) hn
    nlinarith
  · exact hc 1
  · change |u 3*e 1|≤‖u‖
    rw [abs_mul]
    exact (mul_le_mul (hc 3) he1 (abs_nonneg _) hn).trans_eq (mul_one _)
  · exact hc 4
  · simp

theorem forwardEndpointInput_norm (e : Fin 2 → ℝ) (he0 : |e 0|≤1) (he1 : |e 1|≤1) :
    ‖forwardEndpointInput e‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change max ‖u 2‖ ‖shootingInitial e u‖≤1*‖u‖
  rw [one_mul]
  exact max_le (norm_le_pi_norm u 2) (shootingInitial_norm_bound e he0 he1 u)

theorem forwardEndpointInput_distance (e : Fin 2 → ℝ) (he0 : |e 0|≤1) (he1 : |e 1|≤1)
    (p q : Parameters) : dist (forwardEndpointInput e p) (forwardEndpointInput e q)≤dist p q := by
  simp only [dist_eq_norm,←map_sub]
  exact ((forwardEndpointInput e).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (forwardEndpointInput_norm e he0 he1) (norm_nonneg _)).trans_eq (one_mul _))

def signedShootingDerivative (e : Fin 2 → ℝ) (p : Parameters) : Parameters →L[ℝ] Parameters :=
  shootingProjection.comp
    ((supportFlowDifferential 1 (by norm_num) (forwardEndpointInput e p)-
      supportFlowDifferential (-1) (by norm_num) (forwardEndpointInput e p)).comp (forwardEndpointInput e))

theorem actualShootingMap_signed (e : Fin 2 → ℝ) (p : Parameters) :
    actualShootingMap e p=
      shootingProjection (supportFlow 1 (by norm_num) (p 2) (shootingInitial e p)-
        supportFlow (-1) (by norm_num) (p 2) (shootingInitial e p))+shootingTarget := by
  change shootingProjection (supportFlow 1 (by norm_num) (p 2) (shootingInitial e p)-
    supportFlow 1 (by norm_num) (-(p 2)) (shootingInitial e p))+shootingTarget=_
  rw [supportFlow_reflection]

theorem actualShootingMap_signed_hasStrictFDerivAt (e : Fin 2 → ℝ) (T : ℝ)
    {c : State} {R : ℝ} (hR : 0<R)
    (hplus : FlowTubeNeighborhood 1 (by norm_num) T c R)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) T c R)
    {p : Parameters} (hlength : p 2∈Ioo 0 T)
    (hinitial : shootingInitial e p∈Metric.ball c (R/4)) :
    HasStrictFDerivAt (actualShootingMap e) (signedShootingDerivative e p) p := by
  have hp := (supportFlow_hasStrictFDerivAt_joint 1 (by norm_num) T hR hplus
    (p:=forwardEndpointInput e p) ⟨hlength,hinitial⟩).comp p (forwardEndpointInput e).hasStrictFDerivAt
  have hm := (supportFlow_hasStrictFDerivAt_joint (-1) (by norm_num) T hR hminus
    (p:=forwardEndpointInput e p) ⟨hlength,hinitial⟩).comp p (forwardEndpointInput e).hasStrictFDerivAt
  have hd := (shootingProjection.hasStrictFDerivAt.comp p (hp.sub hm)).add_const shootingTarget
  convert! hd using 1
  · funext a
    exact actualShootingMap_signed e a

theorem actualShootingDerivative_eq_signed (e : Fin 2 → ℝ) (T : ℝ)
    {c : State} {R : ℝ} (hR : 0<R)
    (hplus : FlowTubeNeighborhood 1 (by norm_num) T c R)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) T c R)
    {p : Parameters} (hlength : p 2∈Ioo 0 T)
    (hinitial : shootingInitial e p∈Metric.ball c (R/4)) :
    actualShootingDerivative e p=signedShootingDerivative e p :=
  (actualShootingMap_hasStrictFDerivAt e T hR hplus hminus hlength hinitial).hasFDerivAt.unique
    (actualShootingMap_signed_hasStrictFDerivAt e T hR hplus hminus hlength hinitial).hasFDerivAt

theorem actualShootingDerivative_sharp_variation
    (e : Fin 2 → ℝ) (he0 : |e 0|≤1) (he1 : |e 1|≤1)
    {T : ℝ} (hT : 0≤T) {c : State} {R K I : ℝ} {S : Set State}
    (hR : 0<R) (hK : 0≤K) (hI : 0≤I)
    (hplus : FlowTubeNeighborhood 1 (by norm_num) T c R)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) T c R)
    (hS : Convex ℝ S) (hsub : S⊆Metric.ball c (R/4))
    (hPplus : ∀a∈S,∀t∈Icc 0 T,‖fderiv ℝ (supportFlow 1 (by norm_num) t) a‖≤K)
    (hPminus : ∀a∈S,∀t∈Icc 0 T,‖fderiv ℝ (supportFlow (-1) (by norm_num) t) a‖≤K)
    (Qplus Qminus : State → ℝ → State →L[ℝ] State)
    (hQcplus : ∀a∈S,ContinuousOn (Qplus a) (Icc 0 T))
    (hQcminus : ∀a∈S,ContinuousOn (Qminus a) (Icc 0 T))
    (hPQplus : ∀a∈S,∀t∈Icc 0 T,
      (fderiv ℝ (supportFlow 1 (by norm_num) t) a).comp (Qplus a t)=ContinuousLinearMap.id ℝ State)
    (hPQminus : ∀a∈S,∀t∈Icc 0 T,
      (fderiv ℝ (supportFlow (-1) (by norm_num) t) a).comp (Qminus a t)=ContinuousLinearMap.id ℝ State)
    (hQplus : ∀a∈S,∀t∈Icc 0 T,‖Qplus a t‖≤I)
    (hQminus : ∀a∈S,∀t∈Icc 0 T,‖Qminus a t‖≤I)
    {p q : Parameters} (hp : p 2∈Ioo 0 T ∧ shootingInitial e p∈S)
    (hq : q 2∈Ioo 0 T ∧ shootingInitial e q∈S) :
    ‖actualShootingDerivative e p-actualShootingDerivative e q‖≤
      (16*trueJointVariationBudget T K I)*dist p q := by
  let B := trueJointVariationBudget T K I
  have hB : 0≤B := by dsimp [B,trueJointVariationBudget]; positivity
  have hsub' : S⊆Metric.ball c R := by
    intro a ha
    have hh := hsub ha
    change dist a c<R/4 at hh
    change dist a c<R
    linarith
  let x := forwardEndpointInput e p
  let y := forwardEndpointInput e q
  have hx : x∈Icc 0 T ×ˢ S := ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2⟩
  have hy : y∈Icc 0 T ×ˢ S := ⟨⟨hq.1.1.le,hq.1.2.le⟩,hq.2⟩
  have hDp := supportFlowDifferential_sharp_variation 1 (by norm_num) hT hK hI hplus hS hsub'
    hPplus Qplus hQcplus hPQplus hQplus hx hy
  have hDm := supportFlowDifferential_sharp_variation (-1) (by norm_num) hT hK hI hminus hS hsub'
    hPminus Qminus hQcminus hPQminus hQminus hx hy
  rw [actualShootingDerivative_eq_signed e T hR hplus hminus hp.1 (hsub hp.2),
    actualShootingDerivative_eq_signed e T hR hplus hminus hq.1 (hsub hq.2)]
  let W := (supportFlowDifferential 1 (by norm_num) x-supportFlowDifferential 1 (by norm_num) y)-
    (supportFlowDifferential (-1) (by norm_num) x-supportFlowDifferential (-1) (by norm_num) y)
  have hW : ‖W‖≤2*B*dist x y := by
    have hn := norm_sub_le (supportFlowDifferential 1 (by norm_num) x-supportFlowDifferential 1 (by norm_num) y)
      (supportFlowDifferential (-1) (by norm_num) x-supportFlowDifferential (-1) (by norm_num) y)
    change ‖W‖≤_ at hn
    change _≤B*dist x y at hDp hDm
    linarith
  have he : signedShootingDerivative e p-signedShootingDerivative e q=
      shootingProjection.comp (W.comp (forwardEndpointInput e)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [signedShootingDerivative,W,x,y,ContinuousLinearMap.comp_apply,sub_apply,map_sub]
    abel
  have hWd : ‖W.comp (forwardEndpointInput e)‖≤2*B*dist x y := by
    exact (W.opNorm_comp_le _).trans
      ((mul_le_mul hW (forwardEndpointInput_norm e he0 he1) (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
  have hxy : dist x y≤dist p q := forwardEndpointInput_distance e he0 he1 p q
  rw [he]
  have hn := (shootingProjection.opNorm_comp_le (W.comp (forwardEndpointInput e))).trans
    (mul_le_mul shootingProjection_norm hWd (norm_nonneg _) (by norm_num))
  have hmul := mul_le_mul_of_nonneg_left hxy (by positivity : 0≤16*B)
  change _≤(16*B)*dist p q
  nlinarith

/-- Pure arithmetic for the certificate's intended actual-matrix budgets.
This does not assert that those matrix bounds have been validated. -/
theorem true_shooting_budget_lt :
    16*trueJointVariationBudget 32 8000 16000<(10:ℝ)^20 := by
  norm_num [trueJointVariationBudget]

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating sharp shooting variation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating sharp shooting variation audit passed for {count} declarations."
