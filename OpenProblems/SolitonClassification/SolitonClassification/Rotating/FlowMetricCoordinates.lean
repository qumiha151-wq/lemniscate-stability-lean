import SolitonClassification.Rotating.FlowInverseODE

/-! Moving-matrix coordinates for the actual variational flow and its
canonical inverse. The reference is an actually differentiable matrix
function. Its derivative is retained in the coefficient, so a polynomial
reference cannot silently lose its differential residual. This proof is
self-contained and imports no other open-problem project. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

abbrev FlowEnd := State →L[ℝ] State

def flowMetricCoefficient (A M dM : FlowEnd) : FlowEnd :=
  Ring.inverse M*(A*M-dM)

def flowMetricForward (σ : ℝ) (hσ : |σ|≤1) (a : State)
    (M : ℝ → FlowEnd) (t : ℝ) : FlowEnd :=
  Ring.inverse (M t)*fderiv ℝ (supportFlow σ hσ t) a

def flowMetricInverse (σ : ℝ) (hσ : |σ|≤1) (a : State)
    (M : ℝ → FlowEnd) (t : ℝ) : FlowEnd :=
  supportFlowInverse σ hσ a t*M t

lemma flowEnd_neg_mul (A B : FlowEnd) : (-A)*B=-(A*B) := by
  ext u i
  rfl

theorem referenceInverse_hasDerivWithinAt {M : ℝ → FlowEnd} {dM : FlowEnd}
    {s : Set ℝ} {t : ℝ} (hM : HasDerivWithinAt M dM s t) (hu : IsUnit (M t)) :
    HasDerivWithinAt (fun r => Ring.inverse (M r))
      (-(Ring.inverse (M t)*dM*Ring.inverse (M t))) s t := by
  obtain ⟨u,hu⟩ := hu
  have hi : (↑u⁻¹ : FlowEnd)=Ring.inverse (M t) := by rw [←Ring.inverse_unit,hu]
  have hdi := hasFDerivAt_ringInverse (𝕜:=ℝ) u
  rw [hu] at hdi
  have hd := hdi.comp_hasDerivWithinAt t hM
  convert! hd using 1
  simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,hi]

theorem metric_forward_algebra (A M dM P : FlowEnd) (hu : IsUnit M) :
    -(Ring.inverse M*dM*Ring.inverse M)*P+Ring.inverse M*(A*P)=
      flowMetricCoefficient A M dM*(Ring.inverse M*P) := by
  have hMP : M*(Ring.inverse M*P)=P := by
    rw [←mul_assoc,Ring.mul_inverse_cancel M hu,one_mul]
  change -(Ring.inverse M*dM*Ring.inverse M)*P+Ring.inverse M*(A*P)=_
  rw [flowEnd_neg_mul]
  simp only [flowMetricCoefficient,mul_sub,sub_mul,mul_assoc,hMP]
  abel

theorem metric_inverse_algebra (A M dM Q : FlowEnd) (hu : IsUnit M) :
    -(Q*A)*M+Q*dM=-(Q*M)*flowMetricCoefficient A M dM := by
  have hMX : M*(Ring.inverse M*(A*M-dM))=A*M-dM := by
    rw [←mul_assoc,Ring.mul_inverse_cancel M hu,one_mul]
  rw [flowEnd_neg_mul,flowEnd_neg_mul]
  simp only [flowMetricCoefficient,mul_assoc]
  rw [hMX]
  simp only [mul_sub,neg_sub]
  abel

theorem flowMetricForward_hasDerivWithinAt (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c a : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Ico 0 T)
    {M : ℝ → FlowEnd} {dM : FlowEnd}
    (hM : HasDerivWithinAt M dM (Ici t) t) (hu : IsUnit (M t)) :
    HasDerivWithinAt (flowMetricForward σ hσ a M)
      (flowMetricCoefficient (flowLinearCoefficient σ hσ a t) (M t) dM*
        flowMetricForward σ hσ a M t) (Ici t) t := by
  have hd := (referenceInverse_hasDerivWithinAt hM hu).mul
    (supportFlow_fderiv_hasDerivWithinAt σ hσ hreg ha ht)
  change HasDerivWithinAt (flowMetricForward σ hσ a M)
    (-(Ring.inverse (M t)*dM*Ring.inverse (M t))*fderiv ℝ (supportFlow σ hσ t) a+
      Ring.inverse (M t)*(flowLinearCoefficient σ hσ a t*fderiv ℝ (supportFlow σ hσ t) a)) (Ici t) t at hd
  simpa only [metric_forward_algebra _ _ _ _ hu,flowMetricForward] using hd

theorem flowMetricInverse_hasDerivWithinAt (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c a : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Ico 0 T)
    {M : ℝ → FlowEnd} {dM : FlowEnd}
    (hM : HasDerivWithinAt M dM (Ici t) t) (hu : IsUnit (M t)) :
    HasDerivWithinAt (flowMetricInverse σ hσ a M)
      (-flowMetricInverse σ hσ a M t*
        flowMetricCoefficient (flowLinearCoefficient σ hσ a t) (M t) dM) (Ici t) t := by
  have hd := (supportFlow_inverse_hasDerivWithinAt σ hσ hreg ha ht).mul hM
  change HasDerivWithinAt (flowMetricInverse σ hσ a M)
    (-(supportFlowInverse σ hσ a t*flowLinearCoefficient σ hσ a t)*M t+
      supportFlowInverse σ hσ a t*dM) (Ici t) t at hd
  simpa only [metric_inverse_algebra _ _ _ _ hu,flowMetricInverse] using hd

theorem flowMetricCoefficient_residual_identity (A B M Z : FlowEnd) :
    flowMetricCoefficient A M (B*M+Z)=Ring.inverse M*((A-B)*M-Z) := by
  simp only [flowMetricCoefficient,sub_mul]
  congr 1
  abel

theorem flowMetricCoefficient_norm_bound {A B M Z : FlowEnd} {I K d ρ : ℝ}
    (hI : 0≤I) (hd : 0≤d) (hInv : ‖Ring.inverse M‖≤I) (hM : ‖M‖≤K)
    (hAB : ‖A-B‖≤d) (hZ : ‖Z‖≤ρ) :
    ‖flowMetricCoefficient A M (B*M+Z)‖≤I*(d*K+ρ) := by
  rw [flowMetricCoefficient_residual_identity]
  apply (norm_mul_le _ _).trans
  apply mul_le_mul hInv _ (norm_nonneg _) hI
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_mul_le _ _).trans (mul_le_mul hAB hM (norm_nonneg _) hd)) hZ)

theorem actual_flowMetricCoefficient_norm_bound (σ : ℝ) (hσ : |σ|≤1)
    {a X : State} {t E I K ρ : ℝ} {M Z : FlowEnd}
    (hx : supportFlow σ hσ t a∈outerTube) (hX : X∈outerTube)
    (hE : 0≤E) (hI : 0≤I) (he : ‖supportFlow σ hσ t a-X‖≤E)
    (hInv : ‖Ring.inverse M‖≤I) (hM : ‖M‖≤K) (hZ : ‖Z‖≤ρ) :
    ‖flowMetricCoefficient (flowLinearCoefficient σ hσ a t) M
      ((σ • fderiv ℝ field X)*M+Z)‖≤I*(4*E*K+ρ) := by
  apply flowMetricCoefficient_norm_bound hI (by positivity) hInv hM _ hZ
  have hf := field_fderiv_difference hx hX
  have hs : ‖σ • (fderiv ℝ field (supportFlow σ hσ t a)-fderiv ℝ field X)‖≤
      ‖fderiv ℝ field (supportFlow σ hσ t a)-fderiv ℝ field X‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans_eq (one_mul _)
  have heq : σ • fderiv ℝ field (supportFlow σ hσ t a)-σ • fderiv ℝ field X=
      σ • (fderiv ℝ field (supportFlow σ hσ t a)-fderiv ℝ field X) := by
    ext u i
    simp [smul_sub]
  change ‖σ • fderiv ℝ field (supportFlow σ hσ t a)-σ • fderiv ℝ field X‖≤4*E
  rw [heq]
  exact hs.trans (hf.trans (mul_le_mul_of_nonneg_left he (by norm_num)))

theorem actual_fderiv_from_metric (σ : ℝ) (hσ : |σ|≤1) (a : State)
    (M : ℝ → FlowEnd) (t : ℝ) (hu : IsUnit (M t)) :
    fderiv ℝ (supportFlow σ hσ t) a=M t*flowMetricForward σ hσ a M t := by
  simp only [flowMetricForward,←mul_assoc,Ring.mul_inverse_cancel _ hu,one_mul]

theorem actual_inverse_from_metric (σ : ℝ) (hσ : |σ|≤1) (a : State)
    (M : ℝ → FlowEnd) (t : ℝ) (hu : IsUnit (M t)) :
    supportFlowInverse σ hσ a t=flowMetricInverse σ hσ a M t*Ring.inverse (M t) := by
  simp only [flowMetricInverse,mul_assoc,Ring.mul_inverse_cancel _ hu,mul_one]

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual moving-matrix coordinate audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual moving-matrix coordinate audit passed for {count} declarations."
