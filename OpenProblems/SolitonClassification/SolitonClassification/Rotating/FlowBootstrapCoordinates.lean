import SolitonClassification.Rotating.FlowBootstrapGeometry
import SolitonClassification.Rotating.FlowMetricSegment

/-! Actual nonlinear state comparison in moving-matrix coordinates.
No actual tube neighborhood or actual state-error bound is assumed.
Pointwise original-field identities are used only where tube membership
has separately been obtained from the proposed error radius. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def bootstrapError (σ : ℝ) (hσ : |σ|≤1) (a : State)
    (X : ℝ → State) (M : ℝ → FlowEnd) (t : ℝ) : State :=
  Ring.inverse (M t) (supportFlow σ hσ t a-X t)

def bootstrapVelocity (σ : ℝ) (x X : State) (M Z : FlowEnd) (r : State) : State :=
  Ring.inverse M (σ • (field x-field X-fderiv ℝ field X (x-X))-
    r-Z (Ring.inverse M (x-X)))

theorem bootstrap_error_reconstruct (σ : ℝ) (hσ : |σ|≤1) (a : State)
    (X : ℝ → State) (M : ℝ → FlowEnd) (t : ℝ) (hu : IsUnit (M t)) :
    supportFlow σ hσ t a-X t=M t (bootstrapError σ hσ a X M t) := by
  have h := congrArg (fun L : FlowEnd => L (supportFlow σ hσ t a-X t))
    (Ring.mul_inverse_cancel (M t) hu)
  exact h.symm

theorem bootstrap_error_continuousOn (σ : ℝ) (hσ : |σ|≤1) (a : State)
    {X : ℝ → State} {M : ℝ → FlowEnd} {S : Set ℝ}
    (hX : ContinuousOn X S) (hM : ContinuousOn M S) (hu : ∀t∈S,IsUnit (M t)) :
    ContinuousOn (bootstrapError σ hσ a X M) S := by
  have hx : Continuous (fun t => supportFlow σ hσ t a) :=
    continuous_iff_continuousAt.mpr fun t => (supportFlow_derivative σ hσ a t).continuousAt
  exact (referenceInverse_continuousOn hM hu).clm_apply (hx.continuousOn.sub hX)

theorem bootstrap_derivative_algebra (σ : ℝ) (x X : State) (M Z : FlowEnd) (r : State)
    (hu : IsUnit M) :
    (-(Ring.inverse M*((σ • fderiv ℝ field X)*M+Z)*Ring.inverse M)) (x-X)+
      Ring.inverse M (σ • field x-(σ • field X+r))=bootstrapVelocity σ x X M Z r := by
  have he : M (Ring.inverse M (x-X))=x-X :=
    congrArg (fun L : FlowEnd => L (x-X)) (Ring.mul_inverse_cancel M hu)
  change -(Ring.inverse M ((σ • fderiv ℝ field X) (M (Ring.inverse M (x-X)))+
    Z (Ring.inverse M (x-X))))+Ring.inverse M (σ • field x-(σ • field X+r))=_
  rw [he]
  simp only [bootstrapVelocity,map_add,map_sub,map_smul,smul_sub,smul_apply]
  abel

theorem bootstrap_error_hasDerivWithinAt (σ : ℝ) (hσ : |σ|≤1) (a : State)
    {X : ℝ → State} {M : ℝ → FlowEnd} {Z : FlowEnd} {r : State} {t : ℝ}
    (hx : supportFlow σ hσ t a∈outerTube) (hu : IsUnit (M t))
    (hX : HasDerivWithinAt X (σ • field (X t)+r) (Ici t) t)
    (hM : HasDerivWithinAt M ((σ • fderiv ℝ field (X t))*M t+Z) (Ici t) t) :
    HasDerivWithinAt (bootstrapError σ hσ a X M)
      (bootstrapVelocity σ (supportFlow σ hσ t a) (X t) (M t) Z r) (Ici t) t := by
  have hd := (referenceInverse_hasDerivWithinAt hM hu).clm_apply
    ((supportFlow_original_derivative σ hσ a t hx).hasDerivWithinAt.sub hX)
  convert! hd using 1
  exact (bootstrap_derivative_algebra σ (supportFlow σ hσ t a) (X t) (M t) Z r hu).symm

theorem bootstrap_physical_error_bound (σ : ℝ) (hσ : |σ|≤1) (a : State)
    {X : ℝ → State} {M : ℝ → FlowEnd} {t K R : ℝ}
    (hu : IsUnit (M t)) (hK : 0≤K) (hM : ‖M t‖≤K)
    (hw : ‖bootstrapError σ hσ a X M t‖≤R) :
    ‖supportFlow σ hσ t a-X t‖≤K*R := by
  rw [bootstrap_error_reconstruct σ hσ a X M t hu]
  exact ((M t).le_opNorm _).trans (mul_le_mul hM hw (norm_nonneg _) hK)

theorem bootstrap_tube_of_error_bound (σ : ℝ) (hσ : |σ|≤1) (a : State)
    {X : ℝ → State} {M : ℝ → FlowEnd} {t K R : ℝ}
    (hu : IsUnit (M t)) (hK : 0≤K) (hM : ‖M t‖≤K)
    (hmargin : outerTubeMargin (X t) (K*R)) (hw : ‖bootstrapError σ hσ a X M t‖≤R) :
    supportFlow σ hσ t a∈outerTube :=
  outerTube_of_margin hmargin (bootstrap_physical_error_bound σ hσ a hu hK hM hw)

theorem bootstrap_velocity_bound (σ : ℝ) (hσ : |σ|≤1)
    {x X : State} {M Z : FlowEnd} {r : State} {K I R ρ δ : ℝ}
    (hx : x∈outerTube) (hX : X∈outerTube) (hu : IsUnit M)
    (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ)
    (hM : ‖M‖≤K) (hInv : ‖Ring.inverse M‖≤I)
    (hZ : ‖Z‖≤ρ) (hr : ‖r‖≤δ) (hw : ‖Ring.inverse M (x-X)‖≤R) :
    ‖bootstrapVelocity σ x X M Z r‖≤I*(2*K^2*R^2+ρ*R+δ) := by
  have he : x-X=M (Ring.inverse M (x-X)) :=
    (congrArg (fun L : FlowEnd => L (x-X)) (Ring.mul_inverse_cancel M hu)).symm
  have hen : ‖x-X‖≤K*R := by
    rw [he]
    exact (M.le_opNorm _).trans (mul_le_mul hM hw (norm_nonneg _) hK)
  have hquad := field_quadratic_remainder_bound hX hx
  have hsq : ‖x-X‖^2≤(K*R)^2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK hR)).mpr hen
  have hs : ‖σ • (field x-field X-fderiv ℝ field X (x-X))‖≤2*K^2*R^2 := by
    rw [norm_smul,Real.norm_eq_abs]
    have hm := mul_le_mul_of_nonneg_right hσ
      (norm_nonneg (field x-field X-fderiv ℝ field X (x-X)))
    nlinarith
  have hz : ‖Z (Ring.inverse M (x-X))‖≤ρ*R :=
    (Z.le_opNorm _).trans (mul_le_mul hZ hw (norm_nonneg _) hρ)
  have hb : ‖σ • (field x-field X-fderiv ℝ field X (x-X))-r-Z (Ring.inverse M (x-X))‖≤
      2*K^2*R^2+ρ*R+δ := by
    exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hs hr)) hz) |>.trans_eq (by ring)
  exact ((Ring.inverse M).le_opNorm _).trans (mul_le_mul hInv hb (norm_nonneg _) hI)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating nonlinear state-coordinate audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating nonlinear state-coordinate audit passed for {count} declarations."
