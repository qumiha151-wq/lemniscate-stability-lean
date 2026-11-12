import CentroidEscape.MetricShootingJacobian
import CentroidEscape.ValidatedRoot

namespace CentroidEscape
noncomputable section
open Set Real
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def centralDifference (f : E → F) (p u : E) (δ : ℝ) : F :=
  (1/(2*δ):ℝ) • (f (p+δ • u)-f (p-δ • u))

/-- A conservative central-difference error bound for a genuine derivative.
The proof uses the actual derivative along the probe segment. -/
theorem centralDifference_error {f : E → F} {D : E → E →L[ℝ] F}
    {p u : E} {R H δ : ℝ} (hH : 0≤H) (hδ : 0<δ) (hδR : δ<R) (hu : ‖u‖=1)
    (hderiv : ∀ x∈Metric.ball p R, HasFDerivAt f (D x) x)
    (hvariation : ∀ x∈Metric.ball p R, ‖D x-D p‖≤H*dist x p) :
    ‖centralDifference f p u δ-D p u‖≤H*δ := by
  let e : ℝ → F := fun s=>f (p+s • u)-s • D p u
  have hmem (s : ℝ) (hs : s∈Icc (-δ) δ) : p+s • u∈Metric.ball p R := by
    change dist (p+s • u) p<R
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,hu,mul_one]
    exact (abs_le.mpr hs).trans_lt hδR
  have hd (s : ℝ) (hs : s∈Icc (-δ) δ) :
      HasDerivAt e ((D (p+s • u)-D p) u) s := by
    have hl : HasDerivAt (fun r : ℝ=>p+r • u) u s := by
      simpa only [id_eq,one_smul] using ((hasDerivAt_id s).smul_const u).const_add p
    have hh := ((hderiv _ (hmem s hs)).comp_hasDerivAt s hl).sub
      ((hasDerivAt_id s).smul_const (D p u))
    convert! hh using 1
    simp only [sub_apply,one_smul]
  have hb (s : ℝ) (hs : s∈Icc (-δ) δ) : ‖(D (p+s • u)-D p) u‖≤H*δ := by
    have ho := (D (p+s • u)-D p).le_opNorm u
    have hv := hvariation _ (hmem s hs)
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,hu,mul_one] at hv
    rw [hu,mul_one] at ho
    exact ho.trans (hv.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hs) hH))
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs=>(hd s hs).hasDerivWithinAt) hb (convex_Icc (-δ) δ)
    (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
  have he : centralDifference f p u δ-D p u=(1/(2*δ):ℝ) • (e δ-e (-δ)) := by
    have hcoeff : (1/(2*δ):ℝ)*(2*δ)=1 := by field_simp
    have he' : e δ-e (-δ)=f (p+δ • u)-f (p-δ • u)-(2*δ) • D p u := by
      dsimp [e]
      simp only [neg_smul,sub_eq_add_neg]
      module
    rw [he',smul_sub,smul_smul,hcoeff,one_smul]
    rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr (by positivity : 0<2*δ))]
  calc
    (1/(2*δ))*‖e δ-e (-δ)‖ ≤ (1/(2*δ))*(H*δ*‖δ-(-δ)‖) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = H*δ := by
      rw [Real.norm_eq_abs,abs_of_pos (by linarith : 0<δ-(-δ))]
      field_simp
      ring

/-- Endpoint enclosures contribute eta/delta to a central-difference column. -/
theorem centralDifference_endpoint_error {f : E → F} {p u : E} {δ η : ℝ}
    (hδ : 0<δ) {yp ym : F} (hp : ‖yp-f (p+δ • u)‖≤η) (hm : ‖ym-f (p-δ • u)‖≤η) :
    ‖(1/(2*δ):ℝ) • (yp-ym)-centralDifference f p u δ‖≤η/δ := by
  have he : (1/(2*δ):ℝ) • (yp-ym)-centralDifference f p u δ=
      (1/(2*δ):ℝ) • ((yp-f (p+δ • u))-(ym-f (p-δ • u))) := by
    unfold centralDifference
    module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr (by positivity : 0<2*δ))]
  have hn := norm_sub_le (yp-f (p+δ • u)) (ym-f (p-δ • u))
  calc
    _ ≤ (1/(2*δ))*(2*η) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = η/δ := by field_simp

def coordinateDirection (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

lemma coordinateDirection_norm (i : Fin 3) : ‖coordinateDirection i‖=1 := by
  simp [coordinateDirection,Pi.norm_single]

lemma coordinate_decomposition (v : Fin 3 → ℝ) :
    v=∑ i : Fin 3, v i • coordinateDirection i := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_succ,coordinateDirection]

def columnOperator (col : Fin 3 → F) : (Fin 3 → ℝ) →L[ℝ] F :=
  ∑ i : Fin 3, (ContinuousLinearMap.toSpanSingleton ℝ (col i)).comp (ContinuousLinearMap.proj i)

lemma columnOperator_apply (col : Fin 3 → F) (v : Fin 3 → ℝ) :
    columnOperator col v=∑ i : Fin 3, v i • col i := by
  simp [columnOperator]

/-- Three verified column errors control the infinity-norm operator error. -/
theorem columnOperator_error (col : Fin 3 → F) (A : (Fin 3 → ℝ) →L[ℝ] F)
    {ε : ℝ} (hε : 0≤ε) (hcol : ∀ i, ‖col i-A (coordinateDirection i)‖≤ε) :
    ‖columnOperator col-A‖≤3*ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : (columnOperator col-A) v=∑ i : Fin 3, v i • (col i-A (coordinateDirection i)) := by
    rw [sub_apply,columnOperator_apply]
    conv_lhs => rhs; rw [coordinate_decomposition v]
    simp only [map_sum,map_smul,Finset.sum_sub_distrib,smul_sub]
  rw [he]
  calc
    _ ≤ ∑ i : Fin 3, ‖v i • (col i-A (coordinateDirection i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖v‖*ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (hcol i) (norm_nonneg _) (norm_nonneg v)
    _ = (3*ε)*‖v‖ := by simp; ring

theorem centralDifference_columns_error {f : (Fin 3 → ℝ) → F}
    {D : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] F} {p : Fin 3 → ℝ} {R H δ η : ℝ}
    (hH : 0≤H) (hη : 0≤η) (hδ : 0<δ) (hδR : δ<R)
    (hderiv : ∀ x∈Metric.ball p R, HasFDerivAt f (D x) x)
    (hvariation : ∀ x∈Metric.ball p R, ‖D x-D p‖≤H*dist x p)
    (yp ym : Fin 3 → F)
    (hp : ∀ i, ‖yp i-f (p+δ • coordinateDirection i)‖≤η)
    (hm : ∀ i, ‖ym i-f (p-δ • coordinateDirection i)‖≤η) :
    ‖columnOperator (fun i=>(1/(2*δ):ℝ) • (yp i-ym i))-D p‖≤3*(H*δ+η/δ) := by
  apply columnOperator_error _ _ (by positivity)
  intro i
  have h1 := centralDifference_endpoint_error hδ (hp i) (hm i)
  have h2 := centralDifference_error hH hδ hδR (coordinateDirection_norm i) hderiv hvariation
  have htri := norm_sub_le_norm_sub_add_norm_sub ((1/(2*δ):ℝ) • (yp i-ym i))
    (centralDifference f p (coordinateDirection i) δ) (D p (coordinateDirection i))
  linarith

/-- Numerical endpoint enclosures now control the derivative of the ACTUAL
three-parameter shooting map. All derivative and variation hypotheses have
already been proved from the true ODE and interior reference. -/
theorem actualShooting_centralDifference_columns_error {T : ℝ} (hT : 0<T)
    (hTmin : 1≤T) (hbudget : shootingExtendedHorizon T≤15/2)
    {p₀ : Fin 3 → ℝ} (hcenter : p₀ 2=T)
    (hc : ∀t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {δ η : ℝ} (hη : 0≤η) (hδ : 0<δ) (hδR : δ<1/10^13)
    (yp ym : Fin 3 → (Fin 3 → ℝ))
    (hp : ∀ i, ‖yp i-actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) (p₀+δ • coordinateDirection i)‖≤η)
    (hm : ∀ i, ‖ym i-actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) (p₀-δ • coordinateDirection i)‖≤η) :
    ‖columnOperator (fun i=>(1/(2*δ):ℝ) • (yp i-ym i))-
      fderiv ℝ (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le)) p₀‖ ≤
      3*((6*10^14)*δ+η/δ) := by
  have hR := MetricStability.metricShootingParameterRadius_lower_bound hTmin hbudget
  have hsub : Metric.ball p₀ (1/10^13:ℝ) ⊆
      Metric.ball p₀ (MetricStability.metricShootingParameterRadius T) :=
    Metric.ball_subset_ball hR.le
  apply centralDifference_columns_error (R:=1/10^13) (by positivity) hη hδ hδR
    (yp:=yp) (ym:=ym) (hp:=hp) (hm:=hm)
  · intro x hx
    exact (MetricStability.actualShootingMap_hasFDerivAt_metric_extended hT hcenter hc
      (hsub hx)).differentiableAt.hasFDerivAt
  · intro x hx
    exact MetricStability.actualShootingMap_fderiv_metric_extended_budget hT hbudget hcenter hc
      (hsub hx) (Metric.mem_ball_self (MetricStability.metricShootingParameterRadius_pos hT))

/-- An approximate center Jacobian and a true derivative variation bound
give the uniform preconditioned derivative bound used by ValidatedRoot. -/
theorem preconditioned_derivative_from_center (D : E → E →L[ℝ] E)
    (B J : E →L[ℝ] E) {p x : E} {β ε H r q₀ : ℝ}
    (hβ : 0≤β) (hH : 0≤H) (hB : ‖B‖≤β)
    (hJ : ‖J-D p‖≤ε) (hD : ‖D x-D p‖≤H*dist x p) (hx : dist x p≤r)
    (hcenter : ‖ContinuousLinearMap.id ℝ E-B.comp J‖≤q₀) :
    ‖ContinuousLinearMap.id ℝ E-B.comp (D x)‖≤q₀+β*(ε+H*r) := by
  have he : ContinuousLinearMap.id ℝ E-B.comp (D x)=
      (ContinuousLinearMap.id ℝ E-B.comp J)+B.comp (J-D x) := by
    ext v
    simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
    abel
  have htri := norm_sub_le_norm_sub_add_norm_sub J (D p) (D x)
  rw [norm_sub_rev (D p) (D x)] at htri
  have hJx : ‖J-D x‖≤ε+H*r := by
    have hh := mul_le_mul_of_nonneg_left hx hH
    linarith
  have hcomp := B.opNorm_comp_le (J-D x)
  have hprod := mul_le_mul hB hJx (norm_nonneg _) hβ
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hcenter (hcomp.trans hprod))

/-- The looser H*delta central-difference bound still leaves ample margin
for the intended finite-difference and Newton radii. -/
theorem finiteDifference_newton_arithmetic_budget :
    (1/(10:ℝ)^9)+2*(3*((6*10^14)*(1/10^25)+(1/10^43)/(1/10^25))+
      (6*10^14)*(1/10^28))<2/10^9 := by
  norm_num

end
end CentroidEscape

#print axioms CentroidEscape.centralDifference_columns_error
#print axioms CentroidEscape.actualShooting_centralDifference_columns_error
#print axioms CentroidEscape.preconditioned_derivative_from_center

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Finite-difference derivative audit passed for {checked} declarations."
