import SolitonClassification.Rotating.ShootingVariation

/-! Actual shooting-center comparison from two state endpoints and two full
initial-value derivative matrices. The phase line is fixed exactly, the
negative-time length column has the correct positive sign, and the physical
projection's factor eight is retained. Numerical bounds remain inputs. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Metric
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def shootingEndpointValue (xplus xminus : State) : Parameters :=
  shootingProjection (xplus-xminus)+shootingTarget

def shootingEndpointDerivative (e : Fin 2 → ℝ) (xplus xminus : State)
    (Pplus Pminus : (State →L[ℝ] State)) : Parameters →L[ℝ] Parameters :=
  shootingProjection.comp
    ((ContinuousLinearMap.toSpanSingleton ℝ (field xplus+field xminus)).comp shootingLength+
      (Pplus-Pminus).comp (shootingInitial e))

theorem shootingEndpointDerivative_apply (e : Fin 2 → ℝ) (xplus xminus : State)
    (Pplus Pminus : (State →L[ℝ] State)) (u : Parameters) :
    shootingEndpointDerivative e xplus xminus Pplus Pminus u=
      shootingProjection ((u 2) • (field xplus+field xminus)+
        (Pplus-Pminus) (shootingInitial e u)) := rfl

theorem shootingEndpointDerivative_length_column (e : Fin 2 → ℝ) (xplus xminus : State)
    (Pplus Pminus : (State →L[ℝ] State)) :
    shootingEndpointDerivative e xplus xminus Pplus Pminus lengthDirection=
      shootingProjection (field xplus+field xminus) := by
  rw [shootingEndpointDerivative_apply]
  have hi : shootingInitial e lengthDirection=0 := congrArg Prod.snd (forward_lengthDirection e)
  change shootingProjection ((1:ℝ) • _+(Pplus-Pminus) (shootingInitial e lengthDirection))=_
  rw [hi,map_zero,one_smul,add_zero]

def shootingPhaseDirection : Parameters := ![0,0,0,1,0]

theorem shootingEndpointDerivative_phase_column (e : Fin 2 → ℝ) (xplus xminus : State)
    (Pplus Pminus : (State →L[ℝ] State)) :
    shootingEndpointDerivative e xplus xminus Pplus Pminus shootingPhaseDirection=
      shootingProjection ((Pplus-Pminus) ![0,e 0/8,0,e 1,0,0]) := by
  rw [shootingEndpointDerivative_apply,shootingInitial_apply]
  simp [shootingPhaseDirection]

theorem shootingEndpointValue_norm_sub_le (xp xm yp ym : State) :
    ‖shootingEndpointValue xp xm-shootingEndpointValue yp ym‖≤
      8*(‖xp-yp‖+‖xm-ym‖) := by
  have he : shootingEndpointValue xp xm-shootingEndpointValue yp ym=
      shootingProjection ((xp-yp)-(xm-ym)) := by
    simp only [shootingEndpointValue,map_sub]
    abel
  rw [he]
  exact ((shootingProjection.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right shootingProjection_norm (norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num))

theorem shootingEndpointDerivative_norm_sub_le (e : Fin 2 → ℝ)
    (he0 : |e 0|≤1) (he1 : |e 1|≤1) {xp xm yp ym : State}
    (hxp : xp∈outerTube) (hxm : xm∈outerTube) (hyp : yp∈outerTube) (hym : ym∈outerTube)
    (Pp Pm Qp Qm : (State →L[ℝ] State)) :
    ‖shootingEndpointDerivative e xp xm Pp Pm-shootingEndpointDerivative e yp ym Qp Qm‖≤
      8*(17*(‖xp-yp‖+‖xm-ym‖)+(‖Pp-Qp‖+‖Pm-Qm‖)) := by
  have hfp : ‖field xp-field yp‖≤17*‖xp-yp‖ := by
    have h:=field_lipschitz_on.dist_le_mul xp hxp yp hyp
    simpa only [dist_eq_norm,NNReal.coe_ofNat] using h
  have hfm : ‖field xm-field ym‖≤17*‖xm-ym‖ := by
    have h:=field_lipschitz_on.dist_le_mul xm hxm ym hym
    simpa only [dist_eq_norm,NNReal.coe_ofNat] using h
  let V := (field xp-field yp)+(field xm-field ym)
  let M := (Pp-Qp)-(Pm-Qm)
  have hV : ‖V‖≤17*(‖xp-yp‖+‖xm-ym‖) := by
    exact (norm_add_le _ _).trans ((add_le_add hfp hfm).trans_eq (by ring))
  have hM : ‖M‖≤‖Pp-Qp‖+‖Pm-Qm‖ := norm_sub_le _ _
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have he : (shootingEndpointDerivative e xp xm Pp Pm-
      shootingEndpointDerivative e yp ym Qp Qm) u=
      shootingProjection ((u 2) • V+M (shootingInitial e u)) := by
    simp only [sub_apply,shootingEndpointDerivative_apply]
    rw [←map_sub]
    apply congrArg shootingProjection
    simp only [V,M,sub_apply]
    module
  rw [he]
  have hu : |u 2|≤‖u‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u 2
  have hv : ‖(u 2) • V‖≤‖u‖*(17*(‖xp-yp‖+‖xm-ym‖)) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hu hV (norm_nonneg _) (norm_nonneg _)
  have hm : ‖M (shootingInitial e u)‖≤(‖Pp-Qp‖+‖Pm-Qm‖)*‖u‖ := by
    exact (M.le_opNorm _).trans
      (mul_le_mul hM (shootingInitial_norm_bound e he0 he1 u) (norm_nonneg _) (by positivity))
  calc
    _ ≤ 8*‖(u 2) • V+M (shootingInitial e u)‖ :=
      (shootingProjection.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right shootingProjection_norm (norm_nonneg _))
    _ ≤ 8*(‖(u 2) • V‖+‖M (shootingInitial e u)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ 8*(‖u‖*(17*(‖xp-yp‖+‖xm-ym‖))+(‖Pp-Qp‖+‖Pm-Qm‖)*‖u‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hv hm) (by norm_num)
    _ = _ := by ring

theorem actualShootingDerivative_endpoint_formula (e : Fin 2 → ℝ) (T : ℝ)
    {c : State} {R : ℝ} (hR : 0<R)
    (hplus : FlowTubeNeighborhood 1 (by norm_num) T c R)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) T c R)
    {p : Parameters} (ht : p 2∈Ioo 0 T)
    (ha : shootingInitial e p∈ball c (R/4)) :
    actualShootingDerivative e p=shootingEndpointDerivative e
      (supportFlow 1 (by norm_num) (p 2) (shootingInitial e p))
      (supportFlow (-1) (by norm_num) (p 2) (shootingInitial e p))
      (fderiv ℝ (supportFlow 1 (by norm_num) (p 2)) (shootingInitial e p))
      (fderiv ℝ (supportFlow (-1) (by norm_num) (p 2)) (shootingInitial e p)) := by
  have ha' : shootingInitial e p∈ball c R := by
    change dist _ _<R
    have hh:=mem_ball.mp ha
    linarith
  have hp:=hplus _ ha' (p 2) ⟨ht.1.le,ht.2.le⟩
  have hm:=hminus _ ha' (p 2) ⟨ht.1.le,ht.2.le⟩
  rw [actualShootingDerivative_eq_signed e T hR hplus hminus ht ha]
  apply ContinuousLinearMap.ext
  intro u
  simp only [signedShootingDerivative,shootingEndpointDerivative_apply,ContinuousLinearMap.comp_apply,
    sub_apply,supportFlowDifferential,ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.toSpanSingleton_apply,forwardEndpointInput,ContinuousLinearMap.prod_apply,
    shootingLength,ContinuousLinearMap.proj_apply,signedClippedField,clippedField_eq hp,
    clippedField_eq hm,one_smul,neg_one_smul]
  apply congrArg shootingProjection
  module

theorem actualShootingValue_endpoint_error (e : Fin 2 → ℝ) (p : Parameters)
    (xp xm : State) {E : ℝ}
    (hp : ‖xp-supportFlow 1 (by norm_num) (p 2) (shootingInitial e p)‖≤E)
    (hm : ‖xm-supportFlow (-1) (by norm_num) (p 2) (shootingInitial e p)‖≤E) :
    ‖shootingEndpointValue xp xm-actualShootingMap e p‖≤16*E := by
  rw [actualShootingMap_signed]
  change ‖shootingEndpointValue xp xm-shootingEndpointValue _ _‖≤_
  exact (shootingEndpointValue_norm_sub_le _ _ _ _).trans (by linarith)

theorem actualShootingDerivative_endpoint_error (e : Fin 2 → ℝ)
    (he0 : |e 0|≤1) (he1 : |e 1|≤1) (T : ℝ)
    {c : State} {R : ℝ} (hR : 0<R)
    (hplus : FlowTubeNeighborhood 1 (by norm_num) T c R)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) T c R)
    {p : Parameters} (ht : p 2∈Ioo 0 T)
    (ha : shootingInitial e p∈ball c (R/4))
    (xp xm : State) (hxp : xp∈outerTube) (hxm : xm∈outerTube)
    (Pp Pm : State →L[ℝ] State) {E D : ℝ}
    (hp : ‖xp-supportFlow 1 (by norm_num) (p 2) (shootingInitial e p)‖≤E)
    (hm : ‖xm-supportFlow (-1) (by norm_num) (p 2) (shootingInitial e p)‖≤E)
    (hPp : ‖Pp-fderiv ℝ (supportFlow 1 (by norm_num) (p 2)) (shootingInitial e p)‖≤D)
    (hPm : ‖Pm-fderiv ℝ (supportFlow (-1) (by norm_num) (p 2)) (shootingInitial e p)‖≤D) :
    ‖shootingEndpointDerivative e xp xm Pp Pm-actualShootingDerivative e p‖≤16*(17*E+D) := by
  have ha' : shootingInitial e p∈ball c R := by
    change dist _ _<R
    have hh:=mem_ball.mp ha
    linarith
  rw [actualShootingDerivative_endpoint_formula e T hR hplus hminus ht ha]
  exact (shootingEndpointDerivative_norm_sub_le e he0 he1 hxp hxm
    (hplus _ ha' (p 2) ⟨ht.1.le,ht.2.le⟩) (hminus _ ha' (p 2) ⟨ht.1.le,ht.2.le⟩)
    _ _ _ _).trans (by linarith)

/-- The finite numerical comparison is separate from the proved actual-flow
error. In particular this lemma does not identify a fixed rational J with
the actual shooting derivative. -/
theorem shooting_center_numeric_transport (e : Fin 2 → ℝ) (p : Parameters)
    (xp xm : State) (Pp Pm : State →L[ℝ] State) (y : Parameters)
    (J : Parameters →L[ℝ] Parameters) {Evalue Ederiv δvalue δderiv : ℝ}
    (hvalue : ‖shootingEndpointValue xp xm-actualShootingMap e p‖≤Evalue)
    (hderiv : ‖shootingEndpointDerivative e xp xm Pp Pm-actualShootingDerivative e p‖≤Ederiv)
    (hy : ‖y-shootingEndpointValue xp xm‖≤δvalue)
    (hJ : ‖J-shootingEndpointDerivative e xp xm Pp Pm‖≤δderiv) :
    ‖y-actualShootingMap e p‖≤δvalue+Evalue ∧
      ‖J-actualShootingDerivative e p‖≤δderiv+Ederiv := by
  constructor
  · exact (norm_sub_le_norm_sub_add_norm_sub _ (shootingEndpointValue xp xm) _).trans
      (add_le_add hy hvalue)
  · exact (norm_sub_le_norm_sub_add_norm_sub _ (shootingEndpointDerivative e xp xm Pp Pm) _).trans
      (add_le_add hJ hderiv)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Shooting endpoint comparison audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual shooting endpoint comparison audited: {count} declarations; standard axioms only."
