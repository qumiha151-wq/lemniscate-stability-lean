import Lemniscate.NormalGraphLowSobolevCoordinates
import Lemniscate.BanachTaylorRemainder

/-! Local sup-norm estimates for the coefficients of the normal-graph equation.
The principal coefficient and all six lower coefficients are functions of H2
data alone. Their common Lipschitz bound and the two-point quadratic remainder
of the constant lower coefficient follow from the proved coefficient smoothness.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

private def normalGraphLowPadding :
    (Fin 2 → C(AddCircle T, ℂ)) →L[ℂ] (Fin 4 → C(AddCircle T, ℂ)) :=
  ContinuousLinearMap.pi fun i =>
    ![(ContinuousLinearMap.proj (0 : Fin 2) :
        (Fin 2 → C(AddCircle T, ℂ)) →L[ℂ] C(AddCircle T, ℂ)),
      ContinuousLinearMap.proj (1 : Fin 2),0,0] i

private theorem normal_graph_low_padding_apply (z : Fin 2 → C(AddCircle T, ℂ)) :
    normalGraphLowPadding T z = ![z 0,z 1,0,0] := by
  funext i
  fin_cases i <;> rfl

/-- The principal coefficient and the six lower coefficients, using only
the value and first physical derivative of an H2 normal graph. -/
def circleNormalGraphSobolevCoefficients
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (u : CircleSobolevSpace T 2) : C(AddCircle T, ℂ) × (Fin 6 → C(AddCircle T, ℂ)) :=
  let z := circleNormalGraphLowCoordinates T u
  (normalGraphPrincipalCoefficient T K ![z 0,z 1,0,0],
    normalGraphLowerCoefficientMap T K c z)

theorem circle_normal_graph_sobolev_coefficients_smooth
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) :
    ContDiffAt ℂ (⊤ : WithTop ℕ∞) (circleNormalGraphSobolevCoefficients T K c) 0 := by
  let P : (Fin 2 → C(AddCircle T, ℂ)) →L[ℂ] (Fin 4 → C(AddCircle T, ℂ)) :=
    normalGraphLowPadding T
  let L : CircleSobolevSpace T 2 →L[ℂ] (Fin 2 → C(AddCircle T, ℂ)) :=
    circleNormalGraphLowCoordinates T
  change ContDiffAt ℂ (⊤ : WithTop ℕ∞)
    (fun u : CircleSobolevSpace T 2 =>
      (normalGraphPrincipalCoefficient T K ![L u 0,L u 1,0,0],
        normalGraphLowerCoefficientMap T K c (L u))) 0
  obtain ⟨_,hzero,hcoeff⟩ := normal_graph_coefficients_smooth_over C(AddCircle T, ℂ) K c
  have hprincipal : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun z : Fin 2 → C(AddCircle T, ℂ) => normalGraphPrincipalCoefficient T K (P z)) 0 := by
    have houter : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
        (normalGraphPrincipalCoefficient T K) (P 0) := by
      simpa only [map_zero, normalGraphPrincipalCoefficient] using! (hcoeff 0 hzero).fst
    exact houter.comp 0 P.contDiff.contDiffAt
  obtain ⟨_,hlowerzero,hlower⟩ := normal_graph_lower_coefficients_smooth_over C(AddCircle T, ℂ) K c
  have hjoint : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun z : Fin 2 → C(AddCircle T, ℂ) =>
        (normalGraphPrincipalCoefficient T K (P z),
          normalGraphLowerCoefficientMap T K c z)) 0 :=
    hprincipal.prodMk (hlower 0 hlowerzero)
  have hjoint' : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun z : Fin 2 → C(AddCircle T, ℂ) =>
        (normalGraphPrincipalCoefficient T K (P z),
          normalGraphLowerCoefficientMap T K c z)) (L 0) := by
    simpa only [map_zero] using hjoint
  have hcomp : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun u : CircleSobolevSpace T 2 =>
        (normalGraphPrincipalCoefficient T K (P (L u)),
          normalGraphLowerCoefficientMap T K c (L u))) 0 :=
    hjoint'.comp 0 L.contDiff.contDiffAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with u
  rw [normal_graph_low_padding_apply T (L u)]

/-- A common H2 ball gives a sup-norm Lipschitz bound for the joint coefficient
map and the required two-point quadratic remainder for its constant lower
coefficient. This ball lies in the existing lower coefficient domain. -/
theorem circle_normal_graph_sobolev_coefficient_bounds
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) :
    let J := circleNormalGraphSobolevCoefficients T K c
    let B0 := fun u : CircleSobolevSpace T 2 => (J u).2 0
    ∃ δ > 0, ∃ C > 0,
      (∀ u : CircleSobolevSpace T 2, ‖u‖ < δ →
        circleNormalGraphLowCoordinates T u ∈ normalGraphLowerCoefficientDomain T K) ∧
      ∀ u : CircleSobolevSpace T 2, ‖u‖ < δ →
        ∀ v : CircleSobolevSpace T 2, ‖v‖ < δ →
          ‖J u-J v‖ ≤ C*‖u-v‖ ∧
            ‖B0 u-B0 v-(fderiv ℝ B0 0) (u-v)‖ ≤ C*(‖u‖+‖v‖)*‖u-v‖ := by
  dsimp only
  let J := circleNormalGraphSobolevCoefficients T K c
  let B0 := fun u : CircleSobolevSpace T 2 => (J u).2 0
  have hJ : ContDiffAt ℝ (⊤ : WithTop ℕ∞) J 0 :=
    (circle_normal_graph_sobolev_coefficients_smooth T K c).restrict_scalars ℝ
  have hJone : ContDiffAt ℝ 1 J 0 := hJ.of_le le_top
  have hBtwo : ContDiffAt ℝ 2 B0 0 :=
    ((contDiffAt_pi.mp hJ.snd) 0).of_le le_top
  obtain ⟨L,s,hs,hLip⟩ := hJone.exists_lipschitzOnWith
  obtain ⟨r,hr,B,hB,hremainder⟩ := exists_local_quadratic_remainder_lipschitz hBtwo
  obtain ⟨hopen,hzero,_⟩ := normal_graph_lower_coefficients_smooth_over C(AddCircle T, ℂ) K c
  have hpre : (circleNormalGraphLowCoordinates T) ⁻¹'
      normalGraphLowerCoefficientDomain T K ∈ 𝓝 (0 : CircleSobolevSpace T 2) := by
    apply (circleNormalGraphLowCoordinates T).continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero, normalGraphLowerCoefficientDomain] using hopen.mem_nhds hzero
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hpre)
  let C : ℝ := max (L:ℝ) B
  have hCL : (L:ℝ) ≤ C := le_max_left _ _
  have hCB : B ≤ C := le_max_right _ _
  have hC : 0 < C := hB.trans_le hCB
  have hsmall {u : CircleSobolevSpace T 2} (hu : ‖u‖ < min d r) :
      u ∈ Metric.ball (0 : CircleSobolevSpace T 2) d ∧
        u ∈ Metric.ball (0 : CircleSobolevSpace T 2) r := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using lt_min_iff.mp hu
  refine ⟨min d r,lt_min hd hr,C,hC,?_,?_⟩
  · intro u hu
    exact (hball (hsmall hu).1).2
  · intro u hu v hv
    have hlip : ‖J u-J v‖ ≤ (L:ℝ)*‖u-v‖ := by
      simpa only [dist_eq_norm] using
        hLip.dist_le_mul u (hball (hsmall hu).1).1 v (hball (hsmall hv).1).1
    have hrem := hremainder u (hsmall hu).2 v (hsmall hv).2
    refine ⟨hlip.trans (mul_le_mul_of_nonneg_right hCL (norm_nonneg _)),?_⟩
    exact hrem.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCB (add_nonneg (norm_nonneg u) (norm_nonneg v)))
      (norm_nonneg _))

end Lemniscate
