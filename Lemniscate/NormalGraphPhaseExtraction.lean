import Lemniscate.NormalGraphAngularVelocity
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! The adjoint phase condition uniquely determines the angular velocity
and the scalar modulated equation of an actual classical normal graph. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

/-- A constant adjoint phase along an actual L2 height trajectory fixes
the angular velocity and the modulated velocity, also after a nonzero
constant time rescaling. Unique differentiability includes genuine
one-sided endpoints. -/
theorem circle_normal_graph_phase_extracts_modulation
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (f : CircleSobolevSpace T 4) (h : ℝ → CircleL2 T)
    (w : CircleL2 T) (a : ℝ) (ha : a≠0) (ω : ℂ) (J : Set ℝ) (τ : ℝ)
    (hτ : τ ∈ J) (hJ : UniqueDiffWithinAt ℝ J τ)
    (hd : HasDerivWithinAt h (a • w) J τ)
    (hphase : ∀ t ∈ J, circleNormalGraphRotationFunctional T ψ (h t)=0)
    (hden : circleNormalGraphRotationFunctional T ψ
      (circleNormalGraphRotationField T K
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)))≠0)
    (hPDE : w+ω • circleNormalGraphRotationField T K
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))=
      circleNormalGraphFlow T K c f) :
    ω=circleNormalGraphAngularVelocity T K c ψ f ∧
      w=circleNormalGraphModulatedFlow T K c ψ f := by
  let ell := circleNormalGraphRotationFunctional T ψ
  let G := circleNormalGraphRotationField T K
    (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))
  let F := circleNormalGraphFlow T K c f
  have hmap : ell (a • w)=a • ell w := (ell.restrictScalars ℝ).map_smul a w
  have he : HasDerivWithinAt (fun t : ℝ => ell (h t)) (a • ell w) J τ := by
    have he₀ := (ell.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt τ hd
    change HasDerivWithinAt (fun t : ℝ => ell (h t)) (ell (a • w)) J τ at he₀
    rw [hmap] at he₀
    exact he₀
  have hz : HasDerivWithinAt (fun t : ℝ => ell (h t)) (0:ℂ) J τ := by
    have hc : HasDerivWithinAt (fun _ : ℝ => (0:ℂ)) (0:ℂ) J τ :=
      (hasDerivAt_const τ (0:ℂ)).hasDerivWithinAt
    exact hc.congr_of_mem (fun t ht => hphase t ht) hτ
  have hwscale : a • ell w=0 := (he.derivWithin hJ).symm.trans (hz.derivWithin hJ)
  have hw : ell w=0 := (smul_eq_zero.mp hwscale).resolve_left ha
  have hnum : ω*ell G=ell F := by
    have ha := congrArg ell hPDE
    simpa only [map_add,map_smul,smul_eq_mul,hw,zero_add] using! ha
  have hω : ω=circleNormalGraphAngularVelocity T K c ψ f :=
    (eq_div_iff hden).mpr hnum
  refine ⟨hω,?_⟩
  calc
    w = F-ω • G := (eq_sub_iff_add_eq).mpr hPDE
    _ = F-circleNormalGraphAngularVelocity T K c ψ f • G :=
      congrArg (fun a : ℂ => F-a • G) hω
    _ = circleNormalGraphModulatedFlow T K c ψ f := by
      simp only [F,G,circleNormalGraphModulatedFlow,
        circleNormalGraphNormalizedRotation,circleNormalGraphAngularVelocity,
        div_eq_mul_inv,smul_smul]

end Lemniscate
