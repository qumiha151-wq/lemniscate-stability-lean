import OpenTranslators.ParameterIntrinsic
import Mathlib.Topology.MetricSpace.Isometry

/-! An unconditional complete, nonstraight, pure-normal translator witness.
Completeness is proved for the metric whose distance is the curve's actual
intrinsic arclength distance, using a separate type for the parameter domain. -/
namespace OpenTranslator.TranslatorPureNormal
noncomputable section
open scoped ContDiff
open TranslatorParameter TranslatorGeometry

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)

/-- A time slice of the parameter line, carrying the actual intrinsic metric
rather than the original coordinate metric. -/
@[ext] structure IntrinsicParameter (_hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)
    (_t : ℝ) where
  val : ℝ

def intrinsicParameterMap (t : ℝ) (u : IntrinsicParameter hz t) : ℝ :=
  parameterFlow hz t u.val

theorem intrinsicParameterMap_injective (t : ℝ) :
    Function.Injective (intrinsicParameterMap hz t) := by
  intro u v h
  have he : u.val=v.val := (parameterFlow_bijective hz t).1 h
  exact IntrinsicParameter.ext he

instance intrinsicParameterMetric (t : ℝ) : MetricSpace (IntrinsicParameter hz t) :=
  MetricSpace.induced (intrinsicParameterMap hz t) (intrinsicParameterMap_injective hz t)
    inferInstance

def intrinsicParameterIsometry (t : ℝ) : IntrinsicParameter hz t ≃ᵢ ℝ where
  toFun := intrinsicParameterMap hz t
  invFun s := ⟨parameterFlow hz (-t) s⟩
  left_inv u := by
    apply IntrinsicParameter.ext
    exact parameterFlow_inverse hz t u.val
  right_inv s := by
    exact (parameterFlow_diffeomorphism hz t).2.2.2.2.1 s
  isometry_toFun := MetricSpace.isometry_induced _ (intrinsicParameterMap_injective hz t)

instance intrinsicParameterComplete (t : ℝ) : CompleteSpace (IntrinsicParameter hz t) :=
  (intrinsicParameterIsometry hz t).completeSpace

/-- The complete metric above is identified with the actual curve's speed
integral, not merely an auxiliary conjugate distance. -/
theorem intrinsicParameter_dist_eq (t : ℝ) (u v : IntrinsicParameter hz t) :
    dist u v=intrinsicDistance (curveX hz t) (curveY hz t) u.val v.val := by
  exact (curve_intrinsicDistance hz t u.val v.val).symm

theorem curve_translation_shape (t u : ℝ) :
    curveX hz t u=curveX hz 0 (parameterFlow hz t u)+t ∧
      curveY hz t u=curveY hz 0 (parameterFlow hz t u) := by
  simp only [curveX,curveY,parameterFlow_zero,add_zero,and_self]

theorem curve_not_in_affine_line
    (h0 : z 0=![Real.pi/2,1,0]) (t : ℝ) :
    ¬∃ A B C : ℝ, (A≠0 ∨ B≠0) ∧ ∀u, A*curveX hz t u+B*curveY hz t u=C := by
  rintro ⟨A,B,C,hAB,hline⟩
  apply not_in_affine_line hz h0
  refine ⟨A,B,C-A*t,hAB,fun s => ?_⟩
  obtain ⟨u,hu⟩ := (parameterFlow_bijective hz t).2 s
  have hh := hline u
  simp only [curveX,curveY,hu] at hh
  linarith

theorem parameterFlow_fixed_origin (h0 : z 0=![Real.pi/2,1,0]) (t : ℝ) :
    parameterFlow hz t 0=0 := by
  have hh : (fun _ : ℝ => (0:ℝ))=fun t => parameterFlow hz t 0 := by
    apply parameterFlow_unique hz rfl
    intro r
    simpa only [parameterField,h0,Matrix.cons_val_zero,Real.cos_pi_div_two,neg_zero]
      using hasDerivAt_const r (0:ℝ)
  exact (congrFun hh t).symm

theorem curve_origin_motion (h0 : z 0=![Real.pi/2,1,0]) (t : ℝ) :
    HasDerivAt (fun r => (curveX hz r 0,curveY hz r 0)) (1,0) t := by
  have h := (curve_time_hasDerivAt hz t 0).1.prodMk (curve_time_hasDerivAt hz t 0).2
  simpa only [parameterFlow_fixed_origin hz h0,h0,Matrix.cons_val_zero,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_pow,mul_zero] using h

theorem curve_origin_curvature (h0 : z 0=![Real.pi/2,1,0]) (t : ℝ) :
    intrinsicCurvature (curveX hz t) (curveY hz t) 0=1 := by
  rw [curve_curvature hz,parameterFlow_fixed_origin hz h0,h0]
  rfl

omit hz in
/-- A global-in-time and global-in-space pure-normal free elastic flow with
nonstraight translating shape and nonzero motion. Every time-slice intrinsic
metric is complete, and the reparametrization is an orientation-preserving
smooth diffeomorphism. No translator, global parameter flow, spatial derivative,
or joint regularity is assumed by this existence theorem. -/
theorem exists_complete_nonstraight_pure_normal_translator :
    ∃ (z : ℝ → TranslatorState) (hz : ∀s, HasDerivAt z (translatorNumerator (z s)) s),
      z 0=![Real.pi/2,1,0] ∧
      ContDiff ℝ ∞ (fun p : ℝ×ℝ => (curveX hz p.1 p.2,curveY hz p.1 p.2)) ∧
      (∀t, Function.Bijective (parameterFlow hz t) ∧
        ContDiff ℝ ∞ (parameterFlow hz t) ∧ ContDiff ℝ ∞ (parameterFlow hz (-t)) ∧
        (∀u,parameterFlow hz (-t) (parameterFlow hz t u)=u) ∧
        (∀u,parameterFlow hz t (parameterFlow hz (-t) u)=u) ∧
        ∀u,0<deriv (parameterFlow hz t) u) ∧
      (∀t u,0<curveSpeed (curveX hz t) (curveY hz t) u) ∧
      (∀t u,HasDerivAt (fun r => (curveX hz r u,curveY hz r u))
        (-intrinsicElasticForce (curveX hz t) (curveY hz t) u*
            unitNormalX (curveX hz t) (curveY hz t) u,
          -intrinsicElasticForce (curveX hz t) (curveY hz t) u*
            unitNormalY (curveX hz t) (curveY hz t) u) t) ∧
      (∀t,CompleteSpace (IntrinsicParameter hz t)) ∧
      (∀t (u v : IntrinsicParameter hz t),dist u v=
        intrinsicDistance (curveX hz t) (curveY hz t) u.val v.val) ∧
      (∀t u,curveX hz t u=curveX hz 0 (parameterFlow hz t u)+t ∧
        curveY hz t u=curveY hz 0 (parameterFlow hz t u)) ∧
      (∀t,¬∃A B C:ℝ,(A≠0∨B≠0) ∧ ∀u,A*curveX hz t u+B*curveY hz t u=C) ∧
      (∀t,HasDerivAt (fun r => (curveX hz r 0,curveY hz r 0)) (1,0) t) ∧
      (∀t,intrinsicCurvature (curveX hz t) (curveY hz t) 0=1) := by
  obtain ⟨z,h0,hz⟩ := exists_global_translator ![Real.pi/2,1,0]
  exact ⟨z,hz,h0,curve_joint_smooth hz,parameterFlow_diffeomorphism hz,
    curve_speed_pos hz,curve_intrinsic_pure_normal_FEF hz,
    fun t => intrinsicParameterComplete hz t,intrinsicParameter_dist_eq hz,
    curve_translation_shape hz,curve_not_in_affine_line hz h0,
    curve_origin_motion hz h0,curve_origin_curvature hz h0⟩

end
end OpenTranslator.TranslatorPureNormal

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Parameter example audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Parameter example audit passed for {count} declarations."
