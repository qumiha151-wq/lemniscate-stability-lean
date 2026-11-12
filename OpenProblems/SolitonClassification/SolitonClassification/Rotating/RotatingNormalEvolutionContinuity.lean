import SolitonClassification.Rotating.RotatingNormalEvolutionScalar

/-! Quantitative initial-data continuity and genuine joint continuity for
the selected global scalar flow. These are proved from its actual ODE. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Real
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem scalarField_deriv_bound (g : PeriodicScalarField) (x : ℝ) :
    ‖deriv g x‖ ≤ scalarLip g := norm_deriv_le_of_lipschitz (scalarField_lipschitz g)

theorem scalarFlow_signed_hasDerivAt (g : PeriodicScalarField) (σ a t : ℝ) :
    HasDerivAt (fun u => scalarFlow g (σ*u) a) (σ*g (scalarFlow g (σ*t) a)) t := by
  convert! (scalarFlow_hasDerivAt g a (σ*t)).scomp t ((hasDerivAt_id t).const_mul σ) using 1
  simp only [smul_eq_mul,mul_one]

theorem scalarFlow_signed_distance (g : PeriodicScalarField) (σ : ℝ) (hσ : |σ|≤1)
    (a b : ℝ) {t : ℝ} (ht : 0≤t) :
    dist (scalarFlow g (σ*t) a) (scalarFlow g (σ*t) b)≤
      dist a b*exp ((scalarLip g:ℝ)*t) := by
  have hLip : LipschitzWith (scalarLip g) (fun x => σ*g x) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro a b
    rw [←mul_sub,norm_mul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans
      (by simpa only [one_mul] using lipschitzWith_iff_norm_sub_le.mp (scalarField_lipschitz g) a b)
  have he := dist_le_of_trajectories_ODE (v:=fun _ x => σ*g x) (K:=scalarLip g)
    (fun _ => hLip)
    (fun r _ => (scalarFlow_signed_hasDerivAt g σ a r).continuousAt.continuousWithinAt)
    (fun r _ => (scalarFlow_signed_hasDerivAt g σ a r).hasDerivWithinAt)
    (fun r _ => (scalarFlow_signed_hasDerivAt g σ b r).continuousAt.continuousWithinAt)
    (fun r _ => (scalarFlow_signed_hasDerivAt g σ b r).hasDerivWithinAt)
    (by simp only [mul_zero,scalarFlow_zero]; exact le_rfl) t ⟨ht,le_rfl⟩
  simpa only [mul_zero,scalarFlow_zero,sub_zero] using he

theorem scalarFlow_distance (g : PeriodicScalarField) (a b t : ℝ) :
    dist (scalarFlow g t a) (scalarFlow g t b)≤dist a b*exp ((scalarLip g:ℝ)*|t|) := by
  by_cases ht : 0≤t
  · simpa only [one_mul,abs_of_nonneg ht] using scalarFlow_signed_distance g 1 (by norm_num) a b ht
  · have hn : t<0 := lt_of_not_ge ht
    simpa only [neg_one_mul,neg_neg,abs_of_neg hn] using
      scalarFlow_signed_distance g (-1) (by norm_num) a b (neg_nonneg.mpr hn.le)

theorem scalarFlow_initial_lipschitz (g : PeriodicScalarField) (t : ℝ) :
    LipschitzWith ⟨exp ((scalarLip g:ℝ)*|t|),(exp_pos _).le⟩ (scalarFlow g t) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist _ _ ≤ exp ((scalarLip g:ℝ)*|t|)*dist a b
  simpa only [mul_comm] using scalarFlow_distance g a b t

theorem scalarFlow_space_continuous (g : PeriodicScalarField) (t : ℝ) :
    Continuous (scalarFlow g t) := (scalarFlow_initial_lipschitz g t).continuous

theorem scalarFlow_time_lipschitz (g : PeriodicScalarField) (a : ℝ) :
    LipschitzWith (scalarBound g) (fun t => scalarFlow g t a) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun t => (scalarFlow_hasDerivAt g a t).differentiableAt
  · intro t
    rw [← NNReal.coe_le_coe,coe_nnnorm,(scalarFlow_hasDerivAt g a t).deriv]
    exact scalarField_norm_bound g _

theorem scalarFlow_time_distance (g : PeriodicScalarField) (a t u : ℝ) :
    dist (scalarFlow g t a) (scalarFlow g u a)≤(scalarBound g:ℝ)*dist t u :=
  (scalarFlow_time_lipschitz g a).dist_le_mul t u

theorem scalarFlow_joint_continuous (g : PeriodicScalarField) :
    Continuous (fun z : ℝ×ℝ => scalarFlow g z.1 z.2) :=
  continuous_prod_of_continuous_lipschitzWith _ (scalarBound g)
    (scalarFlow_space_continuous g) (scalarFlow_time_lipschitz g)

def scalarFlowHomeomorph (g : PeriodicScalarField) (t : ℝ) : ℝ ≃ₜ ℝ where
  toEquiv := scalarFlowEquiv g t
  continuous_toFun := scalarFlow_space_continuous g t
  continuous_invFun := scalarFlow_space_continuous g (-t)

end
end SolitonClassification.Rotating.NormalEvolution

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Scalar flow continuity audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual scalar-flow joint continuity audited: {count} declarations; standard axioms only."
