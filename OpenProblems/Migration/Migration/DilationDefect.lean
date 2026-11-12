import Migration.SupportVirial
import Migration.NormalSupportPositive

/-! The best-dilation residual of the actual elastic force of a smooth
closed unit-speed curve. Force balance, virial, positive energy, and
positive normal-distance energy are derived from that same curve. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace MigrationGeometry

def dilationCoefficient (x y : ℝ → ℝ) (L : ℝ) : ℝ :=
  bendingEnergy x y L / normalDistanceSquared x y L (regressionCenter x y L)

def dilationResidual (x y : ℝ → ℝ) (L s : ℝ) : ℝ :=
  elasticForce x y s+dilationCoefficient x y L*normalSupport x y (regressionCenter x y L) s

def dilationDefect (x y : ℝ → ℝ) (L : ℝ) : ℝ :=
  dissipation x y L-(bendingEnergy x y L)^2/
    normalDistanceSquared x y L (regressionCenter x y L)

theorem dilationResidual_continuous {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (L : ℝ) :
    Continuous (dilationResidual x y L) :=
  (elasticForce_smooth hx hy).continuous.add
    ((normalSupport_continuous hx hy _).const_mul _)

theorem dilationResidual_periodic {x y : ℝ → ℝ} {L : ℝ}
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L) :
    Function.Periodic (dilationResidual x y L) L := by
  intro s
  simp only [dilationResidual,elasticForce,normalSupport,hpx s,hpy s,
    signedCurvature_periodic hpx hpy s,
    periodic_actual_deriv (periodic_actual_deriv (signedCurvature_periodic hpx hpy)) s,
    periodic_actual_deriv hpx s,periodic_actual_deriv hpy s]

section ClosedCurve
variable {x y : ℝ → ℝ} {L : ℝ}
variable (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
variable (hL : 0 < L) (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
variable (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1)
include hx hy hL hpx hpy hu

theorem dilationCoefficient_pos : 0 < dilationCoefficient x y L :=
  div_pos (bendingEnergy_pos hx hy hL hpx hpy hu)
    (regressionCenter_distance_pos hx hy hL hpx hpy (fun s _ => hu s))

omit hL in
/-- Exact actual-force expansion for every candidate dilation coefficient. -/
theorem elasticForce_dilation_square_integral (b : ℝ) :
    (∫ s in 0..L, (elasticForce x y s+b*normalSupport x y (regressionCenter x y L) s)^2) =
      dissipation x y L-2*b*bendingEnergy x y L+
        b^2*normalDistanceSquared x y L (regressionCenter x y L) := by
  have cf := (elasticForce_smooth hx hy).continuous
  have cp := normalSupport_continuous hx hy (regressionCenter x y L)
  calc
    _ = ∫ s in 0..L, (elasticForce x y s^2+
        (2*b)*(elasticForce x y s*normalSupport x y (regressionCenter x y L) s))+
        b^2*(normalSupport x y (regressionCenter x y L) s)^2 := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (f := fun s => elasticForce x y s^2+
          (2*b)*(elasticForce x y s*normalSupport x y (regressionCenter x y L) s))
        (g := fun s => b^2*(normalSupport x y (regressionCenter x y L) s)^2)
        (((cf.pow 2).add ((cf.mul cp).const_mul (2*b))).intervalIntegrable 0 L)
        (((cp.pow 2).const_mul (b^2)).intervalIntegrable 0 L),
        intervalIntegral.integral_add
        (f := fun s => elasticForce x y s^2)
        (g := fun s => (2*b)*(elasticForce x y s*normalSupport x y (regressionCenter x y L) s))
        ((cf.pow 2).intervalIntegrable 0 L)
        (((cf.mul cp).const_mul (2*b)).intervalIntegrable 0 L),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        elasticForce_normalSupport_integral hx hy hpx hpy hu]
      dsimp [dissipation,normalDistanceSquared]
      ring

/-- The actual dissipation defect is exactly the integral of the actual
residual squared; neither virial nor positivity is an input hypothesis. -/
theorem dilationDefect_eq_integral_square :
    dilationDefect x y L=∫ s in 0..L, dilationResidual x y L s^2 := by
  have hJ := ne_of_gt (regressionCenter_distance_pos hx hy hL hpx hpy (fun s _ => hu s))
  have hi := elasticForce_dilation_square_integral hx hy hpx hpy hu
    (dilationCoefficient x y L)
  change dilationDefect x y L =
    ∫ s in 0..L, (elasticForce x y s+
      dilationCoefficient x y L*normalSupport x y (regressionCenter x y L) s)^2
  rw [hi]
  dsimp [dilationDefect,dilationCoefficient]
  field_simp
  ring

theorem dilationDefect_nonneg : 0 ≤ dilationDefect x y L := by
  rw [dilationDefect_eq_integral_square hx hy hL hpx hpy hu]
  exact intervalIntegral.integral_nonneg_of_forall hL.le (fun _ => sq_nonneg _)

/-- Orthogonality to the actual centered normal support. -/
theorem dilationResidual_support_orthogonal :
    (∫ s in 0..L, dilationResidual x y L s*
      normalSupport x y (regressionCenter x y L) s)=0 := by
  have cf := (elasticForce_smooth hx hy).continuous
  have cp := normalSupport_continuous hx hy (regressionCenter x y L)
  have hJ := ne_of_gt (regressionCenter_distance_pos hx hy hL hpx hpy (fun s _ => hu s))
  calc
    _ = ∫ s in 0..L,
        elasticForce x y s*normalSupport x y (regressionCenter x y L) s+
        dilationCoefficient x y L*(normalSupport x y (regressionCenter x y L) s)^2 := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [dilationResidual]
      ring
    _ = 0 := by
      rw [intervalIntegral.integral_add
        (f := fun s => elasticForce x y s*normalSupport x y (regressionCenter x y L) s)
        (g := fun s => dilationCoefficient x y L*(normalSupport x y (regressionCenter x y L) s)^2)
        ((cf.mul cp).intervalIntegrable 0 L)
        (((cp.pow 2).const_mul (dilationCoefficient x y L)).intervalIntegrable 0 L),
        intervalIntegral.integral_const_mul,elasticForce_normalSupport_integral hx hy hpx hpy hu]
      change -bendingEnergy x y L+dilationCoefficient x y L*
        normalDistanceSquared x y L (regressionCenter x y L)=0
      dsimp [dilationCoefficient]
      rw [div_mul_cancel₀ _ hJ]
      ring

/-- Orthogonality to both actual normal components, from the actual
force balance and the already proved inverse-defined-center balance. -/
theorem dilationResidual_normal_balance :
    (∫ s in 0..L, dilationResidual x y L s*(-deriv y s))=0 ∧
    (∫ s in 0..L, dilationResidual x y L s*deriv x s)=0 := by
  have cf := (elasticForce_smooth hx hy).continuous
  have cp := normalSupport_continuous hx hy (regressionCenter x y L)
  have hf := elasticForce_balance hx hy hpx hpy hu
  have hc := regressionCenter_balance hx hy hL
    (by simpa using hpx 0) (by simpa using hpy 0) (fun s _ => hu s)
  have hcx := congrFun hc 0
  have hcy := congrFun hc 1
  change (∫ s in 0..L, normalSupport x y (regressionCenter x y L) s*(-deriv y s))=0 at hcx
  change (∫ s in 0..L, normalSupport x y (regressionCenter x y L) s*deriv x s)=0 at hcy
  have haux (r : ℝ → ℝ) (hr : Continuous r)
      (hf0 : (∫ s in 0..L, elasticForce x y s*r s)=0)
      (hp0 : (∫ s in 0..L, normalSupport x y (regressionCenter x y L) s*r s)=0) :
      (∫ s in 0..L, dilationResidual x y L s*r s)=0 := by
    calc
      _ = ∫ s in 0..L, elasticForce x y s*r s+
          dilationCoefficient x y L*(normalSupport x y (regressionCenter x y L) s*r s) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [dilationResidual]
        ring
      _ = 0 := by
        rw [intervalIntegral.integral_add
          (f := fun s => elasticForce x y s*r s)
          (g := fun s => dilationCoefficient x y L*(normalSupport x y (regressionCenter x y L) s*r s))
          ((cf.mul hr).intervalIntegrable 0 L)
          (((cp.mul hr).const_mul (dilationCoefficient x y L)).intervalIntegrable 0 L),
          intervalIntegral.integral_const_mul,hf0,hp0,mul_zero,add_zero]
  exact ⟨haux _ (contDiff_infty_iff_deriv.mp hy).2.continuous.neg hf.1 hcx,
    haux _ (contDiff_infty_iff_deriv.mp hx).2.continuous hf.2 hcy⟩

/-- Vanishing defect is equivalent to the actual centered dilation-profile
equation everywhere on the curve, not merely an almost-everywhere relation. -/
theorem dilationDefect_eq_zero_iff :
    dilationDefect x y L=0 ↔
      ∀ s, elasticForce x y s = -dilationCoefficient x y L*
        normalSupport x y (regressionCenter x y L) s := by
  have he := dilationDefect_eq_integral_square hx hy hL hpx hpy hu
  constructor
  · intro hzero s
    have hzI : ∀ t ∈ Icc 0 L, dilationResidual x y L t=0 := by
      intro t ht
      by_contra hn
      have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (f := fun _ : ℝ => (0:ℝ)) (g := fun s => dilationResidual x y L s^2)
        hL continuous_const.continuousOn ((dilationResidual_continuous hx hy L).pow 2).continuousOn
        (fun s _ => sq_nonneg _) ⟨t,ht,sq_pos_of_ne_zero hn⟩
      simp only [intervalIntegral.integral_zero] at hi
      rw [hzero] at he
      linarith
    obtain ⟨t,ht,hst⟩ := (dilationResidual_periodic hpx hpy).exists_mem_Ico₀ hL s
    have hz : dilationResidual x y L s=0 := hst.trans (hzI t ⟨ht.1,ht.2.le⟩)
    dsimp [dilationResidual] at hz
    linarith
  · intro hprofile
    rw [he]
    calc
      _ = ∫ s in 0..L, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [dilationResidual]
        rw [hprofile s]
        ring
      _ = 0 := intervalIntegral.integral_zero

end ClosedCurve
end MigrationGeometry

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`MigrationGeometry).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Dilation defect audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Dilation defect audit passed for {count} declarations; standard axioms only."
