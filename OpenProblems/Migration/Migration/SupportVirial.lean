import Migration.ForceIdentities

/-! Actual tangent-support virial and strictly positive bending energy.
The support derivative is derived from the real coordinate derivatives,
unit speed and the previously derived actual Frenet identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace MigrationGeometry

def tangentSupport (x y : ℝ → ℝ) (d : Fin 2 → ℝ) (s : ℝ) : ℝ :=
  (x s-d 0)*deriv x s+(y s-d 1)*deriv y s

theorem tangentSupport_hasDerivAt {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (d : Fin 2 → ℝ) (s : ℝ) :
    HasDerivAt (tangentSupport x y d) (1+signedCurvature x y s*normalSupport x y d s) s := by
  have hdx := ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) s).hasDerivAt
  have hdy := ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) s).hasDerivAt
  have h := (((hx.differentiable (by simp) s).hasDerivAt.sub_const (d 0)).mul hdx).add
    (((hy.differentiable (by simp) s).hasDerivAt.sub_const (d 1)).mul hdy)
  apply h.congr_deriv
  rw [frenet_x hx hy hu s,frenet_y hx hy hu s]
  dsimp [normalSupport]
  linear_combination hu s

theorem tangentSupport_periodic {x y : ℝ → ℝ} {L : ℝ}
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L) (d : Fin 2 → ℝ) :
    Function.Periodic (tangentSupport x y d) L := by
  intro s
  simp only [tangentSupport,hpx s,hpy s,periodic_actual_deriv hpx s,periodic_actual_deriv hpy s]

/-- The integral of actual curvature times normal support is minus the
actual arclength period, for every choice of center. -/
theorem curvature_normalSupport_integral {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (d : Fin 2 → ℝ) :
    (∫ s in 0..L, signedCurvature x y s*normalSupport x y d s) = -L := by
  have ck := (signedCurvature_smooth hx hy).continuous
  have cp := normalSupport_continuous hx hy d
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := L) (fun s _ => tangentSupport_hasDerivAt hx hy hu d s)
    ((continuous_const.add (ck.mul cp)).intervalIntegrable 0 L)
  have hp := tangentSupport_periodic hpx hpy d 0
  simp only [zero_add] at hp
  rw [hp,sub_self,intervalIntegral.integral_add
    (f := fun _ : ℝ => (1:ℝ)) (g := fun s => signedCurvature x y s*normalSupport x y d s)
    (intervalIntegrable_const) ((ck.mul cp).intervalIntegrable 0 L)] at hd
  norm_num only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hd
  linarith

theorem exists_curvature_ne_zero {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) :
    ∃ s ∈ Icc 0 L, signedCurvature x y s ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz : (∫ s in 0..L, signedCurvature x y s*normalSupport x y 0 s)=0 := by
    calc
      _ = ∫ s in 0..L, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hL.le] at hs
        simp only [hn s hs,zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  rw [curvature_normalSupport_integral hx hy hpx hpy hu] at hz
  linarith

/-- Positive bending energy follows from actual closed geometry; it is
not supplied as an extra hypothesis for the dilation coefficient. -/
theorem bendingEnergy_pos {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) : 0 < bendingEnergy x y L := by
  obtain ⟨s,hs,hn⟩ := exists_curvature_ne_zero hx hy hL hpx hpy hu
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0:ℝ)) (g := fun s => signedCurvature x y s^2)
    hL continuous_const.continuousOn ((signedCurvature_smooth hx hy).continuous.pow 2).continuousOn
    (fun s _ => sq_nonneg _) ⟨s,hs,sq_pos_of_ne_zero hn⟩
  simp only [intervalIntegral.integral_zero] at hi
  exact div_pos hi (by norm_num)

end MigrationGeometry

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`MigrationGeometry).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Support virial audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Support virial audit passed for {count} declarations; standard axioms only."
