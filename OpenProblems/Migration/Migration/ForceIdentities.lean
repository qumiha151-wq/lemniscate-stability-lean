import Migration.NormalRegression
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual elastic-force balance and dilation virial for smooth closed
unit-speed coordinate curves. The elementary Frenet argument is adapted
from the independently compiled OpenTranslators/ImmersionFrenet.lean;
there is no import from that or any other open-problem project. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace MigrationGeometry

def signedCurvature (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv x s * deriv (deriv y) s - deriv y s * deriv (deriv x) s
def elasticForce (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv (deriv (signedCurvature x y)) s + signedCurvature x y s^3/2
def stressX (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  signedCurvature x y s^2/2*deriv x s-deriv (signedCurvature x y) s*deriv y s
def stressY (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  signedCurvature x y s^2/2*deriv y s+deriv (signedCurvature x y) s*deriv x s
def bendingEnergy (x y : ℝ → ℝ) (L : ℝ) : ℝ :=
  (∫ s in 0..L, signedCurvature x y s^2)/2
def dissipation (x y : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ s in 0..L, elasticForce x y s^2

theorem signedCurvature_smooth {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) :
    ContDiff ℝ ∞ (signedCurvature x y) := by
  have hx₁ := (contDiff_infty_iff_deriv.mp hx).2
  have hy₁ := (contDiff_infty_iff_deriv.mp hy).2
  exact (hx₁.mul (contDiff_infty_iff_deriv.mp hy₁).2).sub
    (hy₁.mul (contDiff_infty_iff_deriv.mp hx₁).2)

theorem elasticForce_smooth {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) :
    ContDiff ℝ ∞ (elasticForce x y) := by
  have hk := signedCurvature_smooth hx hy
  exact (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hk).2).2.add
    ((hk.pow 3).div_const 2)

theorem tangent_acceleration_orthogonal {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (s : ℝ) :
    deriv x s*deriv (deriv x) s+deriv y s*deriv (deriv y) s=0 := by
  have hdx := ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) s).hasDerivAt
  have hdy := ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) s).hasDerivAt
  have hd := (hdx.pow 2).add (hdy.pow 2)
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
  change HasDerivAt (fun u => (deriv x u)^2+(deriv y u)^2)
    (2*deriv x s*deriv (deriv x) s+2*deriv y s*deriv (deriv y) s) s at hd
  have he : (fun u => (deriv x u)^2+(deriv y u)^2) = fun _ => (1:ℝ) := funext hu
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const s (1:ℝ))
  linarith

theorem frenet_x {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (s : ℝ) :
    deriv (deriv x) s = -signedCurvature x y s*deriv y s := by
  have ho := tangent_acceleration_orthogonal hx hy hu s
  dsimp [signedCurvature]
  linear_combination -deriv (deriv x) s * hu s + deriv x s * ho

theorem frenet_y {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (s : ℝ) :
    deriv (deriv y) s = signedCurvature x y s*deriv x s := by
  have ho := tangent_acceleration_orthogonal hx hy hu s
  dsimp [signedCurvature]
  linear_combination -deriv (deriv y) s * hu s + deriv y s * ho

theorem stressX_hasDerivAt {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (s : ℝ) :
    HasDerivAt (stressX x y) (-elasticForce x y s*deriv y s) s := by
  have hk := signedCurvature_smooth hx hy
  have hk₁ := (contDiff_infty_iff_deriv.mp hk).2
  have hdx := ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) s).hasDerivAt
  have hdy := ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) s).hasDerivAt
  have h := ((((hk.differentiable (by simp) s).hasDerivAt.pow 2).div_const 2).mul hdx).sub
    ((hk₁.differentiable (by simp) s).hasDerivAt.mul hdy)
  apply h.congr_deriv
  dsimp [elasticForce]
  rw [frenet_x hx hy hu s, frenet_y hx hy hu s]
  ring

theorem stressY_hasDerivAt {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (s : ℝ) :
    HasDerivAt (stressY x y) (elasticForce x y s*deriv x s) s := by
  have hk := signedCurvature_smooth hx hy
  have hk₁ := (contDiff_infty_iff_deriv.mp hk).2
  have hdx := ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) s).hasDerivAt
  have hdy := ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) s).hasDerivAt
  have h := ((((hk.differentiable (by simp) s).hasDerivAt.pow 2).div_const 2).mul hdy).add
    ((hk₁.differentiable (by simp) s).hasDerivAt.mul hdx)
  apply h.congr_deriv
  dsimp [elasticForce]
  rw [frenet_x hx hy hu s, frenet_y hx hy hu s]
  ring

theorem periodic_actual_deriv {f : ℝ → ℝ} {L : ℝ}
    (hp : Function.Periodic f L) : Function.Periodic (deriv f) L := by
  intro s
  have he : (fun u => f (u+L))=f := funext hp
  simpa only [deriv_comp_add_const] using congrArg (fun g => deriv g s) he

theorem signedCurvature_periodic {x y : ℝ → ℝ} {L : ℝ}
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L) :
    Function.Periodic (signedCurvature x y) L := by
  intro s
  simp only [signedCurvature, periodic_actual_deriv hpx s, periodic_actual_deriv hpy s,
    periodic_actual_deriv (periodic_actual_deriv hpx) s,
    periodic_actual_deriv (periodic_actual_deriv hpy) s]

theorem stressX_periodic {x y : ℝ → ℝ} {L : ℝ}
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L) :
    Function.Periodic (stressX x y) L := by
  intro s
  simp only [stressX, signedCurvature_periodic hpx hpy s,
    periodic_actual_deriv (signedCurvature_periodic hpx hpy) s,
    periodic_actual_deriv hpx s, periodic_actual_deriv hpy s]

theorem stressY_periodic {x y : ℝ → ℝ} {L : ℝ}
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L) :
    Function.Periodic (stressY x y) L := by
  intro s
  simp only [stressY, signedCurvature_periodic hpx hpy s,
    periodic_actual_deriv (signedCurvature_periodic hpx hpy) s,
    periodic_actual_deriv hpx s, periodic_actual_deriv hpy s]

/-- Translation-force balance is obtained by integrating actual stress
derivatives around the closed curve. -/
theorem elasticForce_balance {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) :
    (∫ s in 0..L, elasticForce x y s*(-deriv y s))=0 ∧
    (∫ s in 0..L, elasticForce x y s*deriv x s)=0 := by
  have cf := (elasticForce_smooth hx hy).continuous
  have cx := (contDiff_infty_iff_deriv.mp hx).2.continuous
  have cy := (contDiff_infty_iff_deriv.mp hy).2.continuous
  have hX := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := L) (fun s _ => stressX_hasDerivAt hx hy hu s)
    ((cf.neg.mul cy).intervalIntegrable 0 L)
  have hY := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := L) (fun s _ => stressY_hasDerivAt hx hy hu s)
    ((cf.mul cx).intervalIntegrable 0 L)
  have pX := stressX_periodic hpx hpy 0
  have pY := stressY_periodic hpx hpy 0
  simp only [zero_add] at pX pY
  constructor
  · simpa only [neg_mul, mul_neg, pX, sub_self] using hX
  · simpa only [pY, sub_self] using hY

def stressVirial (x y : ℝ → ℝ) (d : Fin 2 → ℝ) (s : ℝ) : ℝ :=
  (x s-d 0)*stressX x y s+(y s-d 1)*stressY x y s

theorem stressVirial_hasDerivAt {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (d : Fin 2 → ℝ) (s : ℝ) :
    HasDerivAt (stressVirial x y d)
      (signedCurvature x y s^2/2+elasticForce x y s*normalSupport x y d s) s := by
  have h := (((hx.differentiable (by simp) s).hasDerivAt.sub_const (d 0)).mul
    (stressX_hasDerivAt hx hy hu s)).add
    (((hy.differentiable (by simp) s).hasDerivAt.sub_const (d 1)).mul
      (stressY_hasDerivAt hx hy hu s))
  apply h.congr_deriv
  dsimp only [stressX,stressY,normalSupport]
  linear_combination (signedCurvature x y s)^2/2 * hu s

/-- Dilation virial for every center, with force and curvature computed
from the same actual closed unit-speed coordinates. -/
theorem elasticForce_normalSupport_integral {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (d : Fin 2 → ℝ) :
    (∫ s in 0..L, elasticForce x y s*normalSupport x y d s)=-bendingEnergy x y L := by
  have ck := (signedCurvature_smooth hx hy).continuous
  have cf := (elasticForce_smooth hx hy).continuous
  have cp := normalSupport_continuous hx hy d
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := L) (fun s _ => stressVirial_hasDerivAt hx hy hu d s)
    ((((ck.pow 2).div_const 2).add (cf.mul cp)).intervalIntegrable 0 L)
  have hp : stressVirial x y d L=stressVirial x y d 0 := by
    have px := hpx 0
    have py := hpy 0
    have pX := stressX_periodic hpx hpy 0
    have pY := stressY_periodic hpx hpy 0
    simp only [zero_add] at px py pX pY
    simp only [stressVirial,px,py,pX,pY]
  have hd' := hd
  rw [hp,sub_self,intervalIntegral.integral_add
    (f := fun s => signedCurvature x y s^2/2)
    (g := fun s => elasticForce x y s*normalSupport x y d s)
    (((ck.pow 2).div_const 2).intervalIntegrable 0 L)
    ((cf.mul cp).intervalIntegrable 0 L),intervalIntegral.integral_div] at hd'
  dsimp [bendingEnergy]
  linarith

end MigrationGeometry

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`MigrationGeometry).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Force identities audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Force identities audit passed for {count} declarations; standard axioms only."
