import Lemniscate.PeriodicProfileShiftSmoothness
import Lemniscate.BernoulliSobolevLinearization

/-! The six actual Bernoulli background coefficients are smooth on the real
cover. Point evaluation of the already smooth profile translation supplies
the profile regularity; all coefficients are polynomial expressions in it. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ContDiff

theorem circle_bernoulli_background_smooth
    (T : ℝ) [Fact (0<T)] (q p : C(AddCircle T,ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).k (x:AddCircle T)) ∧
    ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).ks (x:AddCircle T)) ∧
    ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).kss (x:AddCircle T)) ∧
    ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).ksss (x:AddCircle T)) ∧
    ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).eta (x:AddCircle T)) ∧
    ContDiff ℝ ∞ (fun x : ℝ => (circleBernoulliBackground T q p).b (x:AddCircle T)) := by
  have hs := circle_profile_time_shift_smooth T q p hq hp
  let ev : C(unitInterval × AddCircle T,ℂ) →L[ℝ] ℂ :=
    (ContinuousMap.evalCLM ℂ ((1:unitInterval),(0:AddCircle T))).restrictScalars ℝ
  have hqline : ContDiff ℝ ∞ (fun x : ℝ => q (x:AddCircle T)) := by
    have hh := ev.contDiff.comp hs.fst
    simpa [ev,circleProfileTimeShift,Function.comp_def] using! hh
  have hpline : ContDiff ℝ ∞ (fun x : ℝ => p (x:AddCircle T)) := by
    have hh := ev.contDiff.comp hs.snd
    simpa [ev,circleProfileTimeShift,Function.comp_def] using! hh
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> dsimp [circleBernoulliBackground]
  · exact contDiff_const.mul hqline
  · exact contDiff_const.mul hpline
  · exact contDiff_const.mul (hqline.pow 3)
  · exact contDiff_const.mul ((hqline.pow 2).mul hpline)
  · exact (hqline.pow 3).neg
  · exact contDiff_const.mul (hqline.mul hpline)

end Lemniscate
