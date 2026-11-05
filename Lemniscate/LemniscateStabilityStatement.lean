import Lemniscate.FreeElasticFlow
import Lemniscate.BernoulliInitialNormalGraph
import Lemniscate.BernoulliReferenceLength
import Lemniscate.NormalGraphCjEstimate

/-! The precise geometric stability statement. This file defines the
target of the main proof; defining the statement is not a proof of it.
Oriented circle diffeomorphisms are represented by smooth increasing real
lifts with smooth inverses and their prescribed period shifts. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter MeasureTheory
open scoped ContDiff Topology

/-- The physical length of the M-fold Bernoulli lemniscate. -/
def lemniscateLength (M : ℕ) : ℝ := 4*(M:ℝ)*Khalf/Real.sqrt 2

/-- The spectral gap stated in the geometric main theorem. -/
def lemniscateGap (M : ℕ) : ℝ :=
  if M=1 then 5 else 1/(2*(M:ℝ)^2)

/-- The physical arclength lift, used with period lemniscateLength M. -/
def lemniscateReference (e : ℝ ≃o ℝ) (s : ℝ) : ℂ :=
  bernoulliCurve (e.symm (Real.sqrt 2*s))

/-- The actual signed curvature of the Bernoulli reference. -/
def lemniscateReferenceCurvature (e : ℝ ≃o ℝ) (s : ℝ) : ℝ :=
  planarSignedCurvature (lemniscateReference e) s

/-- The actual reference curvature is the profile used in the evolution
equation, when e is its scaled arclength coordinate. -/
theorem lemniscate_reference_curvature
    (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (s : ℝ) :
    lemniscateReferenceCurvature e s=3*bernoulliProfileQ (e.symm (Real.sqrt 2*s)) := by
  simpa only [lemniscateReferenceCurvature,lemniscateReference,Function.comp_def] using!
    (bernoulli_arclength_frame e he s).2.2.2.2.2.2.2.1

/-- The paper's scale-invariant signed-curvature profile deviation. -/
def lemniscateCurvatureDeviation (e : ℝ ≃o ℝ) (M : ℕ) (γ : ℝ → ℂ) : ℝ :=
  normalizedCurvatureProfileError (lemniscateLength M) (2*Real.pi) γ
    (lemniscateReferenceCurvature e)

/-- The original initial length divided by the reference length. -/
def lemniscateInitialScale (M : ℕ) (γ : ℝ → ℂ) : ℝ :=
  (∫ u in (0:ℝ)..(2*Real.pi),‖deriv γ u‖)/lemniscateLength M

/-- The qualitative and quantitative conclusions use one fixed
translation, one limiting rotation and one family of parameter changes
for all spatial orders and rates. -/
def LemniscateConvergence
    (e : ℝ ≃o ℝ) (M : ℕ) (γ₀ : ℝ → ℂ) (Y : ℝ → ℝ → ℂ)
    (εRate CRate : Ioo (0:ℝ) (lemniscateGap M) → ℕ → ℝ) : Prop :=
  let a := lemniscateInitialScale M γ₀
  let ρ : ℝ → ℝ := fun t : ℝ => (a^4+30*t)^(1/4:ℝ)
  0<a ∧ ∃ p₀ Rlim : ℂ,‖Rlim‖=1 ∧ ∃ χ : ℝ → (ℝ ≃o ℝ),
    (∀ t : ℝ,0≤t →
      ContDiff ℝ ∞ (χ t : ℝ → ℝ) ∧
      ContDiff ℝ ∞ ((χ t).symm : ℝ → ℝ) ∧
      ∀ s : ℝ,χ t (s+lemniscateLength M)=χ t s+2*Real.pi) ∧
    (∀ j : ℕ,Tendsto (fun t : ℝ => periodicCjNorm j
      (fun s : ℝ => Y t (χ t s)/(ρ t:ℂ)-Rlim*lemniscateReference e s)) atTop (𝓝 0)) ∧
    ∀ (μ : Ioo (0:ℝ) (lemniscateGap M)) (j : ℕ),
      lemniscateCurvatureDeviation e M γ₀<εRate μ j →
      ∀ t : ℝ,a^4≤t → periodicCjNorm j
        (fun s : ℝ => (Y t (χ t s)-p₀)/(ρ t:ℂ)-Rlim*lemniscateReference e s)≤
          CRate μ j*(1+30*t/a^4)^(-(μ:ℝ)/30)*
            Real.sqrt (lemniscateCurvatureDeviation e M γ₀)

/-- The full main theorem includes a global solution of the projected
equation and identifies every given smooth solution with the same initial
curve. All neighborhoods and rate constants are chosen before that curve.
Only spatial C-infinity convergence is asserted. -/
def LemniscateStabilityStatement (e : ℝ ≃o ℝ) : Prop :=
  ∀ M : ℕ,0<M → ∃ ε>0,
    ∃ εRate CRate : Ioo (0:ℝ) (lemniscateGap M) → ℕ → ℝ,
      (∀ μ j,0<εRate μ j ∧ εRate μ j≤ε ∧ 0<CRate μ j) ∧
      ∀ γ₀ : ℝ → ℂ,
      ContDiff ℝ ∞ γ₀ → Function.Periodic γ₀ (2*Real.pi) →
      (∀ s : ℝ,deriv γ₀ s≠0) → lemniscateCurvatureDeviation e M γ₀<ε →
      (∃ Y : ℝ → ℝ → ℂ,
        IsFreeElasticFlow Y ∧ (∀ s : ℝ,Y 0 s=γ₀ s) ∧
        (∀ t : ℝ,0≤t → ContDiff ℝ ∞ (Y t) ∧
          Function.Periodic (Y t) (2*Real.pi)) ∧
        ContinuousOn (fun z : ℝ × ℝ => Y z.1 z.2)
          (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ∧
        ContinuousOn (fun z : ℝ × ℝ => deriv (Y z.1) z.2)
          (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ∧
        LemniscateConvergence e M γ₀ Y εRate CRate) ∧
      ∀ Y : ℝ → ℝ → ℂ,
        ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2)
          (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) →
        (∀ t : ℝ,0≤t → Function.Periodic (Y t) (2*Real.pi)) →
        IsFreeElasticFlow Y → (∀ s : ℝ,Y 0 s=γ₀ s) →
        LemniscateConvergence e M γ₀ Y εRate CRate

end Lemniscate
