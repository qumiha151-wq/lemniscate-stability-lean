import SolitonClassification.ScalarReconstructionProfile
import SolitonClassification.ScalarReconstructionPeriodicity

/-! Actual smooth closed unit-speed soliton curves reconstructed from the
scalar equation and integer tangent holonomy, through all curvature zeros. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

def reconstructedX (k : ℝ → ℝ) (a b s₀ : ℝ) : ℝ → ℝ :=
  profileX (normalCoefficient k a b s₀) (tangentCoefficient k a b s₀) (curvatureAngle k)

def reconstructedY (k : ℝ → ℝ) (a b s₀ : ℝ) : ℝ → ℝ :=
  profileY (normalCoefficient k a b s₀) (tangentCoefficient k a b s₀) (curvatureAngle k)

theorem coefficients_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (a b s₀ : ℝ) :
    ContDiff ℝ ∞ (normalCoefficient k a b s₀) ∧
      ContDiff ℝ ∞ (tangentCoefficient k a b s₀) := by
  have hf := force_smooth hk
  have hh := candidateSupport_smooth hk a b s₀
  exact ⟨((contDiff_const.mul hf).sub (contDiff_const.mul hh)).div_const (a^2+b^2),
    ((contDiff_const.mul hf).add (contDiff_const.mul hh)).div_const (a^2+b^2)⟩

theorem reconstructed_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (a b s₀ : ℝ) :
    ContDiff ℝ ∞ (reconstructedX k a b s₀) ∧ ContDiff ℝ ∞ (reconstructedY k a b s₀) := by
  obtain ⟨hp,hq⟩ := coefficients_smooth hk a b s₀
  have ht := curvatureAngle_smooth hk
  exact ⟨(hq.mul ht.cos).sub (hp.mul ht.sin),(hq.mul ht.sin).add (hp.mul ht.cos)⟩

theorem reconstructed_hasDerivAt {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ : ℝ) (hanchor : k s₀≠0)
    (hden : a^2+b^2≠0) (s : ℝ) :
    HasDerivAt (reconstructedX k a b s₀) (Real.cos (curvatureAngle k s)) s ∧
      HasDerivAt (reconstructedY k a b s₀) (Real.sin (curvatureAngle k s)) s :=
  ⟨profileX_hasDerivAt k _ _ _ s
      (normalCoefficient_hasDerivAt hk hS s₀ hanchor s)
      (tangentCoefficient_hasDerivAt hk hS s₀ hanchor hden s)
      (curvatureAngle_hasDerivAt hk.continuous s),
    profileY_hasDerivAt k _ _ _ s
      (normalCoefficient_hasDerivAt hk hS s₀ hanchor s)
      (tangentCoefficient_hasDerivAt hk hS s₀ hanchor hden s)
      (curvatureAngle_hasDerivAt hk.continuous s)⟩

theorem reconstructed_unit_speed {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ : ℝ) (hanchor : k s₀≠0)
    (hden : a^2+b^2≠0) (s : ℝ) :
    deriv (reconstructedX k a b s₀) s^2+deriv (reconstructedY k a b s₀) s^2=1 :=
  profile_unit_speed k _ _ _ s
    (normalCoefficient_hasDerivAt hk hS s₀ hanchor s)
    (tangentCoefficient_hasDerivAt hk hS s₀ hanchor hden s)
    (curvatureAngle_hasDerivAt hk.continuous s)

theorem reconstructed_curvature {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ : ℝ) (hanchor : k s₀≠0)
    (hden : a^2+b^2≠0) (s : ℝ) :
    deriv (reconstructedX k a b s₀) s*deriv (deriv (reconstructedY k a b s₀)) s-
      deriv (reconstructedY k a b s₀) s*deriv (deriv (reconstructedX k a b s₀)) s=k s :=
  profile_signed_curvature k _ _ _
    (normalCoefficient_hasDerivAt hk hS s₀ hanchor)
    (tangentCoefficient_hasDerivAt hk hS s₀ hanchor hden)
    (curvatureAngle_hasDerivAt hk.continuous) s

theorem reconstructed_soliton_equation (k : ℝ → ℝ) (a b s₀ s : ℝ)
    (hden : a^2+b^2≠0) :
    deriv (deriv k) s+k s^3/2 =
      -a*(reconstructedX k a b s₀ s*(-Real.sin (curvatureAngle k s))+
        reconstructedY k a b s₀ s*Real.cos (curvatureAngle k s))-
      b*(reconstructedX k a b s₀ s*Real.cos (curvatureAngle k s)+
        reconstructedY k a b s₀ s*Real.sin (curvatureAngle k s)) := by
  change force k s = _
  dsimp only [reconstructedX,reconstructedY]
  rw [normal_support,tangent_support]
  exact force_eq_coefficients k a b s₀ s hden

theorem candidateSupport_periodic {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b L : ℝ} (hS : ScalarEquation k a b) (hper : Function.Periodic k L)
    (s₀ : ℝ) (hanchor : k s₀≠0) :
    Function.Periodic (candidateSupport k a b s₀) L :=
  candidateSupport_periodic_of_global_identity hk hper s₀ hanchor
    (candidateSupport_eq_quotient_global hk hS s₀ hanchor)

theorem reconstructed_intrinsic_soliton_equation {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) {a b : ℝ} (hS : ScalarEquation k a b)
    (s₀ : ℝ) (hanchor : k s₀≠0) (hden : a^2+b^2≠0) (s : ℝ) :
    deriv (deriv k) s+k s^3/2 =
      -a*(reconstructedX k a b s₀ s*(-deriv (reconstructedY k a b s₀) s)+
        reconstructedY k a b s₀ s*deriv (reconstructedX k a b s₀) s)-
      b*(reconstructedX k a b s₀ s*deriv (reconstructedX k a b s₀) s+
        reconstructedY k a b s₀ s*deriv (reconstructedY k a b s₀) s) := by
  obtain ⟨hx,hy⟩ := reconstructed_hasDerivAt hk hS s₀ hanchor hden s
  rw [hx.deriv,hy.deriv]
  exact reconstructed_soliton_equation k a b s₀ s hden

theorem coefficients_periodic {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b L : ℝ} (hS : ScalarEquation k a b) (hper : Function.Periodic k L)
    (s₀ : ℝ) (hanchor : k s₀≠0) :
    Function.Periodic (normalCoefficient k a b s₀) L ∧
      Function.Periodic (tangentCoefficient k a b s₀) L := by
  have hH := candidateSupport_periodic hk hS hper s₀ hanchor
  constructor <;> intro s <;>
    simp only [normalCoefficient,tangentCoefficient,force_periodic hper s,hH s]

theorem reconstructed_periodic {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b L : ℝ} (hS : ScalarEquation k a b) (hper : Function.Periodic k L)
    (s₀ : ℝ) (hanchor : k s₀≠0) (m : ℤ)
    (hhol : (∫ u in 0..L, k u)=m*(2*Real.pi)) :
    Function.Periodic (reconstructedX k a b s₀) L ∧
      Function.Periodic (reconstructedY k a b s₀) L := by
  obtain ⟨hp,hq⟩ := coefficients_periodic hk hS hper s₀ hanchor
  exact profile_periodic _ _ _ L m hp hq (fun s => by
    rw [curvatureAngle_period_shift hk.continuous hper,hhol])

/-- Complete scalar-to-curve converse: the only input data are a smooth nonzero
periodic scalar-equation solution, nonzero soliton parameters, and integral
tangent holonomy. Both support reconstruction and position closure are proved. -/
theorem exists_closed_soliton_of_scalar_equation {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) {a b L : ℝ} (hS : ScalarEquation k a b)
    (hL : 0<L) (hper : Function.Periodic k L) (hnonzero : ∃ s₀, k s₀≠0)
    (hden : a^2+b^2≠0) (m : ℤ)
    (hhol : (∫ u in 0..L, k u)=m*(2*Real.pi)) :
    ∃ X Y : ℝ → ℝ, 0<L ∧
      ContDiff ℝ ∞ X ∧ ContDiff ℝ ∞ Y ∧
      Function.Periodic X L ∧ Function.Periodic Y L ∧
      (∀ s, deriv X s^2+deriv Y s^2=1) ∧
      (∀ s, deriv X s*deriv (deriv Y) s-deriv Y s*deriv (deriv X) s=k s) ∧
      (∀ s, deriv (deriv k) s+k s^3/2 =
        -a*(X s*(-deriv Y s)+Y s*deriv X s)-
        b*(X s*deriv X s+Y s*deriv Y s)) := by
  obtain ⟨s₀,hanchor⟩ := hnonzero
  obtain ⟨hx,hy⟩ := reconstructed_smooth hk a b s₀
  obtain ⟨hpx,hpy⟩ := reconstructed_periodic hk hS hper s₀ hanchor m hhol
  exact ⟨reconstructedX k a b s₀,reconstructedY k a b s₀,hL,hx,hy,hpx,hpy,
    reconstructed_unit_speed hk hS s₀ hanchor hden,
    reconstructed_curvature hk hS s₀ hanchor hden,
    reconstructed_intrinsic_soliton_equation hk hS s₀ hanchor hden⟩

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar curve audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Scalar curve audit passed for {count} declarations."
