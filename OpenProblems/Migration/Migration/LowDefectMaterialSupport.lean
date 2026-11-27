import Migration.LowDefectPositionSeries
import Migration.LowDefectHarmonicSupport

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Actual normalized position supremum and directional support, obtained
from the full Fourier series of the arclength-parametrized immersion. -/
theorem material_normalized_support {t : ℝ} (ht : t∈I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤14/100) :
    let p := c.materialSlice ht
    let G := p.fractionalPosition (c.arclengthCentroid t)
    let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
    let H := 575/1000*Real.sqrt D+133/1000*D
    (∀x∈Icc (0:ℝ) 1, ‖G x‖≤1+H) ∧
    ∀e : ℂ, ‖e‖=1 → ∃x∈Ico (0:ℝ) 1, 1-132/1000*D-H ≤ inner ℝ e (G x) := by
  let p := c.materialSlice ht
  let T := p.fractionalTangent
  let B := c.arclengthCentroid t
  let G := p.fractionalPosition B
  let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
  let H := 575/1000*Real.sqrt D+133/1000*D
  let A := LowDefect.Tangent.coeff G 1
  have dpos : 0≤D := div_nonneg (c.curvatureOscillation_nonneg ht _) (sq_nonneg _)
  change D≤14/100 at small
  have ct : Continuous T := continuous_iff_continuousAt.mpr fun x=>(p.fractionalTangent_hasDerivAt x).continuousAt
  obtain ⟨t0,mass,m1,m2⟩ := c.material_tangent_fourier_data ht turn
  have gz : LowDefect.Tangent.coeff G 0=0 := by
    have m := c.material_fractional_position_mean ht
    change (∫x in (0:ℝ)..1,G x)=0 at m
    simp [LowDefect.Tangent.coeff,fourierCoeffOn_eq_integral,m]
  have cap := c.material_second_harmonic_bounds ht turn small
  have err : ∀x∈Ico (0:ℝ) 1, ‖G x-A*fourier 1 (x:AddCircle (1:ℝ))‖≤H :=
    fun _ hx => LowDefect.Tangent.position_harmonic_error ct (p.fractionalPosition_der B)
      (p.fractionalPosition_per B) gz m2 cap.2 hx
  have an : ‖A‖=‖LowDefect.Tangent.coeff T 1‖ := by
    dsimp only [A,G]
    rw [LowDefect.Tangent.position_coefficient ct (p.fractionalPosition_der B) (p.fractionalPosition_per B) (by decide : (1:ℤ)≠0)]
    simp
  have mn := mass.summable.sum_le_tsum ({1}:Finset ℤ) (fun n _ => show 0≤LowDefect.Tangent.energy T n from sq_nonneg _)
  rw [mass.tsum_eq] at mn
  simp only [Finset.sum_singleton] at mn
  change ‖LowDefect.Tangent.coeff T 1‖^2≤1 at mn
  have upper : ‖A‖≤1 := by rw [an]; nlinarith
  have low := cap.1
  change 1-‖LowDefect.Tangent.coeff T 1‖^2≤26/100*D at low
  have lower : 1-132/1000*D≤‖A‖ := by
    rw [an]
    apply le_of_sq_le_sq _ (norm_nonneg _)
    nlinarith only [low,mul_le_mul_of_nonneg_right small dpos,dpos]
  change (∀x∈Icc (0:ℝ) 1, ‖G x‖≤1+H) ∧ _
  constructor
  · intro x hx
    have b (s) (hs : s∈Ico (0:ℝ) 1) := (LowDefect.Tangent.harmonic_outer err s hs).trans (add_le_add upper (le_refl H))
    rcases lt_or_eq_of_le hx.2 with l|eq
    · exact b x ⟨hx.1,l⟩
    · subst x
      rw [show G 1=G 0 from p.fractionalPosition_per B]
      exact b 0 ⟨le_rfl,by norm_num⟩
  · intro e unit
    obtain ⟨x,hx,val⟩ := LowDefect.Tangent.harmonic_support err e unit
    exact ⟨x,hx,(sub_le_sub_right lower H).trans val⟩

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.material_normalized_support
