import Migration.AngularSpectralExample

noncomputable section
namespace MigrationGeometry.AngularGauge.Example

/-- Identifies the five actual pointwise initial angle-velocity harmonics
with the imaginary Fourier numerators used by the integer residual. -/
theorem firstVelocity_modes (x : ℝ) : firstVelocity x=
    (-2/4800000:ℝ)*(1918824*Real.sin (2*x)-346160*Real.sin (4*x)-
      13973*Real.sin (6*x)+190*Real.sin (8*x)+3*Real.sin (10*x)) := by
  have step (a : ℝ) : Real.sin (a+2*x)=2*Real.cos (2*x)*Real.sin a-Real.sin (a-2*x) := by
    rw [Real.sin_add,Real.sin_sub]; ring
  have two := step (2*x)
  rw [← show 4*x=2*x+2*x by ring,sub_self,Real.sin_zero,sub_zero] at two
  have three := step (4*x)
  rw [← show 6*x=4*x+2*x by ring,show 4*x-2*x=2*x by ring] at three
  have four := step (6*x)
  rw [← show 8*x=6*x+2*x by ring,show 6*x-2*x=4*x by ring] at four
  have five := step (8*x)
  rw [← show 10*x=8*x+2*x by ring,show 8*x-2*x=6*x by ring] at five
  rw [five,four,three,two]; unfold firstVelocity pol B; ring

end MigrationGeometry.AngularGauge.Example
#print axioms MigrationGeometry.AngularGauge.Example.firstVelocity_modes
