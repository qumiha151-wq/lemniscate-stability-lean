import Migration.AngularWienerBound

noncomputable section
open Set
namespace MigrationGeometry.AngularGauge.FourierExample

/-- Nonlinear coefficient for the operator acting on the angle error. -/
def coefficient (v w : ℝ) := (5*v*w+w^2+(5/2)*v^4)/2+(5/2)*v^2+2*v*w

def slab : ℝ := 1/1000000
def radius : ℝ := 7/100000000
def defectBound : ℝ := 47091/1000000000

/-- Quantitative first-contact threshold including the kernel integral and
roundup in both input derivative bounds. -/
theorem numerical_barrier {V W R : ℝ}
    (v : 0 ≤ V) (w : 0 ≤ W) (r : 0 ≤ R)
    (iv : V ≤ 120000222/100000000 + radius/2)
    (iw : W ≤ 40000573/100000000 + radius)
    (ir : R ≤ defectBound) :
    (slab+Real.sqrt (2*slab))*(R+coefficient V W*radius) ≤ 67490/1000000000000 ∧
    (67490/1000000000000 : ℝ)<radius := by
  have monotone : coefficient V W ≤
      coefficient (120000222/100000000+radius/2) (40000573/100000000+radius) := by
    unfold coefficient
    gcongr <;> norm_num [radius]
  have sqrtbound : Real.sqrt (2*slab) ≤ 1/707 := by
    rw [Real.sqrt_le_left (by norm_num : (0:ℝ)≤1/707)]
    norm_num [slab]
  have cp : 0 ≤ R+coefficient V W*radius := by unfold coefficient radius; positivity
  have step := mul_le_mul (add_le_add_right sqrtbound slab)
    (add_le_add ir (mul_le_mul_of_nonneg_right monotone (by norm_num [radius]))) cp
    (by norm_num [slab] : (0:ℝ)≤slab+1/707)
  refine ⟨step.trans ?_, ?_⟩ <;> norm_num [coefficient,radius,defectBound,slab]

/-- A trajectory satisfying the integrated Fourier error inequality stays
within the radius on the entire slab, starting from exact initial data. -/
theorem numerical_slab {e : ℝ → ℝ} {V W R : ℝ}
    (v : 0 ≤ V) (w : 0 ≤ W) (r : 0 ≤ R)
    (iv : V ≤ 120000222/100000000 + radius/2)
    (iw : W ≤ 40000573/100000000 + radius)
    (ir : R ≤ defectBound)
    (ct : ContinuousOn e (Icc 0 slab)) (init : e 0 = 0)
    (estimate : ∀t∈Icc 0 slab,(∀s∈Icc 0 t,e s ≤ radius) →
      e t ≤ (slab+Real.sqrt (2*slab))*(R+coefficient V W*radius)) :
    ∀t∈Icc 0 slab,e t<radius := by
  have bd := numerical_barrier v w r iv iw ir
  apply slab_barrier ct (by rw [init]; norm_num [radius]) bd.2
  intro t ht h
  exact (estimate t ht h).trans bd.1

end MigrationGeometry.AngularGauge.FourierExample
#print axioms MigrationGeometry.AngularGauge.FourierExample.numerical_barrier
#print axioms MigrationGeometry.AngularGauge.FourierExample.numerical_slab
