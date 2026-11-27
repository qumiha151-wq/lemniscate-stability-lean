import Migration.CurveKinematics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.ContinuousMap.Algebra

noncomputable section
open MeasureTheory Set
namespace MigrationGeometry.Flow.MultiBending

abbrev Fn := C(ℝ,ℝ)

def mass (P : ℝ) : Fn →ₗ[ℝ] ℝ where
  toFun a := ∫s in 0..P,a s
  map_add' a b := intervalIntegral.integral_add (a.continuous.intervalIntegrable ..) (b.continuous.intervalIntegrable ..)
  map_smul' c a := intervalIntegral.integral_const_mul c a

theorem mass_one (P : ℝ) : mass P 1=P := by simp [mass]

theorem mass_mono (P : ℝ) (hp : 0≤P) (a b : Fn) (h : ∀t∈Icc 0 P, a t≤b t) :
    mass P a ≤ mass P b :=
  intervalIntegral.integral_mono_on hp (a.continuous.intervalIntegrable ..) (b.continuous.intervalIntegrable ..) h

def norm2 (P : ℝ) (a : Fn) := Real.sqrt (mass P (a^2))

theorem mass_sq_nonneg (P : ℝ) (hp : 0≤P) (a : Fn) : 0≤mass P (a^2) :=
  intervalIntegral.integral_nonneg_of_forall hp (fun s=>sq_nonneg (a s))

theorem norm_sq (P : ℝ) (hp : 0≤P) (a : Fn) : (norm2 P a)^2=mass P (a^2) :=
  Real.sq_sqrt (mass_sq_nonneg _ hp _)

theorem abs_mass_product (P : ℝ) (hp : 0≤P) (a b : Fn) :
    |mass P (a*b)|≤norm2 P a*norm2 P b :=
  (intervalIntegral.abs_integral_le_integral_abs hp).trans (interval_integral_abs_mul_le a.continuous b.continuous hp)

theorem norm_sub (P : ℝ) (hp : 0≤P) (a b : Fn) :
    norm2 P (a-b)≤norm2 P a+norm2 P b := by
  have expand : (a-b)^2=a^2-(2:ℝ) • (a*b)+b^2 := by ext t; simp [smul_eq_mul]; ring
  have h := (abs_le.mp (abs_mass_product P hp a b)).1
  have nn (w : Fn) : 0≤norm2 P w := Real.sqrt_nonneg _
  have z := norm_sq P hp (a-b)
  rw [expand,map_add,map_sub,map_smul,smul_eq_mul] at z
  nlinarith only [z,h,norm_sq P hp a,norm_sq P hp b,nn (a-b),nn a,nn b]

theorem norm_smul (P : ℝ) (_hp : 0≤P) {c : ℝ} (hc : 0≤c) (a : Fn) :
    norm2 P (c • a)=c*norm2 P a := by
  have expand : (c • a)^2=(c^2) • (a^2) := by ext t; simp [smul_eq_mul,mul_pow]
  unfold norm2
  rw [expand,map_smul,smul_eq_mul,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]

theorem norm_pointwise (P : ℝ) (hp : 0≤P) {a b : Fn} {K : ℝ} (hk : 0≤K)
    (h : ∀t∈Icc 0 P, |a t|≤K*|b t|) : norm2 P a≤K*norm2 P b := by
  rw [←norm_smul P hp hk]
  apply Real.sqrt_le_sqrt
  apply mass_mono P hp
  intro t ht
  change a t^2≤(K*b t)^2
  apply sq_le_sq.mpr
  rw [abs_mul,abs_of_nonneg hk]
  exact h t ht

end MigrationGeometry.Flow.MultiBending
