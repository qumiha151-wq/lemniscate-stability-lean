import LengthGrowth.ActualFlow.TrigonometricPrescription
import LengthGrowth.ActualFlow.TrigonometricPhysicalRate
import LengthGrowth.ActualFlow.MulticoverAngleRealization

noncomputable section
open MeasureTheory Function Set
open scoped ContDiff
namespace LengthGrowth.Multicover.Trigonometric
open LengthGrowth.Multicover.Outward

def primitiveWave (s : ℝ) := 2*Real.sin s+Real.sin (3*s)/96

def liftAngle (n : ℕ) (m a A s : ℝ) := m*s + a*Real.sin s + (A/n)*primitiveWave (n*s)

def curvatureField (n : ℕ) (m a A : ℝ) : Fn :=
  m • (1 : Fn) + a • signedMode 1 + A • trigWave n

theorem lift_smooth (n : ℕ) (m a A : ℝ) : ContDiff ℝ ∞ (liftAngle n m a A) := by
  unfold liftAngle primitiveWave
  fun_prop

private theorem linearDeriv (c s : ℝ) : HasDerivAt (fun t : ℝ => c*t) c s := by
  simpa using (hasDerivAt_id s).const_mul c

theorem lift_derivative {n : ℕ} (hn : 0 < n) (m a A : ℝ) :
    deriv (liftAngle n m a A) = curvatureField n m a A := by
  have nz : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  funext s
  have d₁ := (linearDeriv (n:ℝ) s).sin.const_mul 2
  have d₃ := (((linearDeriv (n:ℝ) s).const_mul 3).sin).div_const 96
  have ds := d₁.add d₃
  have h := ((linearDeriv m s).add ((Real.hasDerivAt_sin s).const_mul a)).add (ds.const_mul (A/n))
  apply h.deriv.trans
  change _ = m*1+a*Real.cos ((1:ℤ)*s)+A*(2*Real.cos _ + Real.cos _/32)
  simp only [Int.cast_one,one_mul,mul_one]
  field_simp
  ring

def spatialForce (k : Fn) : ℝ→ℝ := fun s => deriv (deriv (fun x => k x)) s + (k s)^3/2

theorem field_scaled (n : ℕ) {m a A : ℝ} (nz : A ≠ 0) :
    curvatureField n m a A = A • scaledCurvature n m a A := by
  ext s
  change m*1 + a*Real.cos ((1:ℤ)*s) + A*trigWave n s = A*(trigWave n s+(m+a*Real.cos s)/A)
  simp only [Int.cast_one,one_mul]
  field_simp
  ring

theorem force_scaled (n : ℕ) {m a A : ℝ} (nz : A ≠ 0) (s : ℝ) :
    spatialForce (curvatureField n m a A) s = A^3 * scaledForce n m a A s := by
  let dn := fun x => linearDeriv (n:ℝ) x
  have first (x : ℝ) : HasDerivAt (fun t => curvatureField n m a A t)
      (-(a*Real.sin x) + A*(2*(-Real.sin (n*x)*n) + (-Real.sin (3*(n*x))*(3*n))/32)) x := by
    change HasDerivAt (fun t : ℝ => m*1+a*Real.cos ((1:ℤ)*t)+A*(2*Real.cos (n*t)+Real.cos (3*(n*t))/32)) _ x
    simp only [Int.cast_one, one_mul, mul_one]
    apply (((hasDerivAt_const x m).add ((Real.hasDerivAt_cos x).const_mul a)).add
      ((((dn x).cos.const_mul 2).add ((((dn x).const_mul 3).cos).div_const 32)).const_mul A)).congr_deriv
    ring
  have secondOne := (((dn s).sin.neg).mul_const (n:ℝ)).const_mul 2
  have secondThree := ((((dn s).const_mul 3).sin.neg).mul_const (3*(n:ℝ))).div_const 32
  have sec := (((Real.hasDerivAt_sin s).const_mul a).neg).add ((secondOne.add secondThree).const_mul A)
  unfold spatialForce
  rw [show deriv (fun x => curvatureField n m a A x) = _ from funext (fun x => (first x).deriv)]
  have deq : deriv (fun x : ℝ => -(a*Real.sin x) + A*(2*(-Real.sin (n*x)*n) +
      (-Real.sin (3*(n*x))*(3*n))/32)) s = _ := sec.deriv
  rw [deq]
  have eq := congrArg (fun v : Fn => v s) (field_scaled n (m:=m) (a:=a) nz)
  change curvatureField n m a A s = A*scaledCurvature n m a A s at eq
  rw [eq]
  change _ = A^3*((n/A)^2*(-2*Real.cos _-9*Real.cos _/32) - a*Real.cos s/A^3 +
    (scaledCurvature n m a A s)^3/2)
  field_simp
  ring

private theorem phase_periodic : Periodic primitiveWave period := by
  intro s
  unfold primitiveWave period
  rw [Real.sin_add_two_pi, show 3*(s+2*Real.pi) = 3*s + (3:ℕ)*(2*Real.pi) by norm_num; ring,
    Real.sin_add_nat_mul_two_pi]

theorem lift_periodic (n : ℕ) (m : ℤ) (a A : ℝ) : Periodic (angleTangent (liftAngle n m a A)) period := by
  intro s
  have hp := (phase_periodic.nsmul n) ((n:ℝ)*s)
  simp only [nsmul_eq_mul] at hp
  have eq : liftAngle n m a A (s+period) = liftAngle n m a A s + (m:ℝ)*period := by
    unfold liftAngle
    rw [mul_add, mul_add, hp, show Real.sin (s+period) = Real.sin s from Real.sin_add_two_pi s]
    ring
  unfold angleTangent
  rw [eq,Complex.ofReal_add,mul_add,Complex.exp_add]
  have one : Complex.exp (Complex.I * (↑((m:ℝ)*period) : ℂ)) = 1 := by
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨m, ?_⟩
    unfold period
    push_cast
    ring
  rw [one,mul_one]

theorem nonzero_closure {n : ℕ} (hn : 0 < n) {m : ℤ} (hm : m ≠ 0) (small : |(m:ℝ)| < n) (A : ℝ) :
    (∫ s in 0..period, angleTangent (liftAngle n m 0 A) s) = 0 := by
  let cell := period/(n:ℝ)
  let v := angleTangent (liftAngle n m 0 A)
  let z := Complex.exp (Complex.I * (↑((m:ℝ)*cell) : ℂ))
  have np : 0 < (n:ℝ) := by exact_mod_cast hn
  have scale : (n:ℝ)*cell = period := by dsimp [cell]; field_simp
  have shift (s : ℝ) : v (s+cell) = z*v s := by
    have angle : liftAngle n m 0 A (s+cell) = (m:ℝ)*cell + liftAngle n m 0 A s := by
      unfold liftAngle
      rw [mul_add, mul_add, scale, phase_periodic]
      ring
    dsimp only [v, z, angleTangent]
    rw [angle, Complex.ofReal_add, mul_add, Complex.exp_add]
  have nontrivial : z ≠ 1 := by
    intro eq
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp eq
    have im := congrArg Complex.im hk
    simp [Complex.mul_im, cell, period] at im
    have eqmk : (m:ℝ) = (k:ℝ)*n := by
      have pi := Real.pi_pos
      field_simp [np.ne'] at im
      nlinarith only [im, pi, mul_pos_iff_of_pos_right (a:=(m:ℝ)-(k:ℝ)*n) pi]
    have hkle : |(k:ℝ)| < 1 := by
      rw [eqmk, abs_mul, abs_of_pos np] at small
      by_contra! bad
      nlinarith only [small, mul_nonneg (sub_nonneg.mpr bad) np.le]
    have hkz : |k| < 1 := by exact_mod_cast hkle
    obtain ⟨kl,ku⟩ := abs_lt.mp hkz
    have kz : k = 0 := by omega
    simp [kz] at eqmk
    exact hm (by exact_mod_cast eqmk)
  have invariant : (∫ s in 0..period, v (s+cell)) = ∫ s in 0..period, v s := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm period cell] using (lift_periodic n m 0 A).intervalIntegral_add_eq cell 0
  simp_rw [shift] at invariant
  rw [intervalIntegral.integral_const_mul] at invariant
  apply (mul_eq_zero.mp (show (z-1)*(∫ s in 0..period, v s) = 0 by
    rw [sub_mul,one_mul,invariant,sub_self])).resolve_left (sub_ne_zero.mpr nontrivial)

end LengthGrowth.Multicover.Trigonometric
#print axioms LengthGrowth.Multicover.Trigonometric.nonzero_closure

