import SolitonClassification.HolonomicFreeze

noncomputable section
open Polynomial Function Set MeasureTheory Real
namespace ClosedSimilarity.Holonomic

def frequency (P : ℝ) (j : ℤ) : ℂ := (2 * Real.pi * Complex.I / (P : ℂ)) * (j : ℂ)

private theorem coeff_derivative {P : ℝ} (hP : 0 < P) {f g : ℝ→ℂ}
    (df : ∀ s, HasDerivAt f (g s) s) (cg : Continuous g) (period : Periodic f P) (n : ℤ) :
    fourierCoeffOn hP g n = frequency P n * fourierCoeffOn hP f n := by
  have endpoint : f P = f 0 := by simpa using period 0
  by_cases hn : n=0
  · subst n
    have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=P)
      (fun s _ => df s) (cg.intervalIntegrable 0 P)
    rw [endpoint,sub_self] at e
    simp [fourierCoeffOn_eq_integral,frequency,e]
  · have e := fourierCoeffOn_of_hasDerivAt hP hn (fun s _ => df s) (cg.intervalIntegrable 0 P)
    rw [endpoint,sub_self,mul_zero,zero_sub] at e
    rw [e]
    have nz : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    have pz : (P:ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    have piz : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [frequency, Complex.ofReal_zero, sub_zero]
    field_simp [nz, pz, piz, Complex.I_ne_zero]

private theorem coeff_add {P : ℝ} (hp : 0 < P) (n : ℤ) {f g : ℝ→ℂ}
    (cf : Continuous f) (cg : Continuous g) :
    fourierCoeffOn hp (fun s => f s + g s) n = fourierCoeffOn hp f n + fourierCoeffOn hp g n := by
  simp only [fourierCoeffOn_eq_integral, ←smul_add]
  congr 1
  let χ := fun s : ℝ => fourier (-n) (s : AddCircle (P-0))
  have cc : Continuous χ := (fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)
  change (∫s in 0..P, χ s • (f s + g s)) = _
  simp only [smul_add]
  exact intervalIntegral.integral_add ((cc.mul cf).intervalIntegrable ..) ((cc.mul cg).intervalIntegrable ..)

private theorem symbol_zero {P : ℝ} (hp : 0 < P) (J : Finset ℕ) (c : ℕ→ℂ)
    (u : ℕ → ℝ → ℂ) (cu : ∀ j, Continuous (u j)) (per : ∀ j, Periodic (u j) P)
    (jet : ∀ j s, HasDerivAt (u j) (u (j+1) s) s)
    (zero : ∀ s, ∑ j ∈ J, c j*u j s = 0) (n : ℤ) :
    (∑ j ∈ J, c j*(frequency P n)^j) * fourierCoeffOn hp (u 0) n = 0 := by
  have jets (j : ℕ) : fourierCoeffOn hp (u j) n = (frequency P n)^j*fourierCoeffOn hp (u 0) n := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [coeff_derivative hp (jet j) (cu _) (per j),ih,pow_succ]
      ring
  have linear (S : Finset ℕ) : fourierCoeffOn hp (fun s => ∑ j ∈ S,c j*u j s) n =
      ∑ j ∈ S, c j*fourierCoeffOn hp (u j) n := by
    classical
    induction S using Finset.induction_on with
    | empty => simp [fourierCoeffOn_eq_integral]
    | @insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      rw [coeff_add hp n (f:=fun s => c k*u k s) (g:=fun s => ∑ j ∈ S, c j*u j s) (continuous_const.mul (cu _))
        (continuous_finsetSum _ (fun j _ => continuous_const.mul (cu j))),
        fourierCoeffOn.const_mul,ih]
  have h := linear J
  simp_rw [zero] at h
  simp only [fourierCoeffOn_eq_integral (fun _ : ℝ => (0:ℂ)),smul_zero,intervalIntegral.integral_zero] at h
  rw [Finset.sum_mul]
  calc
    _ = ∑ j ∈ J, c j*fourierCoeffOn hp (u j) n := by
      apply Finset.sum_congr rfl
      intro j _
      conv_rhs => rw [jets j]
      ring
    _ = 0 := h.symm

theorem fourier_support_finite {P : ℝ} (hp : 0 < P) (J : Finset ℕ)
    (u : ℕ → ℝ → ℂ) (p : ℕ → Polynomial ℂ) (cu : ∀ j, Continuous (u j))
    (per : ∀ j, Periodic (u j) P) (jet : ∀ j s, HasDerivAt (u j) (u (j+1) s) s)
    (nonzero : ∃ j ∈ J, p j ≠ 0)
    (ode : ∀ s : ℝ, ∑ j ∈ J, (p j).eval (s : ℂ)*u j s = 0) :
    (support (fourierCoeffOn hp (u 0))).Finite := by
  classical
  obtain ⟨c,⟨j,hj,cj⟩,h⟩ := frozen_annihilator hp J u p (fun i _ => per i) nonzero ode
  let Q : Polynomial ℂ := ∑ i ∈ J, Polynomial.monomial i (c i)
  have nz : Q ≠ 0 := by
    intro z
    apply cj
    have e := congrArg (fun k : Polynomial ℂ => k.coeff j) z
    simpa [Q, Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,hj] using e
  have fp : (2 * (Real.pi:ℂ) * Complex.I / (P:ℂ)) ≠ 0 := by
    have pi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have pz : (P:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) pi) Complex.I_ne_zero) pz
  have inject : Injective (frequency P) := by
    intro i j h
    have z : (i:ℂ) = (j:ℂ) := mul_left_cancel₀ fp h
    exact_mod_cast z
  have fin := (Polynomial.finite_setOfPred_isRoot nz).preimage inject.injOn
  apply fin.subset
  intro n hn
  have s := (mul_eq_zero.mp (symbol_zero hp J c u cu per jet h n)).resolve_right hn
  change Q.eval (frequency P n) = 0
  simpa [Q, Polynomial.eval_finsetSum] using s

end ClosedSimilarity.Holonomic
#print axioms ClosedSimilarity.Holonomic.fourier_support_finite

