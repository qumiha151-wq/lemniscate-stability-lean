import SolitonClassification.TrigRationalChart

noncomputable section
open Polynomial Set Filter
open scoped Polynomial Topology
namespace ClosedSimilarity.TrigCurvature
open ScalarReconstruction

private theorem differential_identity {a b L : ℝ} (z : PeriodicSupportProfile a b L) (s : ℝ) :
    (z.k s)^6=2*a*z.k s^2-2*z.k s^3*deriv (deriv z.k) s-
      2*z.k s*deriv (deriv (force z.k)) s+
      2*deriv z.k s*deriv (force z.k) s+2*b*deriv z.k s := by
  have h := scalarEquation_of_periodicSupportProfile z s
  dsimp only [numerator,supportDerivative] at h
  have hF : force z.k s=deriv (deriv z.k) s+z.k s^3/2 := rfl
  linear_combination 2*h - 2*z.k s^3*hF

private theorem divides_sixth {a b L u w : ℝ} (z : PeriodicSupportProfile a b L)
    (hw : w≠0) {n : ℕ} {p : ℝ[X]} (rep : Represents u w z.k n p) :
    (Q^n)^2 ∣ p^6 := by
  have dk : Differentiable ℝ z.k := fun s => (z.dk s).differentiableAt
  have ddk : Differentiable ℝ (deriv z.k) := by
    rw [show deriv z.k=z.v from funext fun s => (z.dk s).deriv]
    exact fun s => (z.dv s).differentiableAt
  have dF : Differentiable ℝ (force z.k) := fun s => (force_hasDerivAt_of_profile z s).differentiableAt
  have ddF : Differentiable ℝ (deriv (force z.k)) := by
    rw [show deriv (force z.k)=fun s => z.k s*profileSupportH z s-b from
      funext fun s => (force_hasDerivAt_of_profile z s).deriv]
    exact (dk.mul (fun s => (profileSupportH_hasDerivAt z s).differentiableAt)).sub_const b
  obtain ⟨p₁,h₁⟩ : ∃ p₁,Represents u w (deriv z.k) n p₁ := ⟨_,represents_deriv hw dk rep⟩
  obtain ⟨p₂,h₂⟩ : ∃ p₂,Represents u w (deriv (deriv z.k)) n p₂ := ⟨_,represents_deriv hw ddk h₁⟩
  let D := Q^n
  let pf := p₂*D^2+C (1/2:ℝ)*p^3
  have hF : Represents u w (force z.k) (n*3) pf := by
    intro x
    simp only [pf,D,eval_add,eval_mul,eval_C,eval_pow,eval_Q,← h₂ x,←rep x,force,pow_mul]
    ring
  obtain ⟨pf₁,f₁⟩ : ∃ pf₁,Represents u w (deriv (force z.k)) (n*3) pf₁ :=
    ⟨_,represents_deriv hw dF hF⟩
  obtain ⟨pf₂,f₂⟩ : ∃ pf₂,Represents u w (deriv (deriv (force z.k))) (n*3) pf₂ :=
    ⟨_,represents_deriv hw ddF f₁⟩
  refine ⟨C (2*a)*p^2*D^2-C 2*p^3*p₂-C 2*p*pf₂+C 2*p₁*pf₁+C (2*b)*p₁*D^3,?_⟩
  apply Polynomial.funext
  intro x
  simp only [D,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_Q,
    ←rep x,←h₁ x,←h₂ x,←f₁ x,←f₂ x,pow_mul]
  linear_combination ((1+x^2)^n)^6*differential_identity z (chart u w x)

/-- The differential equation removes every stereographic denominator. -/
theorem cancel_all {a b L u w : ℝ} (z : PeriodicSupportProfile a b L)
    (hw : w≠0) {n : ℕ} {p : ℝ[X]} (rep : Represents u w z.k n p) :
    ∃ h : ℝ[X],Represents u w z.k 0 h := by
  induction n generalizing p with
  | zero => exact ⟨p,rep⟩
  | succ n ih =>
    have dd := divides_sixth z hw rep
    have powdiv : Q ∣ p^6 := (dvd_pow_self Q (Nat.succ_ne_zero n)).trans
      ((dvd_pow_self (Q^(n+1)) (by norm_num : (2:ℕ)≠0)).trans dd)
    obtain ⟨h,eq⟩ := Q_prime.dvd_of_dvd_pow powdiv
    apply ih (p:=h)
    intro x
    have hh := rep x
    rw [eq,eval_mul,eval_Q,pow_succ] at hh
    have hn : 1+x^2≠0 := ne_of_gt (by positivity)
    exact mul_right_cancel₀ hn (by linear_combination hh)

theorem chart_constant_of_rep {a b L u w : ℝ} (z : PeriodicSupportProfile a b L)
    (hL : L≠0) (hw : w≠0) {n : ℕ} {p : ℝ[X]} (rep : Represents u w z.k n p) :
    ∃ c : ℝ,∀ x,z.k (chart u w x)=c := by
  obtain ⟨h,hh⟩ := cancel_all z hw rep
  have ev (x) : h.eval x=z.k (chart u w x) := by simpa only [pow_zero,mul_one] using (hh x).symm
  obtain ⟨B,hB⟩ := (z.periodic_k.isBounded_of_continuous hL z.continuous_k).exists_norm_le
  have hb : IsBoundedUnder (·≤·) atTop (fun x=>|h.eval x|) :=
    ⟨B,Filter.eventually_map.mpr (Eventually.of_forall fun x => by
      rw [ev,←Real.norm_eq_abs]
      exact hB _ (mem_range_self (chart u w x)))⟩
  have hn := Polynomial.eq_C_of_degree_le_zero ((h.isBoundedUnder_abs_atTop_iff).mp hb)
  refine ⟨h.coeff 0,fun x => ?_⟩
  rw [←ev x,congrArg (Polynomial.eval x) hn,eval_C]

end ClosedSimilarity.TrigCurvature
