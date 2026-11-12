import CentroidEscape.VariableOrderTaylor
import CentroidEscape.MetricBudget

/-! Finite scalar residuals at arbitrary N<=160, with the exact N=60 value. -/
namespace CentroidEscape.MetricStability
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def orderScalarMajorant (N : ℕ) : ℝ[X] :=
  ∑ n ∈ Finset.range (N+1), monomial n (majorantCoeff n : ℝ)

lemma orderScalarMajorant_coeff (N n : ℕ) :
    (orderScalarMajorant N).coeff n=if n<N+1 then (majorantCoeff n:ℝ) else 0 := by
  simp [orderScalarMajorant,coeff_monomial,Finset.mem_range]

lemma orderScalarMajorant_zero (N : ℕ) : (orderScalarMajorant N).coeff 0=1 := by
  simp [orderScalarMajorant_coeff,majorantCoeff_zero]

lemma orderScalarMajorant_nonneg (N n : ℕ) : 0≤(orderScalarMajorant N).coeff n := by
  rw [orderScalarMajorant_coeff]
  split_ifs <;> positivity

lemma orderScalarMajorant_linear_zero {N : ℕ} (hN : N≤160) (n : ℕ) (hn : n<N) :
    (linearMajorantResidual (orderScalarMajorant N)).coeff n=0 := by
  rw [linearMajorantResidual_coeff,orderScalarMajorant_coeff,orderScalarMajorant_coeff,
    if_pos (by omega : n+1<N+1),if_pos (by omega : n<N+1)]
  have hh := majorantCoeff_recurrence ⟨n,by omega⟩
  have hr : (n+1:ℝ)*(majorantCoeff (n+1):ℝ)=6*(2*n+1)*(majorantCoeff n:ℝ) := by
    exact_mod_cast hh
  linarith

def orderScalarResidual (N : ℕ) : ℝ[X] :=
  C 2*(orderScalarMajorant N)^3-C (1/3)*derivative (orderScalarMajorant N)

lemma orderScalarResidual_low {N : ℕ} (hN : N≤160) (n : ℕ) (hn : n<N) :
    (orderScalarResidual N).coeff n=0 := by
  have hh := cubic_defect_coeff_zero (orderScalarMajorant_zero N)
    (orderScalarMajorant_linear_zero hN) n hn
  simp only [coeff_sub,coeff_C_mul] at hh
  simp only [orderScalarResidual,coeff_sub,coeff_C_mul]
  linarith

lemma orderScalarResidual_nonneg {N : ℕ} (hN : N≤160) (n : ℕ) :
    0≤(orderScalarResidual N).coeff n := by
  by_cases hn : n<N
  · rw [orderScalarResidual_low hN n hn]
  · have hd : (derivative (orderScalarMajorant N)).coeff n=0 := by
      rw [coeff_derivative,orderScalarMajorant_coeff,if_neg (by omega),zero_mul]
    simp only [orderScalarResidual,coeff_sub,coeff_C_mul,hd,mul_zero,sub_zero]
    have hu2 := coeff_mul_nonneg_all (orderScalarMajorant_nonneg N) (orderScalarMajorant_nonneg N)
    have hu3 := coeff_mul_nonneg_all hu2 (orderScalarMajorant_nonneg N) n
    have hp : (orderScalarMajorant N)^3=
        orderScalarMajorant N*orderScalarMajorant N*orderScalarMajorant N := by ring
    rw [hp]
    positivity

def orderDisplacementMajorant (N : ℕ) : ℝ[X] := C (1/3)*(orderScalarMajorant N-1)

lemma orderDisplacementMajorant_zero (N : ℕ) : (orderDisplacementMajorant N).coeff 0=0 := by
  simp [orderDisplacementMajorant,orderScalarMajorant_zero]

lemma orderDisplacementMajorant_pos (N n : ℕ) (hn : 0<n) :
    (orderDisplacementMajorant N).coeff n=(orderScalarMajorant N).coeff n/3 := by
  simp [orderDisplacementMajorant,coeff_sub,coeff_one,ne_of_gt hn]
  ring

lemma orderDisplacementMajorant_nonneg (N n : ℕ) : 0≤(orderDisplacementMajorant N).coeff n := by
  by_cases hn : n=0
  · simp [hn,orderDisplacementMajorant_zero]
  · rw [orderDisplacementMajorant_pos N n (Nat.pos_of_ne_zero hn)]
    exact div_nonneg (orderScalarMajorant_nonneg N n) (by norm_num)

lemma orderDisplacementMajorant_agrees {N : ℕ} (hN : N≤160) (n : ℕ) (hn : n≤N) :
    (orderDisplacementMajorant N).coeff n=displacementMajorant.coeff n := by
  by_cases hz : n=0
  · simp [hz,orderDisplacementMajorant_zero,displacementMajorant_zero]
  · rw [orderDisplacementMajorant_pos N n (Nat.pos_of_ne_zero hz),
      displacementMajorant_coeff_pos n (Nat.pos_of_ne_zero hz),
      orderScalarMajorant_coeff,scalarMajorant_coeff,if_pos (by omega),if_pos (by omega)]

def forcingPolynomial (w : ℝ[X]) : ℝ[X] := C 2+C 18*w+C 54*w^2+C 54*w^3

lemma forcingPolynomial_order_eq (N : ℕ) :
    forcingPolynomial (orderDisplacementMajorant N)=C 2*(orderScalarMajorant N)^3 := by
  have hu : orderScalarMajorant N=1+C 3*orderDisplacementMajorant N := by
    rw [orderDisplacementMajorant,← mul_assoc,← C_mul]
    norm_num
  rw [forcingPolynomial,hu]
  simp only [C_ofNat]
  ring

lemma orderScalarForcing_high (N n : ℕ) (hn : N≤n) :
    (forcingPolynomial (orderDisplacementMajorant N)).coeff n=(orderScalarResidual N).coeff n := by
  have hd : (derivative (orderScalarMajorant N)).coeff n=0 := by
    rw [coeff_derivative,orderScalarMajorant_coeff,if_neg (by omega),zero_mul]
  simp only [forcingPolynomial_order_eq,orderScalarResidual,coeff_sub,coeff_C_mul,hd,mul_zero,sub_zero]

lemma majorant60_rational_value :
    (∑ n ∈ Finset.range 61, (majorantCoeff n:ℚ)*(1/100:ℚ)^n)=majorant60Value := by
  decide +kernel

lemma majorant60_rational_derivative :
    (∑ n ∈ Finset.range 61, (majorantCoeff n:ℚ)*n*(1/100:ℚ)^(n-1))=majorant60Derivative := by
  decide +kernel

lemma orderScalarMajorant60_value : (orderScalarMajorant 60).eval (1/100)=(majorant60Value:ℝ) := by
  have hh := congrArg (fun q:ℚ=>(q:ℝ)) majorant60_rational_value
  simpa [orderScalarMajorant,eval_finsetSum] using hh

lemma orderScalarMajorant60_derivative_value :
    (derivative (orderScalarMajorant 60)).eval (1/100)=(majorant60Derivative:ℝ) := by
  have hh := congrArg (fun q:ℚ=>(q:ℝ)) majorant60_rational_derivative
  simpa [orderScalarMajorant,derivative_monomial,eval_finsetSum] using hh

theorem orderScalarResidual60_value : (orderScalarResidual 60).eval (1/100)=(finiteResidual60:ℝ) := by
  simp only [orderScalarResidual,eval_sub,eval_mul,eval_C,eval_pow,
    orderScalarMajorant60_value,orderScalarMajorant60_derivative_value]
  simp [finiteResidual60]
  ring

theorem orderScalarResidual60_uniform {t : ℝ} (ht : 0≤t) (htmax : t≤1/100) :
    (orderScalarResidual 60).eval t≤(finiteResidual60:ℝ) := by
  rw [← orderScalarResidual60_value]
  exact eval_monotone_of_coeff_nonneg (orderScalarResidual_nonneg (by omega : 60≤160)) ht htmax

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.orderScalarResidual60_uniform
