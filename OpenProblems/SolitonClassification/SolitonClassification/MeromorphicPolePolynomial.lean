import SolitonClassification.MeromorphicTaylorExtraction

noncomputable section
open Complex Polynomial Filter Set
open scoped Topology Polynomial
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature

def polyR (a b:ℂ) (P:ℂ[X]) : ℂ[X] :=
  let D1:=polyStep (-1) P
  let D2:=polyStep (-2) D1
  let D3:=polyStep (-3) D2
  let D4:=polyStep (-4) D3
  C 2*(P*D4-D1*D3)+(C 3*(P^2*D1^2)+C 5*(P^3*D2))+P^6-
    X^4*(C (2*a)*P^2)-X^4*(C (2*b)*D1)

def polyDefect (P:ℂ[X]) := polyStep (-2) (polyStep (-1) P)+C (2/9:ℂ)*P^3

theorem residual_approx {k:ℂ→ℂ} {x a b:ℂ} {P:ℂ[X]} (h:Approx x (-1) k P) :
    Approx x (-6) (ordinaryResidual a b k) (polyR a b P) := by
  let D1:=polyStep (-1) P
  let D2:=polyStep (-2) D1
  let D3:=polyStep (-3) D2
  let D4:=polyStep (-4) D3
  have d1 : Approx x (-2) (deriv k) D1 := h.deriv_step
  have d2 : Approx x (-3) (deriv (deriv k)) D2 := d1.deriv_step
  have d3 : Approx x (-4) (deriv (deriv (deriv k))) D3 := d2.deriv_step
  have d4 : Approx x (-5) (deriv (deriv (deriv (deriv k)))) D4 := d3.deriv_step
  have q : Approx x (-6) (ordinaryQuadratic k) (C 2*(P*D4-D1*D3)) := ((h.mul d4).sub (d1.mul d3)).smul 2
  have r : Approx x (-6) (ordinaryQuartic k) (C 3*(P^2*D1^2)+C 5*(P^3*D2)) :=
    (((h.pow 2).mul (d1.pow 2)).smul 3).add (((h.pow 3).mul d2).smul 5)
  have t := ((h.pow 2).smul (2*a)).shift (n:=(-6:ℤ)) (m:=(4:ℤ)) (by norm_num)
  have u := (d1.smul (2*b)).shift (n:=(-6:ℤ)) (m:=(4:ℤ)) (by norm_num)
  exact ((((q.add r).add (h.pow 6)).sub t).sub u)

theorem defect_approx {k:ℂ→ℂ} {x:ℂ} {P:ℂ[X]} (h:Approx x (-1) k P) :
    Approx x (-3) (fun z=>deriv (deriv k) z+(2/9:ℂ)*k z^3) (polyDefect P) :=
  h.deriv_step.deriv_step.add ((h.pow 3).smul (2/9))

theorem coeff_polyStep (n:ℤ) (P:ℂ[X]) (i:ℕ) :
    (polyStep n P).coeff i=((i:ℂ)+n)*P.coeff i := by
  cases i with
  | zero => simp [polyStep]
  | succ i =>
    rw [polyStep,coeff_add,coeff_C_mul,coeff_X_mul,coeff_derivative]
    push_cast;ring

private theorem coeff_prod (P Q:ℂ[X]) (i:ℕ) : (P*Q).coeff i =
    ∑j∈Finset.range (i+1),P.coeff j*Q.coeff (i-j) := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem coeff_product0 (P Q:ℂ[X]) : (P*Q).coeff 0=P.coeff 0*Q.coeff 0 := by
  rw [coeff_prod];norm_num [Finset.sum_range_succ]

theorem coeff_product1 (P Q:ℂ[X]) : (P*Q).coeff 1=P.coeff 0*Q.coeff 1+P.coeff 1*Q.coeff 0 := by
  rw [coeff_prod];norm_num [Finset.sum_range_succ]

theorem coeff_product2 (P Q:ℂ[X]) : (P*Q).coeff 2=P.coeff 0*Q.coeff 2+P.coeff 1*Q.coeff 1+P.coeff 2*Q.coeff 0 := by
  rw [coeff_prod];norm_num [Finset.sum_range_succ]

theorem coeff_product3 (P Q:ℂ[X]) : (P*Q).coeff 3=P.coeff 0*Q.coeff 3+P.coeff 1*Q.coeff 2+P.coeff 2*Q.coeff 1+P.coeff 3*Q.coeff 0 := by
  rw [coeff_prod];norm_num [Finset.sum_range_succ]

theorem coeff_product4 (P Q:ℂ[X]) : (P*Q).coeff 4=P.coeff 0*Q.coeff 4+P.coeff 1*Q.coeff 3+P.coeff 2*Q.coeff 2+P.coeff 3*Q.coeff 1+P.coeff 4*Q.coeff 0 := by
  rw [coeff_prod];norm_num [Finset.sum_range_succ]

theorem coeff_product5 (P Q:ℂ[X]) : (P*Q).coeff 5=P.coeff 0*Q.coeff 5+P.coeff 1*Q.coeff 4+P.coeff 2*Q.coeff 3+P.coeff 3*Q.coeff 2+P.coeff 4*Q.coeff 1+P.coeff 5*Q.coeff 0 := by
  rw [coeff_prod];norm_num [Finset.sum_range_succ]

end ClosedSimilarity.MeromorphicCurvature
#print axioms ClosedSimilarity.MeromorphicCurvature.residual_approx
