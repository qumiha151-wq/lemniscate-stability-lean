import SolitonClassification.MeromorphicPolePolynomial

noncomputable section
open Complex Polynomial
open scoped Polynomial
set_option maxHeartbeats 3600000
set_option linter.unusedSimpArgs false
namespace ClosedSimilarity.MeromorphicCurvature

theorem residual_coeff0 (a b:ℂ) (P:ℂ[X]) :
    (polyR a b P).coeff 0=36*(P.coeff 0)^2+13*(P.coeff 0)^4+(P.coeff 0)^6 := by
  simp only [polyR,coeff_add,coeff_sub,coeff_C_mul,coeff_polyStep,pow_succ,pow_zero,one_mul,
    coeff_product0,coeff_product1,coeff_product2,coeff_product3,coeff_product4,coeff_product5,
    coeff_X,coeff_one,coeff_C]
  norm_num;ring

theorem residual_coeff1 (a b:ℂ) (P:ℂ[X]) :
    (polyR a b P).coeff 1=48*(P.coeff 0)*(P.coeff 1)+36*(P.coeff 0)^3*(P.coeff 1)+6*(P.coeff 0)^5*(P.coeff 1) := by
  simp only [polyR,coeff_add,coeff_sub,coeff_C_mul,coeff_polyStep,pow_succ,pow_zero,one_mul,
    coeff_product0,coeff_product1,coeff_product2,coeff_product3,coeff_product4,coeff_product5,
    coeff_X,coeff_one,coeff_C]
  norm_num;ring

theorem residual_coeff2 (a b:ℂ) (P:ℂ[X]) :
    (polyR a b P).coeff 2=60*(P.coeff 0)*(P.coeff 2)+33*(P.coeff 0)^2*(P.coeff 1)^2+30*(P.coeff 0)^3*(P.coeff 2)+6*(P.coeff 0)^5*(P.coeff 2)+15*(P.coeff 0)^4*(P.coeff 1)^2 := by
  simp only [polyR,coeff_add,coeff_sub,coeff_C_mul,coeff_polyStep,pow_succ,pow_zero,one_mul,
    coeff_product0,coeff_product1,coeff_product2,coeff_product3,coeff_product4,coeff_product5,
    coeff_X,coeff_one,coeff_C]
  norm_num;ring

theorem residual_coeff3 (a b:ℂ) (P:ℂ[X]) :
    (polyR a b P).coeff 3=72*(P.coeff 0)*(P.coeff 3)+34*(P.coeff 0)^3*(P.coeff 3)+54*(P.coeff 0)^2*(P.coeff 1)*(P.coeff 2)+10*(P.coeff 0)*(P.coeff 1)^3+6*(P.coeff 0)^5*(P.coeff 3)+30*(P.coeff 0)^4*(P.coeff 1)*(P.coeff 2)+20*(P.coeff 0)^3*(P.coeff 1)^3 := by
  simp only [polyR,coeff_add,coeff_sub,coeff_C_mul,coeff_polyStep,pow_succ,pow_zero,one_mul,
    coeff_product0,coeff_product1,coeff_product2,coeff_product3,coeff_product4,coeff_product5,
    coeff_X,coeff_one,coeff_C]
  norm_num;ring

theorem residual_coeff4 (a b:ℂ) (P:ℂ[X]) :
    (polyR a b P).coeff 4=96*(P.coeff 0)*(P.coeff 4)+48*(P.coeff 0)^3*(P.coeff 4)+72*(P.coeff 0)^2*(P.coeff 1)*(P.coeff 3)+24*(P.coeff 0)^2*(P.coeff 2)^2+24*(P.coeff 0)*(P.coeff 1)^2*(P.coeff 2)+6*(P.coeff 0)^5*(P.coeff 4)+30*(P.coeff 0)^4*(P.coeff 1)*(P.coeff 3)+15*(P.coeff 0)^4*(P.coeff 2)^2+60*(P.coeff 0)^3*(P.coeff 1)^2*(P.coeff 2)+15*(P.coeff 0)^2*(P.coeff 1)^4-2*a*(P.coeff 0)^2+2*b*(P.coeff 0) := by
  simp only [polyR,coeff_add,coeff_sub,coeff_C_mul,coeff_polyStep,pow_succ,pow_zero,one_mul,
    coeff_product0,coeff_product1,coeff_product2,coeff_product3,coeff_product4,coeff_product5,
    coeff_X,coeff_one,coeff_C]
  norm_num;ring

theorem residual_coeff5 (a b:ℂ) (P:ℂ[X]) :
    (polyR a b P).coeff 5=192*(P.coeff 0)*(P.coeff 5)+72*(P.coeff 0)^3*(P.coeff 5)+120*(P.coeff 0)^2*(P.coeff 1)*(P.coeff 4)+72*(P.coeff 0)^2*(P.coeff 2)*(P.coeff 3)+48*(P.coeff 0)*(P.coeff 1)^2*(P.coeff 3)+24*(P.coeff 0)*(P.coeff 1)*(P.coeff 2)^2+6*(P.coeff 0)^5*(P.coeff 5)+30*(P.coeff 0)^4*(P.coeff 1)*(P.coeff 4)+30*(P.coeff 0)^4*(P.coeff 2)*(P.coeff 3)+60*(P.coeff 0)^3*(P.coeff 1)^2*(P.coeff 3)+60*(P.coeff 0)^3*(P.coeff 1)*(P.coeff 2)^2+60*(P.coeff 0)^2*(P.coeff 1)^3*(P.coeff 2)+6*(P.coeff 0)*(P.coeff 1)^5-4*a*(P.coeff 0)*(P.coeff 1) := by
  simp only [polyR,coeff_add,coeff_sub,coeff_C_mul,coeff_polyStep,pow_succ,pow_zero,one_mul,
    coeff_product0,coeff_product1,coeff_product2,coeff_product3,coeff_product4,coeff_product5,
    coeff_X,coeff_one,coeff_C]
  norm_num;ring

end ClosedSimilarity.MeromorphicCurvature
#print axioms ClosedSimilarity.MeromorphicCurvature.residual_coeff5
