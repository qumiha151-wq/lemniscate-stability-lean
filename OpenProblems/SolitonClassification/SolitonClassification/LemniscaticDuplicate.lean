import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace ClosedSimilarity.LemniscaticExtension
set_option backward.isDefEq.respectTransparency false

def U {K : Type*} [Field K] (x y : K) := 2*x*y/(1+x^4)
def V {K : Type*} [Field K] (x : K) := (1-6*x^4+x^8)/(1+x^4)^2
def double (p : ℂ × ℂ) : ℂ × ℂ := (U p.1 p.2,V p.1)

theorem derivative_U {K : Type*} [NontriviallyNormedField K] [CharZero K]
    {u v : K→K} {z : K} (du : HasDerivAt u (v z) z) (dv : HasDerivAt v (-2*u z^3) z)
    (e : v z^2+u z^4=1) (nz : 1+u z^4≠0) :
    HasDerivAt (fun t=>U (u t) (v t)) (2*V (u z)) z := by
  convert! (((du.const_mul 2).mul dv).div ((du.pow 4).const_add 1) nz) using 1
  dsimp only [U,V,Pi.pow_apply,Pi.mul_apply]
  field_simp [nz]
  linear_combination (-1+3*u z^4)*e

theorem derivative_V {K : Type*} [NontriviallyNormedField K] [CharZero K]
    {u v : K→K} {z : K} (du : HasDerivAt u (v z) z)
    (e : v z^2+u z^4=1) (nz : 1+u z^4≠0) :
    HasDerivAt (fun t=>V (u t)) (-4*U (u z) (v z)^3) z := by
  have dn : HasDerivAt (fun t=>1-6*u t^4+u t^8) _ z := HasDerivAt.add (HasDerivAt.sub (hasDerivAt_const z (1:K)) ((du.pow 4).const_mul 6)) (du.pow 8)
  have db : HasDerivAt (fun t=>1+u t^4) _ z := HasDerivAt.const_add 1 (du.pow 4)
  have dd := db.pow 2
  convert! dn.div dd (pow_ne_zero 2 nz) using 1
  dsimp only [U,V,Pi.pow_apply,Pi.add_apply,Pi.sub_apply]
  field_simp [nz]
  linear_combination -32*u z^3*v z*(1+u z^4)*e

def quarterTurn (p : ℂ × ℂ) : ℂ × ℂ := (Complex.I*p.1,p.2)

theorem double_quarterTurn (p : ℂ × ℂ) : double (quarterTurn p)=quarterTurn (double p) := by
  have ii : Complex.I^4=1 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,Complex.I_sq];norm_num
  have iii : Complex.I^8=1 := by rw [show (8:ℕ)=4*2 by decide,pow_mul,ii,one_pow]
  apply Prod.ext <;> simp only [quarterTurn,double,U,V,mul_pow,ii,iii,one_mul]
  ring

end ClosedSimilarity.LemniscaticExtension
