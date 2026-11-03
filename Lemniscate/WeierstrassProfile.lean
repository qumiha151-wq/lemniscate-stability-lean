import Lemniscate.WeierstrassEquation
import Mathlib.Analysis.Complex.RealDeriv

/-! A normalized shifted Weierstrass solution of f''=1-3*f^2. The scalar
normalization is explicit; its existence is proved separately in
SquareWeierstrassPositive.lean. -/
noncomputable section
namespace Lemniscate
open Complex

def unitSquarePeriods : PeriodPair where
  ω₁ := 1
  ω₂ := I
  indep := by
    rw [← Complex.coe_basisOneI]
    exact Complex.basisOneI.linearIndependent

private theorem unit_square_midline_regular (a x : ℝ) :
    (a:ℂ)*(x:ℂ)+I/2 ∉ unitSquarePeriods.lattice := by
  intro h
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp h
  have him := congrArg Complex.im he
  norm_num [unitSquarePeriods] at him
  have hn : (2*n:ℤ) = 1 := by
    exact_mod_cast (show (2:ℝ)*(n:ℝ) = 1 by linarith only [him])
  omega

def normalizedWeierstrass (a x : ℝ) : ℂ :=
  -2*(a:ℂ)^2*unitSquarePeriods.weierstrassP ((a:ℂ)*(x:ℂ)+I/2)

def normalizedWeierstrassDerivative (a x : ℝ) : ℂ :=
  -2*(a:ℂ)^3*unitSquarePeriods.derivWeierstrassP ((a:ℂ)*(x:ℂ)+I/2)

theorem normalized_weierstrass_data (a : ℝ)
    (hnorm : 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1) :
    normalizedWeierstrass a 0 = 1 ∧ normalizedWeierstrassDerivative a 0 = 0 ∧
    normalizedWeierstrass a (1/(2*a)) = 0 ∧
    ∀ x : ℝ,
      HasDerivAt (normalizedWeierstrass a) (normalizedWeierstrassDerivative a x) x ∧
      HasDerivAt (normalizedWeierstrassDerivative a)
        (1-3*(normalizedWeierstrass a x)^2) x := by
  let L := unitSquarePeriods
  let E := L.weierstrassP (1/2)
  have hs : L.ω₂ = I*L.ω₁ := by simp only [L,unitSquarePeriods,mul_one]
  obtain ⟨hg3,hrot,hcrit,hanti,hdiag⟩ := square_weierstrass_symmetry L hs
  change L.weierstrassP (I/2) = -E at hanti
  change L.weierstrassP ((1+I)/2) = 0 at hdiag
  have hDI : L.derivWeierstrassP (I/2) = 0 := hcrit ⟨L.ω₂,L.ω₂_mem_lattice⟩
  have hE : E ≠ 0 := by
    intro h
    change 2*(a:ℂ)^2*E = 1 at hnorm
    rw [h,mul_zero] at hnorm
    norm_num at hnorm
  have haC : (a:ℂ) ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide),mul_zero,zero_mul] at hnorm
    norm_num at hnorm
  have hg2 : L.g₂ = 4*E^2 := by
    have h := L.derivWeierstrassP_sq (L.ω₁/2) L.ω₁_div_two_notMem_lattice
    rw [hcrit ⟨L.ω₁,L.ω₁_mem_lattice⟩,hg3] at h
    change (0:ℂ)^2 = 4*E^3-L.g₂*E-0 at h
    apply mul_right_cancel₀ hE
    linear_combination h
  have hscale : (a:ℂ)^4*L.g₂ = 1 := by
    calc
      (a:ℂ)^4*L.g₂ = (2*(a:ℂ)^2*E)^2 := by rw [hg2]; ring
      _ = 1 := by rw [hnorm]; norm_num
  have hline (z : ℂ) : HasDerivAt (fun w : ℂ => (a:ℂ)*w+I/2) (a:ℂ) z := by
    convert! ((hasDerivAt_id z).const_mul (a:ℂ)).add_const (I/2) using 1
    simp only [mul_one]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp only [normalizedWeierstrass]
    rw [Complex.ofReal_zero,mul_zero,zero_add]
    rw [hanti]
    linear_combination hnorm
  · dsimp only [normalizedWeierstrassDerivative]
    rw [Complex.ofReal_zero,mul_zero,zero_add,hDI,mul_zero]
  · have hp : (a:ℂ)*((1/(2*a):ℝ):ℂ)+I/2 = (1+I)/2 := by
      push_cast
      field_simp [haC]
    change -2*(a:ℂ)^2*L.weierstrassP _ = 0
    rw [hp,hdiag,mul_zero]
  · intro x
    have hP := (L.analyticOnNhd_weierstrassP _ (unit_square_midline_regular a x)).differentiableAt.hasDerivAt
    rw [L.deriv_weierstrassP] at hP
    have hD := weierstrass_second_order L _ (unit_square_midline_regular a x)
    constructor
    · convert! (((hP.comp (x:ℂ) (hline (x:ℂ))).const_mul (-2*(a:ℂ)^2)).comp_ofReal) using 1
      dsimp only [normalizedWeierstrassDerivative,L]
      ring
    · convert! (((hD.comp (x:ℂ) (hline (x:ℂ))).const_mul (-2*(a:ℂ)^3)).comp_ofReal) using 1
      dsimp only [normalizedWeierstrass]
      linear_combination -hscale

end Lemniscate
