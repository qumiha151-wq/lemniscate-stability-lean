import Lemniscate.Algebra
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-! Rotation of a square period lattice forces g3=0 and the sign change of
the Weierstrass function under z -> i*z. These identities are proved by
reindexing the defining lattice sums. -/
noncomputable section
namespace Lemniscate
open Complex

private theorem square_lattice_mul_I_mem (L : PeriodPair) (hs : L.ω₂ = I*L.ω₁)
    (z : ℂ) (hz : z ∈ L.lattice) : I*z ∈ L.lattice := by
  obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hz
  apply PeriodPair.mem_lattice.mpr
  refine ⟨-n,m,?_⟩
  simp only [Int.cast_neg,hs]
  ring_nf
  simp only [Complex.I_sq]
  ring

private def squareLatticeRotation (L : PeriodPair) (hs : L.ω₂ = I*L.ω₁) :
    L.lattice ≃ L.lattice where
  toFun z := ⟨I*(z:ℂ),square_lattice_mul_I_mem L hs z z.property⟩
  invFun z := ⟨-(I*(z:ℂ)),L.lattice.neg_mem (square_lattice_mul_I_mem L hs z z.property)⟩
  left_inv z := by
    apply Subtype.ext
    change -(I*(I*(z:ℂ))) = z
    simp only [← mul_assoc,Complex.I_mul_I,neg_one_mul,neg_neg]
  right_inv z := by
    apply Subtype.ext
    change I*(-(I*(z:ℂ))) = z
    simp only [mul_neg,← mul_assoc,Complex.I_mul_I,neg_one_mul,neg_neg]

theorem square_weierstrass_symmetry (L : PeriodPair) (hs : L.ω₂ = I*L.ω₁) :
    L.g₃ = 0 ∧ (∀ z : ℂ, L.weierstrassP (I*z) = -L.weierstrassP z) ∧
      (∀ l : L.lattice, L.derivWeierstrassP ((l:ℂ)/2) = 0) ∧
      L.weierstrassP (L.ω₂/2) = -L.weierstrassP (L.ω₁/2) ∧
      L.weierstrassP ((L.ω₁+L.ω₂)/2) = 0 := by
  have hG : L.G 6 = 0 := by
    rw [← CharZero.eq_neg_self_iff,PeriodPair.G]
    conv_lhs => rw [← (squareLatticeRotation L hs).tsum_eq (fun l : L.lattice => ((l:ℂ)^6)⁻¹)]
    change (∑' l : L.lattice, ((I*(l:ℂ))^6)⁻¹) =
      -(∑' l : L.lattice, ((l:ℂ)^6)⁻¹)
    rw [← tsum_neg]
    apply tsum_congr
    intro l
    have hI6 : (I:ℂ)^6 = -1 := by
      calc
        I^6 = (I^2)^3 := by ring
        _ = -1 := by rw [Complex.I_sq]; norm_num
    simp only [mul_pow,hI6,neg_one_mul,inv_neg]
  have hrot (z : ℂ) : L.weierstrassP (I*z) = -L.weierstrassP z := by
    rw [PeriodPair.weierstrassP,PeriodPair.weierstrassP]
    conv_lhs => rw [← (squareLatticeRotation L hs).tsum_eq
      (fun l : L.lattice => 1/(I*z-(l:ℂ))^2-1/(l:ℂ)^2)]
    change (∑' l : L.lattice, (1/(I*z-I*(l:ℂ))^2-1/(I*(l:ℂ))^2)) =
      -(∑' l : L.lattice, (1/(z-(l:ℂ))^2-1/(l:ℂ)^2))
    rw [← tsum_neg]
    apply tsum_congr
    intro l
    rw [← mul_sub I z (l:ℂ)]
    simp only [mul_pow,Complex.I_sq,neg_one_mul,div_neg]
    ring
  refine ⟨by simp only [PeriodPair.g₃,hG,mul_zero],hrot,?_,?_,?_⟩
  · intro l
    have h := L.derivWeierstrassP_add_coe (-((l:ℂ)/2)) l
    rw [show -((l:ℂ)/2)+(l:ℂ) = (l:ℂ)/2 by ring,L.derivWeierstrassP_neg] at h
    exact CharZero.eq_neg_self_iff.mp h
  · simpa only [hs,mul_div_assoc] using hrot (L.ω₁/2)
  · let z := (L.ω₁+L.ω₂)/2
    have hIz : I*z = z-L.ω₁ := by
      dsimp only [z]
      rw [hs]
      ring_nf
      simp only [Complex.I_sq]
      ring
    have h := hrot z
    rw [hIz,L.weierstrassP_sub_coe z ⟨L.ω₁,L.ω₁_mem_lattice⟩] at h
    exact CharZero.eq_neg_self_iff.mp h

end Lemniscate
