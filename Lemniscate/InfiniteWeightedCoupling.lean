import Lemniscate.FiniteEnergyCertificate

/-! Extend the finite weighted Cauchy estimate to a genuine convergent
Fourier pairing. No finite truncation is substituted for the series. -/
namespace Lemniscate
open Complex Filter
open scoped ComplexConjugate Topology

theorem infinite_weighted_coupling {ι κ : Type*} [Fintype ι]
    (B : ι → κ → ℂ) (δ : ι → ℝ) (ω : κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (hδ : ∀ i, 0 < δ i) (hω : ∀ j, 0 < ω j)
    (hC : Summable (fun j => ∑ i, ‖B i j‖^2/(δ i*ω j)))
    (hW : Summable (fun j => ω j*‖y j‖^2)) (z : ℂ)
    (hz : HasSum (fun j => ∑ i, conj (x i)*B i j*y j) z) :
    ‖z‖^2 ≤ (∑' j, ∑ i, ‖B i j‖^2/(δ i*ω j))*
      (∑ i, δ i*‖x i‖^2)*(∑' j, ω j*‖y j‖^2) := by
  classical
  have hcn (j : κ) : 0 ≤ ∑ i, ‖B i j‖^2/(δ i*ω j) := by
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (hδ i) (hω j)))
  have hwn (j : κ) : 0 ≤ ω j*‖y j‖^2 :=
    mul_nonneg (hω j).le (sq_nonneg _)
  have hxn : 0 ≤ ∑ i, δ i*‖x i‖^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hδ i).le (sq_nonneg _))
  have hfinite (J : Finset κ) :
      ‖∑ j ∈ J, ∑ i, conj (x i)*B i j*y j‖^2 ≤
        (∑' j, ∑ i, ‖B i j‖^2/(δ i*ω j))*
          (∑ i, δ i*‖x i‖^2)*(∑' j, ω j*‖y j‖^2) := by
    have hc := finite_weighted_coupling Finset.univ J B δ ω x y
      (fun i _ => hδ i) (fun j _ => hω j)
    rw [Finset.sum_comm] at hc
    have hCJ : (∑ i, ∑ j ∈ J, ‖B i j‖^2/(δ i*ω j)) ≤
        ∑' j, ∑ i, ‖B i j‖^2/(δ i*ω j) := by
      rw [Finset.sum_comm]
      exact Summable.sum_le_tsum J (fun j _ => hcn j) hC
    have hWJ := Summable.sum_le_tsum J (fun j _ => hwn j) hW
    exact hc.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hCJ hxn) hWJ
      (Finset.sum_nonneg (fun j _ => hwn j))
      (mul_nonneg (tsum_nonneg hcn) hxn))
  have hlim : Tendsto (fun J : Finset κ => ‖∑ j ∈ J, ∑ i, conj (x i)*B i j*y j‖^2)
      atTop (𝓝 (‖z‖^2)) := (hz : Tendsto _ _ _).norm.pow 2
  exact le_of_tendsto hlim (Eventually.of_forall hfinite)

end Lemniscate
