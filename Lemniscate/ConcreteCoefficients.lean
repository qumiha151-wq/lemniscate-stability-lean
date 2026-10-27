import Lemniscate.CosineMatrix
import Lemniscate.ThetaBounds

/-! Instantiations at Q = exp(-pi), r = theta(Q)^(-4). These conclusions
have no unproved numerical parameter hypotheses. The identification of these
series with the Jacobi curvature and geometric operator is not claimed here. -/
namespace Lemniscate.CoarseArithmetic

noncomputable def nome : ℝ := Real.exp (-Real.pi)
noncomputable def thetaParameter : ℝ := thetaR nome

theorem theta_nome_fourier_enclosure (j : ℕ) :
    Contains (hInterval j) (fourierCoefficient thetaParameter nome j) :=
  fourier_enclosure _ _ j (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])) (refined_nome_bounds.mono (by norm_num [qlo, nomeLower]) (by norm_num [qhi, nomeUpper]))

theorem theta_nome_cosine_matrix_enclosure (j k : ℕ) :
    Contains (cosineEntry j k) (cosineMatrixEntry thetaParameter nome j k) :=
  cosine_matrix_enclosure _ _ j k (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])) (refined_nome_bounds.mono (by norm_num [qlo, nomeLower]) (by norm_num [qhi, nomeUpper]))

theorem theta_nome_fourier_tail_bound (L : ℕ) (hL : 0 < L) :
    (∑' n : ℕ, evenCoefficient thetaParameter nome (n+L)) ≤
      (8*(rhi:ℝ)/(1-(qhi:ℝ)^2))*(tail1 qhi L : ℝ) :=
  fourier_tail_bound _ _ L (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])) (refined_nome_bounds.mono (by norm_num [qlo, nomeLower]) (by norm_num [qhi, nomeUpper])) hL

end Lemniscate.CoarseArithmetic
