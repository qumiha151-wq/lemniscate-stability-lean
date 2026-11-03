import Lemniscate.CosineMatrix
import Lemniscate.WeierstrassFrequencyBounds

/-! Instantiations at Q = exp(-pi) and the squared fundamental frequency
derived from the actual lemniscate. Its numerical bounds are proved from the
lattice series. The Fourier identification remains a separate obligation. -/
namespace Lemniscate.CoarseArithmetic

noncomputable def nome : ℝ := Real.exp (-Real.pi)

theorem frequency_nome_fourier_enclosure (j : ℕ) :
    Contains (hInterval j) (fourierCoefficient lemniscateFrequencySquared nome j) :=
  fourier_enclosure _ _ j (lemniscate_frequency_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, frequencyLower]) (by norm_num [rhi, frequencyUpper])) (refined_nome_bounds.mono (by norm_num [qlo, nomeLower]) (by norm_num [qhi, nomeUpper]))

theorem frequency_nome_cosine_matrix_enclosure (j k : ℕ) :
    Contains (cosineEntry j k) (cosineMatrixEntry lemniscateFrequencySquared nome j k) :=
  cosine_matrix_enclosure _ _ j k (lemniscate_frequency_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, frequencyLower]) (by norm_num [rhi, frequencyUpper])) (refined_nome_bounds.mono (by norm_num [qlo, nomeLower]) (by norm_num [qhi, nomeUpper]))

theorem frequency_nome_fourier_tail_bound (L : ℕ) (hL : 0 < L) :
    (∑' n : ℕ, evenCoefficient lemniscateFrequencySquared nome (n+L)) ≤
      (8*(rhi:ℝ)/(1-(qhi:ℝ)^2))*(tail1 qhi L : ℝ) :=
  fourier_tail_bound _ _ L (lemniscate_frequency_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, frequencyLower]) (by norm_num [rhi, frequencyUpper])) (refined_nome_bounds.mono (by norm_num [qlo, nomeLower]) (by norm_num [qhi, nomeUpper])) hL

end Lemniscate.CoarseArithmetic
