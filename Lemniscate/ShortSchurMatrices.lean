import Lemniscate.ShortSchurData

/-! The actual seven-mode finite-rank matrices used in the shorter proof.
The parameters are the period scale and the Fourier coefficients of q².
No row inequality or old even-frequency certificate is an input here. -/
namespace Lemniscate
open Matrix Finset

noncomputable def shortOuter (u v : Fin 15 → ℝ) : Matrix (Fin 15) (Fin 15) ℝ :=
  fun i j => u i * v j

noncomputable def shortHouseholder (h : ℕ → ℝ) : Matrix (Fin 15) (Fin 15) ℝ :=
  let e := shortRotationHead h
  let u := e + shortAnchorHead
  1 - (1 / (1 + ∑ i, e i * shortAnchorHead i)) • shortOuter u u

noncomputable def shortNeutral (h : ℕ → ℝ) : Matrix (Fin 15) (Fin 15) ℝ :=
  1 + shortOuter (shortRotationHead h) (shortAdjointHead h - shortRotationHead h)

noncomputable def shortNeutralInv (h : ℕ → ℝ) : Matrix (Fin 15) (Fin 15) ℝ :=
  1 - shortOuter (shortRotationHead h) (shortAdjointHead h - shortRotationHead h)

noncomputable def shortCenterProjection : Matrix (Fin 15) (Fin 15) ℝ :=
  shortOuter shortAnchorHead shortAnchorHead

noncomputable def shortStableProjection : Matrix (Fin 15) (Fin 15) ℝ :=
  1 - shortCenterProjection

noncomputable def shortBlochEntry (r : ℝ) (h : ℕ → ℝ) (k : Fin 5) (n m : ℤ) : ℝ :=
  let H := h ((n-m).natAbs / 2)
  ![(15/2:ℝ)*r*n*(7*m-n)*H - (if n=m then 4*r^2*(n:ℝ)^4+42 else 0),
    r*((75/2:ℝ)*n+(105/2:ℝ)*m)*H - (if n=m then 16*r^2*(m:ℝ)^3 else 0),
    45*r*H - (if n=m then 24*r^2*(m:ℝ)^2 else 0),
    if n=m then -16*r^2*(m:ℝ) else 0,
    if n=m then -4*r^2 else 0] k

noncomputable def shortBlochHead (r : ℝ) (h : ℕ → ℝ) (k : Fin 5) :
    Matrix (Fin 15) (Fin 15) ℝ :=
  fun i j => shortBlochEntry r h k (shortHeadFrequency i) (shortHeadFrequency j)

noncomputable def shortSymmetric (M : Matrix (Fin 15) (Fin 15) ℝ) :=
  (1/2:ℝ) • (M + Mᵀ)

noncomputable def shortTransformedCoefficient (r : ℝ) (h : ℕ → ℝ) (k : Fin 5) :
    Matrix (Fin 15) (Fin 15) ℝ :=
  let U := shortHouseholder h
  if k=0 then U * shortSymmetric (shortBlochHead r h 0) * U
  else if k=4 then (-4*r^2) • 1
  else shortSymmetric (U * shortNeutral h * shortBlochHead r h k * shortNeutralInv h * U)

noncomputable def shortGHeadCoefficient (r : ℝ) (h : ℕ → ℝ) (k : Fin 5) :
    Matrix (Fin 15) (Fin 15) ℝ :=
  let P₀ := shortCenterProjection
  let P := shortStableProjection
  let H := shortTransformedCoefficient r h
  ![P*H 0*P + P₀*H 1*P + P*H 1*P₀ + P₀*H 2*P₀ + (1/2:ℝ) • 1,
    P*H 1*P + P₀*H 2*P + P*H 2*P₀,
    P*H 2*P + P₀*H 3*P + P*H 3*P₀ + (-4*r^2) • P₀,
    P*H 3*P,
    (-4*r^2) • P] k

def shortBernsteinWeight (j k : Fin 5) : ℚ :=
  if k.val ≤ j.val then
    (Nat.choose j.val k.val : ℚ) / (2^k.val * Nat.choose 4 k.val)
  else 0

noncomputable def shortBernsteinHead (r : ℝ) (h : ℕ → ℝ) (j : Fin 5) :
    Matrix (Fin 15) (Fin 15) ℝ :=
  ∑ k : Fin 5, (shortBernsteinWeight j k : ℝ) • shortGHeadCoefficient r h k

noncomputable def shortLowBasis (i : Fin 15) (k : Fin 7) : ℝ :=
  let n := shortHeadFrequency i
  let c := fun m : ℤ => if n=m ∨ n= -m then 1 / Real.sqrt 2 else 0
  let a := fun m : ℤ => if n=m then 1 / Real.sqrt 2
    else if n= -m then -1 / Real.sqrt 2 else 0
  ![if n=0 then 1 else 0, c 2, a 2, c 4, a 4, c 6, a 6] k

noncomputable def shortLowShearPerturbation : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => if i=0 ∧ j=2 then -(1/7:ℝ) else 0

noncomputable def shortLowShear : Matrix (Fin 7) (Fin 7) ℝ :=
  (1 : Matrix (Fin 7) (Fin 7) ℝ) + shortLowShearPerturbation

noncomputable def shortLowRotation : Matrix (Fin 7) (Fin 7) ℝ := fun i j =>
  if i=1 ∧ j=1 ∨ i=1 ∧ j=3 ∨ i=3 ∧ j=1 then 1 / Real.sqrt 2
  else if i=3 ∧ j=3 then -1 / Real.sqrt 2
  else if i=j ∧ i≠1 ∧ i≠3 then 1 else 0

noncomputable def shortLowWeightedBasis : Matrix (Fin 15) (Fin 7) ℝ :=
  fun i k => shortLowBasis i k / max 1 ((shortHeadFrequency i : ℝ)^2)

noncomputable def shortLowEmbedding : Matrix (Fin 15) (Fin 7) ℝ :=
  shortLowWeightedBasis * (shortLowShear * shortLowRotation)

noncomputable def shortLowBernstein (r : ℝ) (h : ℕ → ℝ) (j : Fin 5) :
    Matrix (Fin 7) (Fin 7) ℝ :=
  shortLowEmbeddingᵀ * shortBernsteinHead r h j * shortLowEmbedding

theorem short_symmetric_transpose (M : Matrix (Fin 15) (Fin 15) ℝ) :
    (shortSymmetric M)ᵀ = shortSymmetric M := by
  simp only [shortSymmetric, transpose_smul, transpose_add, transpose_transpose]
  congr 1
  exact add_comm _ _

end Lemniscate
