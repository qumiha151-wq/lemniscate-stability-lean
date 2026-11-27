import SolitonClassification.CentreDirectionBounds

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress.Data
variable {δ : ℝ} (z : Data δ)

/-- The Cartesian coordinates recovered from normal and tangential support. -/
def labX (θ : ℝ → ℝ) (s : ℝ) := z.q s*Real.cos (θ s)-z.p s*Real.sin (θ s)
def labY (θ : ℝ → ℝ) (s : ℝ) := z.q s*Real.sin (θ s)+z.p s*Real.cos (θ s)

theorem lab_rates {θ : ℝ → ℝ} {s : ℝ} (d : HasDerivAt θ (z.K s/δ) s) (hd : 0<δ) :
    HasDerivAt (z.labX θ) (Real.cos (θ s)) s ∧ HasDerivAt (z.labY θ) (Real.sin (θ s)) s := by
  constructor
  · convert! ((z.dq s).mul d.cos).sub ((z.dp s).mul d.sin) using 1
    field_simp [hd.ne']; ring
  · convert! ((z.dq s).mul d.sin).add ((z.dp s).mul d.cos) using 1
    field_simp [hd.ne']; ring

theorem lab_lipschitz {θ : ℝ → ℝ} {s t : ℝ} (st : s≤t) (hd : 0<δ)
    (d : ∀x∈Icc s t, HasDerivAt θ (z.K x/δ) x) :
    |z.labX θ t-z.labX θ s|≤t-s ∧ |z.labY θ t-z.labY θ s|≤t-s := by
  have h (f g : ℝ → ℝ) (df : ∀x∈Icc s t, HasDerivAt f (g x) x)
      (bg : ∀x, |g x|≤1) : |f t-f s|≤t-s := by
    have h := (convex_Icc s t).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (df x hx).differentiableAt)
      (fun x hx => by rw [(df x hx).deriv,Real.norm_eq_abs]; exact bg x)
      (left_mem_Icc.mpr st) (right_mem_Icc.mpr st)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr st),one_mul] using h
  exact ⟨h _ _ (fun x hx => (z.lab_rates (d x hx) hd).1) (fun x => Real.abs_cos_le_one _),
    h _ _ (fun x hx => (z.lab_rates (d x hx) hd).2) (fun x => Real.abs_sin_le_one _)⟩

theorem lab_stress_frame {s : ℝ} (θ : ℝ → ℝ) (ap : 0<z.amplitude s) :
    let X := Direction.horizontal (z.shape s) (z.slope s) (θ s)
    let Y := Direction.vertical (z.shape s) (z.slope s) (θ s)
    z.labX θ s=z.along s*X-z.across s*Y ∧ z.labY θ s=z.along s*Y+z.across s*X := by
  have rs : z.root s^2=z.amplitude s := Real.sq_sqrt ap.le
  have energy := z.amplitude_sq s
  have shapeSq : (z.shape s)^2=z.K s^2/z.amplitude s := by rw [shape,div_pow,rs]
  dsimp only
  unfold Direction.horizontal Direction.vertical
  rw [shapeSq]
  unfold labX labY along across slope radial transverse
  constructor <;> field_simp [ap.ne'] <;> ring_nf at energy ⊢ <;> grind

end ClosedSimilarity.OuterStress.Data

