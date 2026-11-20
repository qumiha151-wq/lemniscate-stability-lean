import SolitonClassification.NoClosedTranslators

/-! The force difference at equal oriented angles measures the chord
projected onto a fixed linear combination of their tangent and normal. -/
noncomputable section
namespace ClosedSimilarity
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem PeriodicSupportProfile.equal_angle_force_difference {a b L : ℝ}
    (z : PeriodicSupportProfile a b L) {θ : ℝ → ℝ}
    (ht : ∀ s, HasDerivAt θ (z.k s) s) {l r h : ℝ} (hl : θ l=h) (hr : θ r=h) :
    (∫ s in l..r, a*Real.sin (θ s-h)+b*Real.cos (θ s-h)) = z.force l-z.force r := by
  let d := fun s => θ s-h
  have hd (s : ℝ) : HasDerivAt d (z.k s) s := (ht s).sub_const h
  have cd : Continuous d := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  let Q := fun s => a*profileY z.p z.q d s+b*profileX z.p z.q d s
  have dq (s : ℝ) : HasDerivAt Q (a*Real.sin (d s)+b*Real.cos (d s)) s :=
    ((profileY_hasDerivAt z.k z.p z.q d s (z.dp s) (z.dq s) (hd s)).const_mul a).add
      ((profileX_hasDerivAt z.k z.p z.q d s (z.dp s) (z.dq s) (hd s)).const_mul b)
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s∈uIcc l r) => dq s)
      ((((Real.continuous_sin.comp cd).const_mul a).add
        ((Real.continuous_cos.comp cd).const_mul b)).intervalIntegrable _ _)
  change (∫ s in l..r, a*Real.sin (d s)+b*Real.cos (d s))=_
  rw [eq]
  simp only [Q,profileX,profileY,d,hl,hr,sub_self,Real.cos_zero,Real.sin_zero,
    mul_zero,mul_one,zero_add,sub_zero,PeriodicSupportProfile.force]
  ring

theorem positive_force_projection_on_fold {a b l r m h : ℝ} {θ : ℝ → ℝ}
    (ha : 0<a) (hb : 0≤b) (ct : Continuous θ) (hlr : l<r) (hm : m∈Icc l r)
    (hp : 0<θ m-h) (band : ∀ s∈Icc l r, 0≤θ s-h ∧ θ s-h<Real.pi/2) :
    0 < ∫ s in l..r, a*Real.sin (θ s-h)+b*Real.cos (θ s-h) := by
  have hh := Real.pi_pos
  have cn (s : ℝ) (hs : s∈Icc l r) : 0<Real.cos (θ s-h) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(band s hs).1],(band s hs).2⟩
  have sn (s : ℝ) (hs : s∈Icc l r) : 0≤Real.sin (θ s-h) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (band s hs).1 (by linarith [(band s hs).2])
  have sp := Real.sin_pos_of_pos_of_lt_pi hp (by linarith [(band m hm).2])
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f:=fun _ => (0:ℝ)) (g:=fun s => a*Real.sin (θ s-h)+b*Real.cos (θ s-h)) hlr
    continuous_const.continuousOn
    ((((Real.continuous_sin.comp (ct.sub continuous_const)).const_mul a).add
      ((Real.continuous_cos.comp (ct.sub continuous_const)).const_mul b)).continuousOn)
    (fun s hs => add_nonneg (mul_nonneg ha.le (sn s ⟨hs.1.le,hs.2⟩))
      (mul_nonneg hb (cn s ⟨hs.1.le,hs.2⟩).le))
    ⟨m,hm,add_pos_of_pos_of_nonneg (mul_pos ha sp) (mul_nonneg hb (cn m hm).le)⟩
  simpa using hi

/-- The actual oriented tangent agrees at labels with the same integrated
curvature. This supplies the angle lift directly from the curve. -/
theorem ClosedUnitFrenetCurve.tangent_eq_of_angle_eq (C : ClosedUnitFrenetCurve)
    {θ : ℝ → ℝ} (hd : ∀ s, HasDerivAt θ (C.k s) s) {l r : ℝ} (h : θ l=θ r) :
    C.tx l=C.tx r ∧ C.ty l=C.ty r := by
  let A := fun s => C.tx s*Real.cos (θ s)+C.ty s*Real.sin (θ s)
  let B := fun s => C.ty s*Real.cos (θ s)-C.tx s*Real.sin (θ s)
  have dA (s : ℝ) : HasDerivAt A 0 s := by
    convert! ((C.dtx s).mul (hd s).cos).add ((C.dty s).mul (hd s).sin) using 1
    ring
  have dB (s : ℝ) : HasDerivAt B 0 s := by
    convert! ((C.dty s).mul (hd s).cos).sub ((C.dtx s).mul (hd s).sin) using 1
    ring
  have ha := is_const_of_deriv_eq_zero (fun s => (dA s).differentiableAt)
    (fun s => (dA s).deriv) l r
  have hb := is_const_of_deriv_eq_zero (fun s => (dB s).differentiableAt)
    (fun s => (dB s).deriv) l r
  dsimp only [A] at ha
  dsimp only [B] at hb
  rw [h] at ha hb
  have hn := Real.sin_sq_add_cos_sq (θ r)
  constructor
  · linear_combination Real.cos (θ r)*ha-Real.sin (θ r)*hb-(C.tx l-C.tx r)*hn
  · linear_combination Real.sin (θ r)*ha+Real.cos (θ r)*hb-(C.ty l-C.ty r)*hn

end ClosedSimilarity
