import Lemniscate.ShortSobolevNorm
import Lemniscate.PeriodicSobolevFourierProjection
import Lemniscate.PeriodicBlochGreen
import Lemniscate.PeriodicHouseholderAnchor

/-! Fourier truncation and the neutral-coordinate projection in the actual
angular-coordinate form norms.  Both orthogonality and contraction are proved
on the weak H4 domain. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem l2_inner_zero_of_fourier_disjoint (f g : CircleL2 T)
    (h : ∀ n : ℤ, fourierCoeff f n = 0 ∨ fourierCoeff g n = 0) :
    inner ℂ f g = 0 := by
  rw [← (fourierBasis (T := T)).repr.inner_map_map f g, lp.inner_eq_tsum]
  calc
    _ = ∑' n : ℤ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      simp only [RCLike.inner_apply', fourierBasis_repr]
      rcases h n with hf | hg
      · simp [hf]
      · simp [hg]
    _ = 0 := tsum_zero

private theorem short_jets_add (f g : circleH4Domain T) :
    shortVJet T (f + g) = shortVJet T f + shortVJet T g ∧
      shortH1Jet T (f + g) = shortH1Jet T f + shortH1Jet T g := by
  have hc := circle_fourierCoeff_add T (f : CircleL2 T) (g : CircleL2 T) 0
  constructor
  · unfold shortVJet
    rw [circle_h4_jet_add]
    change WithLp.toLp 2 (fourierCoeff ((f : CircleL2 T) + (g : CircleL2 T)) 0,
      (shortAngularFrequency T)⁻¹ ^ 2 •
        ((circleH4Jet T f).second + (circleH4Jet T g).second)) = _
    rw [hc, smul_add]
    rfl
  · unfold shortH1Jet
    rw [circle_h4_jet_add]
    change WithLp.toLp 2 ((f : CircleL2 T) + (g : CircleL2 T),
      (shortAngularFrequency T)⁻¹ •
        ((circleH4Jet T f).first + (circleH4Jet T g).first)) = _
    rw [smul_add]
    rfl

theorem short_jet_inner_zero_of_fourier_disjoint (f g : circleH4Domain T)
    (h : ∀ n : ℤ, fourierCoeff (f : CircleL2 T) n = 0 ∨
      fourierCoeff (g : CircleL2 T) n = 0) :
    inner ℂ (shortVJet T f) (shortVJet T g) = 0 ∧
      inner ℂ (shortH1Jet T f) (shortH1Jet T g) = 0 := by
  have hfirst : inner ℂ (circleH4Jet T f).first (circleH4Jet T g).first = 0 := by
    apply l2_inner_zero_of_fourier_disjoint T
    intro n
    rw [fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hfirst,
      fourier_of_weak_circle_deriv T _ _ (circleH4Jet T g).hfirst]
    rcases h n with hf | hg
    · exact Or.inl (by rw [hf, mul_zero])
    · exact Or.inr (by rw [hg, mul_zero])
  have hsecond : inner ℂ (circleH4Jet T f).second (circleH4Jet T g).second = 0 := by
    apply l2_inner_zero_of_fourier_disjoint T
    intro n
    rw [fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hsecond,
      fourier_of_weak_circle_deriv T _ _ (circleH4Jet T g).hsecond,
      fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hfirst,
      fourier_of_weak_circle_deriv T _ _ (circleH4Jet T g).hfirst]
    rcases h n with hf | hg
    · exact Or.inl (by rw [hf, mul_zero, mul_zero])
    · exact Or.inr (by rw [hg, mul_zero, mul_zero])
  have hmean : inner ℂ (fourierCoeff (f : CircleL2 T) 0)
      (fourierCoeff (g : CircleL2 T) 0) = 0 := by
    rcases h 0 with hf | hg
    · simp [hf]
    · simp [hg]
  have hbase := l2_inner_zero_of_fourier_disjoint T _ _ h
  constructor
  · change inner ℂ (fourierCoeff (f : CircleL2 T) 0) (fourierCoeff (g : CircleL2 T) 0) +
      inner ℂ (((shortAngularFrequency T)⁻¹ ^ 2 : ℝ) • (circleH4Jet T f).second)
        (((shortAngularFrequency T)⁻¹ ^ 2 : ℝ) • (circleH4Jet T g).second) = 0
    rw [hmean, zero_add]
    simp only [inner_smul_left_eq_star_smul, inner_smul_right_eq_smul, hsecond, smul_zero]
  · change inner ℂ (f : CircleL2 T) (g : CircleL2 T) +
      inner ℂ ((shortAngularFrequency T)⁻¹ • (circleH4Jet T f).first)
        ((shortAngularFrequency T)⁻¹ • (circleH4Jet T g).first) = 0
    rw [hbase, zero_add]
    simp only [inner_smul_left_eq_star_smul, inner_smul_right_eq_smul, hfirst, smul_zero]

private theorem short_norm_decomposition (f p : circleH4Domain T)
    (hv : inner ℂ (shortVJet T p) (shortVJet T (f - p)) = 0)
    (hh : inner ℂ (shortH1Jet T p) (shortH1Jet T (f - p)) = 0) :
    (shortVNorm T f ^ 2 = shortVNorm T p ^ 2 + shortVNorm T (f - p) ^ 2) ∧
    (shortH1Norm T f ^ 2 = shortH1Norm T p ^ 2 + shortH1Norm T (f - p) ^ 2) ∧
    shortVNorm T p ≤ shortVNorm T f ∧ shortVNorm T (f - p) ≤ shortVNorm T f ∧
    shortH1Norm T p ≤ shortH1Norm T f ∧ shortH1Norm T (f - p) ≤ shortH1Norm T f := by
  have hd : p + (f - p) = f := by abel
  have hvs : shortVJet T f = shortVJet T p + shortVJet T (f - p) := by
    rw [← (short_jets_add T p (f - p)).1, hd]
  have hhs : shortH1Jet T f = shortH1Jet T p + shortH1Jet T (f - p) := by
    rw [← (short_jets_add T p (f - p)).2, hd]
  have hV : shortVNorm T f ^ 2 = shortVNorm T p ^ 2 + shortVNorm T (f - p) ^ 2 := by
    unfold shortVNorm
    rw [hvs]
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hv
  have hH : shortH1Norm T f ^ 2 = shortH1Norm T p ^ 2 + shortH1Norm T (f - p) ^ 2 := by
    unfold shortH1Norm
    rw [hhs]
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hh
  refine ⟨hV, hH, ?_, ?_, ?_, ?_⟩
  all_goals
    nlinarith [short_v_norm_nonneg T f, short_v_norm_nonneg T p,
      short_v_norm_nonneg T (f - p), short_h1_norm_nonneg T f,
      short_h1_norm_nonneg T p, short_h1_norm_nonneg T (f - p),
      sq_nonneg (shortVNorm T p), sq_nonneg (shortVNorm T (f - p)),
      sq_nonneg (shortH1Norm T p), sq_nonneg (shortH1Norm T (f - p))]

def shortFourierProjectionH4 (I : Finset ℤ) (f : circleH4Domain T) : circleH4Domain T :=
  ⟨circleFourierProjection T I (f : CircleL2 T),
    circleFourierProjection T I (circleH4Jet T f).first,
    circleFourierProjection T I (circleH4Jet T f).second,
    circleFourierProjection T I (circleH4Jet T f).third,
    circleFourierProjection T I (circleH4Jet T f).fourth,
    circle_fourier_projection_weak_deriv T I _ _ (circleH4Jet T f).hfirst,
    circle_fourier_projection_weak_deriv T I _ _ (circleH4Jet T f).hsecond,
    circle_fourier_projection_weak_deriv T I _ _ (circleH4Jet T f).hthird,
    circle_fourier_projection_weak_deriv T I _ _ (circleH4Jet T f).hfourth⟩

theorem short_fourier_projection_h4_fourier (I : Finset ℤ) (f : circleH4Domain T) (n : ℤ) :
    fourierCoeff (shortFourierProjectionH4 T I f : CircleL2 T) n =
      if n ∈ I then fourierCoeff (f : CircleL2 T) n else 0 :=
  circle_fourier_projection_fourier T I _ n

/-- Every finite Fourier projection is orthogonal and contractive in both
angular-coordinate norms, including its complementary projection. -/
theorem short_fourier_projection_decomposition (I : Finset ℤ) (f : circleH4Domain T) :
    let p := shortFourierProjectionH4 T I f
    inner ℂ (shortVJet T p) (shortVJet T (f - p)) = 0 ∧
    inner ℂ (shortH1Jet T p) (shortH1Jet T (f - p)) = 0 ∧
    (shortVNorm T f ^ 2 = shortVNorm T p ^ 2 + shortVNorm T (f - p) ^ 2) ∧
    (shortH1Norm T f ^ 2 = shortH1Norm T p ^ 2 + shortH1Norm T (f - p) ^ 2) ∧
    shortVNorm T p ≤ shortVNorm T f ∧ shortVNorm T (f - p) ≤ shortVNorm T f ∧
    shortH1Norm T p ≤ shortH1Norm T f ∧ shortH1Norm T (f - p) ≤ shortH1Norm T f := by
  dsimp only
  have ho := short_jet_inner_zero_of_fourier_disjoint T
    (shortFourierProjectionH4 T I f) (f - shortFourierProjectionH4 T I f) (by
      intro n
      have hsub : fourierCoeff ((f - shortFourierProjectionH4 T I f : circleH4Domain T) :
          CircleL2 T) n = fourierCoeff (f : CircleL2 T) n -
          fourierCoeff (shortFourierProjectionH4 T I f : CircleL2 T) n := by
        simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply,
          Submodule.coe_sub, inner_sub_right]
      rw [hsub, short_fourier_projection_h4_fourier]
      by_cases hn : n ∈ I
      · exact Or.inr (by rw [if_pos hn, sub_self])
      · exact Or.inl (if_neg hn))
  exact ⟨ho.1, ho.2, short_norm_decomposition T _ _ ho.1 ho.2⟩

/-- The first sine/cosine frequency eigenspace projection has the same
orthogonality in V and H1 as in L2.  This applies to the actual unit anchor
and hence to P0 and I-P0, without assuming either weighted contraction. -/
theorem short_frequency_two_projection_decomposition (a f : circleH4Domain T)
    (ha : inner ℂ (a : CircleL2 T) (a : CircleL2 T) = 1)
    (ha₀ : fourierCoeff (a : CircleL2 T) 0 = 0)
    (ha₂ : (circleH4Jet T a).second =
      ((-4 * shortAngularFrequency T ^ 2 : ℝ) : ℂ) • (a : CircleL2 T)) :
    let p := inner ℂ (a : CircleL2 T) (f : CircleL2 T) • a
    inner ℂ (shortVJet T p) (shortVJet T (f - p)) = 0 ∧
    inner ℂ (shortH1Jet T p) (shortH1Jet T (f - p)) = 0 ∧
    (shortVNorm T f ^ 2 = shortVNorm T p ^ 2 + shortVNorm T (f - p) ^ 2) ∧
    (shortH1Norm T f ^ 2 = shortH1Norm T p ^ 2 + shortH1Norm T (f - p) ^ 2) ∧
    shortVNorm T p ≤ shortVNorm T f ∧ shortVNorm T (f - p) ≤ shortVNorm T f ∧
    shortH1Norm T p ≤ shortH1Norm T f ∧ shortH1Norm T (f - p) ≤ shortH1Norm T f := by
  let c := inner ℂ (a : CircleL2 T) (f : CircleL2 T)
  let p : circleH4Domain T := c • a
  let r : circleH4Domain T := f - p
  have har : inner ℂ (a : CircleL2 T) (r : CircleL2 T) = 0 := by
    simp only [r, p, Submodule.coe_sub, Submodule.coe_smul_of_tower,
      inner_sub_right, inner_smul_right, ha, mul_one, c, sub_self]
  have har₂ : inner ℂ (a : CircleL2 T) (circleH4Jet T r).second = 0 := by
    rw [← circle_h4_second_green T a r, ha₂, inner_smul_left, har, mul_zero]
  have hfirst : inner ℂ (circleH4Jet T a).first (circleH4Jet T r).first = 0 := by
    rw [circle_weak_integration_by_parts T _ _ _ _
      (circleH4Jet T a).hfirst (circleH4Jet T r).hsecond, har₂, neg_zero]
  have hsecond : inner ℂ (circleH4Jet T a).second (circleH4Jet T r).second = 0 := by
    rw [ha₂, inner_smul_left, har₂, mul_zero]
  have hp₀ : fourierCoeff (p : CircleL2 T) 0 = 0 := by
    change fourierCoeff (c • (a : CircleL2 T)) 0 = 0
    rw [circle_fourierCoeff_smul, ha₀, mul_zero]
  have hp₁ : (circleH4Jet T p).first = c • (circleH4Jet T a).first := by
    rw [show p = c • a from rfl, circle_h4_jet_smul]
    rfl
  have hp₂ : (circleH4Jet T p).second = c • (circleH4Jet T a).second := by
    rw [show p = c • a from rfl, circle_h4_jet_smul]
    rfl
  have hpbase : inner ℂ (p : CircleL2 T) (r : CircleL2 T) = 0 := by
    change inner ℂ (c • (a : CircleL2 T)) (r : CircleL2 T) = 0
    rw [inner_smul_left, har, mul_zero]
  have hv : inner ℂ (shortVJet T p) (shortVJet T r) = 0 := by
    change inner ℂ (fourierCoeff (p : CircleL2 T) 0) (fourierCoeff (r : CircleL2 T) 0) +
      inner ℂ (((shortAngularFrequency T)⁻¹ ^ 2 : ℝ) • (circleH4Jet T p).second)
        (((shortAngularFrequency T)⁻¹ ^ 2 : ℝ) • (circleH4Jet T r).second) = 0
    rw [hp₀, inner_zero_left, zero_add, hp₂]
    simp only [inner_smul_left_eq_star_smul, inner_smul_right_eq_smul,
      hsecond, smul_zero]
  have hh : inner ℂ (shortH1Jet T p) (shortH1Jet T r) = 0 := by
    change inner ℂ (p : CircleL2 T) (r : CircleL2 T) +
      inner ℂ ((shortAngularFrequency T)⁻¹ • (circleH4Jet T p).first)
        ((shortAngularFrequency T)⁻¹ • (circleH4Jet T r).first) = 0
    rw [hpbase, zero_add, hp₁]
    simp only [inner_smul_left_eq_star_smul, inner_smul_right_eq_smul,
      hfirst, smul_zero]
  exact ⟨hv, hh, short_norm_decomposition T f p hv hh⟩

theorem short_anchor_second_derivative :
    (circleH4Jet T (circleHouseholderAnchorH4 T)).second =
      ((-4 * shortAngularFrequency T ^ 2 : ℝ) : ℂ) • circleHouseholderAnchor T := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_deriv T _ _
      (circleH4Jet T (circleHouseholderAnchorH4 T)).hsecond,
    fourier_of_weak_circle_deriv T _ _
      (circleH4Jet T (circleHouseholderAnchorH4 T)).hfirst,
    circle_householder_anchor_h4_coe, circle_fourierCoeff_smul,
    circle_householder_anchor_fourier]
  by_cases hp : n = 2
  · subst n
    norm_num [circleFrequencyFactor, shortAngularFrequency, mul_pow, Complex.I_sq]
    push_cast
    ring_nf <;> simp [Complex.I_sq]
  by_cases hm : n = -2
  · subst n
    norm_num [circleFrequencyFactor, shortAngularFrequency, mul_pow, Complex.I_sq]
    push_cast
    ring_nf <;> simp [Complex.I_sq]
  · simp only [if_neg hp, if_neg hm, sub_self, mul_zero]

/-- In particular, the actual fixed neutral projection P0 and its complement
are orthogonal and contractive for both angular-coordinate norms. -/
theorem short_anchor_projection_decomposition (f : circleH4Domain T) :
    let p := inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) •
      circleHouseholderAnchorH4 T
    inner ℂ (shortVJet T p) (shortVJet T (f - p)) = 0 ∧
    inner ℂ (shortH1Jet T p) (shortH1Jet T (f - p)) = 0 ∧
    (shortVNorm T f ^ 2 = shortVNorm T p ^ 2 + shortVNorm T (f - p) ^ 2) ∧
    (shortH1Norm T f ^ 2 = shortH1Norm T p ^ 2 + shortH1Norm T (f - p) ^ 2) ∧
    shortVNorm T p ≤ shortVNorm T f ∧ shortVNorm T (f - p) ≤ shortVNorm T f ∧
    shortH1Norm T p ≤ shortH1Norm T f ∧ shortH1Norm T (f - p) ≤ shortH1Norm T f := by
  have ha₀ : fourierCoeff (circleHouseholderAnchor T) 0 = 0 := by
    norm_num [circle_householder_anchor_fourier]
  simpa only [circle_householder_anchor_h4_coe] using
    short_frequency_two_projection_decomposition T (circleHouseholderAnchorH4 T) f
      (by simpa only [circle_householder_anchor_h4_coe] using circle_householder_anchor_unit T)
      ha₀ (short_anchor_second_derivative T)

end Lemniscate
