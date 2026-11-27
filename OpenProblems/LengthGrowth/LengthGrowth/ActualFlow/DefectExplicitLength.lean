import LengthGrowth.ActualFlow.DefectFlowSublevel

noncomputable section
open Set Filter Topology MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem bending_sublevel_invariant (hf : c.IsNormalFEF)
    (initial : 2*c.normalizedProduct 0≤4*Real.pi^2+36) {t : ℝ} (ht : 0≤t) :
    2*c.normalizedProduct t≤4*Real.pi^2+36 := by
  apply LengthGrowth.DefectFour.sublevel_forward (U:=fun s => 2*c.normalizedProduct s)
    ht (continuousOn_const.mul c.normalizedProduct_continuousOn) initial
  intro s hs eq
  have strict := c.bending_rate_strict hs (by linarith only [eq]) eq.le
  exact ⟨2*(c.energy s*c.lengthRate s-c.length s*c.dissipation s),by linarith,
    (c.normalizedProduct_right_derivative hf hs).const_mul 2⟩

theorem bending_product_antitone (hf : c.IsNormalFEF)
    (initial : 2*c.normalizedProduct 0≤4*Real.pi^2+36) : AntitoneOn c.normalizedProduct (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) c.normalizedProduct_continuousOn
  · rw [interior_Ici]
    exact fun t ht => (c.normalizedProduct_hasDerivAt_normal hf ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    have pos : 0<t := ht
    have low : 2*Real.pi^2≤c.normalizedProduct t := c.sharp_energy_length pos.le
    have hd := c.normalizedProduct_hasDerivAt_normal hf pos
    rw [hd.deriv]
    rcases lt_or_eq_of_le low with above|floor
    · have h := c.bending_rate_strict pos.le (by linarith only [above])
        (c.bending_sublevel_invariant hf initial pos.le)
      linarith
    · have hmin : IsLocalMin c.normalizedProduct t := by
        filter_upwards [lt_mem_nhds pos] with x hx
        exact floor ▸ (c.sharp_energy_length (le_of_lt hx))
      exact (hmin.hasDerivAt_eq_zero hd).le

/-- The explicit physical-time estimate including the original length at
time zero; the normalization is U = 2 E L. -/
theorem bending_explicit_length (hf : c.IsNormalFEF)
    (initial : 2*c.normalizedProduct 0≤4*Real.pi^2+36) {t : ℝ} (ht : 0≤t) :
    c.length t≤2*c.length 0 ∨ c.length t^4≤4*(2*c.normalizedProduct 0)^2*t := by
  by_cases short : c.length t≤2*c.length 0
  · exact Or.inl short
  right
  have half : c.length t/2∈Icc (c.length 0) (c.length t) :=
    ⟨by linarith,by linarith [c.length_pos ht]⟩
  obtain ⟨s,hs,eq⟩ := intermediate_value_Icc ht (c.length_continuousOn.mono Icc_subset_Ici_self) half
  have sec := c.secant_sq_le_energy_drop hf hs.1 hs.2
  rw [show c.length t-c.length s=c.length s by linarith only [eq]] at sec
  have sq : c.length s^2≤t*c.energy s^2 := by
    nlinarith only [sec,mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg (c.energy t)),
      mul_nonneg hs.1 (sq_nonneg (c.energy s))]
  have anti := c.bending_product_antitone hf initial self_mem_Ici hs.1 hs.1
  have asq := pow_le_pow_left₀ (c.normalizedProduct_nonneg s) anti 2
  have prod : c.length s^4≤t*(c.normalizedProduct 0)^2 := by
    have b := mul_le_mul_of_nonneg_left asq ht
    unfold normalizedProduct at b
    change c.length s^4≤t*(c.energy 0*c.length 0)^2
    linarith only [b,mul_le_mul_of_nonneg_right sq (sq_nonneg (c.length s))]
  rw [eq] at prod
  linarith only [prod]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.bending_explicit_length
