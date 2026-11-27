import LengthGrowth.ActualFlow.DefectFourBarrier

noncomputable section
open Set Filter Topology

namespace LengthGrowth.DefectFour

/-- The exact normalized signed evolution has negative derivative given the
Fourier and projected-square estimates. The branch W≤0.11 keeps the
favorable signs of the terms involving Q, I3, and I4. -/
theorem signed_evolution_coercive {t x g b p q W C J Z rem Y : ℝ}
    (t0 : 0≤t) (t1 : t≤501/1000) (x0 : 0≤x) (x1 : x≤4/5)
    (b0 : 0≤b) (bg : b≤g) (p0 : 0≤p) (w0 : 0≤W) (wmax : W≤11/100)
    (freq : g≤x*(227/500+(17/500)*t)) (fourth : g*t≤x*(81/500+(17/500)*t^2))
    (proj : p^2≤(t*b)^2-(7/44)*x^2*t^4) (q2 : q≤2) (qz : q≤10*t^2-8*t^4)
    (cubic : |J|≤t^3*b) (nonpos : rem≤0)
    (corr : C=(3/2)*p+g*b/2) (square : C≤1 → (1-C)^2≤Z)
    (signed : Y= -4*Z+q-(16-4*W)*J-(5-W)*(t*b)^2+rem) :
    Y≤ -(1/40) := by
  apply spectral_barrier t0 t1 x0 x1 b0 bg p0 freq fourth proj q2 qz
  change ((3/2)*p+g*b/2≤1 → _)
  intro ha
  have hZ := square (corr ▸ ha)
  have hJ : -(16-4*W)*J≤16*t^3*b := by
    have lower := neg_le_abs J
    have major := mul_le_mul_of_nonneg_left (lower.trans cubic) (show 0≤16-4*W by linarith)
    have scale := mul_le_mul_of_nonneg_right (show 16-4*W≤16 by linarith) (show 0≤t^3*b by positivity)
    linarith only [major,scale]
  have quartic := mul_le_mul_of_nonneg_right (show (489/100:ℝ)≤5-W by linarith) (sq_nonneg (t*b))
  rw [corr] at hZ
  linarith only [signed,hZ,hJ,quartic,nonpos]

/-- Continuous induction at a strict inward boundary; the right derivative
at the initial time is enough even when the initial value is the threshold. -/
theorem sublevel_forward {U : ℝ → ℝ} {C T : ℝ} (T0 : 0≤T)
    (cont : ContinuousOn U (Ici 0)) (initial : U 0≤C)
    (inward : ∀s, 0≤s → U s=C → ∃d : ℝ, d<0 ∧ HasDerivWithinAt U d (Ici 0) s) :
    U T≤C := by
  let S := U ⁻¹' Iic C
  have closed : IsClosed (S ∩ Icc 0 T) := by
    rw [inter_comm]
    exact (cont.mono Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have barrier := closed.Icc_subset_of_forall_mem_nhdsWithin (show 0∈S from initial) (by
    intro s hs
    have ge : 0≤s := hs.2.1
    have inside : U s≤C := hs.1
    have inc : Ioi s ⊆ Ici 0 := fun y hy => ge.trans (le_of_lt hy)
    rcases lt_or_eq_of_le inside with strict|eq
    · have h := (cont s ge).mono inc
      exact Filter.mem_of_superset (h.eventually_lt_const strict)
        (fun y hy => show U y≤C from le_of_lt hy)
    · obtain ⟨d,hd,df⟩ := inward s ge eq
      have neg := ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).mp
        (df.mono inc)).eventually_lt_const hd
      filter_upwards [self_mem_nhdsWithin,neg] with y hy slopeNeg
      rw [slope_def_field] at slopeNeg
      have h : U y - U s < 0 := by
        have hh := (div_lt_iff₀ (sub_pos.mpr hy)).mp slopeNeg
        simpa only [zero_mul] using hh
      exact show U y≤C by linarith)
  exact barrier ⟨T0,le_rfl⟩

end LengthGrowth.DefectFour

namespace LengthGrowth.ActualFlow.ForwardImmersion

/-- The inward derivative implication on the defect-four boundary entails
fourth-root growth for the genuine material length of the same flow. -/
theorem quarter_length_of_defect_four_boundary (c : ForwardImmersion) (hf : c.IsNormalFEF)
    (h0 : 2*c.normalizedProduct 0 ≤ 4*Real.pi^2+4)
    (inward : ∀s, 0≤s → 2*c.normalizedProduct s=4*Real.pi^2+4 →
      ∃d : ℝ, d<0 ∧ HasDerivWithinAt (fun t => 2*c.normalizedProduct t) d (Ici 0) s) :
    c.HasQuarterLengthBound := by
  apply c.quarter_length_of_bounded_absoluteCurvature hf
  apply c.bounded_absoluteCurvature_of_bounded_energyLength
  refine ⟨(4*Real.pi^2+4)/2,fun t ht => ?_⟩
  have h := LengthGrowth.DefectFour.sublevel_forward (U:=fun s => 2*c.normalizedProduct s)
    ht (continuousOn_const.mul c.normalizedProduct_continuousOn) h0 inward
  change c.normalizedProduct t≤_
  linarith

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.DefectFour.signed_evolution_coercive
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_defect_four_boundary
