import Lemniscate.PeriodicParabolicH2EnergyIdentity
import Lemniscate.PeriodicSobolevEnergyNorm
import Lemniscate.PeriodicParabolicEstimates
import Lemniscate.PeriodicSobolevPrincipalEstimate
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Uniqueness in a small continuous-H2 neighborhood of the actual parabolic space.

The mixed H2-H4 remainder and principal elliptic estimate give a difference
energy inequality with a genuine integrable time coefficient. The Bochner
energy identity and an absolutely continuous integrating factor force the
difference to vanish. No small maximal-regularity norm is required.
-/

noncomputable section
namespace Lemniscate
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

private theorem ac_comp_of_dist_control
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (K : ℝ≥0)
    (hcontrol : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b,
      dist (g (f x)) (g (f y)) ≤ (K:ℝ)*dist (f x) (f y)) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  refine squeeze_zero' (Eventually.of_forall (fun _ =>
    Finset.sum_nonneg (fun _ _ => dist_nonneg))) ?_
    (by simpa using hf.const_mul (K:ℝ))
  rw [eventually_inf_principal]
  filter_upwards with J hJ
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hJi := (show J ∈ AbsolutelyContinuousOnInterval.disjWithin a b from hJ)
  simp only [AbsolutelyContinuousOnInterval.disjWithin,mem_ofPred_eq] at hJi
  exact hcontrol _ (hJi.1 i hi).1 _ (hJi.1 i hi).2

private theorem scalar_exp_ac {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (f x)) a b := by
  obtain ⟨C,hC⟩ := hf.exists_bound
  have hin (x : ℝ) (hx : x ∈ uIcc a b) : f x ∈ Icc (-C) C := by
    have hh := hC x hx
    rw [Real.norm_eq_abs] at hh
    exact abs_le.mp hh
  have hsmooth : ContDiffOn ℝ 1 Real.exp (Icc (-C) C) := Real.contDiff_exp.contDiffOn
  obtain ⟨K,hK⟩ := hsmooth.exists_lipschitzOnWith (by decide)
    (convex_Icc _ _) isCompact_Icc
  exact ac_comp_of_dist_control hf K
    (fun x hx y hy => hK.dist_le_mul _ (hin x hx) _ (hin y hy))

private theorem unit_interval_primitive_zero_of_integrable_coefficient
    (E J k : unitInterval → ℝ)
    (hE : ∀ t, 0 ≤ E t) (hE0 : E 0 = 0)
    (hJint : Integrable J volume) (hkint : Integrable k volume)
    (hprimitive : ∀ t : unitInterval,
      E t-E 0 = ∫ r in Iic t, J r ∂volume)
    (hbound : ∀ᵐ t ∂volume, J t ≤ k t*E t) :
    ∀ t : unitInterval, E t = 0 := by
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  have hclamp (t : unitInterval) : clamp (t:ℝ) = t := Set.projIcc_val zero_le_one t
  let j : ℝ → ℝ := fun r => J (clamp r)
  let l : ℝ → ℝ := fun r => k (clamp r)
  have hjOn : IntegrableOn j (Icc (0:ℝ) 1) volume := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).mp
    simpa only [Function.comp_def,j,hclamp] using hJint
  have hlOn : IntegrableOn l (Icc (0:ℝ) 1) volume := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).mp
    simpa only [Function.comp_def,l,hclamp] using hkint
  have hj : IntervalIntegrable j volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hjOn
  have hl : IntervalIntegrable l volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hlOn
  let P : ℝ → ℝ := fun r => E 0+∫ s in (0:ℝ)..r, j s
  let A : ℝ → ℝ := fun r => -(∫ s in (0:ℝ)..r, l s)
  have hP (t : unitInterval) : P (t:ℝ) = E t := by
    have hp := hprimitive t
    change E 0+(∫ r in (0:ℝ)..(t:ℝ), j r) = E t
    rw [← unit_interval_setIntegral j t]
    have hi : (∫ r in Iic t, j (r:ℝ) ∂volume) = ∫ r in Iic t, J r ∂volume := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro r _
      simp only [j,hclamp]
    rw [hi,← hp]
    ring
  have hconstant : AbsolutelyContinuousOnInterval (fun _ : ℝ => E 0) 0 1 :=
    (show ContDiffOn ℝ 1 (fun _ : ℝ => E 0) (uIcc 0 1) from
      contDiff_const.contDiffOn).absolutelyContinuousOnInterval
  have hPac : AbsolutelyContinuousOnInterval P 0 1 :=
    hconstant.fun_add (hj.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hAac : AbsolutelyContinuousOnInterval A 0 1 :=
    (hl.absolutelyContinuousOnInterval_intervalIntegral (by simp)).neg
  let W : ℝ → ℝ := fun r => Real.exp (A r)*P r
  have hWac : AbsolutelyContinuousOnInterval W 0 1 := (scalar_exp_ac hAac).fun_mul hPac
  have hBrestrict : ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) 1), j r ≤ l r*P r := by
    rw [← unitInterval.measurePreserving_coe.map_eq]
    apply unitInterval.measurableEmbedding_coe.ae_map_iff.mpr
    filter_upwards [hbound] with t ht
    simpa only [j,l,hclamp,hP] using ht
  have hB : ∀ᵐ r ∂volume, r ∈ uIcc (0:ℝ) 1 → j r ≤ l r*P r := by
    rw [uIcc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Icc).mp hBrestrict
  have hWderiv : ∀ᵐ r ∂volume, r ∈ uIcc (0:ℝ) 1 → deriv W r ≤ 0 := by
    filter_upwards [hj.ae_hasDerivAt_integral,hl.ae_hasDerivAt_integral,hB]
      with r hjr hlr hBr hmem
    have hPr : HasDerivAt P (j r) r := (hjr hmem 0 (by simp)).const_add (E 0)
    have hAr : HasDerivAt A (-l r) r := (hlr hmem 0 (by simp)).neg
    have hWr : HasDerivAt W (Real.exp (A r)*(j r-l r*P r)) r := by
      convert! hAr.exp.mul hPr using 1 <;> ring
    rw [hWr.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (hBr hmem))
  intro t
  have hWtac : AbsolutelyContinuousOnInterval W 0 (t:ℝ) :=
    hWac.mono (uIcc_subset_uIcc (by simp) (by
      simpa only [uIcc_of_le zero_le_one] using t.property))
  have hWint : (∫ r in (0:ℝ)..(t:ℝ), deriv W r) ≤ 0 := by
    rw [intervalIntegral.integral_of_le t.property.1]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_of_ae hWderiv,ae_restrict_mem measurableSet_Ioc] with r hr hrt
    exact hr (by rw [uIcc_of_le zero_le_one]; exact ⟨hrt.1.le,hrt.2.trans t.property.2⟩)
  have hWzero : W 0 = 0 := by simp [W,P,A,hE0]
  have hWtle : W (t:ℝ) ≤ 0 := by
    have hd : W (t:ℝ)-W 0 ≤ 0 := by rw [← hWtac.integral_deriv_eq_sub]; exact hWint
    rwa [hWzero,sub_zero] at hd
  have hWeq : Real.exp (A (t:ℝ))*E t = 0 :=
    le_antisymm (by simpa only [W,hP t] using hWtle)
      (mul_nonneg (Real.exp_pos _).le (hE t))
  exact (mul_eq_zero.mp hWeq).resolve_left (Real.exp_pos _).ne'

private theorem difference_energy_real
    (p H n x y B C δ E e R : ℝ)
    (hp : 0 ≤ p) (hH : 0 ≤ H) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hn : n ≤ 10*p) (hEnorm : H^2 ≤ 2*E)
    (hδ : 20*C*δ ≤ 1/4)
    (hR : R ≤ C*(2*δ*n+(x+y)*H))
    (he : e ≤ -p^2+p*(B*H+R)) (hδpos : 0 ≤ δ) :
    e ≤ (6*(1+B^2+C^2))*(1+x^2+y^2)*E := by
  have hE : 0 ≤ E := by nlinarith only [hEnorm,sq_nonneg H]
  have hR' : R ≤ 20*C*δ*p+C*(x+y)*H := by
    calc
      R ≤ C*(2*δ*n+(x+y)*H) := hR
      _ ≤ C*(2*δ*(10*p)+(x+y)*H) := by gcongr
      _ = 20*C*δ*p+C*(x+y)*H := by ring
  let b := B+C*(x+y)
  have hY : p*b*H ≤ p^2/4+b^2*H^2 := by
    nlinarith only [sq_nonneg (p/2-b*H)]
  have he' : e ≤ b^2*H^2 := by
    have hmul := mul_le_mul_of_nonneg_right hδ (sq_nonneg p)
    have hh := mul_le_mul_of_nonneg_left hR' hp
    dsimp only [b] at hY ⊢
    nlinarith only [he,hh,hmul,hY,sq_nonneg p]
  let A := 1+B^2+C^2
  have hAs : 0 ≤ A := by dsimp only [A]; positivity
  have hBA : B^2 ≤ A := by dsimp only [A]; nlinarith only [sq_nonneg C]
  have hCA : C^2 ≤ A := by dsimp only [A]; nlinarith only [sq_nonneg B]
  have hb3 : b^2 ≤ 3*(B^2+C^2*x^2+C^2*y^2) := by
    dsimp only [b]
    nlinarith only [sq_nonneg (B-C*x),sq_nonneg (B-C*y),sq_nonneg (C*x-C*y)]
  have hbA : b^2 ≤ 3*A*(1+x^2+y^2) := by
    calc
      b^2 ≤ 3*(B^2+C^2*x^2+C^2*y^2) := hb3
      _ ≤ 3*(A+A*x^2+A*y^2) := by gcongr
      _ = 3*A*(1+x^2+y^2) := by ring
  calc
    e ≤ b^2*H^2 := he'
    _ ≤ b^2*(2*E) := mul_le_mul_of_nonneg_left hEnorm (sq_nonneg b)
    _ ≤ (3*A*(1+x^2+y^2))*(2*E) :=
      mul_le_mul_of_nonneg_right hbA (mul_nonneg (by norm_num) hE)
    _ = (6*(1+B^2+C^2))*(1+x^2+y^2)*E := by dsimp only [A]; ring

private theorem linear_part_rearrange {G : Type*} [AddCommGroup G]
    (p b d : G) (h : p-b = -d) : d = -p+b := by
  calc
    d = -(-d) := (neg_neg d).symm
    _ = -(p-b) := congrArg Neg.neg h.symm
    _ = b-p := neg_sub p b
    _ = -p+b := sub_eq_neg_add b p

section Actual
open Complex
variable (T : ℝ) [Fact (0 < T)]

private def uniquenessH2Inclusion :
    CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
  (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)

private theorem nonlinear_difference_energy
    (F : CircleSobolevSpace T 4 → CircleL2 T)
    (D : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T)
    (hBA : ∀ f, circleSobolevPrincipalOperator T f-B (uniquenessH2Inclusion T f) = -(D f))
    (δ₀ C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδ₀ : δ ≤ δ₀)
    (habsorb : 20*C*δ ≤ 1/4)
    (htame : ∀ f g : CircleSobolevSpace T 4,
      ‖uniquenessH2Inclusion T f‖ < δ₀ → ‖uniquenessH2Inclusion T g‖ < δ₀ →
      ‖F f-F g-D (f-g)‖ ≤ C*
        ((‖uniquenessH2Inclusion T f‖+‖uniquenessH2Inclusion T g‖)*‖f-g‖+
          (‖f‖+‖g‖)*‖uniquenessH2Inclusion T (f-g)‖))
    (f g : CircleSobolevSpace T 4)
    (hf : ‖uniquenessH2Inclusion T f‖ < δ) (hg : ‖uniquenessH2Inclusion T g‖ < δ) :
    (inner ℂ (circleSobolevPrincipalOperator T (f-g)) (F f-F g)).re ≤
      (6*(1+‖B‖^2+C^2))*(1+‖f‖^2+‖g‖^2)*
        (‖circleSobolevCoordinate T 4 0 (f-g)‖^2+
          4*‖circleSobolevCoordinate T 4 2 (f-g)‖^2) := by
  let w := f-g
  let P := circleSobolevPrincipalOperator T w
  let R := F f-F g-D w
  let E := ‖circleSobolevCoordinate T 4 0 w‖^2+4*‖circleSobolevCoordinate T 4 2 w‖^2
  have hlinear : D w = -P+B (uniquenessH2Inclusion T w) := by
    have hh := hBA w
    change P-B (uniquenessH2Inclusion T w) = -(D w) at hh
    exact linear_part_rearrange P (B (uniquenessH2Inclusion T w)) (D w) hh
  have hF : F f-F g = -P+B (uniquenessH2Inclusion T w)+R := by
    dsimp only [R]
    rw [hlinear]
    abel
  have hR : ‖R‖ ≤ C*(2*δ*‖w‖+(‖f‖+‖g‖)*‖uniquenessH2Inclusion T w‖) := by
    have hh := htame f g (hf.trans_le hδ₀) (hg.trans_le hδ₀)
    calc
      ‖R‖ ≤ C*((‖uniquenessH2Inclusion T f‖+‖uniquenessH2Inclusion T g‖)*‖w‖+
          (‖f‖+‖g‖)*‖uniquenessH2Inclusion T w‖) := hh
      _ ≤ C*(2*δ*‖w‖+(‖f‖+‖g‖)*‖uniquenessH2Inclusion T w‖) := by
        gcongr <;> linarith only [hf,hg]
  have hN : ‖w‖ ≤ 10*‖P‖ := circle_sobolev_principal_estimate T w
  have hnorm : ‖uniquenessH2Inclusion T w‖^2 ≤ 2*E := by
    have hh := (circle_sobolev_energy_norm_equivalence T (0 : CircleL2 T →L[ℂ] CircleL2 T)
      0 (by norm_num) (uniquenessH2Inclusion T w)).1
    simpa only [uniquenessH2Inclusion,ContinuousLinearMap.comp_apply,
      circle_sobolev_inclusion_coordinate,circle_sobolev_coordinate_apply,zero_mul,add_zero]
      using! hh
  have he : (inner ℂ P (F f-F g)).re ≤
      -‖P‖^2+‖P‖*(‖B‖*‖uniquenessH2Inclusion T w‖+‖R‖) := by
    rw [hF]
    have hb : (inner ℂ P (B (uniquenessH2Inclusion T w))).re ≤
        ‖P‖*(‖B‖*‖uniquenessH2Inclusion T w‖) := by
      simpa only [RCLike.re_eq_complex_re] using
        (re_inner_le_norm (𝕜 := ℂ) P (B (uniquenessH2Inclusion T w))).trans
          (mul_le_mul_of_nonneg_left (B.le_opNorm (uniquenessH2Inclusion T w)) (norm_nonneg P))
    have hr : (inner ℂ P R).re ≤ ‖P‖*‖R‖ := by
      simpa only [RCLike.re_eq_complex_re] using re_inner_le_norm (𝕜 := ℂ) P R
    have hself : (inner ℂ P P).re = ‖P‖^2 := by
      simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) P).symm
    simp only [inner_add_right,inner_neg_right,Complex.add_re,Complex.neg_re,hself]
    calc
      -‖P‖^2+(inner ℂ P (B (uniquenessH2Inclusion T w))).re+(inner ℂ P R).re ≤
          -‖P‖^2+‖P‖*(‖B‖*‖uniquenessH2Inclusion T w‖)+‖P‖*‖R‖ :=
        add_le_add (add_le_add (le_refl (-‖P‖^2)) hb) hr
      _ = -‖P‖^2+‖P‖*(‖B‖*‖uniquenessH2Inclusion T w‖+‖R‖) := by ring
  exact difference_energy_real ‖P‖ ‖uniquenessH2Inclusion T w‖ ‖w‖ ‖f‖ ‖g‖ ‖B‖ C δ E
    (inner ℂ P (F f-F g)).re ‖R‖ (norm_nonneg P) (norm_nonneg (uniquenessH2Inclusion T w))
    B.opNorm_nonneg hC hN hnorm habsorb hR he hδ

private theorem parabolic_map_sub_ae
    {E G : Type*} [NormedAddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : E →L[ℂ] Lp G 2 (volume : Measure unitInterval)) (U V : E) :
    (L (U-V) : unitInterval → G) =ᵐ[volume] fun r => L U r-L V r := by
  have heq := L.map_sub U V
  filter_upwards [Lp.coeFn_sub (L U) (L V)] with r hr
  exact (congrArg (fun z : Lp G 2 (volume : Measure unitInterval) => z r) heq).trans
    (by simpa only [Pi.sub_apply] using hr)

set_option maxHeartbeats 1200000 in
/-- Uniqueness in the actual parabolic class requires only small continuous
H2 curves and a common initial value, without a small parabolic-norm bound. -/
theorem circle_parabolic_nonlinear_uniqueness
    (F : CircleSobolevSpace T 4 → CircleL2 T)
    (D : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T)
    (hBA : ∀ f, circleSobolevPrincipalOperator T f-
      B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) = -(D f))
    (δ₀ C : ℝ) (hδ₀ : 0 < δ₀) (hC : 0 ≤ C)
    (htame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ₀ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ₀ →
      ‖F f-F g-D (f-g)‖ ≤ C*
        ((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖)) :
    ∃ δ > 0, δ ≤ δ₀ ∧ ∀ τ : ℝ, 0 < τ → ∀ U V : CircleParabolicSpace T τ,
      circleParabolicInitialValue T τ U = circleParabolicInitialValue T τ V →
      ‖circleParabolicCurve T τ U‖ < δ → ‖circleParabolicCurve T τ V‖ < δ →
      (∀ᵐ r : unitInterval ∂volume, circleParabolicTimeDerivative T τ U r = F (circleParabolicH4 T τ U r)) →
      (∀ᵐ r : unitInterval ∂volume, circleParabolicTimeDerivative T τ V r = F (circleParabolicH4 T τ V r)) →
      U = V := by
  let δ := min δ₀ (1/(80*C+1))
  have hden : 0 < 80*C+1 := by positivity
  have hδ : 0 < δ := lt_min hδ₀ (one_div_pos.mpr hden)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have habsorb : 20*C*δ ≤ 1/4 := by
    have hh := (le_div_iff₀ hden).mp (min_le_right δ₀ (1/(80*C+1)))
    change δ*(80*C+1) ≤ 1 at hh
    nlinarith only [hh,hδ.le]
  refine ⟨δ,hδ,hδle,?_⟩
  intro τ hτ U V hinit hU hV hPU hPV
  let W : CircleParabolicSpace T τ := U-V
  let f := circleParabolicH4 T τ U
  let g := circleParabolicH4 T τ V
  let w := circleParabolicH4 T τ W
  let v := circleParabolicTimeDerivative T τ W
  let A : CircleTimeL2 T := (circleSobolevPrincipalOperator T).compLpL 2 volume w
  let E : unitInterval → ℝ := fun r =>
    ‖circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ W r)‖^2+
      4*‖circleSobolevCoordinate T 2 2 (circleParabolicCurve T τ W r)‖^2
  let J : unitInterval → ℝ := fun r => (2*τ)*(inner ℂ (A r) (v r)).re
  let K : ℝ := 6*(1+‖B‖^2+C^2)
  let k : unitInterval → ℝ := fun r => (2*τ*K)*(1+‖f r‖^2+‖g r‖^2)
  have hW4 : ∀ᵐ r ∂volume, w r = f r-g r := by
    simpa only [W,w,f,g] using! parabolic_map_sub_ae (circleParabolicH4 T τ) U V
  have hWv := parabolic_map_sub_ae (circleParabolicTimeDerivative T τ) U V
  have hWA := (circleSobolevPrincipalOperator T).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) w
  have hWval := circle_parabolic_value_ae T τ W
  have hWlow := circle_parabolic_h2_h4_ae T τ W
  have hsmallU : ∀ᵐ r ∂volume, ‖uniquenessH2Inclusion T (f r)‖ < δ := by
    filter_upwards [circle_parabolic_h2_h4_ae T τ U] with r hr
    have hn := congrArg (fun z : CircleSobolevSpace T 2 => ‖z‖) hr
    exact hn.symm.le.trans_lt (((circleParabolicCurve T τ U).norm_coe_le_norm r).trans_lt hU)
  have hsmallV : ∀ᵐ r ∂volume, ‖uniquenessH2Inclusion T (g r)‖ < δ := by
    filter_upwards [circle_parabolic_h2_h4_ae T τ V] with r hr
    have hn := congrArg (fun z : CircleSobolevSpace T 2 => ‖z‖) hr
    exact hn.symm.le.trans_lt (((circleParabolicCurve T τ V).norm_coe_le_norm r).trans_lt hV)
  have hE0 : E 0 = 0 := by
    have hi : circleParabolicInitialValue T τ W = 0 := by
      calc
        circleParabolicInitialValue T τ W = circleParabolicInitialValue T τ U-circleParabolicInitialValue T τ V :=
          (circleParabolicInitialValue T τ).map_sub U V
        _ = 0 := sub_eq_zero.mpr hinit
    change circleParabolicCurve T τ W 0 = 0 at hi
    simp only [E,hi,map_zero,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,add_zero]
  have hint : Integrable (fun r : unitInterval => (inner ℂ (A r) (v r)).re) volume := by
    simpa only [RCLike.reCLM_apply,RCLike.re_eq_complex_re] using
      (RCLike.reCLM : ℂ →L[ℝ] ℝ).integrable_comp (L2.integrable_inner (𝕜 := ℂ) A v)
  have hJint : Integrable J volume := hint.const_mul (2*τ)
  have hfint : Integrable (fun r : unitInterval => ‖f r‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hgint : Integrable (fun r : unitInterval => ‖g r‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hkint : Integrable k volume :=
    (((integrable_const (1:ℝ)).add hfint).add hgint).const_mul (2*τ*K)
  have hprimitive (t : unitInterval) : E t-E 0 = ∫ r in Iic t, J r ∂volume := by
    have hh := circle_parabolic_h2_energy_identity T τ W t
    have hi : (∫ r in Iic t,
        (inner ℂ (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ W r)+
          (4:ℂ) • circleSobolevCoordinate T 4 4 (w r)) (v r)).re ∂volume) =
        ∫ r in Iic t, (inner ℂ (A r) (v r)).re ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hWval,ae_restrict_of_ae hWA] with r hr hAr
      rw [hr,hAr] <;> rfl
    exact (hh.trans (congrArg ((2*τ)*·) hi)).trans (integral_const_mul (2*τ) _).symm
  have hbound : ∀ᵐ r ∂volume, J r ≤ k r*E r := by
    filter_upwards [hW4,hWv,hWA,hWlow,hsmallU,hsmallV,hPU,hPV]
      with r hwr hvr hAr hlowr hfr hgr hpur hpvr
    have hb := nonlinear_difference_energy T F D B hBA δ₀ C δ hC hδ.le hδle habsorb
      htame (f r) (g r) hfr hgr
    change circleParabolicCurve T τ W r =
      circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (w r)) at hlowr
    have hq : circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ W r) =
        circleSobolevCoordinate T 4 0 (f r-g r) := by
      have hh : circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ W r) =
          circleSobolevCoordinate T 4 0 (w r) :=
        (congrArg (circleSobolevCoordinate T 2 0) hlowr).trans (by rfl)
      exact hh.trans (congrArg (circleSobolevCoordinate T 4 0) hwr)
    have hd : circleSobolevCoordinate T 2 2 (circleParabolicCurve T τ W r) =
        circleSobolevCoordinate T 4 2 (f r-g r) := by
      have hh : circleSobolevCoordinate T 2 2 (circleParabolicCurve T τ W r) =
          circleSobolevCoordinate T 4 2 (w r) :=
        (congrArg (circleSobolevCoordinate T 2 2) hlowr).trans (by rfl)
      exact hh.trans (congrArg (circleSobolevCoordinate T 4 2) hwr)
    have hva : v r = F (f r)-F (g r) :=
      hvr.trans (congrArg₂ (fun x y : CircleL2 T => x-y) hpur hpvr)
    have hae : A r = circleSobolevPrincipalOperator T (f r-g r) :=
      hAr.trans (congrArg (circleSobolevPrincipalOperator T) hwr)
    have he : (inner ℂ (A r) (v r)).re ≤ K*(1+‖f r‖^2+‖g r‖^2)*E r := by
      simpa only [K,E,hae,hva,hq,hd] using hb
    have hs := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2*τ)
    simpa only [J,k,mul_assoc] using hs
  have hzero := unit_interval_primitive_zero_of_integrable_coefficient E J k
    (fun r => by dsimp only [E]; positivity) hE0 hJint hkint hprimitive hbound
  have hcurve : ∀ r : unitInterval, circleParabolicCurve T τ W r = 0 := by
    intro r
    have hcompare : ‖circleParabolicCurve T τ W r‖^2 ≤ 2*E r := by
      simpa only [E,zero_mul,add_zero] using
        (circle_sobolev_energy_norm_equivalence T (0 : CircleL2 T →L[ℂ] CircleL2 T)
          0 (by norm_num) (circleParabolicCurve T τ W r)).1
    have he : ‖circleParabolicCurve T τ W r‖^2 ≤ 0 :=
      hcompare.trans_eq (by rw [hzero r,mul_zero])
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm he (sq_nonneg _)))
  have hwzero : w = 0 := by
    apply Lp.ext
    filter_upwards [hWval,Lp.coeFn_zero (CircleSobolevSpace T 4) 2
      (volume : Measure unitInterval)] with r hr hzr
    have hw : w r = 0 := by
      apply circle_sobolev_value_injective T 4
      have hh := hr.symm
      simpa only [hcurve r,map_zero] using hh
    exact hw.trans hzr.symm
  have hfg : f = g := by
    have hh := (circleParabolicH4 T τ).map_sub U V
    have hsub : f-g = 0 := hh.symm.trans hwzero
    exact sub_eq_zero.mp hsub
  have hvUV : circleParabolicTimeDerivative T τ U = circleParabolicTimeDerivative T τ V := by
    apply Lp.ext
    filter_upwards [hPU,hPV] with r hr hs
    have hh := congrArg (fun z : CircleTimeH4 T => z r) hfg
    exact hr.trans ((congrArg F hh).trans hs.symm)
  have hcUV : circleParabolicCurve T τ U = circleParabolicCurve T τ V := by
    have hh := (circleParabolicCurve T τ).map_sub U V
    have hz : circleParabolicCurve T τ W = 0 := by
      apply ContinuousMap.ext
      exact hcurve
    exact sub_eq_zero.mp (hh.symm.trans hz)
  apply Subtype.ext
  exact Prod.ext hcUV (Prod.ext hfg hvUV)

end Actual
end Lemniscate
